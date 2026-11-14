"""Validate current build, kernel, comparator and bilingual page evidence."""
from datetime import datetime, timezone
import hashlib
import json
import re

from project_sources import ROOT, declaration_owner, library_sources
from verification_inputs import (
    BUILD_COMMAND, COMPARATOR_AXIOMS, DECLARATIONS, DEPENDENCY_OUTPUTS, FULL_TYPE_CHECK, PUBLICATION,
    build_inputs, comparator_inputs, comparator_targets, manifest_revisions, verification_tool_inputs,
)

AUDIT = 'verification/independent-audit/'
STANDARD_AXIOMS = COMPARATOR_AXIOMS


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(name):
    return json.loads((ROOT / name).read_text())


def digest(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def relative_file(name):
    path = (ROOT / name).resolve()
    require(path.is_relative_to(ROOT), f'Evidence outside the project: {name}')
    require(path.is_file(), f'Missing evidence: {name}')
    return str(path.relative_to(ROOT))


def unique_rows(rows, field):
    values = {row[field]: row for row in rows}
    require(len(values) == len(rows), f'Duplicate {field} in evidence')
    return values


def verify_comparator_inputs(result, manifest):
    config = read(AUDIT + 'comparator-project/comparator.json')
    comparator_targets(manifest, config)
    require(result.get('input_hashes') == comparator_inputs(ROOT, ROOT / AUDIT, manifest),
            'Comparator inputs changed since the run')
    require(result.get('build_sha256') == digest('verification/current-build.json'),
            'Comparator result belongs to a different build')
    require(result.get('independent_full_types_sha256') == digest(AUDIT + 'independent-full-types.json'),
            'Independent full-type output changed since the run')


def validate_current_evidence():
    """Return a new record only after all current evidence has been checked."""
    evidence = set()

    def include(name):
        name = relative_file(name)
        evidence.add(name)
        return name

    build = read(include('verification/current-build.json'))
    require(build['exit_code'] == 0, 'Current project build failed')
    require(build['wall_seconds'] >= 0 and build['command'] == list(BUILD_COMMAND),
            'Incomplete warning-free build record')
    build_start = datetime.fromisoformat(build['start_utc'])
    require(build_start.tzinfo is not None, 'Build timestamp requires a timezone')
    build_log = include(build['log'])
    require(digest(build_log) == build['log_sha256'], 'Build log hash changed')
    require('Build completed successfully' in (ROOT / build_log).read_text(),
            'Current full-build log does not contain successful completion')

    require(build.get('input_hashes') == build_inputs(ROOT),
            'Build inputs differ from the recorded run. Rerun verify_project.py.')
    require(build.get('dependency_revisions') == manifest_revisions(ROOT),
            'The build did not record the pinned dependency revisions')
    for name in build['input_hashes']:
        include(name)
    require(build.get('verification_tool_hashes') == verification_tool_inputs(ROOT),
            'Verification tools differ from the recorded run. Rerun verify_project.py.')
    for name in build['verification_tool_hashes']:
        include(name)

    audits = read(include('verification/current-audits.json'))
    audit_steps = unique_rows(audits, 'label')
    expected_steps = {
        'proof-policy': (['python3', 'scripts/check_proof_policy.py'],
            'verification/current-proof-policy.log'),
        'public-api': (['python3', 'scripts/check_public_api.py'], 'verification/current-public-api.log'),
        'entrypoints': (['python3', 'scripts/check_entrypoints.py'],
            'verification/current-entrypoints.log'),
        'definitions': (['python3', 'scripts/check_definitions.py'], 'verification/current-definitions.log'),
        'types': (['python3', 'scripts/check_reviewed_types.py'], 'verification/current-types.log'),
        'axioms': (['python3', 'scripts/audit_proofs.py'], 'verification/current-axioms.log'),
        'dependency-graph': (['lake', 'env', 'lean',
            DECLARATIONS + 'DeclarationAudit.lean'], DECLARATIONS + 'compile.log'),
        'dependency-analysis': (['python3', DECLARATIONS + 'analyze.py'],
            DECLARATIONS + 'analyze-recheck.log'),
        'dependency-imports': (['python3', PUBLICATION + 'audit_imports.py'],
            PUBLICATION + 'imports-recheck.log'),
        'comparator-prepare': (['python3', AUDIT + 'prepare_comparator.py'],
            'verification/current-comparator-prepare.log'),
        'comparator': (['python3', AUDIT + 'run_comparator.py'], 'verification/current-comparator.log'),
    }
    require(set(audit_steps) == set(expected_steps), 'Incomplete current audit sequence')
    for label, (command, log) in expected_steps.items():
        row = audit_steps[label]
        require(row['exit_code'] == 0 and row['command'] == command and row['log'] == log,
                f'Current audit step failed or differs: {label}')
        require(datetime.fromisoformat(row['start_utc']) >= build_start and row['wall_seconds'] >= 0,
                f'Current audit step predates the build: {label}')
        require(digest(include(log)) == row['log_sha256'], f'Current audit log hash changed: {label}')

    audit_outputs = {
        'proof-policy': ['verification/proof-policy.json'],
        'public-api': ['verification/public-api.json'],
        'entrypoints': ['verification/entrypoints.json'],
        'definitions': ['reviewed-definitions.json'],
        'types': ['reviewed-types.json'],
        'axioms': ['proof-status.json', 'proof-status-raw.json'],
        'comparator': [AUDIT + 'comparator-result.json', AUDIT + 'independent-full-types.json'],
        **DEPENDENCY_OUTPUTS,
    }
    for label, paths in audit_outputs.items():
        require(audit_steps[label].get('output_hashes') == {name: digest(include(name)) for name in paths},
                f'Audit output changed since the run: {label}')

    api = read('verification/public-api.json')
    api_baseline = read('reference/public-api.json')
    require(api['all_preserved'] is True and api['input_hashes'] == build['input_hashes'] and
            api['reference_sha256'] == digest('reference/public-api.json') and
            api['count'] == len(api_baseline['names']) and
            api['signatures'] == api_baseline['signatures'], 'Public API compatibility evidence differs')
    from check_proof_policy import violations
    production_sources = [ROOT / 'ConditionalGoldbach.lean', *library_sources(ROOT)]
    policy_check = read('verification/proof-policy.json')
    require(policy_check == dict(production_files=len(production_sources),
                no_global_overrides=True, all_sources_reachable=True) and
            not any(violations(p.read_text()) for p in production_sources) and
            set(production_sources) == {ROOT / 'ConditionalGoldbach.lean',
                *(ROOT / 'ConditionalGoldbach').rglob('*.lean')}, 'Production proof policy differs')

    from check_entrypoints import enforce
    entrypoints = read('verification/entrypoints.json')
    require(entrypoints['input_hashes'] == build['input_hashes'] and
            entrypoints['dependency_revisions'] == manifest_revisions(ROOT),
            'Entrypoint checks used different build inputs')
    require(entrypoints['policy_sha256'] == digest(include('scripts/entrypoints.json')),
            'Entrypoint policy changed since the run')
    policy = read('scripts/entrypoints.json')['entries']
    consumers = unique_rows(entrypoints['entries'], 'module')
    require(set(consumers) == {e['module'] for e in policy}, 'Entrypoint inventory differs')
    for entry in policy:
        consumer = consumers[entry['module']]
        require(consumer['declarations'] == entry['declarations'] and
                consumer['example'] == entry.get('example', '') and
                consumer['counts'] == enforce(entry, set(consumer['imported_modules'])),
                'Entrypoint exports or import counts differ')

    status = read(include('proof-status.json'))
    raw = unique_rows(read(include('proof-status-raw.json')), 'name')
    require(status['compiled_constants'] == len(raw) and not status['admitted_constants'],
            'Compiled constant inventory differs or includes admissions')
    for name, row in raw.items():
        require(set(row['axioms']) <= STANDARD_AXIOMS and not row['contains_sorry_directly'],
                f'Unapproved proof dependencies in compiled constant: {name}')
    original = read(include('reference/declarations.json'))
    theorem_names = {'ConditionalGoldbach.' + name for name, row in original.items()
                     if row['kind'] == 'theorem'}
    definition_names = {'ConditionalGoldbach.' + name for name, row in original.items()
                        if row['kind'] != 'theorem'}
    require(len(theorem_names) == 102 and len(definition_names) == 171,
            'Reviewed declaration inventory changed')
    declarations = unique_rows(status['declarations'], 'name')
    reviewed = {name for name, row in declarations.items() if row['original']}
    require(reviewed == theorem_names | definition_names, 'Reviewed source coverage differs')
    for name, row in declarations.items():
        require(row['status'] in {'kernel_closed', 'definition'} and row['kernel_closed'],
                f'Unclosed declaration: {name}')
        require(not row['pending_local_dependencies'] and not row['contains_sorry_directly'],
                f'Pending declaration dependencies: {name}')
        require(set(row['axioms']) <= STANDARD_AXIOMS, f'Unapproved axioms: {name}')
        require(row['axioms'] == raw[name]['axioms'] and
                row['contains_sorry_directly'] == raw[name]['contains_sorry_directly'],
                f'Raw kernel audit differs: {name}')
    theorem_rows = [row for row in declarations.values() if row['source_kind'] in {'theorem', 'lemma'}]
    require(status['original_theorem_counts'] == {
        'kernel_closed': 102, 'proof_written_dependencies_pending': 0, 'pending_direct_sorry': 0},
        'Reviewed theorem counts differ')
    require(status['all_public_theorem_counts'] == {
        'kernel_closed': len(theorem_rows), 'proof_written_dependencies_pending': 0,
        'pending_direct_sorry': 0} and not status['unusual_axioms'], 'Public kernel audit failed')
    source_hashes = {str(path.relative_to(ROOT)): digest(path)
                     for path in library_sources(ROOT)}
    require({row['file']: row['sha256'] for row in status['source_files']} == source_hashes,
            'Proof audit does not match the current import closure')

    types = read(include('reviewed-types.json'))
    definitions = read(include('reviewed-definitions.json'))
    require(set(unique_rows(types, 'name')) == theorem_names and
            all(row['reviewed_type_preserved'] is True for row in types), 'Reviewed type check failed')
    require(set(unique_rows(definitions, 'name')) == definition_names and
            all(row['reviewed_definition_preserved'] is True for row in definitions),
            'Reviewed definition check failed')
    for name, phrase in [('types', 'All 102 reviewed theorem types'),
                         ('definitions', 'All 171 reviewed definition bodies')]:
        log = include(f'verification/current-{name}.log')
        require(phrase in (ROOT / log).read_text(), f'Missing successful {name} check output')
    axioms_output = read(include('verification/current-axioms.log'))
    for key in ['original_theorem_counts', 'all_public_theorem_counts', 'unusual_axioms', 'main_results']:
        require(axioms_output[key] == status[key], f'Current axiom log differs: {key}')

    manifest = read(include(AUDIT + 'comparator-manifest.json'))
    comparator = read(include(AUDIT + 'comparator-result.json'))
    verify_comparator_inputs(comparator, manifest)
    for name in comparator['input_hashes']:
        include(name)
    for key in ['accepted', 'negative_controls_rejected', 'library_sources_unchanged',
                'reference_sources_unchanged', 'all_independent_full_types_equal',
                'staged_references_match_frozen_sources']:
        require(comparator[key] is True, f'Comparator check failed: {key}')
    require(set(comparator['permitted_axioms']) == STANDARD_AXIOMS,
            'Comparator axiom allowance differs')
    runs = unique_rows(comparator['runs'], 'name')
    expected_runs = {'independent-full-types-build': 0, 'comparator': 0,
                     'control-condition': 1, 'control-quantifier': 1, 'control-definition': 1}
    require(set(runs) == set(expected_runs), 'Incomplete comparator run set')
    require(runs['independent-full-types-build']['command'] == list(FULL_TYPE_CHECK),
            'Expected fresh elaboration of the full-type checker')
    for name, exit_code in expected_runs.items():
        row = runs[name]
        log = include(AUDIT + row['log'])
        require(row['exit_code'] == exit_code and digest(log) == row['log_sha256'],
                f'Comparator run or log failed: {name}')
        if name != 'independent-full-types-build':
            require(bool(row.get('sandbox_phases')) and 'phase_log' in row,
                    f'Missing comparator sandbox phase timings: {name}')
        if 'phase_log' in row:
            phase_log = include(AUDIT + row['phase_log'])
            require(digest(phase_log) == row['phase_log_sha256'] and
                    row['sandbox_phases'] == [json.loads(line) for line in
                        (ROOT / phase_log).read_text().splitlines()],
                    f'Comparator phase timings differ: {name}')
        require(datetime.fromisoformat(row['start_utc']) >= build_start,
                f'Comparator run predates current build: {name}')
        if name.startswith('control-'):
            text = (ROOT / log).read_text().lower()
            require(any(s in text for s in ['mismatch', 'does not match', 'do not match']),
                    f'Negative control failed for an unrelated reason: {name}')
    require(runs['comparator']['command'] == ['lake', 'comparator', '--config', 'comparator.json'],
            'Expected the full comparator configuration')
    adapter = include(AUDIT + 'bwrap_local_dependencies.py')
    require(digest(adapter) == comparator['sandbox_adapter_sha256'], 'Comparator adapter changed')
    frozen = read(include(AUDIT + 'frozen-source-hashes.json'))
    full_sources = source_hashes | {'ConditionalGoldbach.lean': digest('ConditionalGoldbach.lean')}
    require(frozen == full_sources, 'Comparator frozen library differs from the current sources')
    for name, expected_hash in manifest['frozen_references'].items():
        require(digest(include(AUDIT + name)) == expected_hash, f'Frozen reference changed: {name}')
    for source, target in [('sections-1-4/Expected.lean', 'Reference14.lean'),
                           ('sections-5-7/Reference.lean', 'Reference57.lean'),
                           ('appendices/Reference.lean', 'ReferenceAB.lean'),
                           ('sections-1-4/Bridges.lean', 'Bridges14.lean'),
                           ('sections-5-7/Bridges.lean', 'Bridges57.lean'),
                           ('appendices/NumericCrossCheck.lean', 'NumericCrossCheck.lean')]:
        staged = include(AUDIT + 'comparator-project/TexAuditComparator/' + target)
        require(digest(staged) == manifest['frozen_references'][source], f'Staged reference changed: {target}')
    checks = read(include(AUDIT + 'independent-full-types.json'))
    require(len(checks) == manifest['statement_count'] == comparator['statement_count'] == 103,
            'Independent type count differs')
    require(all(row['full_type_definitionally_equal'] is True for row in checks) and
            {(row['expected'], row['actual']) for row in checks} ==
            {(row['expected'], row['actual']) for row in manifest['statements']},
            'Independent full type comparison differs')
    require(theorem_names <= set(unique_rows(manifest['statements'], 'actual')),
            'Comparator omits reviewed theorem statements')
    config = read(include(AUDIT + 'comparator-project/comparator.json'))
    require(manifest['definition_body_count'] == len(manifest['definitions']) == 96 and
            len(comparator_targets(manifest, config)) == 218, 'Comparator target inventory differs')
    require(comparator['definition_body_count'] == 96 and comparator['comparator_target_count'] == 218 and
            comparator['semantic_bridge_count'] == len(manifest['semantic_bridges']) == 18,
            'Comparator result inventory differs')
    summary = read(include(AUDIT + 'summary.json'))
    require(summary['comparator'] == comparator and summary['current_build'] == build,
            'Independent summary does not contain current verification results')
    final = read(include(AUDIT + 'final-comparison.json'))
    numeric = read(include(AUDIT + 'appendices/numeric-verification.json'))
    for record in [summary, final, numeric]:
        require(record['comparator_result_sha256'] == digest(AUDIT + 'comparator-result.json') and
                record['comparator_manifest_sha256'] == digest(AUDIT + 'comparator-manifest.json') and
                record['independent_full_types_sha256'] == digest(AUDIT + 'independent-full-types.json'),
                'Derived audit evidence has stale inputs')
    require(final['statements'] == [row | {'mechanical_status': 'passed_actual_comparator',
                'full_type_definitionally_equal': True} for row in manifest['statements']] and
            final['definitions'] == [row | {
                'mechanical_status': 'passed_kernel_checked_definition_body_equality_and_actual_comparator'}
                for row in manifest['definitions']] and
            final['semantic_bridges'] == manifest['semantic_bridges'] and
            final['numeric_cross_checks'] == manifest['numerical_cross_checks'],
            'Derived per-target comparison differs from the verified manifest')
    require(numeric['theorem'] in config['theorem_names'] and
            numeric['comparator_run'] == runs['comparator'] and
            numeric['lean_file_sha256'] == digest(AUDIT + 'appendices/NumericCrossCheck.lean') and
            numeric['actual_definition_source'] == declaration_owner('ConditionalGoldbach.unorderedPrimePairs', ROOT) and
            numeric['actual_definition_source_sha256'] == digest(declaration_owner('ConditionalGoldbach.unorderedPrimePairs', ROOT)),
            'Numerical certificate does not match the current comparator')

    pages = {}
    for language, suffix, html_suffix in [('en', '', ''), ('zh', '-zh', '.zh')]:
        page = include(f'progress{html_suffix}.html')
        rendered = read(include(f'progress{suffix}-verification.json'))
        browser = read(include(f'progress{suffix}-browser-verification.json'))
        require(rendered['language'] == browser['language'] == language, 'Progress page language differs')
        require(rendered['html_sha256'] == browser['html_sha256'] == digest(page) and
                rendered['input_sha256'] == browser['input_sha256'] == digest('proof-status.json'),
                f'Stale progress page: {language}')
        require(browser['source_hashes_match'] is True and browser['source_exact'] is True and
                not browser['errors'] and not browser['network'] and browser['initial_visible'] == 102,
                f'Progress browser check failed: {language}')
        require(not rendered['formula_errors'] and rendered['reviewed_types_verified'] is True,
                f'Progress generation failed: {language}')
        report_page = include(AUDIT + f'report{html_suffix}.html')
        report_build = read(include(AUDIT + f'report{suffix}-build.json'))
        report_browser = read(include(AUDIT + f'report{suffix}-browser.json'))
        require(report_build['language'] == report_browser['language'] == language,
                'Independent report language differs')
        require(report_build['html_sha256'] == report_browser['html_sha256'] == digest(report_page),
                f'Stale independent report: {language}')
        require(report_build['current_build_sha256'] == digest('verification/current-build.json'),
                f'Independent report build record is stale: {language}')
        require(report_build['comparator_result_sha256'] == digest(AUDIT + 'comparator-result.json')
                and report_build['proof_status_sha256'] == digest('proof-status.json'),
                f'Independent report audit inputs are stale: {language}')
        require(report_browser['passed'] is True and not report_browser['errors'] and
                not report_browser['network'] and report_browser['statement_cards'] == 103 and
                report_build['statement_cards'] == 103 and not report_build['math_errors'],
                f'Independent report browser check failed: {language}')
        pages[language] = {'progress': browser, 'independent_report': report_browser}

    migration = read(include('verification/naming-migration.json'))
    require(re.fullmatch(r'[0-9a-f]{40}', migration['base_commit']), 'Missing migration base commit')
    migrated = unique_rows(migration['sources'], 'after')
    reviewed_path = include('reference/Reviewed.lean')
    baseline = migrated['formalization/' + reviewed_path]
    require(digest(reviewed_path) == baseline['after_sha256'], 'Reviewed Lean baseline changed')
    tex = ROOT.parent / 'outputs/formalization-preparation/conditional-goldbach.tex'
    tex_sha256 = hashlib.sha256(tex.read_bytes()).hexdigest()
    require(tex_sha256 == '0d36bddbed7c6a74a36c7b87a469fdc96f4b4692aa5c95a2890a1c4f5f59b125',
            'Source paper bytes changed')
    for name in ['README.md', 'README.zh.md', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                 'package.json', 'package-lock.json', 'requirements-review.txt',
                 'verification/README.md', 'verification/README.zh.md', 'reference/inventory.json',
                 'reference/statements-math-en.json', 'reference/statements-math-zh.json',
                 'scripts/check_definitions.py', 'scripts/check_reviewed_types.py', 'scripts/audit_proofs.py',
                 'scripts/ProofAudit.lean', 'scripts/test_verification.py',
                 'scripts/check_entrypoints.py', 'scripts/entrypoints.json',
                 'scripts/check_public_api.py', 'scripts/check_proof_policy.py', 'scripts/check_project.py',
                 'scripts/review_page.js', 'scripts/render_verified.py',
                 'scripts/project_sources.py', 'scripts/verification_inputs.py', 'scripts/build_progress.py', 'scripts/test_progress.cjs',
                 'scripts/update_verification.py', 'scripts/package_verified.py', 'scripts/refresh_audit_summary.py',
                 'scripts/verify_project.py', 'scripts/refresh_dependency_records.py',
                 DECLARATIONS + 'DeclarationAudit.lean', DECLARATIONS + 'analyze.py',
                 PUBLICATION + 'audit_imports.py',
                 AUDIT + 'prepare_comparator.py', AUDIT + 'run_comparator.py',
                 AUDIT + 'build_report.py', AUDIT + 'test_report.cjs', AUDIT + 'summary.json']:
        include(name)
    lake = read('lake-manifest.json')
    packages = {package['name']: package for package in lake['packages']}
    require(lake['name'] == 'conditionalGoldbach', 'Lake package name differs')
    return {
        'schema_version': 3, 'generated_at_utc': datetime.now(timezone.utc).isoformat(),
        'stage': 'Current project build, kernel audits, full comparator and bilingual reports verified',
        'build': build | {'log': build_log}, 'audits': audits,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'mathlib_commit': packages['mathlib']['rev'],
        'project_dependency': {key: packages['goldbach'][key] for key in ['name', 'url', 'rev']},
        'original_theorem_counts': status['original_theorem_counts'],
        'all_public_theorem_counts': status['all_public_theorem_counts'],
        'reviewed_type_checks': {'count': len(types), 'all_passed': True},
        'reviewed_definition_checks': {'count': len(definitions), 'all_passed': True},
        'standard_axioms': sorted(STANDARD_AXIOMS), 'unusual_axioms': status['unusual_axioms'],
        'main_pending_dependencies': {name: row['pending_local_dependencies'] for name, row in declarations.items()
                                      if name.split('.')[-1] in {'theorem_1_1', 'theorem_1_2', 'primePair_consequence'}},
        'baseline': {'lean_sha256': digest(reviewed_path), 'tex_sha256': tex_sha256,
                     'original_lean_sha256': baseline['before_sha256'],
                     'original_git_commit': migration['base_commit'],
                     'naming_migration': 'verification/naming-migration.json'},
        'source_files': [{'file': name, 'sha256': value} for name, value in sorted(full_sources.items())],
        'comparator': comparator, 'ui': pages,
        'evidence_files': [{'file': name, 'sha256': digest(name)} for name in sorted(evidence)],
    }


if __name__ == '__main__':
    verification = validate_current_evidence()
    (ROOT / 'verification.json').write_text(json.dumps(verification, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'verified': True, 'original': verification['original_theorem_counts'],
                      'comparator_targets': verification['comparator']['comparator_target_count'],
                      'languages': list(verification['ui'])}, indent=2))
