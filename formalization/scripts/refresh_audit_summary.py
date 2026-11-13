"""Derive audit summaries from a completed current comparator run."""
from datetime import datetime, timezone
import hashlib
import json

from project_sources import ROOT, library_sources
from update_verification import AUDIT, STANDARD_AXIOMS, digest, read, require, unique_rows

audit = ROOT / AUDIT
build = read('verification/current-build.json')
started = datetime.fromisoformat(build['start_utc'])
require(build['exit_code'] == 0 and digest(build['log']) == build['log_sha256'],
        'Current build has not passed or its log changed')
result = read(AUDIT + 'comparator-result.json')
for key in ['accepted', 'negative_controls_rejected', 'library_sources_unchanged',
            'reference_sources_unchanged', 'all_independent_full_types_equal',
            'staged_references_match_frozen_sources']:
    require(result[key] is True, f'Comparator check failed: {key}')
require(set(result['permitted_axioms']) == STANDARD_AXIOMS, 'Unexpected permitted axioms')
runs = unique_rows(result['runs'], 'name')
expected_runs = {'independent-full-types-build': 0, 'comparator': 0,
                 'control-condition': 1, 'control-quantifier': 1, 'control-definition': 1}
require(set(runs) == set(expected_runs), 'Missing comparator runs')
for name, exit_code in expected_runs.items():
    row = runs[name]
    require(row['exit_code'] == exit_code and datetime.fromisoformat(row['start_utc']) >= started,
            f'Failed or stale run: {name}')
    require(digest(AUDIT + row['log']) == row['log_sha256'], f'Changed run log: {name}')
    if name.startswith('control-'):
        text = (audit / row['log']).read_text().lower()
        require(any(s in text for s in ['mismatch', 'does not match', 'do not match']),
                f'Negative control failed for an unrelated reason: {name}')
require(runs['comparator']['command'] == ['lake', 'comparator', '--config', 'comparator.json'],
        'Expected the complete comparator configuration')
require(digest(AUDIT + 'bwrap_local_dependencies.py') == result['sandbox_adapter_sha256'],
        'Comparator adapter changed')

manifest = read(AUDIT + 'comparator-manifest.json')
config = read(AUDIT + 'comparator-project/comparator.json')
types = read(AUDIT + 'independent-full-types.json')
require(len(types) == 103 and all(row['full_type_definitionally_equal'] is True for row in types),
        'Full-type comparison failed')
type_map = {(row['expected'], row['actual']): row for row in types}
require(set(type_map) == {(row['expected'], row['actual']) for row in manifest['statements']},
        'Full-type mapping differs from manifest')
targets = ([row['comparator_target'] for row in manifest['statements'] + manifest['definitions']] +
           manifest['semantic_bridges'] + manifest['numerical_cross_checks'])
require(len(targets) == len(set(targets)) == manifest['target_count'] == 218 and
        set(targets) == set(config['theorem_names']), 'Comparator target inventory differs')
sources = library_sources() + [ROOT / 'ConditionalGoldbach.lean']
hashes = {str(path.relative_to(ROOT)): digest(path) for path in sources}
require(read(AUDIT + 'frozen-source-hashes.json') == hashes, 'Frozen library sources changed')
for name, expected in manifest['frozen_references'].items():
    require(digest(AUDIT + name) == expected, f'Frozen reference changed: {name}')

now = datetime.now(timezone.utc).isoformat()
provenance = {
    'generated_at_utc': now,
    'comparator_result_sha256': digest(AUDIT + 'comparator-result.json'),
    'comparator_manifest_sha256': digest(AUDIT + 'comparator-manifest.json'),
    'independent_full_types_sha256': digest(AUDIT + 'independent-full-types.json'),
}
final = provenance | {
    'statements': [row | {
        'mechanical_status': 'passed_actual_comparator',
        'full_type_definitionally_equal': type_map[(row['expected'], row['actual'])]['full_type_definitionally_equal'],
    } for row in manifest['statements']],
    'definitions': [row | {'mechanical_status': 'passed_kernel_checked_definition_body_equality_and_actual_comparator'}
                    for row in manifest['definitions']],
    'semantic_bridges': manifest['semantic_bridges'],
    'numeric_cross_checks': manifest['numerical_cross_checks'],
}

target = 'TexAuditAB.Numeric.unorderedPrimePairs_eq_905'
require(target in manifest['numerical_cross_checks'] and target in config['theorem_names'],
        'Current comparator did not include the numerical certificate')
numeric = provenance | {
    'status': 'certified_by_current_lean_comparator',
    'theorem': target,
    'theorem_type': 'ConditionalGoldbach.unorderedPrimePairs = 905',
    'lean_file': 'NumericCrossCheck.lean',
    'lean_file_sha256': digest(AUDIT + 'appendices/NumericCrossCheck.lean'),
    'actual_definition_source': 'ConditionalGoldbach/Definitions.lean',
    'actual_definition_source_sha256': digest('ConditionalGoldbach/Definitions.lean'),
    'verification_method': 'The complete comparator run replays this target through the Lean kernel.',
    'comparator_record': '../comparator-result.json',
    'comparator_run': runs['comparator'],
    'permitted_axioms': sorted(STANDARD_AXIOMS),
    'library_sources_match_frozen_audit': True,
    'scope': 'Exact unordered prime-pair count 905 for N = 30030 by finite enumeration.',
    'method': [
        'Prove trialPrime n = true iff Nat.Prime n using Nat.prime_def_le_sqrt.',
        'Check the finite cardinality with decide +kernel.',
        'Identify the enumerated set with ConditionalGoldbach.unorderedPrimePairs by extensionality.',
    ],
}
inventory = read('reference/inventory.json')
original = read('reference/declarations.json')
numeric_groups = read(AUDIT + 'appendices/uncovered-numerics.json')
numeric_en = read('reference/audit-numerics-en.json')
numeric_groups = [row | numeric_en[row['id']] for row in numeric_groups]
for row in numeric_groups:
    if row['id'] == 'B-number-08':
        row['status'] = 'direct_prime_enumeration_certified'
summary = provenance | {
    'scope': 'Reviewed theorem statements, independent definitions, semantic bridges, and the finite prime-count certificate.',
    'named_results': len(inventory['statements']),
    'original_theorem_statements': sum(row['kind'] == 'theorem' for row in original.values()),
    'independent_full_types': len(types),
    'definition_families': len(inventory['definitions']),
    'reviewed_definition_declarations': sum(row['kind'] != 'theorem' for row in original.values()),
    'independently_reconstructed_definition_bodies': len(manifest['definitions']),
    'distinct_definition_targets': len({row['actual'] for row in manifest['definitions']}),
    'semantic_bridge_theorems': len(manifest['semantic_bridges']),
    'numerical_cross_checks': manifest['numerical_cross_checks'],
    'comparator_targets': len(targets),
    'comparator': result,
    'current_build': build,
    'source_tex_sha256': hashlib.sha256(
        (ROOT.parent / 'outputs/formalization-preparation/conditional-goldbach.tex').read_bytes()).hexdigest(),
    'source_metrics': {
        'library_files': len(sources) - 1, 'files_with_entry': len(sources),
        'physical_lines_with_entry': sum(len(path.read_text().splitlines()) for path in sources),
        'nonblank_lines_with_entry': sum(sum(bool(line.strip()) for line in path.read_text().splitlines())
                                        for path in sources),
    },
    'numerical_claim_groups': numeric_groups,
}
for name, value in [('final-comparison.json', final), ('appendices/numeric-verification.json', numeric),
                    ('summary.json', summary)]:
    (audit / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'refreshed': ['final-comparison.json', 'appendices/numeric-verification.json', 'summary.json'],
                  'comparator_targets': len(targets), 'generated_at_utc': now}, indent=2))
