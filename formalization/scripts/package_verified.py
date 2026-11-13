"""Package the current verified import closure and explicitly selected evidence."""
import hashlib
import json
import zipfile

from project_sources import ROOT
from update_verification import AUDIT, read, require, validate_current_evidence

workspace = ROOT.parent
verification = read('verification.json')
current = validate_current_evidence()
require(verification['schema_version'] == 2, 'Run update_verification.py first')
for key in current:
    if key != 'generated_at_utc':
        require(verification[key] == current[key], f'Verification is stale: {key}')
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()

files = {ROOT / row['file'] for row in verification['source_files'] + verification['evidence_files']}


def add(base, names):
    for name in names:
        path = base / name
        require(path.is_file(), f'Missing package member: {path}')
        files.add(path)


add(ROOT, [
    'verification.json', 'package.json', 'requirements-review.txt',
    'verification/current-audits.json', 'scripts/check_naming_migration.py', 'scripts/write_progress_report.py',
    'scripts/verify_project.py', 'scripts/refresh_dependency_records.py',
    'reference/Reviewed.lean', 'reference/declarations.json', 'reference/inventory.json',
    'reference/preamble.txt', 'reference/statements-math-en.json', 'reference/statements-math-zh.json',
    'reference/progress-language-en.json', 'reference/audit-numerics-en.json', 'scripts/render_math.cjs',
    'progress-desktop.png', 'progress-mobile.png', 'progress-zh-desktop.png', 'progress-zh-mobile.png',
])
add(workspace, ['README.md', 'README.zh.md', 'docs/dependencies.md', 'docs/dependencies.zh.md'])
audit = ROOT / AUDIT
add(audit, [
    'README.txt', 'README.zh.txt', 'package_audit.py', 'measure_build.py',
    'report-desktop.png', 'report-mobile.png', 'report-zh-desktop.png', 'report-zh-mobile.png',
    'sections-1-4/coverage.json', 'sections-1-4/statement-coverage.json', 'sections-1-4/make_coverage.py',
    'sections-5-7/definition-matrix.json', 'sections-5-7/statement-matrix.json',
    'sections-5-7/semantic-matrix.md', 'sections-5-7/semantic-matrix.zh.md',
    'sections-5-7/report.md', 'sections-5-7/report.zh.md', 'sections-5-7/build_matrix.py',
    'appendices/definition-families.json', 'appendices/uncovered-numerics.json',
    'appendices/numeric-verification.json', 'appendices/audit-report.md', 'appendices/audit-report.zh.md',
    'appendices/TypeAssignments.lean', 'appendices/make_manifest.py', 'appendices/write_report.py',
])
comparator_project = audit / 'comparator-project'
add(comparator_project, [
    'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'TexAuditComparator.lean',
    'TexAuditComparator/Challenge.lean', 'TexAuditComparator/Solution.lean',
    'TexAuditComparator/CheckTypes.lean',
])
for kind in ['condition', 'quantifier', 'definition']:
    add(comparator_project, [f'control-{kind}.json'])
    for side in ['Challenge', 'Solution']:
        add(comparator_project, [f'TexAuditComparator/Control{kind.title()}{side}.lean'])

# These source-review pages are linked from the current bilingual reports.
# Their mathematical snapshots are distinct from the current kernel evidence.
preparation = workspace / 'outputs/formalization-preparation'
add(preparation, ['conditional-goldbach.tex', 'conditional-goldbach.lean',
                 'review.html', 'review.zh.html', 'dependency-review.html', 'dependency-review.zh.html',
                 'abstract-bridge-cross-check.json', 'auxiliary-definitions-cross-check.json',
                 'cross-check.json', 'dependency-audit.json', 'dependency-graph-cross-check.json',
                 'dependency-graph.json', 'dependency-html-verification.json', 'dependency-verification.json',
                 'final-results.json', 'html-verification.json', 'inventory.json', 'lean-dependencies.json',
                 'pdf-excerpts.json', 'semantic-audit.json', 'snapshot-migration.json', 'source-audit.json',
                 'tex-audit.json', 'tex-cross-check.json', 'tex-index.json', 'verification.json'])
for stem in ['README', 'report', 'dependency-audit', 'tex-audit', 'semantic-audit']:
    add(preparation, [stem + '.md', stem + '.zh.md'])
publication = ROOT / 'verification/publication'
add(publication, ['audit_imports.py', 'verification.json', 'dependencies-imports.json', 'dependencies-provenance.json',
                  'dependencies-imports.txt', 'dependencies-imports.zh.txt'])
declaration_audit = publication / 'declaration-audit'
add(declaration_audit, ['DeclarationAudit.lean', 'analyze.py', 'metadata.json', 'source-hashes.json',
                        'imported-modules.json', 'reviewed-names.json', 'reviewed-requiring-mertens.json',
                        'summary.json', 'report.md', 'report.zh.md'])
for scope in ['theorem_1_1', 'theorem_1_2', 'primePair_consequence', 'reviewed_102',
              'public_library', 'all_local_declarations']:
    add(declaration_audit, [scope + '.json', scope + '-external-declarations.tsv'])
files = sorted(files)
manifest = [{'file': str(path.relative_to(workspace)), 'sha256': sha(path),
             'bytes': path.stat().st_size} for path in files]
destination = workspace / 'outputs/conditional-goldbach-formalized.zip'
destination.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(destination, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in files:
        archive.write(path, path.relative_to(workspace))
    archive.writestr('manifest.json', json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
with zipfile.ZipFile(destination) as archive:
    require(archive.testzip() is None, 'ZIP integrity check failed')
    require(len(archive.namelist()) == len(manifest) + 1, 'Unexpected ZIP member count')
    for item in manifest:
        require(hashlib.sha256(archive.read(item['file'])).hexdigest() == item['sha256'],
                f'ZIP member hash failed: {item["file"]}')
report = {
    'file': str(destination.relative_to(workspace)), 'bytes': destination.stat().st_size,
    'sha256': sha(destination), 'files': len(files), 'all_member_hashes_verified': True,
    'verification_sha256': sha(ROOT / 'verification.json'),
    'original_theorems_kernel_closed': verification['original_theorem_counts']['kernel_closed'],
    'comparator_targets': verification['comparator']['comparator_target_count'],
    'report_languages': sorted(verification['ui']),
    'dependency_note': 'Lake fetches the pinned Git dependencies recorded in lake-manifest.json.',
}
(workspace / 'outputs/conditional-goldbach-formalized-verification.json').write_text(
    json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(report, ensure_ascii=False, indent=2))
