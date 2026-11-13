"""Package the checked proof import closure and its review evidence."""
from pathlib import Path
import hashlib, json, zipfile
from project_sources import ROOT, library_sources

workspace = ROOT.parent
status = json.loads((ROOT / 'proof-status.json').read_text())
verification = json.loads((ROOT / 'verification.json').read_text())
assert status['original_theorem_counts'] == {
    'kernel_closed': 102, 'proof_written_dependencies_pending': 0, 'pending_direct_sorry': 0}
assert not status['unusual_axioms']
assert all(row['status'] in ['kernel_closed', 'definition'] for row in status['declarations'])
assert verification['original_theorem_counts'] == status['original_theorem_counts']
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for entry in status['source_files'] + verification['evidence_files']:
    assert sha(ROOT / entry['file']) == entry['sha256'], entry['file']

files = set(library_sources()) | {ROOT / 'LiLiuGoldbach.lean'}
for name in ['README.md', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
             'package.json', 'requirements-review.txt', 'draft-modules.json',
             'verification.json', 'progress-desktop.png', 'progress-mobile.png']:
    files.add(ROOT / name)
files.update(ROOT / entry['file'] for entry in verification['evidence_files'])
files.update((ROOT / 'reference').glob('*'))
files.update((ROOT / 'verification').glob('*.json'))
files.update((ROOT / 'scripts').glob('*.py'))
files.update((ROOT / 'scripts').glob('*.cjs'))
# Keep the original review and dependency pages at the relative paths linked
# by progress.html; these are explicitly historical statement-review snapshots.
files.update((workspace / 'outputs/formalization-preparation').glob('*'))
files = sorted(path for path in files if path.is_file())
manifest = [{'file': str(path.relative_to(workspace)), 'sha256': sha(path),
             'bytes': path.stat().st_size} for path in files]
destination = workspace / 'outputs/LiLiuGoldbach16-formalized.zip'
with zipfile.ZipFile(destination, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in files:
        archive.write(path, path.relative_to(workspace))
    archive.writestr('manifest.json', json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
with zipfile.ZipFile(destination) as archive:
    assert archive.testzip() is None
    for item in manifest:
        assert hashlib.sha256(archive.read(item['file'])).hexdigest() == item['sha256']
report = {'file': str(destination), 'bytes': destination.stat().st_size,
          'sha256': sha(destination), 'files': len(files), 'all_member_hashes_verified': True,
          'original_theorems_kernel_closed': 102,
          'dependency_note': 'Requires the existing goldbach project and the pinned Lean/Mathlib environment recorded in verification.json.'}
(workspace / 'outputs/LiLiuGoldbach16-formalized-verification.json').write_text(
    json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(report, ensure_ascii=False, indent=2))
