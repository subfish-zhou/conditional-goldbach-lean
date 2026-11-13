"""Record one completed build/audit/UI checkpoint without inferring proof completion."""
from pathlib import Path
import hashlib, json, re, sys

ROOT = Path(__file__).resolve().parents[1]
checkpoint = int(sys.argv[1])
read = lambda name: json.loads((ROOT / name).read_text())
digest = lambda name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
status = read('proof-status.json')
browser = read('progress-browser-verification.json')
verification = read('verification.json')
build_path = f'work/proof-wave2/integration-build{checkpoint}.log'
build = (ROOT / build_path).read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', build)
assert jobs, 'The full build did not finish successfully.'
for source in status['source_files']:
    assert digest(source['file']) == source['sha256'], source['file']
assert browser['source_hashes_match'] and browser['source_exact']
assert not browser['errors'] and not browser['network']
assert browser['input_sha256'] == digest('proof-status.json')
assert browser['html_sha256'] == digest('progress.html')
assert 'All 102' in (ROOT / f'work/proof-wave2/types-summary{checkpoint}.log').read_text()
assert 'All 171' in (ROOT / f'work/proof-wave2/definitions-summary{checkpoint}.log').read_text()
counts = status['original_theorem_counts']
complete = (counts['kernel_closed'] == 102 and not status['unusual_axioms']
            and not status['all_public_theorem_counts']['pending_direct_sorry']
            and not status['all_public_theorem_counts']['proof_written_dependencies_pending']
            and all(row['status'] != 'definition_pending_dependencies' for row in status['declarations']))
verification['stage'] = ('All 102 reviewed theorem declarations kernel-closed with preserved types and definitions'
                         if complete else 'Ongoing full-paper proof implementation; intermediate verified checkpoint, not completion')
verification['build'] = {
    'command': 'flock /tmp/liliu-build.lock lake build', 'exit_code': 0,
    'jobs': int(jobs[1]), 'log': build_path,
    'warning_note': ('No original theorem has a transitive sorryAx dependency.' if complete else
                     f"{counts['pending_direct_sorry']} original declarations still directly contain sorry; successful compilation is not proof completion")}
for key in ['original_theorem_counts', 'all_public_theorem_counts', 'unusual_axioms', 'source_files']:
    verification[key] = status[key]
verification['main_pending_dependencies'] = {
    row['name']: row['pending_local_dependencies'] for row in status['declarations']
    if row['name'].split('.')[-1] in ['theorem_1_1', 'theorem_1_2', 'primePair_consequence']}
evidence = [build_path, 'proof-status.json', 'proof-status-raw.json', 'reviewed-types.json',
            'reviewed-definitions.json', 'source-coverage.json', 'progress-verification.json',
            'progress-browser-verification.json', 'progress.html', 'README.md',
            'verification/appendix-b4-cross-check.json']
evidence += [f'work/proof-wave2/{name}{checkpoint}.log' for name in
             ['audit-summary', 'types-summary', 'definitions-summary', 'html-build', 'html-browser']]
verification['evidence_files'] = [{'file': name, 'sha256': digest(name)} for name in evidence]
verification['ui'] = browser
verification['appendix_b4_cross_check'] = 'verification/appendix-b4-cross-check.json'
verification['limits'][1] = (f"{status['all_public_theorem_counts']['kernel_closed']} closed public theorem/lemma "
                             'declarations include helpers; original paper statement status is tracked separately.')
(ROOT / 'verification.json').write_text(json.dumps(verification, ensure_ascii=False, indent=2) + '\n')
print({'checkpoint': checkpoint, 'original': counts, 'complete': complete})
