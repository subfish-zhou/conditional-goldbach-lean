"""Check the historical library rename using the two Git snapshots."""
from pathlib import Path
import hashlib,json,re,subprocess

PROJECT=Path(__file__).resolve().parents[1]
REPOSITORY=PROJECT.parent
MIGRATION_COMMIT = '14c132a382c52f89d2403ff7ba9397a0432bc1d3'
record=json.loads((PROJECT/'verification/naming-migration.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
for row in record['sources']:
    before=subprocess.check_output(['git','cat-file','blob',row['before_git_blob']],cwd=REPOSITORY)
    after=subprocess.check_output(
        ['git', 'show', f"{MIGRATION_COMMIT}:{row['after']}"], cwd=REPOSITORY)
    assert sha(before)==row['before_sha256'],row['after']
    assert sha(after)==row['after_sha256'],row['after']
    # The two original identities are read from the source, avoiding a legacy
    # project identifier in the current checker or module graph.
    expected=before
    for old in record['identifier_mapping']:
        expected=re.sub(rb'\b'+old.encode()+rb'\b',b'ConditionalGoldbach',expected)
    assert expected==after, f"Change beyond identifier replacement: {row['after']}"
assert len(record['sources'])==255
print('All 254 library source files and the reviewed baseline differ only by project identifiers.')
