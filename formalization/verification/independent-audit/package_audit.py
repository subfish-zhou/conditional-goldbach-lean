"""Package audit evidence without caches or the duplicate benchmark checkout."""
from pathlib import Path
import hashlib,json,zipfile

audit=Path(__file__).resolve().parent
root=audit.parents[2]
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result=read(audit/'comparator-result.json')
browser=read(audit/'report-browser.json')
assert result['accepted'] and result['negative_controls_rejected']
assert result['all_independent_full_types_equal'] and result['staged_references_match_frozen_sources']
assert result['library_sources_unchanged'] and result['reference_sources_unchanged']
assert browser['passed'] and browser['html_sha256']==sha(audit/'report.html')
files=[]
for p in audit.rglob('*'):
    rel=p.relative_to(audit)
    if not p.is_file() or any(x in rel.parts for x in ['.lake','__pycache__','benchmark-project']):continue
    if p.suffix in ['.py','.lean','.cjs','.json','.html','.md','.txt','.log','.png','.toml'] or p.name=='lean-toolchain':
        files.append(p)
tex=root/'outputs/formalization-preparation/LiLiuGoldbach16.tex'
files.append(tex)
files=sorted(files)
archive=root/'outputs/LiLiuGoldbach16-independent-audit.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in files:z.write(p,str(p.relative_to(root)))
with zipfile.ZipFile(archive) as z:
    for p in files:assert hashlib.sha256(z.read(str(p.relative_to(root)))).hexdigest()==sha(p)
record=dict(archive=str(archive),bytes=archive.stat().st_size,sha256=sha(archive),
    files=len(files),contents_sha256={str(p.relative_to(root)):sha(p) for p in files},
    purpose='Independent audit supplement; the frozen main proof library is unchanged.')
(root/'outputs/LiLiuGoldbach16-independent-audit-verification.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='contents_sha256'},ensure_ascii=False,indent=2))
