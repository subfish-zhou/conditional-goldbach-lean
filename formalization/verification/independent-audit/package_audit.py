"""Package audit evidence without caches or the duplicate benchmark checkout."""
from pathlib import Path
import hashlib,json,sys,zipfile

audit=Path(__file__).resolve().parent
root=audit.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0, str(audit.parents[1] / 'scripts'))
from update_verification import verify_comparator_inputs

read = lambda p: json.loads(p.read_text())
result = read(audit / 'comparator-result.json')
manifest = read(audit / 'comparator-manifest.json')
verify_comparator_inputs(result, manifest)
assert result['accepted'] and result['negative_controls_rejected']
assert result['all_independent_full_types_equal'] and result['staged_references_match_frozen_sources']
assert result['library_sources_unchanged'] and result['reference_sources_unchanged']
for suffix, page_suffix in [('', ''), ('-zh', '.zh')]:
    render = read(audit / f'report{suffix}-build.json')
    browser = read(audit / f'report{suffix}-browser.json')
    assert render['comparator_result_sha256'] == sha(audit / 'comparator-result.json')
    assert browser['passed'] and browser['html_sha256'] == render['html_sha256']
    assert render['html_sha256'] == sha(audit / f'report{page_suffix}.html')

files=[]
for p in audit.rglob('*'):
    rel=p.relative_to(audit)
    if not p.is_file() or any(x in rel.parts for x in ['.lake','__pycache__','benchmark-project']):continue
    if p.suffix in ['.py','.lean','.cjs','.json','.html','.md','.txt','.log','.png','.toml'] or p.name=='lean-toolchain':
        files.append(p)
tex=root/'outputs/formalization-preparation/conditional-goldbach.tex'
files.append(tex)
for name in ['quality-refactor.md', 'quality-refactor.zh.md', 'quality-refactor.json',
             'quality-baseline.tar.gz', 'quality-before-build.log', 'quality-after-build.log',
             'quality-convolution.md', 'quality-convolution.zh.md', 'quality-convolution.json',
             'quality-convolution-baseline.tar.gz', 'imports.md', 'imports.zh.md']:
    files.append(root / 'docs' / name)
files=sorted(files)
archive=root/'outputs/conditional-goldbach-independent-audit.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in files:z.write(p,str(p.relative_to(root)))
with zipfile.ZipFile(archive) as z:
    for p in files:assert hashlib.sha256(z.read(str(p.relative_to(root)))).hexdigest()==sha(p)
record=dict(archive=str(archive),bytes=archive.stat().st_size,sha256=sha(archive),
    files=len(files),contents_sha256={str(p.relative_to(root)):sha(p) for p in files},
    purpose='Independent TeX references, comparator results, and bilingual review pages.')
(root/'outputs/conditional-goldbach-independent-audit-verification.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='contents_sha256'},ensure_ascii=False,indent=2))
