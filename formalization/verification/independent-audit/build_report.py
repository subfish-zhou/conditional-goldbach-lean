"""Render the current independent audit as an offline English or Chinese page."""
from pathlib import Path
import argparse, base64, hashlib, html, json, re, subprocess, sys
from pygments import highlight
from pygments.lexers import get_lexer_by_name
from pygments.formatters import HtmlFormatter

parser=argparse.ArgumentParser()
parser.add_argument('--lang',choices=['en','zh'],default='en')
args=parser.parse_args()
is_en=args.lang=='en'
suffix='' if is_en else '.zh'
audit=Path(__file__).resolve().parent
project=audit.parents[1]
root=project.parent
sys.path.insert(0, str(project/'scripts'))
from project_sources import declaration_source
from update_verification import verify_comparator_inputs
read=lambda p:json.loads(p.read_text())
esc=html.escape
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
choose=lambda en,zh:en if is_en else zh
result=read(audit/'comparator-result.json')
assert result['accepted'] and result['negative_controls_rejected']
assert result['library_sources_unchanged'] and result['reference_sources_unchanged']
build=read(project/'verification/current-build.json')
assert build['exit_code']==0, 'Current project build has not passed'
manifest=read(audit/'comparator-manifest.json')
verify_comparator_inputs(result, manifest)
checks=read(audit/'independent-full-types.json')
assert len(checks)==103 and all(r['full_type_definitionally_equal'] for r in checks)
assert {(r['expected'],r['actual']) for r in checks}=={(r['expected'],r['actual']) for r in manifest['statements']}
copies=[('sections-1-4/Expected.lean','Reference14.lean'),
        ('sections-5-7/Reference.lean','Reference57.lean'),
        ('appendices/Reference.lean','ReferenceAB.lean'),
        ('sections-1-4/Bridges.lean','Bridges14.lean'),
        ('sections-5-7/Bridges.lean','Bridges57.lean'),
        ('appendices/NumericCrossCheck.lean','NumericCrossCheck.lean')]
assert all(sha(audit/source)==sha(audit/'comparator-project/TexAuditComparator'/target)==manifest['frozen_references'][source]
    for source,target in copies), 'Independent references or comparator staging differ from frozen references'
source=root/'outputs/formalization-preparation/conditional-goldbach.tex'
expected_tex_sha256='0d36bddbed7c6a74a36c7b87a469fdc96f4b4692aa5c95a2890a1c4f5f59b125'
assert sha(source)==expected_tex_sha256, 'Bundled TeX differs from the audited source'
proof_status=read(project/'proof-status.json')
assert all(sha(project/r['file'])==r['sha256'] for r in proof_status['source_files']), 'Proof audit source hashes are stale'
source_decl={d['name']:d for d in proof_status['declarations']}
original=read(project/'reference/declarations.json')
definition_names={'ConditionalGoldbach.'+n for n,d in original.items() if d['kind']!='theorem'}
covered=set()
for r in read(audit/'sections-1-4/coverage.json')['rows']:
    covered.update(d['name'] for d in r.get('lean_declarations',[]))
for r in read(audit/'sections-5-7/definition-matrix.json'):
    covered.update(r.get('actual_declarations',[]))
covered.update(r['actual'] for r in read(audit/'appendices/definitions-comparison.json'))
covered.update('ConditionalGoldbach.'+r['label'] for r in read(audit/'appendices/definition-families.json'))
assert definition_names<=covered
inventory=read(project/'reference/inventory.json')
summaries=read(project/f'reference/statements-math-{args.lang}.json')
family={n:r for r in inventory['statements'] for n in r['actual_lean_declarations']}
fresh={r['actual']:r for r in read(audit/'sections-5-7/statement-matrix.json')}
fresh.update({r['actual']:r for r in read(audit/'appendices/comparison.json')})
numeric=read(audit/'appendices/uncovered-numerics.json')
numeric_en=read(project/'reference/audit-numerics-en.json')
for r in numeric:
    if is_en:r.update(numeric_en[r['id']])
    elif r['id']=='B-number-08':
        r['scope']='独立审计补充证明已通过 Lean 内核枚举认证无序素数对计数为905。积分误差认证路径、有理校正值及其余数值展示仍待完成。'

commands=re.compile(r'^(?:(?:noncomputable|private|protected|local)\s+)*(?:def|abbrev|theorem|lemma|structure|namespace|end|section|import|open|attribute|set_option)\b')
def snippet(path,name=None,line=None):
    lines=path.read_text().splitlines()
    if line is None:
        line=next(i for i,l in enumerate(lines) if re.match(r'^(?:noncomputable\s+)?def\s+'+re.escape(name.split('.')[-1])+r'(?:\s|\{|\()',l))
    else:line-=1
    end=line+1
    while end<len(lines) and not commands.match(lines[end]):end+=1
    return '\n'.join(lines[line:end]).rstrip()
lexer=get_lexer_by_name('lean')
formatter=HtmlFormatter()
code=lambda s:highlight(s,lexer,formatter)
ref_file={'sections-1-4':'Expected.lean','sections-5-7':'Reference.lean','appendices':'Reference.lean'}
formulas=[]
math_pattern=re.compile(r'\\\[(.*?)\\\]|\\\((.*?)\\\)',re.S)
def rich(text):
    def sub(m):
        i=len(formulas)
        formulas.append(dict(id=str(i),tex=m[1] if m[1] is not None else m[2],display=m[1] is not None))
        return f'@@MATH{i}@@'
    return esc(math_pattern.sub(sub,text)).replace('\n','<br>')
cards=[]
for r in manifest['statements']:
    f=family.get(r['actual'])
    entry=summaries.get(f['label'] if f else r['actual'])
    assert entry is not None or r['actual']=='ConditionalGoldbach.variable_uniform_spectral_bound'
    title=entry['title'] if entry else choose('Appendix A · Uniform spectral bound',r['label'])
    prose=entry['summary'] if entry else choose(
        r'Fix \(c>0\) before choosing the constants and threshold. The uniform spectral estimate is independent of the weight \(\phi\) and growth function \(h\).',
        r'先固定 \(c>0\)，再选择常数与阈值；统一谱估计的常数独立于权函数 \(\phi\) 和增长函数 \(h\)。')
    expected=snippet(audit/r['audit_group']/ref_file[r['audit_group']],r['expected'])
    live=source_decl[r['actual']]
    livecode=declaration_source(project/live['file'],live['source_range'])
    note=''
    if not is_en:
        info=fresh.get(r['actual'],{})
        note=info.get('findings') or info.get('semantic_note') or info.get('semantic_assessment') or ''
        if isinstance(note,(dict,list)):note=json.dumps(note,ensure_ascii=False)
        quant=info.get('quantifiers') or info.get('quantifier_review') or info.get('quantifier_scope') or info.get('implicit_conditions') or ''
        note=str(quant)+' '+str(info.get('standing_and_implicit_conditions',''))+' '+str(note)
    name=r['actual'].split('.')[-1]
    companion=f is not None and r['actual']!=f['actual_lean_declarations'][0]
    family_note=choose('Companion statement in this result family.','此项为该结果族的配套声明。') if companion else ''
    cards.append(f'''<article class="item" id="audit-{esc(name)}" data-search="{esc((name+' '+title+' '+prose).lower())}">
<h3>{esc(title)} <small>{esc(name)}</small></h3><div class="pair"><div class="explanation">{'<p class="muted">'+family_note+'</p>' if family_note else ''}<p>{rich(prose)}</p>
<p><b>{choose('TeX lines:','TeX 行：')}</b> {esc(str(r['tex_lines']))}</p>{'<p>'+esc(note)+'</p>' if note.strip() else ''}
<p class="pass">{choose('Full-type comparison passed · comparator passed','完整类型比较通过 · comparator 通过')}</p>
<a href="../../progress{suffix}.html#decl-{esc(r['actual'].replace('.','-'))}">{choose('View the proof and its dependencies','查看证明及传递依赖')}</a></div>
<div class="lean"><p>{choose('Independently reconstructed complete proposition (Prop definition)','独立重建的完整命题（Prop 定义）')}</p>{code(expected)}
<details><summary>{choose('Current proved source:','当前已证明源码：')} {esc(live['file'])}:{live['line']}</summary>{code(livecode)}</details></div></div></article>''')
math=subprocess.run(['node',str(project/'scripts/render_math.cjs')],input=json.dumps(formulas),text=True,capture_output=True,check=True)
rendered=json.loads(math.stdout)
assert not rendered['errors']
body='\n'.join(cards)
for i,value in rendered['rendered'].items():body=body.replace(f'@@MATH{i}@@',value)
katex=project/'node_modules/katex'
if not katex.exists():katex=root/'work/html/runtime/node_modules/katex'
kcss=(katex/'dist/katex.min.css').read_text()
def font(m):
    p=katex/'dist'/m[1]
    mime='font/woff2' if p.suffix=='.woff2' else 'font/woff' if p.suffix=='.woff' else 'font/ttf'
    return 'url(data:'+mime+';base64,'+base64.b64encode(p.read_bytes()).decode()+')'
kcss=re.sub(r'url\((fonts/[^)]+)\)',font,kcss)
numrows=''.join(f'<tr><td>{esc(r["id"])}</td><td>{esc(str(r["tex_lines"]))}</td><td>{esc(r["claim"])}</td><td>{esc(r["scope"])}</td></tr>' for r in numeric)
defrows=''.join(f'<tr><td>{esc(r["expected"])}</td><td>{esc(r["actual"])}</td><td>{choose("Definition-body equality passed","定义体等式通过")}</td></tr>' for r in manifest['definitions'])
source_files=[project/'ConditionalGoldbach.lean',*sorted((project/'ConditionalGoldbach').rglob('*.lean'))]
source_lines=sum(len(p.read_text().splitlines()) for p in source_files)
nonempty_lines=sum(sum(bool(line.strip()) for line in p.read_text().splitlines()) for p in source_files)
cmp=next(r for r in result['runs'] if r['name']=='comparator')
css='''*{box-sizing:border-box}body{margin:0;background:#f5f7fa;color:#203244;font:15px/1.65 system-ui,sans-serif;overflow-wrap:anywhere}main{max-width:1500px;margin:auto;padding:24px}h1{font-size:28px}h2{font-size:22px;margin-top:32px}h3{font-size:18px;margin:0;padding:14px 18px;border-bottom:1px solid #dbe2e8}p{margin:10px 0}a{color:#145c86}.notice{padding:18px;background:#fff4dd;border-left:4px solid #af761c}.pass{color:#166a4d}.muted,small{color:#617383}small{display:block;font:12px/1.5 monospace;overflow-wrap:anywhere}.item{background:white;border:1px solid #d2dde6;border-radius:7px;margin:16px 0;overflow:hidden}.pair{display:grid;grid-template-columns:minmax(280px,.9fr) minmax(0,1.3fr)}.explanation,.lean{padding:16px;min-width:0}.explanation{overflow-x:auto}.lean{border-left:1px solid #dbe2e8;background:#f8fafc}pre{overflow:auto;max-height:640px;font:12px/1.65 monospace}.highlight{overflow:auto}.katex-display{overflow:auto}table{border-collapse:collapse;width:100%;background:white}th,td{border:1px solid #d2dde6;padding:10px;text-align:left;vertical-align:top;overflow-wrap:anywhere}details{margin:12px 0}summary{cursor:pointer}input{width:100%;padding:12px;font:inherit;border:1px solid #9eb0bf;border-radius:5px}.filter{position:sticky;top:0;background:#f5f7faed;padding:10px 0;z-index:1}.tablewrap{overflow:auto}code{font-size:.9em}footer{font-size:12px;color:#617383;margin:30px 0}@media(max-width:750px){main{padding:14px}.pair{display:block}.lean{border-left:0;border-top:1px solid #dbe2e8}.filter{position:static}}'''
if is_en:
    intro=f'''<p>The independent audit covers 38 named results, 102 reviewed theorem statements, and 121 definition families containing 171 declarations. A further uniform-constant result brings the complete proposition comparison to 103 statements.</p>
<div class="notice"><b>Audit result:</b> The reviewed theorem families and semantic bridges agree with the paper on their stated domains. Appendix B's concrete integral-error certificates and several numerical calculations remain outstanding; their status is listed below.</div>
<p>The TeX-to-Lean correspondence is checked by mathematical review. Lean checks equality between the independent references and the proved statements, and the comparator replays the proof dependencies.</p>
<h2>Current source and verification</h2><table><tr><th>Measure</th><th>Result</th></tr>
<tr><td>Proof source, including the entry point</td><td>{len(source_files)} files; {source_lines:,} lines; {nonempty_lines:,} nonempty lines</td></tr>
<tr><td>Latest build check</td><td>{build['wall_seconds']:.2f} seconds · passed · <a href="../current-build.json">build record</a></td></tr>
<tr><td>Comparator run</td><td>{cmp['wall_seconds']:.2f} seconds · Lean kernel replay with dependency checks</td></tr></table>
<p><a href="../../../docs/quality-refactor.md">Refactor measurements: source size, imports, and full rebuild timings</a></p>
<h2>Mechanical checks</h2><p class="pass">103 complete proposition types match; 96 independent definition-body equalities and {len(manifest['semantic_bridges'])} semantic bridges pass. The direct enumeration certificate establishes 905 unordered prime pairs. All {manifest['target_count']} comparator targets pass with only propext, Classical.choice, and Quot.sound permitted.</p>
<p>The 103 propositions comprise the original 102 and Appendix A.2's constant-independence result. The 96 definition comparisons include repeated checks across sections. Negative controls changing a condition, swapping quantifiers, or replacing a definition are rejected.</p>
<p>Challenge declarations specify comparison targets. Solution declarations provide the proofs, whose transitive axiom sets are checked by the comparator.</p>
<h2>Interfaces and semantic bridges</h2><ul>
<li><code>PositiveKernel</code> states nonnegativity of the real part. The character-kernel Hermitian theorem and real-valued quadratic-form theorem establish the complex positive-kernel interpretation.</li>
<li>The <code>Module.finrank</code> bound is paired with the finite-dimensionality theorem.</li>
<li><code>completedL</code> uses entire continuation. The bridge results identify its Gamma formula on the applicable domain and match zeros and multiplicities with the original L-function.</li>
<li>The Hardy space uses a weighted L² realization. Unique representations, boundary limits, closed trace ranges, and integral-operator existence and uniqueness connect it to the paper. Zero eigenvalues preserve the spectral products and square sums.</li>
<li>Appendix A.2's <code>variable_uniform_spectral_bound</code> gives constants independent of the weight. Character-sum truncations are covered by mathematical review; the manifest identifies the separately checked equality bridges.</li></ul>
<h2>Appendix B numerical coverage</h2><p>The audit supplement proves <code>unorderedPrimePairs = 905</code> by direct Lean-kernel enumeration. The integral-error calculation leading to the same integer is an outstanding certification task. <a href="appendices/NumericCrossCheck.lean">Enumeration proof</a>.</p>'''
else:
    intro=f'''<p>独立审计覆盖38个命名结论、102个审阅定理声明，以及121个定义族中的171个声明。增加附录A.2的常数独立性结果后，共对照103个完整命题。</p>
<div class="notice"><b>审计结果：</b>已审阅定理族及语义桥梁在原文规定的域内对应一致。附录B的具体积分误差证书和部分数值计算仍待完成，逐项状态见下表。</div>
<p>TeX到独立Lean参考的对应经过数学语义审阅；Lean检查独立参考与实际证明的完整类型等同性，comparator重放证明依赖。</p>
<h2>当前源码与验证</h2><table><tr><th>项目</th><th>结果</th></tr>
<tr><td>含入口的证明源码</td><td>{len(source_files)}个文件；{source_lines:,}行；非空行{nonempty_lines:,}</td></tr>
<tr><td>最近一次构建检查</td><td>{build['wall_seconds']:.2f}秒 · 通过 · <a href="../current-build.json">构建记录</a></td></tr>
<tr><td>Comparator</td><td>{cmp['wall_seconds']:.2f}秒 · Lean内核重放与传递依赖检查</td></tr></table>
<p><a href="../../../docs/quality-refactor.zh.md">本轮改造：源码规模、导入闭包与全量重编译耗时</a></p>
<h2>机械检查</h2><p class="pass">103项完整命题类型一致；96项独立定义体等式；{len(manifest['semantic_bridges'])}项语义桥梁；直接枚举认证905个无序素数对。全部{manifest['target_count']}个comparator目标通过，仅允许propext、Classical.choice、Quot.sound。</p>
<p>103项包括原102项与附录A.2的常数独立性结果。96项定义对照含跨章节重复核查。改变条件、交换量词、替换定义的对照实验均被拒绝。</p>
<h2>接口与语义桥梁</h2><ul><li>PositiveKernel的实部非负性结合Hermitian定理与二次型实值性，对应复正核。</li><li>Module.finrank上界与有限维定理共同使用。</li><li>completedL的整延拓在适用域与Gamma公式一致，零点及重数与原L函数对应。</li><li>加权L²实现通过唯一表示、边界极限、闭迹空间和积分算子的存在唯一性连接原文Hardy空间；补零特征值保持谱乘积与平方和。</li><li>variable_uniform_spectral_bound给出独立于权函数的常数；字符和截断经过语义审阅，独立等式桥梁列于清单。</li></ul>
<h2>附录B数值覆盖</h2><p>补充证明通过Lean内核直接枚举认证 <code>unorderedPrimePairs = 905</code>。由积分误差得到同一整数的具体认证仍待完成。<a href="appendices/NumericCrossCheck.lean">枚举证明</a>。</p>'''
page=f'''<!doctype html><html lang="{choose('en','zh-CN')}"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>ConditionalGoldbach · {choose('Independent audit','独立审计')}</title><style>{kcss}\n{formatter.get_style_defs('.highlight')}\n{css}</style><main>
<h1>ConditionalGoldbach · {choose('Independent TeX audit','原始TeX独立审计')}</h1>
<nav><a class="language-link" href="report.html" lang="en">English</a> · <a class="language-link" href="report.zh.html" lang="zh-CN">简体中文</a> · <a href="../../progress{suffix}.html">{choose('Formalization progress','形式化进展')}</a></nav>
{intro}<div class="tablewrap"><table><tr><th>{choose('ID','编号')}</th><th>{choose('TeX lines','TeX行')}</th><th>{choose('Numerical claim','数值主张')}</th><th>{choose('Coverage','覆盖状态')}</th></tr>{numrows}</table></div>
<p><a href="summary.json">{choose('Machine summary','机器摘要')}</a> · <a href="comparator.log">{choose('Comparator log','Comparator日志')}</a> · <a href="independent-full-types.json">{choose('Complete type checks','完整类型结果')}</a> · <a href="comparator-project/comparator.json">{choose('Reproducible configuration','复跑配置')}</a></p>
<h2>{choose('Independent proposition comparison','独立命题对照')}</h2><p><a href="sections-1-4/coverage.json">{choose('Sections 1–4 coverage','第1–4节覆盖')}</a> · <a href="sections-5-7/semantic-matrix.md">{choose('Sections 5–7 review','第5–7节审阅')}</a> · <a href="appendices/audit-report.md">{choose('Appendix review','附录审阅')}</a></p>
<div class="filter"><input id="search" placeholder="{choose('Search theorem number, name, title, or hypothesis','搜索定理编号、名称、标题或条件')}" aria-label="{choose('Search independent propositions','搜索独立命题')}"></div>{body}
<h2>{choose('Independently reconstructed definitions','独立重建的定义体')}</h2><div class="tablewrap"><table><tr><th>{choose('Independent reference','独立参考')}</th><th>{choose('Actual definition','实际定义')}</th><th>{choose('Result','机械结果')}</th></tr>{defrows}</table></div>
<footer>{choose('Audited TeX SHA256:','原始TeX SHA256：')} {sha(source)}.<br>{choose('Current proof-source hashes match the axiom audit. Formulas, fonts, and Lean highlighting are embedded for offline use.','当前证明源码哈希与公理审计一致；公式、字体和Lean语法高亮均离线内嵌。')}<details><summary>KaTeX MIT License</summary><pre>{esc((katex/'LICENSE').read_text())}</pre></details></footer></main>
<script>document.getElementById('search').addEventListener('input',function(){{const q=this.value.toLowerCase().trim();document.querySelectorAll('.item').forEach(e=>e.hidden=!e.dataset.search.includes(q));}});</script></html>'''
output=audit/f'report{suffix}.html'
output.write_text(page)
record=dict(language=args.lang,html_sha256=sha(output),bytes=len(page.encode()),statement_cards=len(cards),math_count=len(formulas),math_errors=rendered['errors'],current_build_sha256=sha(project/'verification/current-build.json'), comparator_result_sha256=sha(audit/'comparator-result.json'), proof_status_sha256=sha(project/'proof-status.json'))
(audit/choose('report-build.json','report-zh-build.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(report=str(output),**record),indent=2))
