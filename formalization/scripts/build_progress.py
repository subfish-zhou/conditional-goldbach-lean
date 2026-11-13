"""Build the English or Chinese offline review from the transitive axiom audit."""
from pathlib import Path
import argparse,base64,hashlib,html,json,re,subprocess
from pygments import lex
from pygments.lexers import get_lexer_by_name
from pygments.lexer import bygroups,inherit,words
from pygments.token import Comment,Generic,Keyword,Name,Number,Operator,String,Text
FORM=Path(__file__).resolve().parents[1];ROOT=FORM.parent;WORK=ROOT/'work/html';REF=FORM/'reference';NODEMODULES=FORM/'node_modules'
if not (NODEMODULES/'katex').exists():NODEMODULES=WORK/'runtime/node_modules'
parser=argparse.ArgumentParser();parser.add_argument('--input',type=Path,default=FORM/'proof-status.json');parser.add_argument('--output',type=Path);parser.add_argument('--lang',choices=['en','zh'],default='en');args=parser.parse_args()
suffix='.zh' if args.lang=='zh' else ''
args.output=args.output or FORM/f'progress{suffix}.html'
language=json.loads((REF/'progress-language-en.json').read_text())
def localized(text):
 if args.lang=='zh':return text
 for original,translated in sorted(language['text'].items(),key=lambda pair:len(pair[0]),reverse=True):text=text.replace(original,translated)
 return text
if not args.input.exists():raise SystemExit('Waiting for proof-status.json: run scripts/audit_proofs.py first.')
data=json.loads(args.input.read_text());esc=html.escape;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for r in data.get('source_files',[]):
 p=FORM/r['file']
 if sha(p)!=r['sha256']:raise SystemExit('Source changed since proof audit: '+r['file'])
inv=json.loads((REF/'inventory.json').read_text());zh=json.loads((REF/f'statements-math-{args.lang}.json').read_text())
family={}
for r in inv['statements']:
 for n in r['actual_lean_declarations']:family[n]=r
kindnames={'theorem':'定理','lemma':'引理','def':'定义','abbrev':'缩写','structure':'结构'}
statusnames={'kernel_closed':'证明已闭合','proof_written_dependencies_pending':'证明体已写，依赖待证','pending_direct_sorry':'证明仍占位','definition':'定义无占位依赖','definition_pending_dependencies':'定义依赖待证'}
statusnotes={
 'kernel_closed':'Lean.collectAxioms 未发现 sorryAx。状态包含被引用定理和定义的传递依赖检查。',
 'proof_written_dependencies_pending':'本声明的证明体已写出，但传递依赖仍含 sorryAx，因此尚未完成端到端证明。',
 'pending_direct_sorry':'本声明的证明体仍直接含 sorry；条件与结论保留，等待证明。',
 'definition':'定义及其传递依赖未发现 sorryAx。',
 'definition_pending_dependencies':'定义的构造或传递依赖仍含 sorryAx；其对象有效性仍有待证义务。'}
custom={
 'theorem_1_1_weight_exists':('主权函数确实存在','用中心为 \\(1/2\\) 的光滑 bump 构造非零、非负、对称且支撑在 \\([1/3,2/3]\\) 的主权函数。'),
 'lemma_3_5_weight_support':('固定支集排除差族','在 \\(N>0\\) 且两个权值非零时，排除两个非零差族；和族只能是 \\(k=1\\)、\\(n+m=N\\)。'),
 'lemma_7_2_convolutions':('卷积积分、有限区间与权质量','证明两类卷积可积、半轴积分等于相应有限区间积分，并识别 \\(y=1\\) 时的权质量。'),
 'proposition_7_4_norm_integrals':('权范数积分的可积性','对 \\(N>0\\) 和任意实边界参数，证明能量积分与实际权范数积分均可积。'),
 'weightMass_pos':('权质量严格为正','连续非零权的平方积分严格为正，供主定理的相对误差与计数下界使用。'),
 'weightMass_nonneg':('权质量非负','平方积分的非负性。'),
 'weightEnergy_nonneg':('权能量非负','正半轴上导数权的平方除以正坐标，积分非负。'),
 'normFunctional_le_exp2_weightEnergy':('权范数的统一上界','在 \\(N>e^{10}\\) 时，直接从积分和支集证明 \\(Q_N\\le e^2\\,\\mathrm{weightEnergy}(\\phi)\\)。'),
 'badGoldbachMass':('高次素数幂对应的坏项','保留原相关和的范围、互素条件与双权，选取至少一项不是素数的贡献。'),
 'badGoldbachMass_le_psi_sub_theta':('由 ψ−θ 控制坏项','将双权坏项控制为 \\((2\\log N/N)(\\psi(N)-\\theta(N))\\)。'),
 'badGoldbachMass_le_sqrt':('高次素数幂坏项的显式界','利用 Mathlib 的 Chebyshev 估计，得到坏项不超过 \\(4(\\log N)^2/\\sqrt N\\)。'),
 'goldbach_le_badGoldbachMass_add_primePairCount':('加权相关和到素数对计数','按好项／坏项拆分有限和，每个素数对的权至多为 \\((\\log N)^2/N\\)。'),
 'companion_contDiff':('伴随权的光滑性','处理平方根在零点的正则性：主权在零点附近为零，乘积仍全局光滑。'),
 'derivativeWeight_support_subset':('导数权仍有固定支集','导数不会把支集扩张到主权闭支集以外。')}
if args.lang=='en':
 kindnames={k:localized(v) for k,v in kindnames.items()}
 statusnames={k:localized(v) for k,v in statusnames.items()}
 statusnotes={k:localized(v) for k,v in statusnotes.items()}
 custom=language['custom']
class LeanLexer(type(get_lexer_by_name('lean'))):
 tokens={'root':[(r'\b(theorem|lemma|def|abbrev|structure)\b(\s+)([^\s({\[:]+)',bygroups(Keyword.Declaration,Text,Name.Function)),(words(('abbrev','scoped','noncomputable','termination_by','decreasing_by'),prefix=r'\b',suffix=r'\b'),Keyword),inherit]}
lexer=LeanLexer(stripnl=False,ensurenl=False)
def highlighted(code,line):
 parts=[''];reconstructed=''
 for token,value in lex(code,lexer):
  reconstructed+=value
  cls='comment' if token in Comment or token in String.Doc else 'sorry' if value=='sorry' or token in Generic.Error else 'keyword' if token in Keyword else 'function' if token in Name.Function else 'number' if token in Number else 'string' if token in String else 'operator' if token in Operator else ''
  for i,v in enumerate(value.split('\n')):
   if i:parts.append('')
   if v:parts[-1]+=f'<span class="tok-{cls}">{esc(v)}</span>' if cls else esc(v)
 assert reconstructed==code
 return ''.join(f'<span class="code-line" data-line="{line+i}">{v}</span>' for i,v in enumerate(parts))
commands=re.compile(r'^(?:(?:noncomputable|private|protected|local)\s+)*(?:def|abbrev|theorem|lemma|structure|instance|namespace|end|open|attribute|set_option|section|import)\b')
def snippet(row):
 p=FORM/row['file'];lines=p.read_text().splitlines();i=row['line']-1
 assert 0<=i<len(lines),(row['name'],i)
 assert re.match(r'^(?:(?:noncomputable|private|protected|local)\s+)*(?:def|abbrev|theorem|lemma|structure)\s+',lines[i]),(row['name'],lines[i])
 j=i+1
 while j<len(lines) and not commands.match(lines[j]):j+=1
 chunk=lines[i:j]
 while True:
  while chunk and not chunk[-1].strip():chunk.pop()
  if chunk and chunk[-1].startswith('--'):chunk.pop();continue
  if chunk and chunk[-1].rstrip().endswith('-/'):
   k=next((k for k in range(len(chunk)-1,0,-1) if chunk[k].lstrip().startswith('/-')),None)
   if k is not None:chunk=chunk[:k];continue
  break
 return '\n'.join(chunk)
records=[];by={r['name']:r for r in data['declarations']}
def pending_refs(row):
 if row.get('pending_local_dependencies') is not None:return row['pending_local_dependencies']
 found=set();seen=set()
 def visit(name):
  if name in seen or name not in by:return
  seen.add(name);d=by[name]
  if d['status']=='pending_direct_sorry':found.add(name);return
  for n in d.get('value_constants',[])+d.get('type_constants',[]):visit(n)
 for n in row.get('value_constants',[])+row.get('type_constants',[]):visit(n)
 return sorted(found)
for d in data['declarations']:
 r=dict(d);r['id']='decl-'+r['name'].replace('.','-');r['short_name']=r['name'].removeprefix('ConditionalGoldbach.');r['code']=snippet(r);r['code_html']=highlighted(r['code'],r['line']);r['kind_zh']=kindnames.get(r['source_kind'],r['source_kind']);r['status_zh']=statusnames.get(r['status'],r['status']);r['status_note']=statusnotes.get(r['status'],'');r['pending_refs']=pending_refs(r)
 f=family.get(r['name']);r['family_label']=f['label'] if f else None
 if r['short_name'] in custom:r['title_zh'],r['summary_tex']=custom[r['short_name']]
 elif f:r['title_zh']=zh[f['label']]['title'];r['summary_tex']=zh[f['label']]['summary']
 elif r['name'] in zh:r['title_zh']=zh[r['name']]['title'];r['summary_tex']=zh[r['name']]['summary']
 else:r['title_zh']='辅助'+r['kind_zh']+' · '+r['short_name'];r['summary_tex']='用于连接原文定义与证明的辅助声明；精确条件、量词和完整证明见右栏。'
 if f:
  r['review_anchor']='statement-'+re.sub(r'[^a-zA-Z0-9_-]+','-',f['label']).strip('-').lower()
  r['summary_context_note']='配套声明：下列原文主条目摘要仅作背景，精确子结论以右栏为准。' if r['name']!=f['actual_lean_declarations'][0] and r['short_name'] not in custom else ''
 else:r['review_anchor']=None;r['summary_context_note']=''
 r['title_zh']=localized(r['title_zh']);r['summary_tex']=localized(r['summary_tex']);r['summary_context_note']=localized(r['summary_context_note'])
 r['search_text']=' '.join([r['name'],r['title_zh'],r['summary_tex'],r['status_zh'],r['file'],r['code'],' '.join(r['pending_refs'])]).lower();records.append(r)
# Stable reviewed order first; auxiliary helpers retain source order.
base=json.loads((REF/'declarations.json').read_text());order={n:i for i,n in enumerate(base)}
records.sort(key=lambda r:(0 if r['original'] else 1,order.get(r['short_name'],999999),r['file'],r['line']))
formula_pattern=re.compile(r'\\\[(.*?)\\\]|\\\((.*?)\\\)',re.S);formulas={}
for r in records:
 for m in formula_pattern.finditer(r['summary_tex']):
  key=(m[1] if m[1] is not None else m[2],m[1] is not None)
  if key not in formulas:formulas[key]='f'+str(len(formulas))
request=[{'id':i,'tex':tex,'display':display} for (tex,display),i in formulas.items()]
proc=subprocess.run(['node',str(FORM/'scripts/render_math.cjs')],input=json.dumps(request,ensure_ascii=False),capture_output=True,text=True)
math=json.loads(proc.stdout)
if proc.returncode or math['errors']:raise SystemExit(json.dumps(math['errors'],ensure_ascii=False))
def rich(s):
 out=[];pos=0
 for m in formula_pattern.finditer(s):
  out.append(esc(s[pos:m.start()]).replace('\n','<br>'));key=(m[1] if m[1] is not None else m[2],m[1] is not None);out.append(math['rendered'][formulas[key]]);pos=m.end()
 out.append(esc(s[pos:]).replace('\n','<br>'));return ''.join(out)
for r in records:r['summary_html']=rich(r['summary_tex'])
kdist=NODEMODULES/'katex/dist';kcss=(kdist/'katex.min.css').read_text();fonts=[]
def inline_font(m):
 match=re.search(r'url\((fonts/[^)]+\.woff2)\)',m[1]);assert match
 fonts.append(match[1]);return 'src:url(data:font/woff2;base64,'+base64.b64encode((kdist/match[1]).read_bytes()).decode()+') format("woff2")'
kcss=re.sub(r'src:([^;}]+)',inline_font,kcss)
typecheck=FORM/'reviewed-types.json';type_rows=json.loads(typecheck.read_text()) if typecheck.exists() else []
types_ok=len(type_rows)==102 and all(r.get('reviewed_type_preserved') for r in type_rows)
type_note=('102 个原审阅定理的完整类型已通过 Lean 定义等同性检查；证明及其传递依赖也已全部核验。' if data['original_theorem_counts']['kernel_closed']==102 else '102 个原审阅定理的完整类型已通过 Lean 定义等同性检查；证明完成状态另由传递公理审计判定。') if types_ok else '102 个基线声明的完整类型正在自动同一性核验；尚未把类型检查状态视为已通过。'
type_note=localized(type_note)
payload={'language':args.lang,'metadata':{k:v for k,v in data.items() if k not in ['declarations']},'records':records,'type_note':type_note,'reviewed_types_verified':types_ok}
serialized=json.dumps(payload,ensure_ascii=False,separators=(',',':')).replace('<','\\u003c').replace('\u2028','\\u2028').replace('\u2029','\\u2029')
css='''*{box-sizing:border-box}html{color-scheme:light}body{margin:0;background:#f4f7fa;color:#172d3d;font:15px/1.65 system-ui,-apple-system,"Noto Sans CJK SC",sans-serif}a{color:#17618c}header{padding:28px max(24px,calc((100vw - 1550px)/2));background:#fff;border-bottom:1px solid #d5dfe7}h1{font-size:27px;margin:0 0 8px}h2{font-size:20px}p{margin:9px 0}.muted{color:#63798a}.intro-links{display:flex;gap:18px;flex-wrap:wrap}main{max-width:1600px;margin:24px auto;padding:0 24px}.notice{border-left:4px solid #b37b25;padding:15px 20px;background:#fff8e9;border-radius:4px}.notice strong{color:#805014}.cards{display:grid;grid-template-columns:repeat(3,1fr);gap:14px;margin:20px 0}.stat{padding:16px 20px;background:#fff;border:1px solid #cedae4;border-radius:8px;text-align:left;color:inherit;cursor:pointer}.stat b{font-size:28px;margin-right:14px}.stat.kernel_closed{border-top:4px solid #278062}.stat.proof_written_dependencies_pending{border-top:4px solid #bb7a21}.stat.pending_direct_sorry{border-top:4px solid #b54f54}.controls{position:sticky;top:0;z-index:3;background:#f4f7faed;backdrop-filter:blur(8px);padding:12px 0;border-bottom:1px solid #d5dfe7}.toolbar{display:flex;gap:12px;flex-wrap:wrap}.tabs{display:flex;gap:6px;flex-wrap:wrap}button,input,select{font:inherit;border:1px solid #b6cad8;border-radius:5px;padding:8px 12px;background:#fff;color:#234658}button{cursor:pointer}button[aria-pressed=true]{background:#245f7c;color:#fff;border-color:#245f7c}input{min-width:250px;flex:1}button:focus-visible,a:focus-visible,input:focus-visible{outline:3px solid #e5ae47;outline-offset:2px}.filter-line{display:flex;gap:8px;margin-top:10px;align-items:center;flex-wrap:wrap}.small{font-size:13px;color:#63798a}.column-head{display:grid;grid-template-columns:minmax(300px,0.85fr) minmax(0,1.4fr);gap:0;margin-top:16px;color:#597386;font-size:13px}.column-head span{padding:10px 18px}.item{margin:18px 0;background:#fff;border:1px solid #ccdae4;border-radius:8px;overflow:hidden;scroll-margin-top:200px}.item[hidden]{display:none}.item-head{padding:16px 20px;border-bottom:1px solid #dce5ed;display:flex;gap:12px;align-items:baseline;flex-wrap:wrap}.item-head h2{margin:0;flex:1;font-size:18px}.badge{font-size:12px;white-space:nowrap;padding:4px 8px;border-radius:4px;background:#eaf0f5}.badge.kernel_closed{background:#e5f4ed;color:#176244}.badge.proof_written_dependencies_pending{background:#fff1d9;color:#8a5715}.badge.pending_direct_sorry,.badge.definition_pending_dependencies{background:#fae9ea;color:#9d373e}.pair{display:grid;grid-template-columns:minmax(300px,0.85fr) minmax(0,1.4fr)}.zh{padding:18px 22px;min-width:0}.lean{min-width:0;border-left:1px solid #dce5ed;background:#f8fafc}.sourcebar{display:flex;justify-content:space-between;gap:10px;align-items:center;padding:8px 14px;border-bottom:1px solid #e3eaf0;font-size:12px;overflow-wrap:anywhere}.sourcebar button{font-size:12px;padding:4px 10px}pre{margin:0;padding:16px 12px 20px;overflow:auto;font:13px/1.75 "DejaVu Sans Mono","Noto Sans Mono",monospace;tab-size:2;max-height:620px}code{font-family:"DejaVu Sans Mono",monospace;font-size:.92em}.code-line{display:block;min-height:1.75em;white-space:pre-wrap;overflow-wrap:anywhere;padding-left:4.2em;position:relative}.code-line::before{content:attr(data-line);position:absolute;left:0;width:3.2em;text-align:right;color:#8798a5;font-size:11px;user-select:none}.tok-comment{color:#6c8976}.tok-keyword{color:#8553a4;font-weight:600}.tok-function{color:#17598e}.tok-number{color:#b46319}.tok-string{color:#9a5c40}.tok-operator{color:#4b718a}.tok-sorry{color:#c23f49;font-weight:700;background:#fff0f0}.katex-display{overflow-x:auto;overflow-y:hidden;padding:5px 0}.zh .katex{font-size:1.05em}.summary-note{font-size:12px;color:#7b694d;background:#fff8eb;padding:7px 10px}.deps{margin:8px 0;padding:0;list-style:none}.deps button{border:0;padding:3px 0;text-align:left;background:transparent;color:#17618c;overflow-wrap:anywhere;font:12px/1.6 monospace}.audit-line{padding:9px 12px;margin:12px 0;border-left:3px solid #a1b5c3;background:#f4f7fa;font-size:13px}.audit-line.kernel_closed{border-color:#278062}.audit-line.proof_written_dependencies_pending{border-color:#bb7a21}.audit-line.pending_direct_sorry{border-color:#b54f54}details{margin:12px 0}summary{cursor:pointer;color:#46677d}.axioms{font-size:12px;overflow-wrap:anywhere}.empty{padding:35px;text-align:center;background:#fff;border-radius:8px}footer{padding:30px 0;color:#63798a;font-size:13px}.copy-result{position:fixed;bottom:20px;left:50%;transform:translateX(-50%);padding:10px 20px;background:#245f7c;color:white;border-radius:6px;z-index:8}.jump-target{box-shadow:0 0 0 3px #e4b45b}.meta pre{max-height:300px;font-size:11px}.critical{display:flex;gap:8px;flex-wrap:wrap}.critical button{font-size:12px;padding:5px 8px}@media(max-width:900px){.pair,.column-head{grid-template-columns:minmax(260px,1fr) minmax(0,1.2fr)}main{padding:0 12px}.zh{padding:14px}.item-head{padding:12px 14px}pre{font-size:12px}.cards{gap:8px}.stat{padding:12px}.stat b{display:block}}@media(max-width:650px){header{padding:20px 16px}h1{font-size:22px}.pair{display:block}.lean{border-left:0;border-top:1px solid #dce5ed}.column-head{display:none}.controls{position:static}.cards{grid-template-columns:1fr}.stat b{display:inline}.toolbar input{width:100%;min-width:0}.item{scroll-margin-top:12px}.sourcebar{align-items:flex-start}pre{max-height:500px}.critical{display:block}.critical button{display:block}.item-head h2{flex-basis:100%}}@media print{.controls,.sourcebar button,.cards,.copy-result{display:none}.pair{display:grid}.item{break-inside:avoid}pre{max-height:none;overflow:visible}body{background:#fff}}'''
js=r'''const D=JSON.parse(document.getElementById('progress-data').textContent),$=id=>document.getElementById(id),rows=D.records,byName=new Map(rows.map(r=>[r.name,r]));let scope='original',status='all';const e=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));const theorem=r=>['theorem','lemma'].includes(r.source_kind);function inScope(r){return scope==='definitions'?!theorem(r):theorem(r)&&(scope==='all'||(scope==='original'?r.original:!r.original))}function originalLink(r){return r.review_anchor?`<a href="../outputs/formalization-preparation/review.html#${e(r.review_anchor)}">原文中文 / Lean 审阅条目</a>`:''}function markup(r){const refs=r.pending_refs.map(n=>`<li><button data-jump="${e(n)}">${e(n.replace('ConditionalGoldbach.',''))}</button></li>`).join('');return `<article class="item" id="${e(r.id)}" data-name="${e(r.name)}"><div class="item-head"><h2>${e(r.title_zh)}</h2><span class="badge ${e(r.status)}">${e(r.status_zh)}</span><span class="small">${r.original?'原审阅声明':'新增辅助'} · ${e(r.kind_zh)}</span></div><div class="pair"><div class="zh"><p><code>${e(r.short_name)}</code></p>${r.summary_context_note?`<p class="summary-note">${e(r.summary_context_note)}</p>`:''}<div class="math-summary">${r.summary_html}</div><div class="audit-line ${e(r.status)}">${e(r.status_note)}</div>${refs?`<details open><summary>显式引用链中的待证依赖（${r.pending_refs.length}）</summary><ul class="deps">${refs}</ul></details>`:''}<details><summary>Lean 传递公理检查</summary><p class="axioms">${r.axioms.length?r.axioms.map(a=>`<code>${e(a)}</code>`).join(' · '):'无公理'}</p><p class="small">即使声明本身没有 sorry，只要依赖含 sorryAx，也不会标为证明闭合。依赖列表按显式常量引用追踪；完整传递判定以 Lean.collectAxioms 为准。</p></details>${originalLink(r)}</div><div class="lean"><div class="sourcebar"><span><a href="${e(r.file)}">${e(r.file)}</a> · L${r.line}</span><button data-copy="${e(r.name)}">复制完整声明</button></div><pre tabindex="0" aria-label="${e(r.name)} 的实际 Lean 证明"><code>${r.code_html}</code></pre></div></div></article>`}const items=new Map();$('list').innerHTML=rows.map(markup).join('');document.querySelectorAll('.item').forEach(n=>items.set(n.dataset.name,n));function filter(){const q=$('search').value.trim().toLowerCase();let shown=0,total=0;for(const r of rows){const ins=inScope(r);if(ins)total++;const visible=ins&&(status==='all'||r.status===status)&&(!q||r.search_text.includes(q));items.get(r.name).hidden=!visible;if(visible)shown++}$('count').textContent=`显示 ${shown} / ${total} 项`;$('empty').hidden=shown!==0;document.querySelectorAll('[data-scope]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.scope===scope)));document.querySelectorAll('[data-status]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.status===status)));$('scope-caption').textContent=scope==='original'?'当前范围：102 个原审阅定理':scope==='added'?'当前范围：新增辅助定理':scope==='definitions'?'当前范围：定义、缩写与结构':'当前范围：全部公开定理'}function jump(name){const r=byName.get(name);if(!r)return;scope=theorem(r)?'all':'definitions';status='all';$('search').value='';filter();items.get(name).scrollIntoView({behavior:'smooth',block:'start'});items.get(name).classList.add('jump-target');setTimeout(()=>items.get(name).classList.remove('jump-target'),1800);history.replaceState(null,'','#'+r.id)}document.addEventListener('click',async ev=>{const b=ev.target.closest('button');if(!b)return;if(b.dataset.scope){scope=b.dataset.scope;status='all';filter()}if(b.dataset.status){if(b.classList.contains('stat'))scope='original';status=b.dataset.status;filter()}if(b.dataset.jump)jump(b.dataset.jump);if(b.dataset.copy){const text=byName.get(b.dataset.copy).code;try{if(navigator.clipboard&&window.isSecureContext)await navigator.clipboard.writeText(text);else{const area=document.createElement('textarea');area.value=text;document.body.append(area);area.select();document.execCommand('copy');area.remove()}$('toast').textContent='已复制完整 Lean 声明';$('toast').hidden=false;setTimeout(()=>$('toast').hidden=true,1600)}catch(err){$('toast').textContent='浏览器阻止复制，请在右栏选择源码';$('toast').hidden=false}}});$('search').addEventListener('input',filter);$('reset').addEventListener('click',()=>{scope='original';status='all';$('search').value='';filter()});const c=D.metadata.original_theorem_counts;for(const k of ['kernel_closed','proof_written_dependencies_pending','pending_direct_sorry'])$(k+'-count').textContent=c[k];$('type-note').textContent=D.type_note;$('meta').textContent=JSON.stringify(D.metadata,null,2);$('baseline-count').textContent=rows.filter(r=>theorem(r)&&r.original).length;$('added-count').textContent=rows.filter(r=>theorem(r)&&!r.original).length;$('all-count').textContent=rows.filter(theorem).length;$('defs-count').textContent=rows.filter(r=>!theorem(r)).length;const critical=[...new Set(['theorem_1_1','theorem_1_2'].flatMap(n=>byName.get('ConditionalGoldbach.'+n)?.pending_refs||[]))].filter(n=>byName.has(n)&&!byName.get(n).kernel_closed);$('critical-label').textContent=critical.length?'主定理待证依赖：':'主定理待证依赖：无';$('critical').innerHTML=critical.map(n=>`<button data-jump="${e(n)}">${e(n.replace('ConditionalGoldbach.',''))}</button>`).join('');$('main-status').innerHTML=['theorem_1_1','theorem_1_2'].map(n=>byName.get('ConditionalGoldbach.'+n)).filter(Boolean).map(r=>`<button data-jump="${e(r.name)}">${e(r.short_name)}：${e(r.status_zh)}</button>`).join('');const mainClosed=['theorem_1_1','theorem_1_2'].every(n=>byName.get('ConditionalGoldbach.'+n)?.kernel_closed);$('main-warning').textContent=c.kernel_closed===102?'102 条原审阅定理（含附录）的传递依赖均未检出 sorryAx；完整类型及原定义已核对。':mainClosed?'两个主定理的传递依赖均未检出 sorryAx；请同时核对类型同一性记录。':'两个主定理目前尚未端到端完成。已写出的推导仍依赖待证的解析与谱论结果，不能把“证明体完成”视为整篇论文已证明。';filter();const initial=rows.find(r=>r.id===decodeURIComponent(location.hash.slice(1)));if(initial)jump(initial.name);'''
template='''<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>ConditionalGoldbach · Lean 形式化进展审阅</title><style>__CSS__</style></head><body><header><h1>ConditionalGoldbach · 形式化进展审阅</h1><p class="muted">左侧核对中文条件和证明状态，右侧查看当前实际 Lean 证明。状态按完整传递公理计算。</p><div class="intro-links"><a href="../outputs/formalization-preparation/dependency-review.html">原文依赖图</a><a href="../outputs/formalization-preparation/review.html">原始中文 / Lean 对照</a><a href="proof-status.json">机器审计 JSON</a></div></header><main><div class="notice"><strong id="main-warning"></strong><p id="main-status" class="critical"></p><p id="critical-label" class="small">主定理待证依赖：</p><div id="critical" class="critical"></div><p id="type-note" class="small"></p></div><div class="cards"><button class="stat kernel_closed" data-status="kernel_closed"><b id="kernel_closed-count"></b>原声明证明已闭合</button><button class="stat proof_written_dependencies_pending" data-status="proof_written_dependencies_pending"><b id="proof_written_dependencies_pending-count"></b>证明体已写，依赖待证</button><button class="stat pending_direct_sorry" data-status="pending_direct_sorry"><b id="pending_direct_sorry-count"></b>原声明仍占位</button></div><div class="controls"><div class="toolbar"><input id="search" type="search" placeholder="搜索定理编号、中文、条件或 Lean 代码…" aria-label="搜索声明"><div class="tabs"><button data-scope="original" aria-pressed="true">原审阅定理 <span id="baseline-count"></span></button><button data-scope="added" aria-pressed="false">新增辅助 <span id="added-count"></span></button><button data-scope="all" aria-pressed="false">全部定理 <span id="all-count"></span></button><button data-scope="definitions" aria-pressed="false">定义 <span id="defs-count"></span></button></div></div><div class="filter-line"><button data-status="all" aria-pressed="true">全部状态</button><button data-status="kernel_closed" aria-pressed="false">证明闭合</button><button data-status="proof_written_dependencies_pending" aria-pressed="false">依赖待证</button><button data-status="pending_direct_sorry" aria-pressed="false">仍占位</button><span id="count" class="small" role="status"></span><span id="scope-caption" class="small"></span></div><div class="column-head"><span>中文说明 · 条件 · 传递依赖状态</span><span>当前 Lean 声明及证明 · 语法高亮</span></div></div><div id="list"></div><div id="empty" class="empty" hidden>没有匹配项。<button id="reset">清除筛选</button></div><footer>此页可离线使用。所有代码逐字取自当前源文件，核对 proof-status.json 的源文件哈希后生成；公式由 KaTeX 预先渲染。<br>标准公理 propext、Classical.choice、Quot.sound 与未证明占位 sorryAx 分开列示。<details class="meta"><summary>完整审计元数据与文件哈希</summary><pre id="meta"></pre></details><details class="meta"><summary>KaTeX MIT License</summary><pre>__LICENSE__</pre></details></footer></main><div id="toast" class="copy-result" hidden></div><script id="progress-data" type="application/json">__DATA__</script><script>__JS__</script></body></html>'''
template=localized(template);js=localized(js)
if args.lang=='en':
 template=template.replace('lang="zh-CN"','lang="en"')
 js=js.replace('）</summary>',')</summary>').replace('：${e(r.status_zh)}',': ${e(r.status_zh)}')
# Historical Chinese pages keep their language suffix and original anchors.
js=js.replace('formalization-preparation/review.html#','formalization-preparation/review.zh.html#')
lang_link='<a class="language-link" href="progress.html" lang="en">English</a> · <a class="language-link" href="progress.zh.html" lang="zh-CN">简体中文</a>'
template=template.replace('<div class="intro-links">','<div class="intro-links">'+lang_link)
output=template.replace('__CSS__',kcss+'\n'+css).replace('__LICENSE__',esc((NODEMODULES/'katex/LICENSE').read_text())).replace('__DATA__',serialized).replace('__JS__',js)
args.output.write_text(output)
verification={'language':args.lang,'input':str(args.input),'input_sha256':sha(args.input),'output':str(args.output),'html_sha256':sha(args.output),'html_bytes':len(output.encode()),'public_declarations':len(records),'original_theorems':sum(r['original'] and r['source_kind'] in ['theorem','lemma'] for r in records),'all_public_theorems':sum(r['source_kind'] in ['theorem','lemma'] for r in records),'formula_count':len(formulas),'formula_errors':math['errors'],'woff2_fonts_embedded':len(fonts),'reviewed_types_verified':types_ok,'all_source_hashes_match':True,'code_text_preserved_by_highlighting':True,'proof_status_source':'Lean.collectAxioms transitively, not textual absence of sorry','no_remote_runtime_dependencies':True}
(FORM/('progress-zh-verification.json' if args.lang=='zh' else 'progress-verification.json')).write_text(json.dumps(verification,ensure_ascii=False,indent=2)+'\n');print(json.dumps(verification,ensure_ascii=False,indent=2))
