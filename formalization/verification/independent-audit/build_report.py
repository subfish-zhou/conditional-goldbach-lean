"""Build the independent audit report; do not infer success from source text."""
from pathlib import Path
import base64, hashlib, html, json, re, subprocess
from pygments import highlight
from pygments.lexers import get_lexer_by_name
from pygments.formatters import HtmlFormatter

audit = Path(__file__).resolve().parent
project = audit.parents[1]
root = project.parent
read = lambda p: json.loads(p.read_text())
esc = html.escape
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
result = read(audit/'comparator-result.json')
assert result['accepted'] and result['negative_controls_rejected']
assert result['library_sources_unchanged'] and result['reference_sources_unchanged']
metrics = read(audit/'metrics.json')
warm = read(audit/'build-warm.json')
cold = read(audit/'build-project-clean.json')
assert warm['exit_code']==cold['exit_code']==0
manifest = read(audit/'comparator-manifest.json')
checks = read(audit/'independent-full-types.json')
assert len(checks)==103 and all(r['full_type_definitionally_equal'] for r in checks)
assert {(r['expected'],r['actual']) for r in checks}=={(r['expected'],r['actual']) for r in manifest['statements']}
copies=[('sections-1-4/Expected.lean','Reference14.lean'),
        ('sections-5-7/Reference.lean','Reference57.lean'),
        ('appendices/Reference.lean','ReferenceAB.lean'),
        ('sections-1-4/Bridges.lean','Bridges14.lean'),
        ('sections-5-7/Bridges.lean','Bridges57.lean'),
        ('appendices/NumericCrossCheck.lean','NumericCrossCheck.lean')]
staged_matches=all(sha(audit/'comparator-project/TexAuditComparator'/target)==
    manifest['frozen_references'][source] for source,target in copies)
assert staged_matches, 'Comparator staging differs from frozen independent references'
result['staged_references_match_frozen_sources']=staged_matches
result['all_independent_full_types_equal']=True
(audit/'comparator-result.json').write_text(json.dumps(result,indent=2)+'\n')
numeric = read(audit/'appendices/uncovered-numerics.json')
for row in numeric:
    if row['id']=='B-number-08':
        row['original_audit_status']=row['status']
        row['status']='partially_certified_by_new_audit_supplement'
        row['scope']='原库没有905命题；本轮已另用内核枚举证明实际无序计数=905。原文通过积分误差获得905的认证路径、有理校正数值及其余数值展示仍未完成。'
original = read(project/'reference/declarations.json')
definition_names = {'LiLiuGoldbach16.'+n for n,d in original.items() if d['kind']!='theorem'}
cov14 = read(audit/'sections-1-4/coverage.json')
cov57 = read(audit/'sections-5-7/definition-matrix.json')
covAB = read(audit/'appendices/definition-families.json')
covered = set()
for r in cov14['rows']: covered.update(d['name'] for d in r.get('lean_declarations',[]))
for r in cov57: covered.update(r.get('actual_declarations',[]))
covered.update(r['actual'] for r in read(audit/'appendices/definitions-comparison.json'))
covered.update('LiLiuGoldbach16.'+r['label'] for r in covAB)
assert definition_names <= covered
source = root/'outputs/formalization-preparation/LiLiuGoldbach16.tex'
# SHA256 of the original attachment, recorded by the independent audit.
expected_tex_sha256 = '0d36bddbed7c6a74a36c7b87a469fdc96f4b4692aa5c95a2890a1c4f5f59b125'
assert sha(source)==expected_tex_sha256, 'Bundled TeX differs from the audited source'
summary = dict(scope='38 named results / 102 reviewed theorem statements, plus one uniform-constant theorem',
    named_results=38, original_theorem_statements=102, independent_full_types=103,
    definition_families=121, reviewed_definition_declarations=171,
    independently_reconstructed_definition_bodies=96,
    distinct_definition_targets=len({r['actual'] for r in manifest['definitions']}),
    semantic_bridge_theorems=len(manifest['semantic_bridges']), numerical_cross_checks=manifest.get('numerical_cross_checks',[]),
    comparator_targets=manifest['target_count'], comparator=result,
    source_tex_sha256=sha(source), metrics=metrics, warm_build=warm, project_clean_build=cold,
    human_semantic_verdict='No unbridged mismatch found in the named theorem clusters on the paper domains. Model-contract distinctions are explicitly recorded.',
    scope_limitation='Concrete numerical experiments and integral-error certificates in Appendix B are not all formalized. TeX-to-reference semantics are independently reviewed, not mechanically parsed or proved.',
    numerical_claim_groups=numeric)
(audit/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')

inventory=read(project/'reference/inventory.json'); zh=read(project/'reference/statements-math-zh.json')
family={n:r for r in inventory['statements'] for n in r['actual_lean_declarations']}
fresh={r['actual']:r for r in read(audit/'sections-5-7/statement-matrix.json')}
fresh.update({r['actual']:r for r in read(audit/'appendices/comparison.json')})
source_decl={d['name']:d for d in read(project/'proof-status.json')['declarations']}
commands=re.compile(r'^(?:(?:noncomputable|private|protected|local)\s+)*(?:def|abbrev|theorem|lemma|structure|namespace|end|section|import|open|attribute|set_option)\b')
def snippet(path, name=None, line=None):
    lines=path.read_text().splitlines()
    if line is None:
        line=next(i for i,l in enumerate(lines) if re.match(r'^(?:noncomputable\s+)?def\s+'+re.escape(name.split('.')[-1])+r'(?:\s|\{|\()',l))
    else: line-=1
    end=line+1
    while end<len(lines) and not commands.match(lines[end]): end+=1
    return '\n'.join(lines[line:end]).rstrip()
lexer=get_lexer_by_name('lean'); formatter=HtmlFormatter()
code=lambda s:highlight(s,lexer,formatter)
ref_file={'sections-1-4':'Expected.lean','sections-5-7':'Reference.lean','appendices':'Reference.lean'}
formulas=[]
math_pattern=re.compile(r'\\\[(.*?)\\\]|\\\((.*?)\\\)',re.S)
def rich(text):
    def sub(m):
        i=len(formulas); formulas.append(dict(id=str(i),tex=m[1] or m[2],display=m[1] is not None))
        return f'@@MATH{i}@@'
    return esc(math_pattern.sub(sub,text))

cards=[]
for r in manifest['statements']:
    f=family.get(r['actual']); title=zh[f['label']]['title'] if f else r['label']
    prose=zh[f['label']]['summary'] if f else '附录 A 的统一谱估计：先固定 c，再选常数与阈值；这些常数不依赖权函数 φ 或增长函数 h。'
    expected=snippet(audit/r['audit_group']/ref_file[r['audit_group']],r['expected'])
    live=source_decl[r['actual']]
    livecode=snippet(project/live['file'],line=live['line'])
    info=fresh.get(r['actual'],{})
    note=info.get('findings') or info.get('semantic_note') or info.get('semantic_assessment') or ''
    if isinstance(note,(dict,list)): note=json.dumps(note,ensure_ascii=False)
    quant=info.get('quantifiers') or info.get('quantifier_review') or info.get('quantifier_scope') or info.get('implicit_conditions') or ''
    if info.get('standing_and_implicit_conditions'):
        quant += ' '+info['standing_and_implicit_conditions']
    name=r['actual'].split('.')[-1]
    cards.append(f'''<article class="item" data-search="{esc((name+' '+title).lower())}">
      <h3>{esc(title)} <small>{esc(name)}</small></h3><div class="pair">
      <div class="zh"><p>{rich(prose)}</p><p class="muted">中文概述用于定位；完整条件和量词见右侧独立命题。</p>
      <p><b>TeX 行：</b>{esc(str(r['tex_lines']))}</p><p>{esc(str(quant))}</p><p>{esc(str(note))}</p>
      <p class="pass">完整类型比较通过 · comparator 通过</p>
      <a href="../../progress.html#decl-{esc(r['actual'].replace('.','-'))}">查看原证明对照页</a></div>
      <div class="lean"><p>独立重建的完整命题（Prop 定义）</p>{code(expected)}
      <details><summary>当前已证明源码：{esc(live['file'])}:{live['line']}</summary>{code(livecode)}</details></div></div></article>''')
math=subprocess.run(['node',str(project/'scripts/render_math.cjs')],input=json.dumps(formulas),text=True,capture_output=True,check=True)
rendered=json.loads(math.stdout);assert not rendered['errors']
body='\n'.join(cards)
for i,value in rendered['rendered'].items():body=body.replace(f'@@MATH{i}@@',value)
katex=project/'node_modules/katex'
if not katex.exists():
    katex=root/'work/html/runtime/node_modules/katex'
kcss=(katex/'dist/katex.min.css').read_text()
def font(m):
    p=katex/'dist'/m[1]
    mime='font/woff2' if p.suffix=='.woff2' else 'font/woff' if p.suffix=='.woff' else 'font/ttf'
    return 'url(data:'+mime+';base64,'+base64.b64encode(p.read_bytes()).decode()+')'
kcss=re.sub(r'url\((fonts/[^)]+)\)',font,kcss)
numrows=''.join(f'<tr><td>{esc(r["id"])}</td><td>{esc(str(r["tex_lines"]))}</td><td>{esc(r["claim"])}</td><td>{esc(r["scope"])}</td></tr>' for r in numeric)
defrows=''.join(f'<tr><td>{esc(r["expected"])}</td><td>{esc(r["actual"])}</td><td>定义体等式通过</td></tr>' for r in manifest['definitions'])
elapsed=metrics['elapsed_formalization_record']['elapsed_seconds']
hours=int(elapsed//3600); minutes=int(elapsed%3600//60); seconds=round(elapsed%60)
cmp=next(r for r in result['runs'] if r['name']=='comparator')
css='''*{box-sizing:border-box}body{margin:0;background:#f5f7fa;color:#203244;font:15px/1.65 system-ui,sans-serif}main{max-width:1500px;margin:auto;padding:24px}h1{font-size:28px}h2{font-size:22px;margin-top:32px}h3{font-size:18px;margin:0;padding:14px 18px;border-bottom:1px solid #dbe2e8}p{margin:10px 0}a{color:#145c86}.notice{padding:18px;background:#fff4dd;border-left:4px solid #af761c}.pass{color:#166a4d}.muted,small{color:#617383}small{display:block;font:12px/1.5 monospace;overflow-wrap:anywhere}.item{background:white;border:1px solid #d2dde6;border-radius:7px;margin:16px 0;overflow:hidden}.pair{display:grid;grid-template-columns:minmax(280px,.9fr) minmax(0,1.3fr)}.zh,.lean{padding:16px;min-width:0}.lean{border-left:1px solid #dbe2e8;background:#f8fafc}pre{overflow:auto;max-height:640px;font:12px/1.65 monospace}.highlight{overflow:auto}.katex-display{overflow:auto}table{border-collapse:collapse;width:100%;background:white}th,td{border:1px solid #d2dde6;padding:10px;text-align:left;vertical-align:top;overflow-wrap:anywhere}details{margin:12px 0}summary{cursor:pointer}input{width:100%;padding:12px;font:inherit;border:1px solid #9eb0bf;border-radius:5px}.filter{position:sticky;top:0;background:#f5f7faed;padding:10px 0;z-index:1}.tablewrap{overflow:auto}code{font-size:.9em}footer{font-size:12px;color:#617383;margin:30px 0}@media(max-width:750px){main{padding:14px}.pair{display:block}.lean{border-left:0;border-top:1px solid #dbe2e8}.filter{position:static}}'''
css += 'body{overflow-wrap:anywhere}.zh{overflow-x:auto}'
page=f'''<!doctype html><html lang="zh-CN"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Li–Liu 原始 TeX 独立审计</title><style>{kcss}\n{formatter.get_style_defs('.highlight')}\n{css}</style><main>
<h1>Li–Liu 原始 TeX 独立审计</h1>
<p>三个独立审计子任务重新读取用户提供的原始 TeX；主证明库保持不变。覆盖38个命名结论、102个审阅声明，以及121个定义族／171个定义声明。</p>
<div class="notice"><b>结论范围：</b>在论文规定的有效域内，命名定理及所列辅助桥梁未发现尚未补足的条件弱化、条件缺失、量词变化或定义含义差异。但附录 B 的具体积分误差证书与数值实验未全部形式化，因此不能称整篇论文的每一个主张都已完成。</div>
<p>TeX → 独立 Lean 参考是人工数学语义审查；参考 → 实际证明由 Lean 机械检查。comparator 本身不会理解 TeX，也不能取代前一层审查。</p>
<h2>规模与时间</h2><table><tr><th>项目</th><th>实测／记录</th></tr>
<tr><td>证明源代码</td><td>253个库文件，29,628行；连入口共254文件、29,629行；非空行27,451。不含依赖库、旧审阅稿与本轮审计代码。</td></tr>
<tr><td>无改动编译复查</td><td>{warm['wall_seconds']:.2f} 秒</td></tr>
<tr><td>本项目全部源码重新编译</td><td>{cold['wall_seconds']/60:.2f} 分钟（{cold['wall_seconds']:.2f}秒）；清空的是独立副本的项目产物，复用Mathlib和Goldbach依赖缓存。8逻辑CPU，Lean工作线程设2；与部分审计活动共享机器。排队等待已排除。</td></tr>
<tr><td>形式化过程记录区间</td><td>{hours}小时{minutes}分{seconds}秒。从证明工程创建到已验证压缩包生成；依据文件时间戳，并非精确的活跃计算时间。未计此前论文拆解和本轮新审计。</td></tr>
<tr><td>真实 comparator</td><td>{cmp['wall_seconds']:.2f}秒；Lean 4.35内置 lake comparator，bwrap隔离开启，两个本地依赖目录额外只读挂载，Lean内核重放。</td></tr></table>
<h2>机械检查</h2><p class="pass">103项独立完整命题类型相等；96项独立定义体等式；{len(manifest['semantic_bridges'])}项额外语义桥梁；另有905的直接枚举证书。共{manifest['target_count']}个comparator目标全部通过，只允许propext、Classical.choice、Quot.sound。</p>
<p>103项＝原102项＋附录A.2的常数独立性结果。96项定义体对照含跨章节重复核查，不等于171项定义全部独立重写。条件改变、量词交换、定义替换三种故意错误的对照实验全部被拒绝。</p>
<p>Challenge中的sorry仅用于指定比较目标；Solution必须给出真实证明，若其传递依赖包含sorryAx就会被拒绝。这些审计参考不由主证明库导入。</p>
<p><a href="summary.json">完整机器摘要</a> · <a href="comparator.log">comparator日志</a> · <a href="independent-full-types.json">逐项完整类型结果</a> · <a href="comparator-project/comparator.json">可复跑配置</a></p>
<h2>必须连同桥梁阅读的接口</h2><ul>
<li>PositiveKernel单独只保证实部非负；字符核的Hermitian定理与独立二次型实值性证明补足通常复正核含义。</li>
<li>Module.finrank上界单独不足以排除无限维；须结合已证明的有限维声明。</li>
<li>completedL使用整延拓；已核实其与Gamma公式在适用域一致、零点及重数与原L函数匹配。</li>
<li>Hardy空间采用加权L²实现；双向唯一表示、真边界极限、闭迹空间、积分算子存在唯一性负责连接原文定义。谱索引补零不改变乘积或平方和。</li>
<li>A.2的主命题单独容许常数依赖φ；额外的variable_uniform_spectral_bound明确消除此依赖。字符有限和截断等部分只做了语义检查，本轮没有为每个改写新建独立等式桥梁。</li></ul>
<h2>附录 B 尚未全部认证的数值主张</h2><p>以下是原形式化库的覆盖缺口。本轮另已用Lean内核认证 <code>unorderedPrimePairs = 905</code>，并纳入comparator；这是直接素数枚举，未使用native_decide或额外公理。它不能代替原文的积分数值与εI误差证书。<a href="appendices/NumericCrossCheck.lean">查看新增枚举证明</a>。</p><div class="tablewrap"><table><tr><th>编号</th><th>TeX行</th><th>原文主张</th><th>范围说明</th></tr>{numrows}</table></div>
<h2>独立命题对照</h2><p><a href="sections-1-4/coverage.json">第1–4节逐定义记录</a> · <a href="sections-5-7/semantic-matrix.md">第5–7节逐项记录</a> · <a href="appendices/audit-report.md">附录逐项记录</a></p><div class="filter"><input id="search" placeholder="搜索定理编号、名称或中文标题" aria-label="搜索独立命题"></div>{body}
<h2>独立重建的定义体</h2><div class="tablewrap"><table><tr><th>独立参考</th><th>实际定义</th><th>机械结果</th></tr>{defrows}</table></div>
<footer>原始附件与审计副本的SHA256一致：{sha(source)}。审计前后254个证明源码文件哈希未变。公式和字体离线内嵌，Lean语法高亮。<details><summary>KaTeX MIT许可证</summary><pre>{esc((katex/'LICENSE').read_text())}</pre></details></footer></main>
<script>document.getElementById('search').addEventListener('input',function(){{const q=this.value.toLowerCase().trim();document.querySelectorAll('.item').forEach(e=>e.hidden=!e.dataset.search.includes(q));}});</script></html>'''
(audit/'report.html').write_text(page)
(audit/'report-build.json').write_text(json.dumps(dict(html_sha256=sha(audit/'report.html'),bytes=len(page.encode()),statement_cards=len(cards),math_count=len(formulas),math_errors=rendered['errors']),indent=2)+'\n')
print(json.dumps(dict(report=str(audit/'report.html'),statements=len(cards),math_count=len(formulas)),indent=2))
