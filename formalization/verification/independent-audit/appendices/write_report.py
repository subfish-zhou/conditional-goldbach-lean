import json, pathlib, hashlib, re
p=pathlib.Path(__file__).parent
root=p.parents[2]
tex=root.parent/'outputs/formalization-preparation/LiLiuGoldbach16.tex'
rows=json.loads((p/'comparison.json').read_text())
defs=json.loads((p/'definitions-comparison.json').read_text())
# Scan live source only to give locations. No reference body is generated from it.
locations={}
for f in (root/'LiLiuGoldbach').rglob('*.lean'):
 for i,line in enumerate(f.read_text().splitlines(),1):
  m=re.match(r'(?:private\s+)?(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure)\s+(\w+)',line)
  if m:locations[m.group(1)]={'file':str(f.resolve()),'line':i}
for coll in [rows,defs]:
 for row in coll:
  row['live_source']=locations.get(row['actual'].split('.')[-1])
# 32 definition-family entries. Catalogue used to locate coverage only, never as evidence.
family_bindings={
 'zeroMultiplicity':['poleOrder'],'variableAlpha':['boundaryParameter'],
 'variableRealization':['variableStrip','variableHardySpace','variableBoundary','variableOperator','variableFunctional','variableVector','variableFunctionalNorm'],
 'variableSpectralProduct':['variableComplexProduct','variableQuaternionProduct'],
 'variableSpectralHypotheses':['pointwiseR','pointwiseZeroFree','eventualR','eventualS'],
 'zeroMultiplicitySquareAverage':['poleMass'],'baselineProductR':['regularEulerFactor'],
 'experimentN':['numericalN'],'smoothStep13':['P'],'wideCutoff':['eta'],'wideCompanion':['W'],
 'wideWeight':['f'],'wideCorrelation':['J'],'unorderedPrimeCount':['primePairCount'],
 'edgeCorrection':['edge'],'primePowerCorrection':['properPowers'],'wideCoefficients':['coefficient'],
 'countingIntegral':['integralI'],'wideDiagonal':['diagonalD'],'approximateMoments':['signedJhat','diagonalDhat'],
 'wideMainMass':['crossMass'],'wideMainIntegral':['mainIntegral'],'wideResidual':['residualB'],
 'momentError':['momentError'],'approximatePrimeCount':['countCentre'],'countError':['countRadius'],
 'wideFunctional':['ellW'],'wideRieszVector':['vectorW'],'quadratureNodes':['node'],
 'quadratureWeights':['nodeWeight'],'finiteSpectralMatrix':['matrixC'],
 'finiteSpectralProduct':['finiteX','finiteSpectrum','eigenvalueList','matrixNorm']}
inv=json.loads((root/'reference/inventory.json').read_text())
family_rows=[]
for entry in inv['definitions']:
 if str(entry['section']).startswith(('A','B')):
  family_rows.append({'label':entry['label'],'section':entry['section'],'independent_references':['TexAuditAB.'+x for x in family_bindings[entry['label']]],'semantic_status':'reviewed_against_original_tex_and_live_definition','boundary_note':'共享核心L函数、Hardy Fourier-Laplace模型、原始谱积的基础数学正确性由主审计覆盖；本项审核附录参数替换、具体公式和选择函数的有效域。'})
missing=[
 {'id':'B-number-01','tex_lines':[4341,4345],'claim':'75个边缘素数对、26个无序真素数幂对；E=44.35776816334822525…，Cpp/2=10.16758713116445818…','status':'not_formalized','scope':'命名B1之外的具体算例；B1只给精确符号恒等式。'},
 {'id':'B-number-02','tex_lines':[4389,4403],'claim':'h=0.1,T=1600；2^20 FFT网格；24阶Euler–Maclaurin、32高度重置；积分输出Jhat≈0.05799599193959489,Dhat≈0.29331844084848136','status':'not_formalized','scope':'未见存储5760个Ihat值、数值积分实现或该输出的有理证书绑定实际integralI。'},
 {'id':'B-number-03','tex_lines':[4408,4419],'claim':'HL预测积分≈908.1405628685、宽权A≈851.831147718741；65位数值积分及C2加速算法参数','status':'not_formalized','scope':'wideMainIntegral有精确定义，未认证该近似；传统HL积分的具体数值也未认证。'},
 {'id':'B-number-04','tex_lines':[4420,4421],'claim':'A−Cpp/2+E≈886.021328750925','status':'not_formalized','scope':'符号校正公式已覆盖；十进制数值未认证。'},
 {'id':'B-number-05','tex_lines':[4430,4437],'claim':'−N Bhat/2≈18.978671254276及rhat≈905.0000000052','status':'not_formalized','scope':'B3的Ihat为任意输入，尚无特定Ihat及该中心的证明。'},
 {'id':'B-number-06','tex_lines':[4475,4486],'claim':'3280个非零a_n；有限变换有理包围证明RMS积分误差<1.68935×10^−5','status':'not_formalized','scope':'这是应用B3得905最关键的未填输入；HasMomentError仅是定义，lemma_B_3将该界作为假设。'},
 {'id':'B-number-07','tex_lines':[4487,4490],'claim':'εr≈0.274758682716，外舍入[904.725241,905.274759]∩Z={905}','status':'not_formalized','scope':'没有在Lean中将真实积分误差传递到该具体区间；一般整数区间lemma不提供这项数值证书。'},
 {'id':'B-number-08','tex_lines':[4491,4496],'claim':'精确905无序对、1810有序对；直接有理求和与独立素数枚举双重检验','status':'not_formalized_in_audited_library','scope':'对活跃LiLiuGoldbach目录检索905未发现对应命题；可另补枚举证书，但不能代替积分误差认证。'},
 {'id':'B-number-09','tex_lines':[4501,4505],'claim':'α30030≈0.09699366','status':'approximation_not_formalized','scope':'精确α及1/9在条带内的证明已存在；仅该十进制展示未认证，不影响B4。'},
 {'id':'B-number-10','tex_lines':[4571,4580],'claim':'L′/L及Euler积数值实现、截止2×10^5；极端特征值≈−0.353421,0.357462；||C||/δ≈0.826864<1；δ≈0.432310239587548','status':'not_formalized','scope':'B5只证明若真实矩阵范数≤δ则零点在临界线；没有已认证的矩阵数值近似/范数上界。'},
 {'id':'B-number-11','tex_lines':[4577,4599],'claim':'截止10^5加倍时端点变化<3×10^−8；显示零点与图形使用完整计算谱','status':'not_formalized','scope':'图片和稳定性展示无形式数值证书；原文本身明确不认证无限算子R。'}]
(p/'uncovered-numerics.json').write_text(json.dumps(missing,ensure_ascii=False,indent=2)+'\n')
(p/'definition-families.json').write_text(json.dumps(family_rows,ensure_ascii=False,indent=2)+'\n')
for filename,data in [('comparison.json',rows),('definitions-comparison.json',defs)]:
 (p/filename).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
md=['# 附录A、B：独立TeX语义审计','',
 '结论：对9个命名命题、8个原审阅辅助命题逐项检查后，未发现这些命题簇存在未补足的条件弱化、量词交换、公式系数变化或关键定义偷换。另纳入 `variable_uniform_spectral_bound`，专门核实A2算子常数与φ无关，因此共有18个完整预期Prop。32个定义族全部覆盖，含48个独立重建的定义体（其中2个是A3辅助定义）。',
 '',
 '这个结论不等于“整篇附录的所有原文主张已形式化”：11组具体数值/计算声明仍无对应的已认证Lean结果。尤其B3没有为实际存储积分值证明εI<1.68935×10⁻⁵，也没有据此认证905的具体区间；B5没有验证实际矩阵范数≤δ。',
 '',
 '证据分两层：TeX→本参考仍是人工数学语义审查；本参考→实际Lean使用类型赋值检查、定义rfl等式桥梁及根任务运行的真实Lean comparator。comparator不能自动证明TeX含义，定义等式也不会替代共享基础对象的数学解释。没有读取旧Reviewed.lean作为语义证据，没有从旧审计报告复制结论。',
 '',
 '原文：`outputs/formalization-preparation/LiLiuGoldbach16.tex`，审阅范围3931–4599。参考：`appendices/Reference.lean`，完全无axiom、sorry。主库只读。以下所有Lean位置来自实际源码。',
 '',
 '## 命题逐项表','',
 '| 条目 / TeX行 | 原公式与隐含条件 | 量词和Lean对应 | 判断与发现 |',
 '|---|---|---|---|']
for row in rows:
 md.append('| '+row['label']+' / '+str(row['tex_lines'])+' | '+row['original_formula'].replace('|','\\|')+' | '+row['quantifiers'].replace('|','\\|')+'<br>`'+row['actual']+'` | '+row['findings'].replace('|','\\|')+' |')
md+=['','## 重点解释','',
 '1. A2主命题形式为 `∀φ ∀c ∃C,c0 ...`，孤立看它允许算子常数依赖φ，比TeX的 `≪c` 少表达一层独立性。实际库的 `variable_uniform_spectral_bound` 是 `∀c>0 ∃C,c0 ...`，完全没有φ或h，已纳入18项比较。因此在完整实际定理簇中没有遗漏。A3的绝对常数同理由 `lemma_A_3_absolute_operator_bound` 保障。',
 '2. TeX写的 `ηGRH ≍c S/(N log N)` 是由给定算子上界提供的宽度。实际库给出正c0与该精确常数倍的零自由性，取ηGRH等于此常数倍即可；这没有主张最大零自由宽度也有相应上界。若作者意在“最大宽度双边估计”，原文需明确新增定义，现形式化不包含该更强解释。',
 '3. A4的liminf以 `∀ε>0 ∃c0>0 ∀0<c<c0` 的最终下界表达；N与选定γ在最外层固定。系数为 `2 * poleCoefficient N γ * log N / (1+γ²)`；poleCoefficient含 `2/φ(N)` 和重数平方。零点阶数为原模数χ的L函数解析阶数，不是仅计不同高度或原始字符数。`c0≤log N/24` 保证所用条带和距离范围。',
 '4. B1用有序p^k+q^ℓ校正，且max(k,ℓ)≥2；最后除2。指数及素数底数截到N不是截断误差：p,q≥2及p^k+q^ℓ=N使这些参数均≤N。边缘校正按p≤q且p<1000求和。实际J也保留(nm,N)=1。',
 '5. B4的f不是主文反射对称的IsWeight。它是零延拓的C6紧支撑宽权；`FiniteModelWeight`只要求C6和支撑严格在(0,1)内。`FiniteModel.modelMass`与`wideModelMass`都是 `∫f(u)f(1−u)du`。实际模型采样和卷积引理使用这个cross mass；未替换为∫f²。B4同时断言泛函可积、有界和实际Riesz表示，避免仅靠choice默认值0冒充Riesz向量。',
 '6. B5有2562节点，即两条边界各1281个，t=j/16−40；权重1/16，端点各减半，不含1/(2π)。矩阵是√wi·E(si,conj sj)/((1+si)(1+conj sj))·√wj；谱由酉对角化关联实际矩阵，范数为复Euclidean空间诱导范数。有限谱结论没有声称证明无限Hardy算子HypothesisR。',
 '',
 '## 定义逐项表','',
 '| TeX行 | 独立公式 / 精确定义 | 实际Lean定义 | 参考定义与语义判断 |','|---|---|---|---|']
for row in defs:
 md.append('| '+str(row['tex_lines'])+' | '+row['formula'].replace('|','\\|')+' | `'+row['actual']+'` | `'+row['expected']+'`；人工语义已审阅，rfl机械桥梁见Reference |')
md+=['','32个原清单定义族与独立参考的完整映射见 `definition-families.json`。这覆盖原列表，另显式重建A3的Mα与平衡因子。共享原始 `residual`、`kernelOperator`、`hardyMeasure`、`spectralPartialQuaternion`、`eigenvalues`、`GRH`等底层对象的全篇解释需结合其他独立审计部分；此处检查附录确实复用同一对象、参数与规范。',
 '', '## 原文附加数值声明：未覆盖清单','',
 '| TeX行 | 原文主张 | 实际覆盖边界 |','|---|---|---|']
for row in missing:md.append('| '+str(row['tex_lines'])+' | '+row['claim']+' | '+row['scope']+' |')
md+=['','这些是“原文附加算例缺口”，不能误报为B1–B5命名定理本身的类型不一致，也不能因为命名定理比较全部通过而忽略。B3的普遍误差传播定理与B5的普遍谱条件结论均已覆盖，具体数值输入尚缺。',
 '', '## 复核方法及可信边界','',
 '- `Reference.lean` 手工从原文公式、条件、量词重建；允许实际共享基础符号，但其附录具体定义另外重建并检查。',
 '- `comparison.json` 包含18个预期Prop、实际完整名、TeX行、公式、量词、判断和实际源码位置，供根任务外部比较器使用。',
 '- `definitions-comparison.json` 包含48个定义体比较，`Reference.lean`的48个bridge定理只用rfl，检查定义展开后的相同函数，而不是仅比较函数类型。',
 '- `TypeAssignments.lean` 对所有18项做实际定理到完整预期Prop的赋值检查。该检查作为烟雾验证；最终以根任务输出的真实comparator结果为准。',
 '- 数学原文并非形式语言；本参考仍需人的复核。尤其A2“供给宽度”的解释、Fourier-Laplace Hardy模型与原文空间的对应，是必须保留的语义边界。','']
(p/'audit-report.md').write_text('\n'.join(md))
print('report written:',len(rows),'statements,',len(defs),'definitions,',len(family_rows),'families,',len(missing),'uncovered numeric groups')
