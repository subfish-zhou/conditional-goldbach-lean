# 附录A、B：独立TeX语义审计

结论：对9个命名命题、8个原审阅辅助命题逐项检查后，未发现这些命题簇存在未补足的条件弱化、量词交换、公式系数变化或关键定义偷换。另纳入 `variable_uniform_spectral_bound`，专门核实A2算子常数与φ无关，因此共有18个完整预期Prop。32个定义族全部覆盖，含48个独立重建的定义体（其中2个是A3辅助定义）。

这个结论不等于“整篇附录的所有原文主张已形式化”：11组具体数值/计算声明仍无对应的已认证Lean结果。尤其B3没有为实际存储积分值证明εI<1.68935×10⁻⁵，也没有据此认证905的具体区间；B5没有验证实际矩阵范数≤δ。

证据分两层：TeX→本参考仍是人工数学语义审查；本参考→实际Lean使用类型赋值检查、定义rfl等式桥梁及根任务运行的真实Lean comparator。comparator不能自动证明TeX含义，定义等式也不会替代共享基础对象的数学解释。没有读取旧Reviewed.lean作为语义证据，没有从旧审计报告复制结论。

原文：`outputs/formalization-preparation/LiLiuGoldbach16.tex`，审阅范围3931–4599。参考：`appendices/Reference.lean`，完全无axiom、sorry。主库只读。以下所有Lean位置来自实际源码。

## 命题逐项表

| 条目 / TeX行 | 原公式与隐含条件 | 量词和Lean对应 | 判断与发现 |
|---|---|---|---|
| A.1 / [3949, 3989] | 固定 c>0；偶 N≥4,N>exp(10c),GRH(N)；Q=e^(2c)/(2π)∫\|V\|²du/u+Oφ,c(1/logN)，Q≤主项，r=<Tv,v>，\|r\|≤Q\|\|T\|\|；紧、自伴、HS及点值界。 | ∀φ∈IsWeight ∀c>0，逐N结论；∃Cφ,c∃N0φ,c∀偶N≥N0 的渐近式。<br>`LiLiuGoldbach16.proposition_A_1` | 已检查：c不随N变化；固定c的常数容许依赖φ,c；c=1由默认参数定义化归。 |
| A.1 operator / [3954, 4004] | 变边界核仍表示同一残差算子；闭边界核平方可积，边界作用可积，存在平方可和谱。 | ∀N,c在A1范围；所有Hardy函数及内点。<br>`LiLiuGoldbach16.proposition_A_1_operator_spec` | 命名命题的构造/算子补充；已检查无额外算术假设。 |
| A.2 / [4018, 4100] | R↔\|\|T\|\|≤δ；开半空间零点排除↔δ/(2√η(1−η))；S↔S(N)/(2h√(1−η))；固定c的GRH界与S/R误差。 | 固定φ,c后∃C,c0，再∀h；S所需N0在∀h之后；GRH恒作为条件。<br>`LiLiuGoldbach16.proposition_A_2` | 已检查开边界严格性、η∈(0,1/2)、S宽≤1/4与h>0；φ无关算子常数另由A2_uniform补足。 |
| A.2 pointwise / [4058, 4068] | \|G−cφS\|≤Cφ,c S/h 或 Cφ,c δ；常数独立h。 | ∀φ,c ∃C>0 ∀N ∀h；不把h放到C之前。<br>`LiLiuGoldbach16.proposition_A_2_pointwise` | 比eventual版更强的逐点误差保证；不要求h先验发散也可在单点使用。 |
| A.2 uniform witness / [4053, 4056] | \|\|T\|\|≪c(logN)²；可取ηGRH=c0(c)S/(NlogN)，因而ηGRH≍c S/(NlogN)。 | ∀c>0 ∃C≥1,c0>0 ∃N0 ∀偶N≥N0；不含φ或h。<br>`LiLiuGoldbach16.variable_uniform_spectral_bound` | 补上主命题类型中φ先于常数量词的依赖歧义；宽度是所供给的宽度，不是最大零自由宽度。 |
| A.3 / [4110, 4134] | Qα≍φ N^(2α)，\|\|T\|\|≤C((logN)²+α⁻²)；e^(2c)(1+c⁻²)在0+及∞发散。 | φ固定后∃上下常数和N0，∀0<α<1/10；绝对C另见A3_absolute。<br>`LiLiuGoldbach16.lemma_A_3` | 主声明C依赖φ的表面歧义由独立绝对算子界消除。 |
| A.3 absolute C / [4112, 4119] | 存在绝对C，使所有充分大偶N且GRH及0<α<1/10时 \|\|T\|\|≤C((logN)²+α⁻²)。 | ∃C>0∃N0∀N∀α；无φ、c、h参数。<br>`LiLiuGoldbach16.lemma_A_3_absolute_operator_bound` | 已检查绝对性，不仅靠主lemma的依赖φ常数。 |
| A.3 product / [4119, 4134] | QαMα≍φ(logN)²e^(2c)(1+c⁻²)及平方比例表达式。 | C>0固定，∃L,U,N0∀N∀c满足0<αN,c<1/10；L,U依赖φ,C而不依赖c。<br>`LiLiuGoldbach16.lemma_A_3_balance` | C为A3_absolute的绝对常数时恢复TeX的≍φ；并未假设对无约束c及固定N有效。 |
| A.3 widths / [4127, 4159] | 充分误差宽与算子界供给宽之比≍φ h²(logN)^4/S²·e^(4c)(1+c⁻²)²。 | 固定φ,C；∃L,U,N0∀N,c,h；两宽均≤1/4且由正范数的反函数给出。<br>`LiLiuGoldbach16.lemma_A_3_width_ratio` | δ<requiredNorm,suppliedNorm与正δ是反函数有效域；在正范数且宽≤1/4时不是额外算术条件。 |
| A.4 / [4181, 4208] | C=2/φ(N)Σodd mχ(1/2+iγ)²>0；liminf c\|\|T\|\|≥2C logN/(1+γ²)>0；\|\|T\|\|≥z/c，R失败，η≤δ²c²/(3z²)。 | 先固定偶N≥4、GRH及选定γ零点；∀ε>0∃c0>0∀0<c<c0；∃z,cobs≤logN/24。<br>`LiLiuGoldbach16.proposition_A_4` | 已检查系数2、平方重数、分母1+γ²、liminf ε量词、小c与固定N顺序；NeZero/ha为类型良定义条件。 |
| A.4 Euler regularity / [4221, 4229] | RN(w)=∏p\|N(1−p^−1−w)∏p>2,p∤N(1+(2p^−w−p^−2w)/(p(p−2)))在0附近解析；S(N)RN(0)=1。 | ∀偶N≥4∃ε>0∀\|w\|<ε；无GRH要求。<br>`LiLiuGoldbach16.proposition_A_4_baseline_product` | 该补充本身不声称Euler因子分解P=ζR；该恒等式在支持定理另行建立。 |
| B.1 / [4286, 4327] | η为C6、对称、[1000,N−1000]为1；f(u)f(1−u)=η(Nu)²/(log(Nu)log(N(1−u)))；rG=NJ/2−Cpp/2+E。 | N=30030,A=16,L=1000；无GRH，无谱假设。<br>`LiLiuGoldbach16.proposition_B_1` | 已检查proper powers按有序对求和、至少一指数≥2、(pq,N)=1、分母kℓ和边缘校正只计无序素数对。 |
| B.2 / [4351, 4378] | Iχ绝对收敛且=−Σa_nχ(n)；J=5760⁻¹Σχ(−1)\|Iχ\|²；D=5760⁻¹Σ\|Iχ\|²。 | 全部5760字符，包括principal；无GRH。<br>`LiLiuGoldbach16.lemma_B_2` | logDerivative χ s= L′/L(1/2+s)确认在3/2线上；range包含0但该项为0；χ(−1)取实部与其±1值相容。 |
| B.3 / [4443, 4463] | 若ε≥0且平均误差平方≤ε²，则\|J−Jhat\|≤2√Dhat ε+ε²；rG位于[rhat−εr,rhat+εr]∩Z。 | ∀Ihat∀ε≥0；准确有限校正；ε输入必须满足真实积分误差界。<br>`LiLiuGoldbach16.lemma_B_3` | 无GRH；包含整数性。不能据此宣称实际数值误差输入已验证。 |
| B.3 main identity / [4413, 4428] | A=NS c_f/2；rG=A−NB/2−Cpp/2+E。 | 固定N和实际宽权；无数值近似假设。<br>`LiLiuGoldbach16.lemma_B_3_main_integral` | cross mass用∫f(u)f(1−u)，不是∫f²。 |
| B.4 / [4501, 4520] | GRH(30030)下B=<T vW,vW>，vW表示ℓW(h)=(2πi)^−1∫N^s Wtilde(s)(1+s)h(s)ds且ℓW有界。 | 所有Hardy h；N固定；ha:α<β由30030>e^10可证，不添加数学假设。<br>`LiLiuGoldbach16.proposition_B_4` | 已检查实际Riesz关系与有界线性泛函同列结论；无HypothesisR；使用同一残差核。 |
| B.4 wide support / [4522, 4530] | f∈C6_c(0,1)；cross mass和主积分可积。 | 实际f，不要求IsWeight主文的C∞、[1/3,2/3]或反射对称。<br>`LiLiuGoldbach16.proposition_B_4_weight` | FiniteModelWeight只要求C6及支撑内含(0,1)；modelMass为cross mass。 |
| B.5 / [4533, 4561] | 2562节点，两边界[-40,40]，步1/16，端点半权，无1/(2π)；X=det(I−4q(1−q)C²/δ²)=∏(1−4λj²q(1−q)/δ²)，X(1−q)=X(q)，\|\|C\|\|≤δ⇒所有零点Re=1/2。 | 章节继承GRH；实谱由酉对角化绑定真实矩阵；条件范数界未声称实际数值通过。<br>`LiLiuGoldbach16.proposition_B_5` | 已检查两√w、核分母、复共轭和Euclidean算子范数；未把有限矩阵等同无限Hardy算子。 |

## 重点解释

1. A2主命题形式为 `∀φ ∀c ∃C,c0 ...`，孤立看它允许算子常数依赖φ，比TeX的 `≪c` 少表达一层独立性。实际库的 `variable_uniform_spectral_bound` 是 `∀c>0 ∃C,c0 ...`，完全没有φ或h，已纳入18项比较。因此在完整实际定理簇中没有遗漏。A3的绝对常数同理由 `lemma_A_3_absolute_operator_bound` 保障。
2. TeX写的 `ηGRH ≍c S/(N log N)` 是由给定算子上界提供的宽度。实际库给出正c0与该精确常数倍的零自由性，取ηGRH等于此常数倍即可；这没有主张最大零自由宽度也有相应上界。若作者意在“最大宽度双边估计”，原文需明确新增定义，现形式化不包含该更强解释。
3. A4的liminf以 `∀ε>0 ∃c0>0 ∀0<c<c0` 的最终下界表达；N与选定γ在最外层固定。系数为 `2 * poleCoefficient N γ * log N / (1+γ²)`；poleCoefficient含 `2/φ(N)` 和重数平方。零点阶数为原模数χ的L函数解析阶数，不是仅计不同高度或原始字符数。`c0≤log N/24` 保证所用条带和距离范围。
4. B1用有序p^k+q^ℓ校正，且max(k,ℓ)≥2；最后除2。指数及素数底数截到N不是截断误差：p,q≥2及p^k+q^ℓ=N使这些参数均≤N。边缘校正按p≤q且p<1000求和。实际J也保留(nm,N)=1。
5. B4的f不是主文反射对称的IsWeight。它是零延拓的C6紧支撑宽权；`FiniteModelWeight`只要求C6和支撑严格在(0,1)内。`FiniteModel.modelMass`与`wideModelMass`都是 `∫f(u)f(1−u)du`。实际模型采样和卷积引理使用这个cross mass；未替换为∫f²。B4同时断言泛函可积、有界和实际Riesz表示，避免仅靠choice默认值0冒充Riesz向量。
6. B5有2562节点，即两条边界各1281个，t=j/16−40；权重1/16，端点各减半，不含1/(2π)。矩阵是√wi·E(si,conj sj)/((1+si)(1+conj sj))·√wj；谱由酉对角化关联实际矩阵，范数为复Euclidean空间诱导范数。有限谱结论没有声称证明无限Hardy算子HypothesisR。

## 定义逐项表

| TeX行 | 独立公式 / 精确定义 | 实际Lean定义 | 参考定义与语义判断 |
|---|---|---|---|
| [3954, 3958] | S={s:α<Re(s)<β} | `LiLiuGoldbach16.strip` | `TexAuditAB.variableStrip`；人工语义已审阅，rfl机械桥梁见Reference |
| [3954, 3958] | Fourier-Laplace Hardy模型Lp²(hardyMeasure α β) | `LiLiuGoldbach16.HardySpace` | `TexAuditAB.variableHardySpace`；人工语义已审阅，rfl机械桥梁见Reference |
| [3954, 3958] | 左右两条无向边界线 | `LiLiuGoldbach16.boundaryPoint` | `TexAuditAB.variableBoundary`；人工语义已审阅，rfl机械桥梁见Reference |
| [3954, 3958] | 不变算术残差核E/((1+s)(1+conj z))在新Hardy空间的作用 | `LiLiuGoldbach16.residualOperator` | `TexAuditAB.variableOperator`；人工语义已审阅，rfl机械桥梁见Reference |
| [3954, 3958] | (2πi)^−1∫N^s Wtilde(s)(1+s)h(s)ds | `LiLiuGoldbach16.functionalValue` | `TexAuditAB.variableFunctional`；人工语义已审阅，rfl机械桥梁见Reference |
| [3954, 3958] | 表示该泛函的Riesz向量 | `LiLiuGoldbach16.rieszVector` | `TexAuditAB.variableVector`；人工语义已审阅，rfl机械桥梁见Reference |
| [3970, 3977] | (2π)^−1∫(Nu)^(2α)V²/(1+(Nu)^(−2(β−α)))du/u | `LiLiuGoldbach16.normFunctional` | `TexAuditAB.variableFunctionalNorm`；人工语义已审阅，rfl机械桥梁见Reference |
| [4020, 4024] | 相同δN尺度的复切片谱积 | `LiLiuGoldbach16.spectralComplex` | `TexAuditAB.variableComplexProduct`；人工语义已审阅，rfl机械桥梁见Reference |
| [4020, 4024] | 四元数谱积为partial products极限 | `LiLiuGoldbach16.spectralQuaternion` | `TexAuditAB.variableQuaternionProduct`；人工语义已审阅，rfl机械桥梁见Reference |
| [4024, 4031] | 所有四元数零点实部1/2 | `LiLiuGoldbach16.SpectralR` | `TexAuditAB.pointwiseR`；人工语义已审阅，rfl机械桥梁见Reference |
| [4024, 4031] | 开半空间Re(q)>1−η无零点 | `LiLiuGoldbach16.SpectralZeroFree` | `TexAuditAB.pointwiseZeroFree`；人工语义已审阅，rfl机械桥梁见Reference |
| [3949, 3953] | αN,c=c/logN | `LiLiuGoldbach16.alpha` | `TexAuditAB.boundaryParameter`；人工语义已审阅，rfl机械桥梁见Reference |
| [4093, 4100] | 固定c的eventual R；阈值依赖c | `LiLiuGoldbach16.HypothesisRAt` | `TexAuditAB.eventualR`；人工语义已审阅，rfl机械桥梁见Reference |
| [4025, 4031] | h正、沿偶数发散及最终η≤1/4；阈值依赖c,h | `LiLiuGoldbach16.HypothesisSAt` | `TexAuditAB.eventualS`；人工语义已审阅，rfl机械桥梁见Reference |
| [4184, 4186] | L函数解析零点阶数，非零点为0 | `LiLiuGoldbach16.zeroMultiplicity` | `TexAuditAB.poleOrder`；人工语义已审阅，rfl机械桥梁见Reference |
| [4187, 4191] | 2/φ(N)Σodd mχ² | `LiLiuGoldbach16.poleCoefficient` | `TexAuditAB.poleMass`；人工语义已审阅，rfl机械桥梁见Reference |
| [4221, 4229] | 有限坏素数积与无限正则Euler积 | `LiLiuGoldbach16.baselineProductR` | `TexAuditAB.regularEulerFactor`；人工语义已审阅，rfl机械桥梁见Reference |
| [4114, 4117] | C((logN)²+α⁻²) | `LiLiuGoldbach16.baselineBound` | `TexAuditAB.operatorMajorant`；人工语义已审阅，rfl机械桥梁见Reference |
| [4119, 4126] | e^(2c)(1+c⁻²) | `LiLiuGoldbach16.balanceFactor` | `TexAuditAB.boundaryCost`；人工语义已审阅，rfl机械桥梁见Reference |
| [4281, 4284] | N=30030 | `LiLiuGoldbach16.experimentN` | `TexAuditAB.numericalN`；人工语义已审阅，rfl机械桥梁见Reference |
| [4292, 4300] | 分段13阶二项式平滑截断 | `LiLiuGoldbach16.cutoffPolynomial` | `TexAuditAB.P`；人工语义已审阅，rfl机械桥梁见Reference |
| [4291, 4295] | A=16,L=1000对称双截断 | `LiLiuGoldbach16.wideCutoff` | `TexAuditAB.eta`；人工语义已审阅，rfl机械桥梁见Reference |
| [4301, 4305] | sqrt(1−u)η(Nu)/sqrt(log(Nu)log(N(1−u)))零延拓 | `LiLiuGoldbach16.wideCompanion` | `TexAuditAB.W`；人工语义已审阅，rfl机械桥梁见Reference |
| [4303, 4305] | W(u)/sqrtu | `LiLiuGoldbach16.wideWeight` | `TexAuditAB.f`；人工语义已审阅，rfl机械桥梁见Reference |
| [4306, 4310] | N⁻¹Σn+m=N,(nm,N)=1 ΛnΛm f(n/N)f(m/N) | `LiLiuGoldbach16.wideCorrelation` | `TexAuditAB.J`；人工语义已审阅，rfl机械桥梁见Reference |
| [4311, 4311] | 无序素数对p≤q,p+q=N | `LiLiuGoldbach16.unorderedPrimePairs` | `TexAuditAB.primePairCount`；人工语义已审阅，rfl机械桥梁见Reference |
| [4311, 4312] | p<L的无序素数对缺失权1−η(p)² | `LiLiuGoldbach16.edgeCorrection` | `TexAuditAB.edge`；人工语义已审阅，rfl机械桥梁见Reference |
| [4312, 4314] | 有序真素数幂校正η(p^k)²/(kℓ) | `LiLiuGoldbach16.primePowerCorrection` | `TexAuditAB.properPowers`；人工语义已审阅，rfl机械桥梁见Reference |
| [4361, 4363] | Λ(n)W(n/N)/sqrt n | `LiLiuGoldbach16.countingCoefficient` | `TexAuditAB.coefficient`；人工语义已审阅，rfl机械桥梁见Reference |
| [4351, 4355] | (2π)⁻¹∫N^(1+it)Wtilde(1+it)L′/L(3/2+it)dt | `LiLiuGoldbach16.countingIntegral` | `TexAuditAB.integralI`；人工语义已审阅，rfl机械桥梁见Reference |
| [4357, 4360] | Σ1≤n<N,(n,N)=1 a_n² | `LiLiuGoldbach16.diagonalCountingMoment` | `TexAuditAB.diagonalD`；人工语义已审阅，rfl机械桥梁见Reference |
| [4445, 4446] | 5760⁻¹Σχχ(−1)\|Ihatχ\|² | `LiLiuGoldbach16.approxSignedMoment` | `TexAuditAB.signedJhat`；人工语义已审阅，rfl机械桥梁见Reference |
| [4445, 4446] | 5760⁻¹Σχ\|Ihatχ\|² | `LiLiuGoldbach16.approxDiagonalMoment` | `TexAuditAB.diagonalDhat`；人工语义已审阅，rfl机械桥梁见Reference |
| [4422, 4422] | c_f=∫0¹ f(u)f(1−u)du | `LiLiuGoldbach16.wideModelMass` | `TexAuditAB.crossMass`；人工语义已审阅，rfl机械桥梁见Reference |
| [4413, 4415] | S(N)∫16^(N/2)η(x)²/(log x log(N−x))dx | `LiLiuGoldbach16.wideMainIntegral` | `TexAuditAB.mainIntegral`；人工语义已审阅，rfl机械桥梁见Reference |
| [4422, 4424] | S(N)c_f−J | `LiLiuGoldbach16.wideResidual` | `TexAuditAB.residualB`；人工语义已审阅，rfl机械桥梁见Reference |
| [4447, 4448] | ε≥0且5760⁻¹Σ\|I−Ihat\|²≤ε² | `LiLiuGoldbach16.HasMomentError` | `TexAuditAB.momentError`；人工语义已审阅，rfl机械桥梁见Reference |
| [4453, 4456] | N Jhat/2−Cpp/2+E | `LiLiuGoldbach16.approxPrimeCount` | `TexAuditAB.countCentre`；人工语义已审阅，rfl机械桥梁见Reference |
| [4457, 4459] | N(2√Dhat ε+ε²)/2 | `LiLiuGoldbach16.countError` | `TexAuditAB.countRadius`；人工语义已审阅，rfl机械桥梁见Reference |
| [4514, 4519] | 固定1/9线上的宽权线性泛函 | `LiLiuGoldbach16.wideFunctional` | `TexAuditAB.ellW`；人工语义已审阅，rfl机械桥梁见Reference |
| [4512, 4514] | 选择实际表示ℓW的Riesz向量；存在性由B4保证 | `LiLiuGoldbach16.wideRieszVector` | `TexAuditAB.vectorW`；人工语义已审阅，rfl机械桥梁见Reference |
| [4533, 4535] | 2×1281节点，左右边界，t=j/16−40 | `LiLiuGoldbach16.spectralNode` | `TexAuditAB.node`；人工语义已审阅，rfl机械桥梁见Reference |
| [4534, 4535] | 1/16，端点半权，无2π归一因子 | `LiLiuGoldbach16.trapezoidWeight` | `TexAuditAB.nodeWeight`；人工语义已审阅，rfl机械桥梁见Reference |
| [4544, 4549] | √wi E(si,conj sj)/((1+si)(1+conj sj)) √wj | `LiLiuGoldbach16.finiteSpectralMatrix` | `TexAuditAB.matrixC`；人工语义已审阅，rfl机械桥梁见Reference |
| [4536, 4541] | det(I−4q(1−q)C²/δ²) | `LiLiuGoldbach16.finiteSpectralFunction` | `TexAuditAB.finiteX`；人工语义已审阅，rfl机械桥梁见Reference |
| [4553, 4560] | C=U diag(real eigenvalues) U*，U*U=UU*=I | `LiLiuGoldbach16.IsFiniteSpectrum` | `TexAuditAB.finiteSpectrum`；人工语义已审阅，rfl机械桥梁见Reference |
| [4553, 4553] | 选择与实际矩阵绑定的实特征值列表 | `LiLiuGoldbach16.finiteEigenvalues` | `TexAuditAB.eigenvalueList`；人工语义已审阅，rfl机械桥梁见Reference |
| [4560, 4561] | 复Euclidean空间单位球上矩阵作用的sup范数 | `LiLiuGoldbach16.finiteMatrixOpNorm` | `TexAuditAB.matrixNorm`；人工语义已审阅，rfl机械桥梁见Reference |

32个原清单定义族与独立参考的完整映射见 `definition-families.json`。这覆盖原列表，另显式重建A3的Mα与平衡因子。共享原始 `residual`、`kernelOperator`、`hardyMeasure`、`spectralPartialQuaternion`、`eigenvalues`、`GRH`等底层对象的全篇解释需结合其他独立审计部分；此处检查附录确实复用同一对象、参数与规范。

## 原文附加数值声明：未覆盖清单

| TeX行 | 原文主张 | 实际覆盖边界 |
|---|---|---|
| [4341, 4345] | 75个边缘素数对、26个无序真素数幂对；E=44.35776816334822525…，Cpp/2=10.16758713116445818… | 命名B1之外的具体算例；B1只给精确符号恒等式。 |
| [4389, 4403] | h=0.1,T=1600；2^20 FFT网格；24阶Euler–Maclaurin、32高度重置；积分输出Jhat≈0.05799599193959489,Dhat≈0.29331844084848136 | 未见存储5760个Ihat值、数值积分实现或该输出的有理证书绑定实际integralI。 |
| [4408, 4419] | HL预测积分≈908.1405628685、宽权A≈851.831147718741；65位数值积分及C2加速算法参数 | wideMainIntegral有精确定义，未认证该近似；传统HL积分的具体数值也未认证。 |
| [4420, 4421] | A−Cpp/2+E≈886.021328750925 | 符号校正公式已覆盖；十进制数值未认证。 |
| [4430, 4437] | −N Bhat/2≈18.978671254276及rhat≈905.0000000052 | B3的Ihat为任意输入，尚无特定Ihat及该中心的证明。 |
| [4475, 4486] | 3280个非零a_n；有限变换有理包围证明RMS积分误差<1.68935×10^−5 | 这是应用B3得905最关键的未填输入；HasMomentError仅是定义，lemma_B_3将该界作为假设。 |
| [4487, 4490] | εr≈0.274758682716，外舍入[904.725241,905.274759]∩Z={905} | 没有在Lean中将真实积分误差传递到该具体区间；一般整数区间lemma不提供这项数值证书。 |
| [4491, 4496] | 精确905无序对、1810有序对；直接有理求和与独立素数枚举双重检验 | 对活跃LiLiuGoldbach目录检索905未发现对应命题；可另补枚举证书，但不能代替积分误差认证。 |
| [4501, 4505] | α30030≈0.09699366 | 精确α及1/9在条带内的证明已存在；仅该十进制展示未认证，不影响B4。 |
| [4571, 4580] | L′/L及Euler积数值实现、截止2×10^5；极端特征值≈−0.353421,0.357462；||C||/δ≈0.826864<1；δ≈0.432310239587548 | B5只证明若真实矩阵范数≤δ则零点在临界线；没有已认证的矩阵数值近似/范数上界。 |
| [4577, 4599] | 截止10^5加倍时端点变化<3×10^−8；显示零点与图形使用完整计算谱 | 图片和稳定性展示无形式数值证书；原文本身明确不认证无限算子R。 |

这些是“原文附加算例缺口”，不能误报为B1–B5命名定理本身的类型不一致，也不能因为命名定理比较全部通过而忽略。B3的普遍误差传播定理与B5的普遍谱条件结论均已覆盖，具体数值输入尚缺。

## 复核方法及可信边界

- `Reference.lean` 手工从原文公式、条件、量词重建；允许实际共享基础符号，但其附录具体定义另外重建并检查。
- `comparison.json` 包含18个预期Prop、实际完整名、TeX行、公式、量词、判断和实际源码位置，供根任务外部比较器使用。
- `definitions-comparison.json` 包含48个定义体比较，`Reference.lean`的48个bridge定理只用rfl，检查定义展开后的相同函数，而不是仅比较函数类型。
- `TypeAssignments.lean` 对所有18项做实际定理到完整预期Prop的赋值检查。该检查作为烟雾验证；最终以根任务输出的真实comparator结果为准。
- 数学原文并非形式语言；本参考仍需人的复核。尤其A2“供给宽度”的解释、Fourier-Laplace Hardy模型与原文空间的对应，是必须保留的语义边界。

最终本地验证：48个定义rfl桥梁全部编译通过（exit 0）；18个完整Prop赋值检查全部通过（exit 0）。真实Lean comparator结果由根任务统一提供。冻结Reference SHA256：`6be27e81044dca6dd2ee92ba114b0eb4709801b47e80cdfae1324de90c3877b1`。
