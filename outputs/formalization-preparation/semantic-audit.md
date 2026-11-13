依赖审计修订 9 已覆盖 **38 个命名结论、121 个定义族**。当前源码有 **102 个定理声明（38 主声明、60 配套、4 辅助）和 171 个定义声明**；类型检查退出码 0，全部定理仍为 `by sorry`。当前源码 SHA-256：`bd3b94f0b7218b1675e5346ba36c05985ab161868f40e8524796912268f34261`。

新增[交互依赖审阅页](dependency-review.html)、[依赖审计台账](dependency-graph.json)和[依赖审计说明](dependency-audit.md)。图中分开记录原文实际证明依赖、声明中的定义引用及构造义务；它不是这些 `sorry` 声明的 Lean 已证依赖图。

5.3 与 5.4 无循环，实际后段顺序是 6.4 → 6.5 → Theorem 6.2。新增 `theorem_6_1_abstract_dictionary`，从原纯谱证明抽出固定及可变条带共用的零点—范数字典；该接口仍未证明，也没有给原附录 A.2 增加调用者假设。总化选择的默认零值不能代替对象存在、核表示或乘积收敛，这些守卫逐条列入依赖审计。

现有项目的复用评估也已下钻校准：`CompletedLogDerivativeConstant.lean` 已给完成 L 函数在任意避零点的 Hadamard 展开；本稿只差非零常数归一化、重数索引、两点相减及正常收敛适配。单位窗零点计数应由 `reference_mass_improved` 正核界导出，不能对两个全局计数上界作差。精确路径与行号见依赖台账 `existing_project_bridges`。

下面保留原始 TeX 阶段的历史叙述、逐条证据及 **五种待用户审查的数学编码选择**；这些选择的状态没有改变。当前验证记录以 `verification.json` 修订 9 为准，历史哈希不代表当前源码。

---

上一轮（原始 TeX 复核，修订 8）已按用户提供的原始 TeX，重新核对 **38 个命名结论、121 个定义族**。现有 Lean 源码包含 171 个定义声明与 101 个定理，类型检查通过，所有证明仍为 `by sorry`。这份记录不构成无遗漏或数学等价性的形式证明。

本轮具体发现和逐子句依据见 [TeX 复核报告](/home/azureuser/Documents/Codex/2026-11-13/files-mentioned-by-the-user-liliugoldbach16/outputs/formalization-preparation/tex-audit.md)、[完整 TeX 台账](/home/azureuser/Documents/Codex/2026-11-13/files-mentioned-by-the-user-liliugoldbach16/outputs/formalization-preparation/tex-audit.json)。原始文件为 [LiLiuGoldbach16.tex](/home/azureuser/Documents/Codex/2026-11-13/files-mentioned-by-the-user-liliugoldbach16/outputs/formalization-preparation/LiLiuGoldbach16.tex)；原PDF继续作为版面参照。

本轮修正中文的 V/Ψ、η/W/f 和 C_{N,γ} 记号；补足 A.1 可变边界算子的真实核表示、L²、可积性与谱存在义务。另把奇特征正交投影、Perron 留数和 Poisson 零参数恒等作用明确成配套接口。这些分别是展示修正、对象表示缺口及证明依赖补充，不能一概称为原论文定理错误。

上一轮发现的权类错误已经修复：`ContDiff ℝ ⊤` 在当前 Mathlib 是解析阶 ω，导致非零紧支撑条件不可能；当前使用真正的 `ContDiff ℝ ∞`。A.2 的过强 GRH 前提、部分收敛及表示义务也已修正。原文 6.5 的第三个估计始终存在于旧 Lean 中，先前中文将其压缩成文字；当前页面独立显示全部三式，配套接口折叠展示。

**仍需审阅的数学编码选择。** TeX 确认原文表达，并不会证明这些编码与原文等价。

- **联合亚纯性用共同非恒零整分母表达**：是否接受在共同分母非零处比较的整个商表示作为本文联合亚纯恒等的编码？其与未来多复变亚纯芽接口的形式等价尚未证明。（Proposition 3.2, Lemma 4.2）
- **Hardy 空间使用加权 Fourier–Laplace L² 模型**：是否接受以 weighted Lp 为实际类型，以唯一表示、线性、等距和边界迹定理对接原文全纯函数空间？这些桥接已列为结论，证明仍空置。（Lemma 5.2）
- **HS 与谱选择限于可数无限正交基的 Hardy 模型**：是否接受该专用可数基接口，以及含零特征值的完整特征基与原文非零谱按重数列出的转换？不能把它视作任意有限或不可分维空间的通用定义。（Proposition 5.3）
- **正迹类、迹与 Fredholm 行列式使用本文专用接口**：是否接受正迹类谱定义及选择无关性接口？现已拆开 A 自身的谱行列式与 A=T² 的桥接，未再把同一个 μ(T)² 乘积改名充当证明；尚未对接通用 trace-class/Fredholm API。（Proposition 6.1, Proposition 6.5）
- **各四元数切片通过同一复整函数表达与转移重数**：是否接受 intrinsic entire 的共同复函数编码及由 all_slices 向各切片传递重数？这不是 Fueter 正则性定义，也不是已有通用四元数 analyticOrder 接口。（Proposition 6.1, Proposition 6.3）

新增接口已独立交叉复核，见 [tex-cross-check.json](/home/azureuser/Documents/Codex/2026-11-13/files-mentioned-by-the-user-liliugoldbach16/outputs/formalization-preparation/tex-cross-check.json)。该历史轮次源码哈希：`997fef646a1980da0a56a8b19ead78113cec5b2a128064b8fb4403ac23022e5a`。当前哈希见本页开头。

**命名条目。**

| 原文条目 | TeX 行段 | 累计状态 | 本轮简注 |
|---|---|---|---|
| Theorem 1.1 | L289–298 | 已修正或补充，待审 | TeX复核：TeX确认主权确为C∞，充分大偶数GRH与预先指定的S(h)并列；C在h之前，阈值可依赖h。 |
| Theorem 1.2 | L315–323 | 已修正或补充，待审 | TeX复核：TeX确认误差为sqrt(S(N)/N)(logN)^(3/2)，且紧邻正文明确R⇒每个可容许S(h)。 |
| Lemma 3.1 | L376–382, L1090–1100 | 已修正或补充，待审 | TeX复核：主结论与TeX一致；新增奇特征正交投影式作为直接依赖，不是修补原主结论。 |
| Proposition 3.2 | L1180–1200 | 数学编码待审 | TeX复核：TeX确认联合亚纯性及极点位置；目前共同非恒零整分母表示继续作为需人审的编码选择。 数学编码选择仍待审。 |
| Lemma 3.3 | L1247–1260 | 已修正或补充，待审 | TeX复核：TeX核实完成L归一化、零点按重数、两个变量共同的绝对局部一致收敛及单位窗计数。 |
| Lemma 3.4 | L1274–1290 | 已修正或补充，待审 | TeX复核：TeX确认参考点2、分母3/2、Gamma修正正负号及非本原Euler修正，未发现新差异。 |
| Lemma 3.5 | L1365–1380 | 已修正或补充，待审 | TeX复核：TeX确认两变量独立竖线积分、无条件与GRH两种σ域、+,+,−三族和支集消去。 |
| Lemma 4.1 | L1480–1497 | 已修正或补充，待审 | TeX复核：TeX确认三个不同积分及+,+,−组合；当前Lean域比正文预告准确地使用正式引理的完整域。 |
| Lemma 4.2 | L1538–1551 | 数学编码待审 | TeX复核：TeX明确写“identity of meromorphic functions”；当前全局共同分母补充保留该语义，未改回仅点值公式。 数学编码选择仍待审。 |
| Lemma 4.3 | L1611–1630 | 已修正或补充，待审 | TeX复核：TeX确认单极点留数、严格条带端点与奇异级数三段界；当前陈述与配套义务齐全。 |
| Proposition 4.4 | L1704–1710 | 本轮未发现差异 | TeX复核：TeX确认无条件全纯域Ω及使用延拓密度；旧PDF审计后的陈述不需再改。 |
| Proposition 4.5 | L1760–1768 | 本轮未发现差异 | TeX复核：TeX确认GRH只在残差/字符核部分引入，两个减号、对称与Hermitian关系无新差异。 |
| Proposition 5.1 | L1834–1855, L1926–1943, L2299–2308 | 已修正或补充，待审 | TeX复核：原TeX确认两个核的Hermitian/全纯性、闭带邻域、Fueter方程与两条距离常数；现稿逐项保留。 |
| Lemma 5.2 | L2030–2046 | 数学编码待审 | TeX复核：原TeX确认任意实端点、配对上确界、双边迹范数及闭迹像；现有主声明与配套声明共同覆盖。 数学编码选择仍待审。 |
| Proposition 5.3 | L1834–1855, L2123–2141, L2299–2308 | 数学编码待审 | TeX复核：原TeX确认四个边界乘积的L²、紧/自伴/HS、谱平方和、精确HS积分及最大特征值；现稿无新增缺项。 数学编码选择仍待审。 |
| Proposition 5.4 | L1834–1855, L2226–2253, L2299–2308 | 已修正或补充，待审 | TeX复核：原TeX确认csc公式及(5.7)等号、(5.8)精确常数和(5.9)固定轮廓；exact_norm与fixed_contour均已存在。 |
| Proposition 6.1 | L1834–1855, L2299–2308, L2388–2409 | 数学编码待审 | TeX复核：原TeX明确普通Fredholm取A=T²，其本征值是μ(T)²；现稿独立正迹类定义与桥接一致，仍属待证专用接口。 数学编码选择仍待审。 |
| Proposition 6.2 | L1834–1855, L2299–2308, L2443–2476 | 已修正或补充，待审 | TeX复核：原TeX确认四条对称、中心乘积、任意纯虚单位切片上的实乘积与实轴下界；现稿及配套收敛声明齐全。 |
| Proposition 6.3 | L1834–1855, L2299–2308, L2493–2511 | 数学编码待审 | TeX复核：原TeX确认三类根、无额外乘积极限零点、有限例外实根对、切片重数及中心偶数阶；现稿覆盖。 数学编码选择仍待审。 |
| Theorem 6.1 | L1834–1855, L2299–2308, L2552–2570 | 已修正或补充，待审 | TeX复核：原TeX确认开半空间与非严格范数界等价，0<η<1/2；宽度式及双边常数保持。 |
| Theorem 6.2 | L1834–1855, L2299–2308, L2616–2629 | 已修正或补充，待审 | TeX复核：原TeX确认GRH仅逐模数假设，常数及充分大阈值绝对；现稿量词与固定倍数宽度相符。 |
| Lemma 6.4 | L1834–1855, L2299–2308, L2655–2664, L2736–2745, L2912–2929 | 已修正或补充，待审 | TeX复核：命名引理本身与原TeX一致；本轮仅补证明依赖：Perron去心留数与Poisson零参数恒等作用、正参数归一化及卷积。 |
| Proposition 6.5 | L1834–1855, L2299–2308, L2975–2986 | 数学编码待审 | TeX复核：原TeX确为P、D、K三式，standing assumptions固定α_N=1/logN；没有新发现的漏式，现有表示与Hardy向量补充仍适用。 数学编码选择仍待审。 |
| Lemma 7.1 | L3282–3297 | 已修正或补充，待审 | TeX复核：TeX确认反演、衰减和0<σ≤1/9的单/双积分；当前Lean全部匹配。 |
| Lemma 7.2 | L3374–3390 | 已修正或补充，待审 | TeX复核：TeX确认两项积分及模型负号，延拓密度和卷积实现没有新差异。 |
| Proposition 7.3 | L3523–3531 | 本轮未发现差异 | TeX复核：精确剩余项、绝对可积与轮廓独立匹配原TeX。 |
| Proposition 7.4 | L3623–3638 | 已修正或补充，待审 | TeX复核：Lean正确；中文Q积分把V(u)误写成Ψ(u)，改回原文V并与Ψ_N(s)区分。 |
| Theorem 7.1 | L3710–3722 | 本轮未发现差异 | TeX复核：TeX确认精确符号、Q范数界和只依赖权的统一估计。 |
| Lemma 7.5 | L3781–3795 | 已修正或补充，待审 | TeX复核：TeX确认逐点误差和沿合法模数子序列的渐近准则。 |
| Proposition A.1 | L3960–3989 | 已修正或补充，待审 | TeX复核：补变量c的实际核表示、边界L²、作用积分可积性和谱数据非空；原假设不加码。 |
| Proposition A.2 | L4033–4068 | 已修正或补充，待审 | TeX复核：TeX确认上一轮GRH量词修复，常数与h独立而阈值可依赖h。 |
| Lemma A.3 | L4110–4134 | 已修正或补充，待审 | TeX复核：TeX确认绝对C、移动边界一致性及合法宽度比，未发现新差异。 |
| Proposition A.4 | L4181–4208 | 已修正或补充，待审 | TeX复核：条件与三个障碍结论匹配；中文改回原文C_{N,γ}，不改Lean公式。 |
| Proposition B.1 | L4316–4327 | 已修正或补充，待审 | TeX复核：Lean正确；中文把η/W/f混名，改为原TeX截断η、伴随权W、宽权f。 |
| Lemma B.2 | L4366–4378 | 本轮未发现差异 | TeX复核：TeX确认全部5760特征、计数线和两个矩；不存在GRH前提。 |
| Lemma B.3 | L4443–4463 | 已修正或补充，待审 | TeX复核：RMS前提、精确修正和整数闭区间完整匹配，数值905证书仍未形式化。 |
| Proposition B.4 | L4507–4520 | 已修正或补充，待审 | TeX复核：TeX确认宽权C6、标准c=1、GRH及相同算子二次型。 |
| Proposition B.5 | L4551–4561 | 本轮未发现差异 | TeX复核：有限谱的全局GRH在TeX中明确；不声称有限谱认证无限算子。 |

**定义族。** 新增配套对象继续归入原有数学定义族；数量不代表所有证明局部记号都需要全局接口。

| 定义族 | TeX 行段 | 累计状态 | 本轮简注 |
|---|---|---|---|
| weight | L151–154 | 已修正或补充，待审 | TeX复核：C∞、非零、非负有界、对称、固定窄支集全部一致；现用ContDiff ℝ ∞，不是解析⊤。 |
| vonMangoldt | L113–115 | 本轮未发现差异 | TeX复核：Λ(p^k)=logp，k≥1；其余为0，直接复用Mathlib。 |
| singularSeries | L117–121 | 本轮未发现差异 | TeX复核：精确2C2乘有限修正；与项目liuSingularSeries的二倍关系保持。 |
| twinPrimeConstant | L117–121 | 本轮未发现差异 | TeX复核：乘积仅p>2，分母(p−1)^2，常数中不另含2。 |
| goldbachCorrelation | L155–164 | 本轮未发现差异 | TeX复核：有序正整数对、n+m=N、(nm,N)=1、1/N和两份φ均一致；有限range截断由支集支持。 |
| weightMass | L160–162 | 本轮未发现差异 | TeX复核：实平方积分0到1；cφ>0由非零光滑主权获得，不能当任意φ的无条件性质。 |
| GRH | L182–185 | 本轮未发现差异 | TeX复核：覆盖导子整除N的所有本原L函数非平凡零点，非仅奇字符；当前GRH定义一致。 |
| spectralScale | L2343–2351 | 本轮未发现差异 | TeX复核：TeX明确δ²=S(N)(logN)³/N，现sqrt与rpow归一化一致；只在充分大偶数域解释。 |
| spectralProduct | L2358–2374, L2388–2409 | 已修正或补充，待审 | TeX复核：TeX的非零谱乘积与现完整基零填充因子1一致；有序四元数有限积、局部一致极限与选择独立的配套声明均保留。 |
| admissibleH | L273–282, L345–346 | 本轮未发现差异 | TeX复核：h预先给定、在实际偶N≥4域为正、沿偶数趋∞、宽度最终≤1/4；全文注明N极限沿偶数。 |
| hypothesisWidth | L276–278 | 本轮未发现差异 | TeX复核：h(N)^2(logN)^3/(N S(N))；实际应用的正性和η≤1/4条件分开保留。 |
| HypothesisS | L273–282 | 本轮未发现差异 | TeX复核：逐大偶N的GRH(N)⇒开半空间无零，不要求定义内部EvenEventually GRH。 |
| HypothesisR | L306–310 | 本轮未发现差异 | TeX复核：逐大偶N的GRH(N)⇒每个四元数零点实部1/2，全部零点量词保持。 |
| oddCharacters | L373–382, L1059–1068 | 已修正或补充，待审 | TeX复核：所有奇字符，包括非本原；非单位取0。新增正交投影支持接口。 定义未改；新增的奇特征正交式作为Lemma 3.1直接依赖。 |
| characterPolynomial | L399–402 | 本轮未发现差异 | TeX复核：Lean使用原文第二种N^(-1/2)有限和，第一种1/sqrt(n)表达由Φ=√uφ和支集转换。 |
| companionWeight | L404–406 | 本轮未发现差异 | TeX复核：Φ(u)=√uφ(u)，实域与原文一致。 |
| diagonalMoment | L391–397 | 本轮未发现差异 | TeX复核：D(N)=N^-1Σ_(n,N)=1 Λ²φ²，n=0项Λ0=0。 |
| characterMoment | L391–397 | 本轮未发现差异 | TeX复核：P(N)=2/varphi(N)Σodd \|Pχ\|²，Euler totient与权φ区分。 |
| characterKernel | L415–419, L627–631 | 数学编码待审 | TeX复核：第二L因子是共轭字符在z处；Lean的conj(gχ(conj z))等价表达。Hermitian形式只在z再共轭后使用。 数学编码选择仍待审。 |
| mellinWeight | L422–427 | 本轮未发现差异 | TeX复核：Mathlib.mellin积分Φ(u)u^(s−1)；全部实竖线反演靠权支集和正则性。 |
| verticalIntegral | L341–346, L422–427 | 本轮未发现差异 | TeX复核：向上ds=i dt，1/(2πi)恰化为高度参数积分的1/(2π)，无符号或2π遗漏。 |
| signedFamilies | L463–477 | 本轮未发现差异 | TeX复核：m=n+kN、n=m+kN、n+m=kN，k≥1和+,+,−对应完整。 |
| signedBeta | L514–517, L1460–1478 | 本轮未发现差异 | TeX复核：K−为三个Beta的+,+,−组合。实际betaIntegral编码只在共同收敛域解释；全局亚纯另用betaGamma组合。 |
| betaFunction | L1469–1478 | 数学编码待审 | TeX复核：原始Beta积分在Re u,Re v>0，Gamma商提供亚纯表达。Mathlib betaIntegral_eq_Gamma_mul_div精确桥接，不需新公理。 数学编码选择仍待审。 |
| gammaRatio | L1533–1535 | 本轮未发现差异 | TeX复核：X1(s)=Γ((3/2−s)/2)/Γ((3/2+s)/2)，上下符号与1/2缩放完整。 |
| diagonalSeries | L529–538, L1582–1594 | 已修正或补充，待审 | TeX复核：正n、互素过滤、Λ²与n^(1+w)一致；Rew>0有显式可和与全纯义务。 |
| densitySeries | L523–526, L529–538 | 本轮未发现差异 | TeX复核：Σk≥1 S(kN)/k^w初始域Rew>1；continuedDensity是另一个延拓总函数，未域外直接使用tsum。 |
| densityEulerProduct | L529–538 | 已修正或补充，待审 | TeX复核：p>2、p不整除N、因子1+p^-w/(p−2)，正常收敛/可乘性已经配套。 |
| betaModel | L529–538, L1688–1693 | 本轮未发现差异 | TeX复核：使用continuedDensity的N^-w S_N(w)K−，不在Beta域使用发散密度级数。 |
| continuedBetaModel | L549–552 | 本轮未发现差异 | TeX复核：S(N)(π/N)^w P_N(w)ζ(1−w)X1(s)X1(z)，不存在额外2因子。 |
| residualKernel | L1734–1742, L1755–1768 | 本轮未发现差异 | TeX复核：E=P−D−K两个减号保留；算子使用E(s,conjz)而非原双全纯形式。 |
| analyticDomain | L1704–1710 | 本轮未发现差异 | TeX复核：Ω的四个严格不等式0<Re s,Re z<3/2全部一致。 |
| logarithmicDerivative | L627–631, L1155–1163 | 本轮未发现差异 | TeX复核：gχ(s)=L′/L(1/2+s,χ)，无负号；Dirichlet级数才是−gχ。 |
| alpha | L1840–1844 | 本轮未发现差异 | TeX复核：TeX在§5及§6都固定α_N=1/logN；不是这里任取自由α。 |
| beta | L1840–1844 | 本轮未发现差异 | TeX复核：TeX固定β=1/8；与实现常数一致。 |
| sigmaStar | L1840–1844 | 本轮未发现差异 | TeX复核：TeX固定σ*=1/9；不与σ_ref=2/logN混淆。 |
| stripWidth | L1840–1844 | 本轮未发现差异 | TeX复核：Δ=β−α_N，符号和顺序一致。 |
| hardyStrip | L1840–1845, L1986–1994 | 本轮未发现差异 | TeX复核：严格开带α<Re s<β；RealizationValid只是旧辅助谓词，当前命名陈述直接给原文假设。 |
| boundarySpace | L1844–1854 | 本轮未发现差异 | TeX复核：两条边界为不交并，正弧长dt，既无orientation也无1/(2π)；Bool×R与两积分之和实现一致。 |
| hardyFunction | L1986–2027 | 数学编码待审 | TeX复核：TeX先定义全纯函数空间，再给加权Lp的酉同构；现实际carrier选Lp，完整桥接仍为待证编码选择。 数学编码选择仍待审。 |
| hardyNormSq | L1986–1994 | 本轮未发现差异 | TeX复核：TeX的同一ε配对内线sup精确保留；IsRawHardy另要求积分存在及一致上界，避免sSup域外默认值。 |
| boundaryTrace | L1995–2001, L2030–2046 | 数学编码待审 | TeX复核：TeX只要求L²单侧极限，无点态边界平滑前提；滤子侧向及两个同源迹已保留。 数学编码选择仍待审。 |
| hardyInnerProduct | L1846–1854, L2040–2044 | 本轮未发现差异 | TeX复核：第一变量线性，边界h·conj g；paperInner=inner g h准确交换Mathlib约定。 |
| weightedResidualKernel | L1897–1906, L1926–1940 | 本轮未发现差异 | TeX复核：分母(1+s)(1+conj z)，分子E(s,conj z)，共轭位置未变。 |
| residualOperator | L1897–1906, L2123–2141 | 已修正或补充，待审 | TeX复核：为Hardy上的有界线性表示选择；原文边界L²算子限制到迹像的理由由配套实现义务支撑，未假定任意核都有效。 |
| hilbertSchmidt | L2100–2110, L2123–2141 | 数学编码待审 | TeX复核：TeX使用通常HS；实现是面向无限可分Hardy空间的N索引基版本，局限保留。 数学编码选择仍待审。 |
| hilbertSchmidtNorm | L2133–2141 | 数学编码待审 | TeX复核：HS²=Σ\|\|Te_j\|\|²及四个边界核平方积分，已同时有MemLp和基无关义务；非HS域外默认0不能使用。 数学编码选择仍待审。 |
| eigenvalueFamily | L2131–2141, L2329–2339 | 数学编码待审 | TeX复核：TeX只枚举非零谱按重数；实现用完整实本征基并以0填充，不改平方和或乘积。 数学编码选择仍待审。 |
| weightFunctional | L3589–3597 | 已修正或补充，待审 | TeX复核：αN<σ<β；N^s、MellinΦ、1+s和上行轮廓1/(2πi)完整，CLM/可积性已有。 |
| rieszVector | L3594–3597 | 已修正或补充，待审 | TeX复核：第一变量线性约定下ell(h)=<h,v>；选择对象由Prop7.4和A1给存在性及真实表示。 |
| functionalNormSq | L3597–3600 | 已修正或补充，待审 | TeX复核：Q定义为两种实际范数平方，3627–3635给含V²的积分；Lean正确，Prop7.4中文V/Ψ需修。 |
| spectralR | L2546–2557 | 本轮未发现差异 | TeX复核：R(N)在所有四元数零点上断言Re=1/2，与TeX等价形式相符。 |
| zeroFreeWidth | L2557–2562 | 本轮未发现差异 | TeX复核：TeX排除Re q>1−η的开半空间，故范数界允许等号；未误改≥。 |
| widthFromNorm | L2563–2570 | 已修正或补充，待审 | TeX复核：(1−sqrt(1−δ²/M²))/2，使用域M>δ>0，配套声明保证(0,1/2)。 |
| residualIntegral | L3514–3519 | 本轮未发现差异 | TeX复核：两个独立向上竖线；N^(s+z)、两Mellin因子、E和(2πi)^−2一致。 |
| derivativeWeight | L3598–3601 | 已修正或补充，待审 | TeX复核：原名V=Φ−uΦ′；Lean正确；不得与PsiN复积分因子混用。 |
| completedLFunction | L1240–1244 | 本轮未发现差异 | TeX复核：解析延拓的完成L函数乘导子幂；精确匹配(d/π)^((u+1)/2)Γ((u+1)/2)L(u)。 |
| nontrivialZeros | L1247–1264 | 本轮未发现差异 | TeX复核：非平凡零点域0<Reρ<1，GRH之后写ρ=1/2+iγ；未先把非平凡零点定义成临界线零点。 |
| zeroMultiplicity | L1247–1249, L4183–4189 | 本轮未发现差异 | TeX复核：mχ(ρ)为L的零点重数，非零点取0；analyticOrderNatAt在实际解析域符合定义。 |
| zeroCount | L1255–1259 | 本轮未发现差异 | TeX复核：半开窗[t,t+1)且按重数计，ncard另有Finite保证。 |
| pairedZeroSum | L1262–1268 | 已修正或补充，待审 | TeX复核：1/(s−iγ)−1/(3/2−iγ)，保留配对以获得绝对局部一致收敛；与zeroDifference的GRH桥接已存在。 |
| eulerCorrection | L1269–1272 | 本轮未发现差异 | TeX复核：仅p\|N且p不整除导子，χ*与logp、p^u−χ*(p)一致；定义实际域Reu>0。 |
| fueterOperator | L1918–1940 | 已修正或补充，待审 | TeX复核：TeX坐标s+zj，j左乘∂z；现Wirtinger一半因子及非交换乘法顺序正确。 |
| hardyWeight | L2003–2007 | 本轮未发现差异 | TeX复核：e^{2aτ}+e^{2bτ}，正密度，对应两个边界范数之和而非平均。 |
| fourierLaplace | L2005–2016 | 数学编码待审 | TeX复核：系数1/sqrt(2π)，指数+sτ、对τ积分；现边界迹与积分有效性义务保留。 数学编码选择仍待审。 |
| evaluationVector | L2213–2241 | 本轮未发现差异 | TeX复核：TeX再生核csc分母4Δ，Riesz向量与函数表达式经Proposition5.4联结；exact_norm给精确等号。 |
| boundaryDistance | L2234–2241 | 本轮未发现差异 | TeX复核：min(Re s−α,β−Re s)，仅内点使用并为正。 |
| sliceRegular | L2369–2374 | 数学编码待审 | TeX复核：TeX使用同一实系数幂级数于所有切片；现同一conjugation-compatible复整函数编码仍须审阅形式等价。 数学编码选择仍待审。 |
| quaternionSlice | L2364–2367 | 本轮未发现差异 | TeX复核：x+yI，I为单位纯虚；集合定义允许任意J，但应用声明都给J.re=0和J²=−1或norm=1。 |
| traceClass | L2376–2386 | 数学编码待审 | TeX复核：TeX的positive compact A以Σa_j<∞刻画；现positive trace-class基定义及到正谱求和桥接一致但未证明。 数学编码选择仍待审。 |
| trace | L2399–2403, L3019–3034 | 数学编码待审 | TeX复核：trace基选择的有效域和基无关已列义务；TeX的tr(T²)=Σμ²、trD精确公式在相应源段。 数学编码选择仍待审。 |
| fredholmDeterminant | L2376–2386, L2404–2408 | 数学编码待审 | TeX复核：原TeX明确ordinary determinant谱定义；positiveFredholmDet取A自身谱，fredholmSquareDet再取T²，避免把同一μ²乘积改名。 数学编码选择仍待审。 |
| spectralRootParameter | L2493–2505 | 本轮未发现差异 | TeX复核：d_j=δ²/μ_j²，仅非零μ使用；μ=0的总化值不被当成根分类参数。 |
| averagedLogDerivativeEnergy | L2655–2664, L2843–2859 | 已修正或补充，待审 | TeX复核：单χ积分与2/φ(N)奇特征平均两种对象均保留，权为(1+t²)^−1。 |
| poissonZeroSum | L2668–2678 | 已修正或补充，待审 | TeX复核：原始非平凡零点按重数、x>0；GRH下以虚部ordinate表示。已存在可和义务。 |
| referenceLine | L2631–2637 | 本轮未发现差异 | TeX复核：σ_ref=2/logN可能超过β，TeX明确Poisson比较允许x≤1/5；不能给它误加σ_ref≤β。 |
| smoothedPerronWeight | L2722–2745 | 已修正或补充，待审 | TeX复核：w_X分段和端点零值一致，X=N/2、x=sqrtX；新配套义务把Perron在v=0的留数1写为去心极限，未把总化0作极点值。 |
| smoothedDirichletPolynomial | L2722–2727 | 本轮未发现差异 | TeX复核：Σ_{n≤X}Λχn^−u w_X(n)，用range(floor X+1)实现；n=0项因Λ(0)=0无贡献。 |
| poissonKernel | L2912–2929 | 已修正或补充，待审 | TeX复核：原TeX明确ℓ=0解释为恒等。新增poissonAction保存该身份；普通poissonKernelReal仅在ℓ>0解释，补可积/非负/归一化和卷积公式。 |
| characterOperator | L2965–2986, L2989–3006 | 本轮未发现差异 | TeX复核：原TeX三分量共用Hardy边界积分核，P的Gram正性/有限秩作为证明理由；现命名结论正迹类与实现均保留。 |
| diagonalOperator | L2965–2986, L3007–3034 | 已修正或补充，待审 | TeX复核：对角核D(s+conj z)/((1+s)(1+conj z))；已具正迹类、实现和d_n接口，rank-one求和的证明仍未展开。 |
| betaOperator | L2965–2986, L3034–3039 | 本轮未发现差异 | TeX复核：原TeXK由P−D−T得到同一边界核；现component_spec同时记录核实现和T=P−D−K，未声明K为正。 |
| diagonalVector | L3007–3018 | 已修正或补充，待审 | TeX复核：d_n=n^−s/(1+s)，n≥1；Hardy元素、两侧迹、π范数和rankOne作用已全部有配套义务。 |
| rankOneOperator | L3016–3034 | 已修正或补充，待审 | TeX复核：TeX线性在第一变量，h↦<h,d>d；Mathlib rankOne d d用inner d h，正好等于paperInner h d。 |
| differenceConvolution | L3362–3368 | 已修正或补充，待审 | TeX复核：C0的u+y为差族正项；正半轴积分正确。 |
| sumConvolution | L3362–3368 | 已修正或补充，待审 | TeX复核：J0原文[0,y]积分；Lean半轴实现经支集桥接等价，对y≤0也为零。 |
| signedConvolution | L3362–3370 | 本轮未发现差异 | TeX复核：H0=2C0−J0；其Mellin变换直接复用mellin，无需新空壳定义。 |
| weightIntegral | L3451–3458 | 已修正或补充，待审 | TeX复核：a0为φ一阶积分，与cφ二阶质量区分；Lean正半轴积分正确。 |
| functionalIntegrand | L3724–3730 | 已修正或补充，待审 | TeX复核：Psi_N(s)=N^s MellinΦ(s)(1+s)，与实变量V完全不同；实际定义正确。 |
| variableAlpha | L3949–3953 | 本轮未发现差异 | TeX复核：c>0先固定，α=c/logN；Lean默认c=1与正文对应。 |
| variableRealization | L3954–3958 | 已修正或补充，待审 | TeX复核：同一kernel但空间和边界依赖c；补A1_operator_spec验证变量c实际积分实现。 |
| variableSpectralProduct | L4020–4024 | 已修正或补充，待审 | TeX复核：从T_Nc谱构造且δ_N不随c变；新增A1谱非空验证其选择域。 |
| variableSpectralHypotheses | L4024–4031 | 已修正或补充，待审 | TeX复核：c先固定、h预给，eventual GRH逐N蕴含；h在无关小模数上的正性不影响eventual结论。 |
| availableNormMajorant | L4107–4119 | 已修正或补充，待审 | TeX复核：Mα=C(log²N+α^-2)，C绝对由无φ参数的辅助声明落实。 |
| zeroMultiplicitySquareAverage | L4183–4190 | 已修正或补充，待审 | TeX复核：C_Nγ平均奇特征的重数平方，至少一个零点；Lean精确，中文Aγ改原名。 |
| baselineProductR | L4224–4233 | 已修正或补充，待审 | TeX复核：包含所有p\|N的有限因子和p>2不除N的无限因子；_baseline_product给近零有效域及S R(0)=1。 |
| experimentN | L4280–4282 | 本轮未发现差异 | TeX复核：固定30030=2·3·5·7·11·13，φ=5760，2880奇χ；不外推。 |
| smoothStep13 | L4295–4299 | 本轮未发现差异 | TeX复核：P为j=7..13二项式和，t≤0/≥1分段；C6而非C∞。 |
| wideCutoff | L4290–4299 | 已修正或补充，待审 | TeX复核：原符号η、两分母984、端点16与N−16；Lean正确，B1中文恢复η。 |
| wideCompanion | L4300–4304 | 已修正或补充，待审 | TeX复核：原符号W，√(1−u)、η(Nu)、两对数平方根；支集外零延拓正确。 |
| wideWeight | L4300–4304 | 已修正或补充，待审 | TeX复核：原符号f=W/√u；主文IsWeight不能套用；C6/紧支集专用义务已存在。 |
| wideCorrelation | L4305–4309 | 本轮未发现差异 | TeX复核：J=N^-1有序n+m=N互素和，两个Λ与f；沿用goldbach通用定义无额外窄权。 |
| unorderedPrimeCount | L4310–4314 | 本轮未发现差异 | TeX复核：p≤q、p+q=N、两者素数；Nat计数精确。 |
| edgeCorrection | L4310–4314 | 本轮未发现差异 | TeX复核：E是p<L的无序素数对补偿1−η(p)^2，无额外1/2。 |
| primePowerCorrection | L4312–4314 | 本轮未发现差异 | TeX复核：有序p^k+q^ell，k,ell≥1且max≥2，互素，分母k·ell；有限范围涵盖所有合法解。 |
| wideCoefficients | L4361–4364 | 本轮未发现差异 | TeX复核：a_n=Λ(n)W(n/N)/√n，n=0实现0不贡献。 |
| countingIntegral | L4351–4356 | 本轮未发现差异 | TeX复核：Re s=1使L参数3/2，1/(2π)dt，无定义负号；求值负号在B2。 |
| wideDiagonal | L4357–4364 | 本轮未发现差异 | TeX复核：1≤n<N互素a_n²；代码range N含零但零项严格为0。 |
| approximateMoments | L4370–4374 | 本轮未发现差异 | TeX复核：两矩同除5760，全χ；签名χ(-1)取实部等价于±1值。近似矩按4445–4446复用公式。 |
| wideMainMass | L4422–4424 | 已修正或补充，待审 | TeX复核：cf=∫0¹f(u)f(1−u)，不擅自改为f²。 |
| wideMainIntegral | L4413–4416 | 已修正或补充，待审 | TeX复核：A=S∫16^{N/2}η²/(logx log(N−x))，lemma_B3_main_integral给NScf/2。 |
| wideResidual | L4422–4428 | 本轮未发现差异 | TeX复核：B=Scf−J，算术误差方向与二次型完全一致。 |
| momentError | L4445–4451 | 本轮未发现差异 | TeX复核：ε≥0及平均范数平方≤ε²，HasMomentError与主hypothesis一致。 |
| approximatePrimeCount | L4453–4456 | 本轮未发现差异 | TeX复核：N Jhat/2−Cpp/2+E，修正项精确不含A的求积误差。 |
| countError | L4457–4462 | 本轮未发现差异 | TeX复核：N/2*(2√Dhat ε+ε²)，误差闭区间和整数性在B3完整表达。 |
| wideFunctional | L4514–4519 | 已修正或补充，待审 | TeX复核：σ*=1/9、MellinW、1+s，与计数Re s=1积分区分。 |
| wideRieszVector | L4514–4519 | 已修正或补充，待审 | TeX复核：标准c=1 Hardy空间中表示ellW；B4给存在性/CLM/可积性，选择默认0不被视为证明。 |
| quadratureNodes | L4537–4539 | 本轮未发现差异 | TeX复核：两条边界各1281节点，−40到40步1/16，总2562；排序仅是实现选择。 |
| quadratureWeights | L4537–4539 | 本轮未发现差异 | TeX复核：所有权正、每边端点半权1/32、内点1/16；无2π因子。 |
| finiteSpectralMatrix | L4544–4549 | 本轮未发现差异 | TeX复核：两平方根权及E(si,conj sj)/((1+si)(1+conj sj))一致。 |
| finiteSpectralProduct | L4540–4561 | 本轮未发现差异 | TeX复核：det(I−4q(1−q)C²/δ²)；谱通过酉相似绑定，opnorm为Euclidean算子范数，GRH下有效。 |
