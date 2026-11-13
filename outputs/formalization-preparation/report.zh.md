> 这里的类型检查、数值和哈希属于重命名前的历史审阅轮次。当前类型保真见 [reviewed-types.json](../../formalization/reviewed-types.json)，源码对应关系见 [naming-migration.json](../../formalization/verification/naming-migration.json)；[snapshot-migration.json](snapshot-migration.json)记录当前快照与Reviewed参考的逐字节一致性及TeX原始哈希。

> 历史审阅快照；当前证明与验证状态见仓库根目录 README。

# Li–Liu 论文的 Lean 形式化准备对照

清点范围为附件全文，包括附录 A、B：**38 条独立命名结论、121 个定义或紧密相关的定义族**。同一条结论在 §2 的预告与后文的正式陈述只计一次。主文件目前含 102 个定理声明，其中 38 个对应原文主标签，60 个记录同一标签下的附带结论，另有 4 个用于定义存在性、归一化及直接推论的辅助声明。

交付代码：[conditional-goldbach.lean](conditional-goldbach.lean)；结构化清单：[inventory.json](inventory.json)。主文件已在 **Lean 4.35.0、Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`** 下完成类型检查，编译退出码为 0。全部 102 个定理证明有意保留 `sorry`，供用户先检查陈述。下文的“已有”指可复用接口或定义，不表示这篇论文的结论已经得到证明。

清单中的全部命名条目与定义族已经过 PDF 审计，并按用户新提供的原始 TeX 再次复核；本轮结果见 [tex-audit.md](tex-audit.md)。累计修正、原文子句与 Lean 对照见 [semantic-audit.md](semantic-audit.md) 和 [semantic-audit.json](semantic-audit.json)。联合亚纯性、Hardy 实现和专用 Fredholm 定义等编码选择仍需用户审阅。逐项公式和编码依据见审计台账。

依赖审计修订 9 入口：[交互依赖审阅页](dependency-review.html)、[依赖图 JSON](dependency-graph.json)、[复核说明](dependency-audit.md)。覆盖完整 38 个命名结论和 121 个定义族；图中分开显示原文证明依赖、声明中的定义引用与构造义务，并非已完成的 Lean 证明 DAG。当前有 171 个定义声明，全部 102 个定理仍为 `by sorry`。

Theorem 6.1 的折叠配套陈述新增 `theorem_6_1_abstract_dictionary`，从原纯谱证明抽出固定和可变条带共用的字典。前提为完整复 Hilbert 空间、自然数索引的 `SpectralData` 存在及正谱尺度；这仍是未证明接口，其谱数据条件针对本文无限维可分模型。

## 先审查的接口与数学约定

1. 原文内积在第一变量线性，Mathlib 在第二变量线性；`paperInner u v = inner v u` 明确转换。
2. 原文奇异级数 `S(N)` 是现有项目 `liuSingularSeries N` 的两倍，不能替换成仓库里同名的有限截断奇异级数。
3. Hardy 空间先用加权 `Lp ℂ 2` 实现，再把其与全纯函数、双侧边界迹的对应单列为 Lemma 5.2 的证明义务。
4. 核算子、Riesz 向量、谱与迹使用有实际表示条件的 `Classical.choose`，并显式规定条件未满足时返回零。相关存在性、唯一性与不依赖选择的断言仍须证明；这种总化并不自动建立原文对象。
5. Hilbert–Schmidt 与正迹类使用自然数索引 Hilbert 基，面向本论文无限维可分 Hardy 空间。附录 B 的有限矩阵单独处理。
6. 固定 N 的解析构造与对 N 一致的估计分开陈述。§6.4 的均匀界、两个渐近主定理、附录 A 的 c 参数，都需要逐项检查量词顺序。
7. 四元数谱函数由有序有限乘积的极限定义；复数 `tprod` 与四元数乘积的一致性、重排不变性另列陈述。有限谱矩阵目前没有与无限算子之间的已认证误差界。
8. `diagonalVector` 给出实际函数，`diagonalHardyVector` 将它装入 Hardy 空间；配套声明给出内部值与边界迹，证明仍待填入。秩一算子复用 `InnerProductSpace.rankOne ℂ d d`。
9. 附录 A.3 已单列两种实际 `spectralWidthFromBound` 的比值，而不仅是代数代理；陈述要求两种宽度均在可用范围内。

## 38 条命名结论

下表列主声明与附带子句。页码使用 PDF 正文页码；确切假设和公式请查看 Lean 声明及 JSON 中保留的原文陈述。

| 原文标签、页码 | 中文提要 | 实际 Lean 声明 |
|---|---|---|
| Theorem 1.1，p. 4 | GRH 与预先指定的谱假设 S 推出带权 Goldbach 渐近式，误差为 Oφ(S(N)/h(N))。 | [ConditionalGoldbach.theorem_1_1](conditional-goldbach.lean#L406)<br>[ConditionalGoldbach.theorem_1_1_weight_exists](conditional-goldbach.lean#L404) |
| Theorem 1.2，p. 5 | GRH 与谱假设 R 推出误差为 Oφ(δN) 的带权 Goldbach 渐近式。 | [ConditionalGoldbach.theorem_1_2](conditional-goldbach.lean#L413)<br>[ConditionalGoldbach.theorem_1_2_hypothesisR_implies_S](conditional-goldbach.lean#L419) |
| Lemma 3.1，p. 15 | 精确有限投影 G(N)=D(N)−P(N)，并有 0≤P(N)≤D(N)≪φ log N。 | [ConditionalGoldbach.lemma_3_1](conditional-goldbach.lean#L429)<br>[ConditionalGoldbach.lemma_3_1_odd_orthogonality](conditional-goldbach.lean#L438) |
| Proposition 3.2，p. 16 | 特征标核的绝对收敛双级数、亚纯性、GRH 下联合全纯性、共轭与交换对称性，以及 Hermitian 核的半正定性和秩界。 | [ConditionalGoldbach.proposition_3_2](conditional-goldbach.lean#L452)<br>[ConditionalGoldbach.proposition_3_2_finite_rank](conditional-goldbach.lean#L1098)<br>[ConditionalGoldbach.proposition_3_2_joint_meromorphic](conditional-goldbach.lean#L1448) |
| Lemma 3.3，p. 17 | 本原奇特征标的完成 L 函数对数导数差等于成对零点和，且单位高度窗口零点数有对数界。 | [ConditionalGoldbach.lemma_3_3](conditional-goldbach.lean#L469) |
| Lemma 3.4，p. 18 | GRH 下成对零点和局部一致绝对收敛，给出 gχ 的 Gamma 与非本原欧拉修正展开，以及固定竖带上的对数平方增长界。 | [ConditionalGoldbach.lemma_3_4](conditional-goldbach.lean#L480)<br>[ConditionalGoldbach.lemma_3_4_normal_convergence](conditional-goldbach.lean#L1103)<br>[ConditionalGoldbach.lemma_3_4_paired_zero_sum](conditional-goldbach.lean#L1460) |
| Lemma 3.5，p. 19 | 特征标二次矩的双 Mellin 表示及三类有符号非对角关系，插入权函数后仅保留 n+m=N。 | [ConditionalGoldbach.lemma_3_5](conditional-goldbach.lean#L492)<br>[ConditionalGoldbach.lemma_3_5_absolute_convergence](conditional-goldbach.lean#L1111)<br>[ConditionalGoldbach.lemma_3_5_small_sigma](conditional-goldbach.lean#L1119)<br>[ConditionalGoldbach.lemma_3_5_weight_support](conditional-goldbach.lean#L1125) |
| Lemma 4.1，p. 21 | 三类连续模型的 Beta 积分恒等式、绝对收敛条件与共同局部密度。 | [ConditionalGoldbach.lemma_4_1](conditional-goldbach.lean#L502)<br>[ConditionalGoldbach.lemma_4_1_absolute_convergence](conditional-goldbach.lean#L1132)<br>[ConditionalGoldbach.lemma_4_1_local_density](conditional-goldbach.lean#L1427)<br>[ConditionalGoldbach.lemma_4_1_signed_model](conditional-goldbach.lean#L1467) |
| Lemma 4.2，p. 21 | 有符号 Beta 组合的等高线界及 Gamma、余弦因子分解。 | [ConditionalGoldbach.lemma_4_2](conditional-goldbach.lean#L510)<br>[ConditionalGoldbach.lemma_4_2_meromorphic](conditional-goldbach.lean#L1434) |
| Lemma 4.3，p. 22 | 对角级数收敛、密度级数的欧拉乘积与亚纯延拓、w=1 的留数、竖带增长界以及奇异级数上下界。 | [ConditionalGoldbach.lemma_4_3](conditional-goldbach.lean#L517)<br>[ConditionalGoldbach.lemma_4_3_uniform](conditional-goldbach.lean#L527)<br>[ConditionalGoldbach.lemma_4_3_density_convergence](conditional-goldbach.lean#L1141)<br>[ConditionalGoldbach.lemma_4_3_euler_product_convergence](conditional-goldbach.lean#L1482) |
| Proposition 4.4，p. 24 | Beta 模型的函数方程形式与 Ω 上全纯延拓。 | [ConditionalGoldbach.proposition_4_4](conditional-goldbach.lean#L533) |
| Proposition 4.5，p. 24 | GRH 下解析余项的联合全纯性、交换与共轭对称性。 | [ConditionalGoldbach.proposition_4_5](conditional-goldbach.lean#L537) |
| Proposition 5.1，p. 27 | 加权余项核的 Hermitian 性、闭带邻域全纯性、原文 Fueter 方程和固定积分线距离。 | [ConditionalGoldbach.proposition_5_1](conditional-goldbach.lean#L550)<br>[ConditionalGoldbach.proposition_5_1_fueter_equation](conditional-goldbach.lean#L1238) |
| Lemma 5.2，p. 28 | 带状 Hardy 空间的 Fourier–Laplace 酉实现、两边界 L² 迹、范数恒等式和迹像闭性。 | [ConditionalGoldbach.lemma_5_2](conditional-goldbach.lean#L565)<br>[ConditionalGoldbach.lemma_5_2_closed_trace_space](conditional-goldbach.lean#L1146)<br>[ConditionalGoldbach.lemma_5_2_representation_spec](conditional-goldbach.lean#L1243)<br>[ConditionalGoldbach.lemma_5_2_boundary_inner](conditional-goldbach.lean#L1418) |
| Proposition 5.3，p. 29 | 余项积分算子的紧性、自伴性、Hilbert–Schmidt 性、平方特征值和与核积分恒等式，以及算子范数的特征值刻画。 | [ConditionalGoldbach.proposition_5_3](conditional-goldbach.lean#L572)<br>[ConditionalGoldbach.proposition_5_3_kernel_integrability](conditional-goldbach.lean#L1261)<br>[ConditionalGoldbach.proposition_5_3_hs_basis_independent](conditional-goldbach.lean#L1270) |
| Proposition 5.4，p. 30 | 显式余割再生核、点值泛函及其范数界，并推出余项核的逐点估计。 | [ConditionalGoldbach.proposition_5_4](conditional-goldbach.lean#L584)<br>[ConditionalGoldbach.proposition_5_4_exact_norm](conditional-goldbach.lean#L1149)<br>[ConditionalGoldbach.proposition_5_4_kernel_pairing](conditional-goldbach.lean#L1276)<br>[ConditionalGoldbach.proposition_5_4_fixed_contour](conditional-goldbach.lean#L1282) |
| Proposition 6.1，p. 33 | 谱无穷乘积的局部一致收敛、枚举无关性、内蕴整切片正则性、TN² 的迹类性质与 Fredholm 行列式表示。 | [ConditionalGoldbach.proposition_6_1](conditional-goldbach.lean#L605)<br>[ConditionalGoldbach.proposition_6_1_enumeration](conditional-goldbach.lean#L1162)<br>[ConditionalGoldbach.proposition_6_1_complex_slice](conditional-goldbach.lean#L1172)<br>[ConditionalGoldbach.proposition_6_1_positive_fredholm_spec](conditional-goldbach.lean#L1291)<br>[ConditionalGoldbach.proposition_6_1_square_determinant](conditional-goldbach.lean#L1302)<br>[ConditionalGoldbach.proposition_6_1_all_slices](conditional-goldbach.lean#L1310)<br>[ConditionalGoldbach.proposition_6_1_spectral_choice_independent](conditional-goldbach.lean#L1318) |
| Proposition 6.2，p. 33 | 谱函数归一化、反射与共轭对称性、中心偶性、临界超平面上的实值性质及实轴外侧下界。 | [ConditionalGoldbach.proposition_6_2](conditional-goldbach.lean#L619)<br>[ConditionalGoldbach.proposition_6_2_centered_product](conditional-goldbach.lean#L1185)<br>[ConditionalGoldbach.proposition_6_2_critical_values](conditional-goldbach.lean#L1191) |
| Proposition 6.3，p. 34 | 全部谱零点按 δN²/μj² 分类，有限个例外实零点对，以及切片重数和中心偶重数。 | [ConditionalGoldbach.proposition_6_3](conditional-goldbach.lean#L627)<br>[ConditionalGoldbach.proposition_6_3_three_cases](conditional-goldbach.lean#L1203)<br>[ConditionalGoldbach.proposition_6_3_factor_central_order](conditional-goldbach.lean#L1215)<br>[ConditionalGoldbach.proposition_6_3_multiplicities](conditional-goldbach.lean#L1224) |
| Theorem 6.1，p. 35 | 谱假设 R 与算子范数界的等价性，无零半空间宽度与范数界的精确转换。 | [ConditionalGoldbach.theorem_6_1](conditional-goldbach.lean#L638)<br>[ConditionalGoldbach.theorem_6_1_abstract_dictionary](conditional-goldbach.lean#L1498)<br>[ConditionalGoldbach.theorem_6_1_width_comparison](conditional-goldbach.lean#L1508) |
| Theorem 6.2，p. 36 | GRH 下统一的 log²N 算子范数基线及 S(N)/(NlogN) 量级的无零宽度。 | [ConditionalGoldbach.theorem_6_2](conditional-goldbach.lean#L648) |
| Lemma 6.4，p. 36 | 奇特征标平均的加权对数导数二次矩界，统一为 O(log²N+σ⁻²)。 | [ConditionalGoldbach.lemma_6_4](conditional-goldbach.lean#L655)<br>[ConditionalGoldbach.lemma_6_4_zero_poisson_convergence](conditional-goldbach.lean#L1342)<br>[ConditionalGoldbach.lemma_6_4_perron_residue](conditional-goldbach.lean#L1350)<br>[ConditionalGoldbach.lemma_6_4_poisson_action_spec](conditional-goldbach.lean#L1357)<br>[ConditionalGoldbach.lemma_6_4_poisson_convolution](conditional-goldbach.lean#L1368) |
| Proposition 6.5，p. 40 | 特征标、对角与 Beta 三个算子分量的正性、迹类与 Hilbert–Schmidt 范数预算。 | [ConditionalGoldbach.proposition_6_5](conditional-goldbach.lean#L661)<br>[ConditionalGoldbach.proposition_6_5_components_spec](conditional-goldbach.lean#L676)<br>[ConditionalGoldbach.proposition_6_5_diagonal_vector_spec](conditional-goldbach.lean#L1331) |
| Lemma 7.1，p. 44 | Mellin 反演、紧实部区间上一致六阶衰减，以及 GRH 下单、双积分表示。 | [ConditionalGoldbach.lemma_7_1](conditional-goldbach.lean#L698)<br>[ConditionalGoldbach.lemma_7_1_absolute_convergence](conditional-goldbach.lean#L1546) |
| Lemma 7.2，p. 45 | 双 Mellin 对角积分等于 D(N)，有符号 Beta 模型积分精确等于 −cφS(N)。 | [ConditionalGoldbach.lemma_7_2](conditional-goldbach.lean#L708)<br>[ConditionalGoldbach.lemma_7_2_absolute_convergence](conditional-goldbach.lean#L1375)<br>[ConditionalGoldbach.lemma_7_2_convolutions](conditional-goldbach.lean#L1561) |
| Proposition 7.3，p. 47 | 余项 Mellin 积分绝对收敛并等于 cφS(N)−G(N)，因此与积分线无关。 | [ConditionalGoldbach.proposition_7_3](conditional-goldbach.lean#L717)<br>[ConditionalGoldbach.proposition_7_3_absolute_convergence](conditional-goldbach.lean#L1387) |
| Proposition 7.4，p. 49 | 权泛函有界且与积分线无关，其范数平方的精确积分式、一致上界和 1/logN 渐近展开。 | [ConditionalGoldbach.proposition_7_4](conditional-goldbach.lean#L722)<br>[ConditionalGoldbach.proposition_7_4_norm_integrals](conditional-goldbach.lean#L1570) |
| Theorem 7.1，p. 50 | 精确恒等式 r(N)=⟨TNvN,vN⟩，以及对 N 一致的 Goldbach 误差上界。 | [ConditionalGoldbach.theorem_7_1](conditional-goldbach.lean#L737)<br>[ConditionalGoldbach.theorem_7_1_uniform](conditional-goldbach.lean#L1514) |
| Lemma 7.5，p. 50 | 由无零区域宽度得到相对算术误差界，以及相对渐近式的充分条件。 | [ConditionalGoldbach.lemma_7_5](conditional-goldbach.lean#L745)<br>[ConditionalGoldbach.lemma_7_5_asymptotic](conditional-goldbach.lean#L1579) |
| Proposition A.1，p. 53 | 可变左边界 α=c/logN 下的 Hardy 算子实现、范数与评价界、精确算术配对和 c=1 特化。 | [ConditionalGoldbach.proposition_A_1](conditional-goldbach.lean#L753)<br>[ConditionalGoldbach.proposition_A_1_operator_spec](conditional-goldbach.lean#L1633) |
| Proposition A.2，p. 54 | 固定 c 下的谱范数等价、GRH 基线，以及 S/R 条件下的带权渐近结论和量词次序。 | [ConditionalGoldbach.proposition_A_2](conditional-goldbach.lean#L787)<br>[ConditionalGoldbach.proposition_A_2_pointwise](conditional-goldbach.lean#L1589) |
| Lemma A.3，p. 55 | 任意左边界下权泛函与可得算子界的平衡，c 参数两端发散和所需无零宽度与基线的比值。 | [ConditionalGoldbach.lemma_A_3](conditional-goldbach.lean#L811)<br>[ConditionalGoldbach.lemma_A_3_balance](conditional-goldbach.lean#L1402)<br>[ConditionalGoldbach.lemma_A_3_width_ratio](conditional-goldbach.lean#L1522)<br>[ConditionalGoldbach.lemma_A_3_absolute_operator_bound](conditional-goldbach.lean#L1600) |
| Proposition A.4，p. 55 | 固定 N 后令 c 趋零，零点极点强制算子范数至少按 1/c 增长，从而得到 R 失败及无零宽度障碍。 | [ConditionalGoldbach.proposition_A_4](conditional-goldbach.lean#L823)<br>[ConditionalGoldbach.proposition_A_4_baseline_product](conditional-goldbach.lean#L1607) |
| Proposition B.1，p. 57 | N=30030 的宽权 C6 截断性质、权函数乘积恒等式及素数幂、边缘校正后的精确计数公式。 | [ConditionalGoldbach.proposition_B_1](conditional-goldbach.lean#L895) |
| Lemma B.2，p. 58 | 绝对收敛计数线上全部特征标积分的有限和表达，以及 J、D 的正交二次矩公式。 | [ConditionalGoldbach.lemma_B_2](conditional-goldbach.lean#L903) |
| Lemma B.3，p. 59 | 由特征标积分的均方误差控制 J 误差，并形成包含真实无序素数对数量的整数区间。 | [ConditionalGoldbach.lemma_B_3](conditional-goldbach.lean#L911)<br>[ConditionalGoldbach.lemma_B_3_main_integral](conditional-goldbach.lean#L1616) |
| Proposition B.4，p. 60 | GRH(30030) 下宽权余项与同一 Hardy 算子的二次型表示。 | [ConditionalGoldbach.proposition_B_4](conditional-goldbach.lean#L928)<br>[ConditionalGoldbach.proposition_B_4_weight](conditional-goldbach.lean#L1623) |
| Proposition B.5，p. 61 | 2562 阶有限 Hermitian 模型的行列式谱乘积、反射对称性和范数条件下的临界线零点结论。 | [ConditionalGoldbach.proposition_B_5](conditional-goldbach.lean#L964) |

## 121 个定义族

状态统计：116 项已给出实际定义，4 项通过已有参数化构造直接复用，1 项直接使用 Mathlib 秩一算子接口。这里的覆盖指对象和接口已经写出；不代表存在性、收敛性或正确性已经证明。

| 原文对象与位置 | 实际接口 | 复用情况 |
|---|---|---|
| φ（§1.2，p. 2） | [ConditionalGoldbach.IsWeight](conditional-goldbach.lean#L33) | 实际定义已写出 |
| Λ(n)（§1.1，p. 2） | [ConditionalGoldbach.mangoldt](conditional-goldbach.lean#L30) | 实际定义已写出；依赖 `ArithmeticFunction.vonMangoldt` |
| S(N)（§1.1，p. 2） | [ConditionalGoldbach.singularSeries](conditional-goldbach.lean#L46) | 实际定义已写出；依赖 `MathlibNt.SieveTheory.SingularSeries.liuSingularSeries` |
| C2（§1.1，p. 2） | [ConditionalGoldbach.C2](conditional-goldbach.lean#L44)<br>[ConditionalGoldbach.prime](conditional-goldbach.lean#L31) | 实际定义已写出；依赖 `MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct` |
| G(N)（§1.2，p. 2） | [ConditionalGoldbach.goldbach](conditional-goldbach.lean#L53)<br>[ConditionalGoldbach.PrimePairCount](conditional-goldbach.lean#L341) | 实际定义已写出 |
| cφ（§1.2，p. 2） | [ConditionalGoldbach.weightMass](conditional-goldbach.lean#L42) | 实际定义已写出 |
| GRH(N)（§1.2，p. 3） | [ConditionalGoldbach.GRH](conditional-goldbach.lean#L73) | 实际定义已写出 |
| δN（§1.2，p. 3） | [ConditionalGoldbach.spectralScale](conditional-goldbach.lean#L267) | 实际定义已写出 |
| XN(q)（§1.2，p. 3） | [ConditionalGoldbach.spectralQuaternion](conditional-goldbach.lean#L279)<br>[ConditionalGoldbach.spectralComplex](conditional-goldbach.lean#L270)<br>[ConditionalGoldbach.spectralPartialQuaternion](conditional-goldbach.lean#L274)<br>[ConditionalGoldbach.CompactUniformLimit](conditional-goldbach.lean#L390)<br>[ConditionalGoldbach.spectralPartialQuaternionReindexed](conditional-goldbach.lean#L1156)<br>[ConditionalGoldbach.centeredSpectralPartial](conditional-goldbach.lean#L1178) | 实际定义已写出 |
| h（§1.2，p. 4） | [ConditionalGoldbach.IsAdmissible](conditional-goldbach.lean#L322)<br>[ConditionalGoldbach.EvenTendstoInfinity](conditional-goldbach.lean#L319)<br>[ConditionalGoldbach.EvenEventually](conditional-goldbach.lean#L317)<br>[ConditionalGoldbach.EvenAsymptotic](conditional-goldbach.lean#L395) | 实际定义已写出 |
| ηN（§1.2，p. 4） | [ConditionalGoldbach.zeroFreeWidth](conditional-goldbach.lean#L314) | 实际定义已写出 |
| S（§1.2，p. 4） | [ConditionalGoldbach.HypothesisS](conditional-goldbach.lean#L337) | 实际定义已写出 |
| R（§1.2，p. 4） | [ConditionalGoldbach.HypothesisR](conditional-goldbach.lean#L334) | 实际定义已写出 |
| XminusN（§2.1.1，p. 5） | [ConditionalGoldbach.oddCharacters](conditional-goldbach.lean#L63)<br>[ConditionalGoldbach.Character](conditional-goldbach.lean#L26) | 实际定义已写出；依赖 `DirichletCharacter.Odd` |
| Pχ（§2.1.1，p. 6） | [ConditionalGoldbach.characterPolynomial](conditional-goldbach.lean#L66) | 实际定义已写出 |
| Φ(u)（§2.1.1，p. 6） | [ConditionalGoldbach.companion](conditional-goldbach.lean#L37) | 实际定义已写出 |
| D(N)（§2.1.1，p. 6） | [ConditionalGoldbach.diagonalMoment](conditional-goldbach.lean#L59) | 实际定义已写出 |
| P(N)（§2.1.1，p. 6） | [ConditionalGoldbach.characterMoment](conditional-goldbach.lean#L70) | 实际定义已写出 |
| PN(s,z)（§2.1.2，p. 6） | [ConditionalGoldbach.characterKernel](conditional-goldbach.lean#L80)<br>[ConditionalGoldbach.arithmeticExpansionTerm](conditional-goldbach.lean#L446)<br>[ConditionalGoldbach.HermitianKernel](conditional-goldbach.lean#L375)<br>[ConditionalGoldbach.PositiveKernel](conditional-goldbach.lean#L377) | 实际定义已写出 |
| PhiTilde(s)（§2.1.2，p. 6） | [ConditionalGoldbach.mellinWeight](conditional-goldbach.lean#L137) | 实际定义已写出；依赖 `mellin` |
| (2πi)^−1 integral_(σ)（§2.1.2，p. 6） | [ConditionalGoldbach.verticalMellin](conditional-goldbach.lean#L141)<br>[ConditionalGoldbach.line](conditional-goldbach.lean#L132) | 实际定义已写出 |
| off diagonal congruence families（§2.1.2，p. 7） | [ConditionalGoldbach.positiveDifferenceFamily](conditional-goldbach.lean#L996)<br>[ConditionalGoldbach.negativeDifferenceFamily](conditional-goldbach.lean#L999)<br>[ConditionalGoldbach.sumFamily](conditional-goldbach.lean#L1002) | 实际定义已写出 |
| Kminus(s,z)（§2.2，p. 7） | [ConditionalGoldbach.betaKernel](conditional-goldbach.lean#L98) | 实际定义已写出 |
| B(s,z)（§4.1，p. 20） | [ConditionalGoldbach.betaGamma](conditional-goldbach.lean#L985)<br>[ConditionalGoldbach.betaDomain](conditional-goldbach.lean#L119) | 实际定义已写出；依赖 `Complex.betaIntegral`, `Complex.Gamma` |
| X1(s)（§2.2，p. 8） | [ConditionalGoldbach.gammaQuotient](conditional-goldbach.lean#L102) | 实际定义已写出 |
| DN(w)（§2.2，p. 8） | [ConditionalGoldbach.diagonalSeries](conditional-goldbach.lean#L84) | 实际定义已写出 |
| SN(w)（§2.2，p. 8） | [ConditionalGoldbach.densitySeries](conditional-goldbach.lean#L88)<br>[ConditionalGoldbach.continuedDensity](conditional-goldbach.lean#L95) | 实际定义已写出 |
| PN(w)（§2.2，p. 8） | [ConditionalGoldbach.densityEulerProduct](conditional-goldbach.lean#L91) | 实际定义已写出 |
| KN(s,z)（§2.2，p. 8） | [ConditionalGoldbach.betaModel](conditional-goldbach.lean#L105)<br>[ConditionalGoldbach.localDensityFactor](conditional-goldbach.lean#L1424) | 实际定义已写出 |
| continued KN（§2.2，p. 8） | [ConditionalGoldbach.continuedModel](conditional-goldbach.lean#L108) | 实际定义已写出 |
| EN(s,z)（§2.2，p. 8） | [ConditionalGoldbach.residual](conditional-goldbach.lean#L113) | 实际定义已写出 |
| Ω（§4.4，p. 24） | [ConditionalGoldbach.analyticDomain](conditional-goldbach.lean#L116) | 实际定义已写出 |
| gχ(s)（§2.3.1，p. 9） | [ConditionalGoldbach.logDerivative](conditional-goldbach.lean#L77) | 实际定义已写出 |
| αN（§2.3.2，p. 9） | [ConditionalGoldbach.alpha](conditional-goldbach.lean#L122) | 实际定义已写出 |
| β（§2.3.2，p. 9） | [ConditionalGoldbach.beta](conditional-goldbach.lean#L124) | 实际定义已写出 |
| σstar（§2.3.2，p. 9） | [ConditionalGoldbach.sigmaStar](conditional-goldbach.lean#L126) | 实际定义已写出 |
| ΔN（§2.3.2，p. 9） | [ConditionalGoldbach.width](conditional-goldbach.lean#L128) | 实际定义已写出 |
| SN（§2.3.2，p. 9） | [ConditionalGoldbach.strip](conditional-goldbach.lean#L130)<br>[ConditionalGoldbach.RealizationValid](conditional-goldbach.lean#L284) | 实际定义已写出 |
| ΓN（§2.3.2，p. 9） | [ConditionalGoldbach.BoundaryParameter](conditional-goldbach.lean#L988)<br>[ConditionalGoldbach.boundaryPoint](conditional-goldbach.lean#L990)<br>[ConditionalGoldbach.boundaryMeasure](conditional-goldbach.lean#L993)<br>[ConditionalGoldbach.boundaryIntegral](conditional-goldbach.lean#L134) | 实际定义已写出 |
| H²(S)（§5.2，p. 27） | [ConditionalGoldbach.HardySpace](conditional-goldbach.lean#L162)<br>[ConditionalGoldbach.IsRawHardy](conditional-goldbach.lean#L167)<br>[ConditionalGoldbach.hardyMeasure](conditional-goldbach.lean#L159) | 实际定义已写出；依赖 `MeasureTheory.Lp` |
| norm h squared（§5.2，p. 27） | [ConditionalGoldbach.rawHardyNormSq](conditional-goldbach.lean#L175) | 实际定义已写出 |
| hα,hβ（§5.2，p. 27） | [ConditionalGoldbach.IsBoundaryTrace](conditional-goldbach.lean#L188)<br>[ConditionalGoldbach.boundaryTraces](conditional-goldbach.lean#L199)<br>[ConditionalGoldbach.interiorLine](conditional-goldbach.lean#L183) | 实际定义已写出；依赖 `MeasureTheory.Lp`, `Filter.Tendsto` |
| inner h,g（§2.3.2，p. 9） | [ConditionalGoldbach.paperInner](conditional-goldbach.lean#L202) | 实际定义已写出；依赖 `inner` |
| EN(s,conj z)/((1+s)(1+conj z))（§2.3.2，p. 9） | [ConditionalGoldbach.weightedKernel](conditional-goldbach.lean#L205) | 实际定义已写出 |
| TN（§2.3.2，p. 9） | [ConditionalGoldbach.residualOperator](conditional-goldbach.lean#L222)<br>[ConditionalGoldbach.kernelOperator](conditional-goldbach.lean#L218)<br>[ConditionalGoldbach.kernelAction](conditional-goldbach.lean#L208)<br>[ConditionalGoldbach.RepresentsKernel](conditional-goldbach.lean#L213) | 实际定义已写出 |
| Hilbert–Schmidt property（§2.3.2，p. 9） | [ConditionalGoldbach.IsHilbertSchmidt](conditional-goldbach.lean#L236) | 实际定义已写出 |
| HS norm（§5.3，p. 29） | [ConditionalGoldbach.hsNorm](conditional-goldbach.lean#L240)<br>[ConditionalGoldbach.BoundaryKernelSquareIntegral](conditional-goldbach.lean#L381) | 实际定义已写出 |
| μj(N)（§2.3.2，p. 10） | [ConditionalGoldbach.SpectralData](conditional-goldbach.lean#L256)<br>[ConditionalGoldbach.eigenvalues](conditional-goldbach.lean#L263) | 实际定义已写出；依赖 `HilbertBasis` |
| ellN（§2.3.3，p. 10） | [ConditionalGoldbach.functionalValue](conditional-goldbach.lean#L295) | 实际定义已写出 |
| vN（§2.3.3，p. 10） | [ConditionalGoldbach.rieszVector](conditional-goldbach.lean#L299) | 实际定义已写出 |
| QN（§2.3.3，p. 10） | [ConditionalGoldbach.normFunctional](conditional-goldbach.lean#L287)<br>[ConditionalGoldbach.weightEnergy](conditional-goldbach.lean#L292) | 实际定义已写出 |
| R(N)（§2.4，p. 13） | [ConditionalGoldbach.SpectralR](conditional-goldbach.lean#L327) | 实际定义已写出 |
| zero-free width η（§2.4，p. 11） | [ConditionalGoldbach.SpectralZeroFree](conditional-goldbach.lean#L330) | 实际定义已写出 |
| η(MN)（§2.4，p. 11） | [ConditionalGoldbach.spectralWidthFromBound](conditional-goldbach.lean#L398) | 实际定义已写出 |
| rσ(N),r(N)（§2.5.1，p. 13） | [ConditionalGoldbach.residualIntegral](conditional-goldbach.lean#L144) | 实际定义已写出 |
| V(u)（§2.5.2，p. 13） | [ConditionalGoldbach.derivativeWeight](conditional-goldbach.lean#L39) | 实际定义已写出 |
| completed primitive odd L（§3.3，p. 17） | [ConditionalGoldbach.completedL](conditional-goldbach.lean#L350) | 实际定义已写出；依赖 `DirichletCharacter.completedLFunction` |
| ρ,γχ（§3.3，p. 17） | [ConditionalGoldbach.ZeroIndex](conditional-goldbach.lean#L346) | 实际定义已写出；依赖 `analyticOrderNatAt` |
| mχ(ρ)（§A.4，p. 55） | [ConditionalGoldbach.zeroMultiplicity](conditional-goldbach.lean#L1010) | 实际定义已写出；依赖 `analyticOrderNatAt` |
| unit-window count（§3.3，p. 17） | [ConditionalGoldbach.zeroWindow](conditional-goldbach.lean#L466) | 实际定义已写出 |
| Zχ(s)（§3.3，p. 18） | [ConditionalGoldbach.pairedZeroSum](conditional-goldbach.lean#L1006)<br>[ConditionalGoldbach.zeroDifference](conditional-goldbach.lean#L353)<br>[ConditionalGoldbach.NormallySummableOn](conditional-goldbach.lean#L369) | 实际定义已写出 |
| eχ(u)（§3.3，p. 18） | [ConditionalGoldbach.eulerCorrection](conditional-goldbach.lean#L356) | 实际定义已写出 |
| ∂sbar+j∂z（§5.1，p. 26） | [ConditionalGoldbach.fueterOperator](conditional-goldbach.lean#L1022)<br>[ConditionalGoldbach.wirtinger](conditional-goldbach.lean#L547)<br>[ConditionalGoldbach.wirtingerBar](conditional-goldbach.lean#L544) | 实际定义已写出 |
| wH,α,β(τ)（§5.2，p. 28） | [ConditionalGoldbach.hardyWeight](conditional-goldbach.lean#L157) | 实际定义已写出 |
| UHψ（§5.2，p. 28） | [ConditionalGoldbach.fourierLaplace](conditional-goldbach.lean#L164) | 实际定义已写出 |
| kz(s)（§5.4，p. 30） | [ConditionalGoldbach.evaluationVector](conditional-goldbach.lean#L304)<br>[ConditionalGoldbach.reproducingKernel](conditional-goldbach.lean#L310) | 实际定义已写出 |
| dN(s)（§5.4，p. 31） | [ConditionalGoldbach.pointDistance](conditional-goldbach.lean#L308) | 实际定义已写出 |
| intrinsic entire slice-regular（§6.1，p. 32） | [ConditionalGoldbach.IntrinsicEntire](conditional-goldbach.lean#L385) | 实际定义已写出 |
| CI（§6.1，p. 32） | [ConditionalGoldbach.quaternionSlice](conditional-goldbach.lean#L1016)<br>[ConditionalGoldbach.complexQuaternion](conditional-goldbach.lean#L1019) | 实际定义已写出；依赖 `Quaternion` |
| positive trace class（§6.1，p. 32） | [ConditionalGoldbach.IsPositiveTraceClass](conditional-goldbach.lean#L245) | 实际定义已写出 |
| trace TN²（§6.1，p. 33） | [ConditionalGoldbach.positiveTrace](conditional-goldbach.lean#L250) | 实际定义已写出 |
| det(Id−tA)（§6.1，p. 32） | [ConditionalGoldbach.positiveFredholmDet](conditional-goldbach.lean#L597)<br>[ConditionalGoldbach.fredholmSquareDet](conditional-goldbach.lean#L601) | 实际定义已写出 |
| dj（§6.2，p. 34） | [ConditionalGoldbach.spectralRootParameter](conditional-goldbach.lean#L1013) | 实际定义已写出 |
| average energy（§6.4.1，p. 36） | [ConditionalGoldbach.averagedLogDerivative](conditional-goldbach.lean#L364)<br>[ConditionalGoldbach.logDerivativeEnergy](conditional-goldbach.lean#L1043) | 实际定义已写出 |
| Qχ(x,t)（§6.4.1，p. 36） | [ConditionalGoldbach.zeroPoisson](conditional-goldbach.lean#L361) | 实际定义已写出 |
| σref（§6.4，p. 36） | [ConditionalGoldbach.referenceLine](conditional-goldbach.lean#L1026) | 实际定义已写出 |
| wX(n)（§6.4.1，p. 37） | [ConditionalGoldbach.smoothedPerronWeight](conditional-goldbach.lean#L1031)<br>[ConditionalGoldbach.perronCutoff](conditional-goldbach.lean#L1028)<br>[ConditionalGoldbach.smoothedPerronKernel](conditional-goldbach.lean#L1040) | 实际定义已写出 |
| Pχ,X(u)（§6.4.1，p. 37） | [ConditionalGoldbach.smoothedDirichletPolynomial](conditional-goldbach.lean#L1036) | 实际定义已写出 |
| Pell(t)（§6.4.1，p. 39） | [ConditionalGoldbach.poissonKernelReal](conditional-goldbach.lean#L1047)<br>[ConditionalGoldbach.realConvolution](conditional-goldbach.lean#L1049)<br>[ConditionalGoldbach.poissonAction](conditional-goldbach.lean#L1055) | 实际定义已写出 |
| PN（§6.4.2，p. 40） | [ConditionalGoldbach.arithmeticOperator](conditional-goldbach.lean#L225) | 实际定义已写出 |
| DN（§6.4.2，p. 40） | [ConditionalGoldbach.diagonalOperator](conditional-goldbach.lean#L228) | 实际定义已写出 |
| KN（§6.4.2，p. 40） | [ConditionalGoldbach.modelOperator](conditional-goldbach.lean#L231) | 实际定义已写出 |
| dn(s)（§6.4.2，p. 41） | [ConditionalGoldbach.diagonalVector](conditional-goldbach.lean#L1058)<br>[ConditionalGoldbach.diagonalHardyVector](conditional-goldbach.lean#L1326) | 实际定义已写出 |
| dn tensor dn（§6.4.2，p. 41） | `InnerProductSpace.rankOne` | Mathlib 直接接口 |
| C0(y)（§7.1，p. 45） | [ConditionalGoldbach.differenceConvolution](conditional-goldbach.lean#L148) | 实际定义已写出 |
| J0(y)（§7.1，p. 45） | [ConditionalGoldbach.sumConvolution](conditional-goldbach.lean#L151) | 实际定义已写出 |
| H0(y)（§7.1，p. 45） | [ConditionalGoldbach.signedConvolution](conditional-goldbach.lean#L154) | 实际定义已写出 |
| a0（§7.1，p. 46） | [ConditionalGoldbach.weightIntegral](conditional-goldbach.lean#L1060) | 实际定义已写出 |
| PsiN(s)（§7.2，p. 50） | [ConditionalGoldbach.functionalIntegrand](conditional-goldbach.lean#L1062) | 实际定义已写出 |
| αN,c（§A.1，p. 53） | [ConditionalGoldbach.alpha](conditional-goldbach.lean#L122) | 按 c 或边界参数复用 |
| SN,c HN,c ΓN,c TN,c ellN,c vN,c QN,c（§A.1，p. 53） | [ConditionalGoldbach.strip](conditional-goldbach.lean#L130)<br>[ConditionalGoldbach.HardySpace](conditional-goldbach.lean#L162)<br>[ConditionalGoldbach.boundaryPoint](conditional-goldbach.lean#L990)<br>[ConditionalGoldbach.residualOperator](conditional-goldbach.lean#L222)<br>[ConditionalGoldbach.functionalValue](conditional-goldbach.lean#L295)<br>[ConditionalGoldbach.rieszVector](conditional-goldbach.lean#L299)<br>[ConditionalGoldbach.normFunctional](conditional-goldbach.lean#L287) | 按 c 或边界参数复用 |
| XN,c（§A.2，p. 54） | [ConditionalGoldbach.spectralQuaternion](conditional-goldbach.lean#L279)<br>[ConditionalGoldbach.spectralComplex](conditional-goldbach.lean#L270) | 按 c 或边界参数复用 |
| R(N,c), S(N,c;hc)（§A.2，p. 54） | [ConditionalGoldbach.HypothesisRAt](conditional-goldbach.lean#L780)<br>[ConditionalGoldbach.HypothesisSAt](conditional-goldbach.lean#L783)<br>[ConditionalGoldbach.SpectralR](conditional-goldbach.lean#L327)<br>[ConditionalGoldbach.SpectralZeroFree](conditional-goldbach.lean#L330) | 按 c 或边界参数复用 |
| Malpha（§6.5,A.3，p. 42,55） | [ConditionalGoldbach.baselineBound](conditional-goldbach.lean#L807)<br>[ConditionalGoldbach.availableNormMajorant](conditional-goldbach.lean#L1066)<br>[ConditionalGoldbach.balanceFactor](conditional-goldbach.lean#L809) | 实际定义已写出 |
| CN,gamma（§A.4，p. 55） | [ConditionalGoldbach.poleCoefficient](conditional-goldbach.lean#L819) | 实际定义已写出 |
| RN(w)（§A.4，p. 56） | [ConditionalGoldbach.baselineProductR](conditional-goldbach.lean#L1070) | 实际定义已写出 |
| N=30030（§B，p. 57） | [ConditionalGoldbach.experimentN](conditional-goldbach.lean#L837) | 实际定义已写出 |
| P(t)（§B.1，p. 57） | [ConditionalGoldbach.cutoffPolynomial](conditional-goldbach.lean#L839) | 实际定义已写出 |
| η(x)（§B.1，p. 57） | [ConditionalGoldbach.wideCutoff](conditional-goldbach.lean#L843) | 实际定义已写出 |
| W(u)（§B.1，p. 57） | [ConditionalGoldbach.wideCompanion](conditional-goldbach.lean#L847) | 实际定义已写出 |
| f(u)（§B.1，p. 57） | [ConditionalGoldbach.wideWeight](conditional-goldbach.lean#L852) | 实际定义已写出 |
| J（§B.1，p. 57） | [ConditionalGoldbach.wideCorrelation](conditional-goldbach.lean#L854) | 实际定义已写出 |
| rG(N)（§B.1，p. 57） | [ConditionalGoldbach.unorderedPrimePairs](conditional-goldbach.lean#L856) | 实际定义已写出 |
| E（§B.1，p. 57） | [ConditionalGoldbach.edgeCorrection](conditional-goldbach.lean#L859) | 实际定义已写出 |
| Cpp（§B.1，p. 57） | [ConditionalGoldbach.primePowerCorrection](conditional-goldbach.lean#L863) | 实际定义已写出 |
| an（§B.2，p. 58） | [ConditionalGoldbach.countingCoefficient](conditional-goldbach.lean#L870) | 实际定义已写出 |
| Iχ（§B.2，p. 58） | [ConditionalGoldbach.countingIntegral](conditional-goldbach.lean#L872) | 实际定义已写出 |
| D（§B.2，p. 58） | [ConditionalGoldbach.diagonalCountingMoment](conditional-goldbach.lean#L876) | 实际定义已写出 |
| Jhat,Dhat（§B.3，p. 59） | [ConditionalGoldbach.approxSignedMoment](conditional-goldbach.lean#L879)<br>[ConditionalGoldbach.approxDiagonalMoment](conditional-goldbach.lean#L882) | 实际定义已写出 |
| cf（§B.3，p. 59） | [ConditionalGoldbach.wideModelMass](conditional-goldbach.lean#L885) | 实际定义已写出 |
| A（§B.3，p. 59） | [ConditionalGoldbach.wideMainIntegral](conditional-goldbach.lean#L1076) | 实际定义已写出 |
| B（§B.3，p. 59） | [ConditionalGoldbach.wideResidual](conditional-goldbach.lean#L887) | 实际定义已写出 |
| epsilonI（§B.3，p. 59） | [ConditionalGoldbach.HasMomentError](conditional-goldbach.lean#L1080) | 实际定义已写出 |
| rhatG（§B.3，p. 59） | [ConditionalGoldbach.approxPrimeCount](conditional-goldbach.lean#L889) | 实际定义已写出 |
| epsilonr（§B.3，p. 59） | [ConditionalGoldbach.countError](conditional-goldbach.lean#L892) | 实际定义已写出 |
| ellW（§B.4，p. 60） | [ConditionalGoldbach.wideFunctional](conditional-goldbach.lean#L920) | 实际定义已写出 |
| vW（§B.4，p. 60） | [ConditionalGoldbach.wideRieszVector](conditional-goldbach.lean#L924) | 实际定义已写出 |
| si（§B.4，p. 60） | [ConditionalGoldbach.spectralNode](conditional-goldbach.lean#L937) | 实际定义已写出 |
| wi（§B.4，p. 60） | [ConditionalGoldbach.trapezoidWeight](conditional-goldbach.lean#L940) | 实际定义已写出 |
| Cij（§B.4，p. 60） | [ConditionalGoldbach.finiteSpectralMatrix](conditional-goldbach.lean#L943) | 实际定义已写出 |
| X30030(q)（§B.4，p. 60） | [ConditionalGoldbach.finiteSpectralFunction](conditional-goldbach.lean#L947)<br>[ConditionalGoldbach.finiteEigenvalues](conditional-goldbach.lean#L957)<br>[ConditionalGoldbach.IsFiniteSpectrum](conditional-goldbach.lean#L952)<br>[ConditionalGoldbach.finiteMatrixOpNorm](conditional-goldbach.lean#L960) | 实际定义已写出；依赖 `Matrix.det` |

## 额外的存在性与对接声明

| 声明 | 用途 |
|---|---|
| [ConditionalGoldbach.singularSeries_eq_existing](conditional-goldbach.lean#L50) | 把原文因子 2 显式写成等式。 |
| [ConditionalGoldbach.interiorLine_memLp](conditional-goldbach.lean#L179) | 把 Fourier–Laplace 内部竖线装入 L²。 |
| [ConditionalGoldbach.boundaryTraces_exist](conditional-goldbach.lean#L195) | 选取双侧 L² 边界迹所需存在性。 |
| [ConditionalGoldbach.primePair_consequence](conditional-goldbach.lean#L423) | 由加权渐近式推出素数对下界的正文直接推论。 |

## 已有项目与 Mathlib 的依赖边界

已有 Goldbach 项目提供 von Mangoldt、素数幂误差处理、奇异级数及若干 Mellin 辅助接口。Mathlib 提供 Mellin 反演、Fourier 的 L² Plancherel、Riesz 表示、紧自伴算子的谱理论、Gamma/Beta 恒等式、秩一算子与可和无穷乘积。清单保留了逐条路径和精确声明名。

当前主模块直接导入 `Mathlib` 与 `goldbach-lean` 的 `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries`。另一项目中的接口及本仓库其他专门模块列为后续证明的可复用候选，并未全部导入或宣称已成功对接；两个现有项目均保持只读。

尚需实质建设的是带状 Hardy 空间的边界迹和等距对应、积分核到 Hilbert–Schmidt 自伴算子的桥接、模数一致估计、迹与谱乘积的接口，以及积分交换的精确域。继续下钻现有三元 Goldbach 项目后，已找到 `CompletedLogDerivativeConstant.lean` 中完成 L 函数在任意避零点的 Hadamard 展开；不必重做这部分解析延拓，仍须证明本稿的非零常数归一化、重数索引、两点差与正常收敛适配。单位窗零点计数应从 `reference_mass_improved` 正核界导出，不能对两个全局上界作差。精确路径和行号见依赖图及 `inventory.json` 的 `audited_project_bridges`。

定义审查宜先核对归一化、共轭、域和量词，再审查总化对象的存在性条件。通过类型检查只说明陈述合法，并不会证明这些 `sorry` 陈述，也不会验证论文推导。
