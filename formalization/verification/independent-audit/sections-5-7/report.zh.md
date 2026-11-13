# 第5–7节独立审计结果

本轮直接逐段读取原始 `outputs/formalization-preparation/conditional-goldbach.tex` 第1823–3858行，并对照当前库的定义和完整定理类型。没有把旧 `Reviewed.lean`、旧语义审阅结论或旧核验报告当作TeX正确性的证据。`inventory.json` 仅用于声明定位及检查清单完整性。

覆盖17个正文命名结论、35个已列审阅辅助条目、2个Hardy构造义务，共54个命题；另逐项核对32个第5–7节定义族，并交叉检查第2节的Hardy/谱/泛函定义。完整逐项对应见 `statement-matrix.json`、`definition-matrix.json` 和可读的 `semantic-matrix.md`，每项列出原TeX行、原公式或条款、条件/量词、当前Lean声明位置和判断。

在本范围未发现使原文结论实质变弱的遗漏、假设偷换或量词变化。该结论需要下列已经逐一核对的表示桥梁；不能只看函数名或一个主定理的短摘要。

## 关键核对

1. **Hardy空间的表示。** `HardySpace a b` 实现为频域的加权L²。独立参考另定义原始“全纯+配对竖线平方积分有界”的 `RawHardy`。`lemma_5_2` 的正向结论给原始Hardy条件和精确上确界范数，反向给每个原始Hardy函数唯一的频域向量。`interiorLine_memLp` 和 `boundaryTraces_exist` 的证明输入没有预先假定待证可积性或迹存在。`IsBoundaryTrace` 是两个真正的L²空间拓扑单侧极限。补充结论给线性、闭像、迹范数和边界内积，这些结果确定了相容的边界迹空间。

2. **算子是实际积分算子。** `kernelOperator` 的全域总定义确实有“不存在则0”分支，但 `proposition_5_3` 在原文条件下给 `RepresentsKernel`，另有 `proposition_5_3_kernel_integrability` 给每个内点、每个Hardy向量的两条边界积分绝对可积。当前 `RepresentsKernel.unique` 和独立桥梁 `selected_operator_unique` 表明该选择与任何实际积分表示一致。因此默认0不代替正文的存在性工作。三分量也分别有相应表示、绝对可积和 `T=P−D−K` 等式。

3. **归一化与内积约定保持。** 边界内积是两条正弧长积分之和，没有 `1/(2π)`；`paperInner u v = inner ℂ v u` 使第一变量线性。Fourier–Laplace系数为 `(2π)^(−1/2)`，竖直Mellin参数化系数为 `(2π)^(−1)`，与向上积分中 `ds=i dt` 相符。评价核系数 `1/(4Δ)`、范数界 `1/(8d)`、二次型里的向量和共轭顺序均正确。

4. **命题6.5的三组估计完整。** 当前 `proposition_6_5` 同时断言P、D正迹类、K为HS，并给 `HS(P)≤tr(P)≤C(log²N+α⁻²)`、`HS(D)≤tr(D)≤Cα⁻²`、`HS(K)≤Cα⁻²`。`∃C>0` 在 `∀N` 之前。对于正文随后强调的可变左边界，另直接检查了 `ComponentNormBounds.component_bounds_of_average`：同一C在 `∀a>0,a<β` 之前，所以并非只在固定N、固定α下取依赖参数的常数。

5. **谱数据与算子真实绑定。** `SpectralData T` 包含真正的Hilbert基、`T(bj)=μj bj` 和平方可和；谱存在由命题5.3证明。实现为了完整基允许μ=0，原文只列非零谱。新增独立 `zero_padding_product`、`zero_padding_square_sum` 证明删除μ=0的索引不改产品和平方和。原库的谱选择独立、排列独立、平方算子行列式补充进一步连接实际算子的谱。`SpectralBasisExistence` 当前构造本身按各eigenspace的正交基组成，故不是任意序列冒充按重数列出的谱。

6. **四元数函数与普通Fredholm行列式一致。** 产品因子是 `1−4μ²q(1−q)/δ²`；复谱产品和ℍ极限有标准切片及所有切片桥梁。`IntrinsicEntire` 以同一个全纯复函数、共轭对称和所有纯虚单位切片表述原文“同一实系数幂级数”的含义；这一步的语义对应由数学审阅确认。行列式使用 `T.comp T`，并证明其谱乘积等于原T的平方谱产品及 `tr(T²)=Σμ²=HS²`。归一化 `X(0)=X(1)=1`、所有对称性、临界值实性、三类零点、非零谱条件、中心阶数及重数保持均由主项加补充完整覆盖。

7. **谱字典保留边界与量词。** 零区是开半空间 `Re q>1−η`，对应非严格算子界 `≤δ/(2√(η(1−η)))`；`0<η<1/2`、`M>δ`、`‖T‖≤M` 及 `η(M)` 均保留。基线定理常数与最终N阈值统一；宽度取固定正倍数 `S/(NlogN)`。标准谱字典不偷偷增加“谱已列全”等条件；算术版本这些条件由前述谱构造提供。

8. **Mellin与二次型的符号、可积性和常数依赖保持。** 字符一重积分前有负号，字符矩双积分因两负号抵消为正；Beta模型积分为 `−cφS`；残差为 `r=P−D+cφS=cφS−G`。所有被TeX称绝对收敛的一/二重积分均有对应 `Integrable` 补充。命题7.4给每条内轮廓的泛函表示、连续线性映射、精确Riesz范数、统一上界和 `Oφ(1/logN)`，不只是固定轮廓的不等式。定理7.1保留 `cφS−G=⟨Tv,v⟩` 精确有符号等式；统一误差常数显式为仅依φ的 `e² weightEnergy φ`。引理7.5把C放在N、η之前，渐近补充用 `∀ε∃B∀合格N,η` 的统一阈值表达趋无穷条件，足以覆盖任何满足原文条件的偶数序列。

## 需要说明的建模差异

- `PositiveKernel` 单独只要求二次型实部非负，确实不足以描述任意复核的通常正定性。在当前字符核中，Hermitian性质独立成立，因此二次型虚部为0。独立 `hermitian_quadratic_real` 与 `character_quadratic_nonnegative_real` 已编译通过。正确语义单位是“此predicate + 已证明Hermitian”，不能推广为两个任意predicate普遍等价。此处没有造成正文结论弱化。
- `IsHilbertSchmidt`、`IsPositiveTraceClass` 通过ℕ索引Hilbert基实现，限定所用可数无限维Hilbert空间类别；不应把它们宣传为任意Hilbert空间上的完全通用定义。当前Hardy空间有这样的真实基，基独立/谱和/迹桥梁齐全。
- `sumConvolution` 用全正半轴积分编码原文 `∫0^y`。在 `IsWeight` 的支撑条件下，`lemma_7_2_convolutions` 明确证明相等。独立公式比较只比较实际全正半轴公式，语义结论另依赖该有限积分桥梁。
- 旧清单 `rankOneOperator` 是建议名而非当前项目中的一个新定义。实际直接使用mathlib `InnerProductSpace.rankOne`，并在 `proposition_6_5_diagonal_vector_spec` 证明正确应用公式。记录为定位元数据差异，不是漏实现。
- `ha : alpha N < beta`、`NeZero N` 为Lean类型构造所需参数，在 `N>e^10` 下可推得；独立 `arithmetic_strip_nonempty` 已核验，因而并非额外数学假设。

## 机械检验边界与产物

`Reference.lean` 包含本轮独立转录的54个完整预期命题（均为 `def ... : Prop`），及26个独立公式级定义。所有54个完整预期命题都用当前实际证明进行类型赋值，Lean编译退出码为0；26个公式级桥梁由 `rfl` 核验，未新增axiom或sorry。`comparison.json` 和 `definitions-comparison.json` 分别提供54项命题、26项定义的目标映射。四个泛型命题保留宇宙参数u。

`Bridges.lean` 包含本轮独立写出的Hermitian二次型实性、字符核非负实值、站立条件导出带宽、选择算子唯一、实际积分表示和零填充不变性等桥梁，编译退出码为0。

本报告记录本节独立审阅与局部编译。完整比较器结果见上级目录 `final-comparison.json`。TeX到独立参考由数学审阅建立对应；参考与实现的类型和定义体由Lean比较器核查。
