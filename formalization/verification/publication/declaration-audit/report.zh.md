# 声明级外部依赖审计

本次检查回答的是“证明项实际引用了什么”，与模块被 `import` 加载是两个层级。

工程确实以 `goldbach-lean` 为包依赖，复用其中的奇异级数和解析数论基础；它没有借用该工程的 **1+1.9 结论、三素数定理或 1+1.9 数值系数/积分证书**。三个主结果实际只触达奇异级数与 Dirichlet L 函数基础。完整的 102 条审阅结果和公共证明库还通过 `lemma_4_3_uniform` 使用了 Mertens 乘积下界，以及该下界在外部库中采用的素数定理证明。

采集版本：Lean `v4.35.0`，外部 `goldbach-lean` 固定提交 `24490c2ab7787238f816d771c9176411dcbda503`。数学源码快照哈希见 `source-hashes.json`；图文件哈希、采集时间及计数口径见 `metadata.json`。采集之后仅改变包地址不会改变这个声明级结论，前提是仍解析到该提交且源码哈希一致。

## 检查方法与范围

`DeclarationAudit.lean` 加载 `ConditionalGoldbach` 后，对本项目所属模块中的声明递归追踪其类型、证明/定义值（包括 opaque 值），并在归纳类型处加入构造子。外部声明的模块来源由 Lean 环境的 `getModuleIdxFor?` 确定，不能用声明名称的前缀代替。保存的每条节点列出了 `type_refs`、`value_refs`、`constructor_refs`。整个检查遍历 90,420 条可达声明，没有找不到的常量。

“公共库”以声明所属模块是 `ConditionalGoldbach*` 且 `isPrivateName = false` 为根，共 2,869 个声明，包含 Lean 自动生成的辅助声明。另对全部 2,938 个本项目声明做了校验，外部依赖集合相同。102 条审阅名单取自此次工程的 `reviewed-types.json`。

| 范围 | 外部项目声明 | 外部项目模块 | 本地直接引用的外部声明 |
|---|---:|---:|---:|
| `theorem_1_1` | 68 | 5 | 20 |
| `theorem_1_2` | 68 | 5 | 20 |
| `primePair_consequence` | 72 | 5 | 22 |
| 原 102 条审阅声明合并 | 839 | 22 | 30 |
| 公共证明库 | 839 | 22 | 30 |
| 含私有声明的全部本项目库 | 839 | 22 | 30 |

以上“外部项目”仅指来自 `goldbach-lean` 自有目录的数学声明，不将 Lean、Mathlib 及其通用工具包混入这些计数。每个范围递归发现的公理都恰为 `Classical.choice`、`Quot.sound`、`propext`；没有 `sorryAx`、额外数学公理或计算信任公理。

## 三个主结果实际复用的内容

五个外部模块为：

| 模块 | `theorem_1_1` / `theorem_1_2` | `primePair_consequence` | 作用 |
|---|---:|---:|---|
| `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries` | 23 | 27 | 奇异级数的定义、Euler 因子、乘积收敛、正性及上下界所需的基础 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries` | 27 | 27 | 非主特征 L 函数在正实部区域的有序级数、尾项估计与函数一致性 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation` | 9 | 9 | Abel 求和的复幂权及变化控制，支撑上述级数估计 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative` | 7 | 7 | 特征周期和为零、部分和界，以及有限 Abel 求和恒等式 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds` | 2 | 2 | 实 ζ 主项级数 `∑ n^(-σ)` 的初等积分比较上界 |

关键接口是：

- `DirichletLConditionalValueSeries.norm_orderedValueSeries_sub_sum_range_le`、`orderedValueSeries_eq_LFunction_of_re_pos`、`character_nat_zero_of_ne_one`，由本项目 `LFunction_polynomial_bound` 使用，以得到 `‖L(s,χ)‖ ≤ q (1 + ‖s‖ / Re(s))`。
- `AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le`，由 `LFunction_sub_one_norm_bound` 使用，控制 `Re(s) > 1` 的 `‖L(s,χ) - 1‖`。虽然声明命名空间含 `LargeSieve`，这里实际借用的是初等级数上界。
- `MathlibNt.SieveTheory.SingularSeries.liuSingularSeries`、`liuUniversalProduct` 及其 Euler 因子和正性结果。本文的 `singularSeries N` 定义为 `2 * liuSingularSeries N`；这只是共享奇异级数归一化，不是调用 1+1.9 定理。
- `primePair_consequence` 另用 `liuUniversalProduct_le_liuSingularSeries` 与相关正性基础，给奇异级数一个统一正下界。

这三个结果的常量闭包都没有 Mertens 或 `PrimeNumberTheoremAnd` 的声明。

## 102 条审阅与完整公共库额外使用的内容

两者的外部声明集合完全相同，均为 839 个声明、22 个模块。唯一触达 Mertens/素数定理链的原审阅声明是 `ConditionalGoldbach.lemma_4_3_uniform`。一条实际引用路径是：

```text
ConditionalGoldbach.lemma_4_3_uniform
→ ConditionalGoldbach.totient_ratio_loglog_bound
→ ConditionalGoldbach.totient_ratio_loglog_large
→ MathlibNt.SieveTheory.MertensTheorem.primeProduct_lower_bound
→ MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order
→ MathlibNt.SieveTheory.MertensTheorem.mertens_second_theorem
→ AnalyticNumberTheory.Mertens.mertensSecond_nat
→ AnalyticNumberTheory.Mertens.mertensSecond_isBigO
→ AnalyticNumberTheory.Mertens.mertensSecond_eventually
→ AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_endpoint_error
→ AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_error
→ AnalyticNumberTheory.PrimeDistribution.chebyshevPsi_medium_error
→ MediumPNT
```

这里 `primeProduct_lower_bound` 给出某个正数 `c` 使 `c / log m ≤ ∏_{p≤m}(1 - 1/p)`，从而帮助本工程证明 `N / φ(N) ≪ log log N`。外部库的 `MediumPNT` 证明的是 `ψ(x) = x + O(x exp(-c (log x)^(1/10)))`，它是素数定理，不是三素数定理。

| 实际触达的外部模块 | 声明数 |
|---|---:|
| `AnalyticNumberTheory.Mertens.Basic` | 4 |
| `AnalyticNumberTheory.Mertens.PartialSummation` | 24 |
| `AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta` | 2 |
| `AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem` | 1 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation` | 9 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries` | 27 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds` | 2 |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative` | 7 |
| `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries` | 33 |
| `MathlibNt.SieveTheory.Arithmetic.MertensTheorem` | 9 |
| `PrimeNumberTheoremAnd.Auxiliary` | 9 |
| `PrimeNumberTheoremAnd.EulerMaclaurin` | 11 |
| `PrimeNumberTheoremAnd.Fourier` | 1 |
| `PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support` | 2 |
| `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic` | 2 |
| `PrimeNumberTheoremAnd.MediumPNT` | 151 |
| `PrimeNumberTheoremAnd.MellinCalculus` | 99 |
| `PrimeNumberTheoremAnd.Rectangle` | 18 |
| `PrimeNumberTheoremAnd.ResidueCalcOnRectangles` | 57 |
| `PrimeNumberTheoremAnd.SmoothExistence` | 33 |
| `PrimeNumberTheoremAnd.ZetaBounds` | 334 |
| `PrimeNumberTheoremAnd.ZetaConj` | 4 |

## 本项目直接引用的完整外部声明列表

下表为“本项目声明 → 外部项目声明”边界处的全部 30 个目标常量；进一步展开外部证明内部的辅助声明后才得到 839 个。`_proof_1` 等由 Lean 生成的常量计入机械审计数量。

| 外部声明 | 作用 |
|---|---|
| `AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le` | 实幂级数的积分比较上界 |
| `DirichletLAbelWeightVariation.cpowWeight` | Abel 求和复幂权的定义 |
| `DirichletLConditionalValueSeries.character_nat_zero_of_ne_one` | 非主特征在 0 处的取值 |
| `DirichletLConditionalValueSeries.norm_orderedValueSeries_sub_sum_range_le` | L 值级数尾项的定量估计 |
| `DirichletLConditionalValueSeries.orderedValueSeries` | L 函数有序值级数定义 |
| `DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos` | 正实部区域中级数与 L 函数相等 |
| `MathlibNt.SieveTheory.MertensTheorem.primeProduct` | Mertens 素数乘积定义 |
| `MathlibNt.SieveTheory.MertensTheorem.primeProduct_lower_bound` | Mertens 乘积正下界，用于 N/φ(N) 界 |
| `MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation` | 奇异级数通用 Euler 乘积的偏差因子定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuCorrection` | 有限素因子修正乘积定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor` | 单个素因子的修正定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor_pos` | 修正因子的正性 |
| `MathlibNt.SieveTheory.SingularSeries.liuCorrection_pos` | 修正乘积的正性 |
| `MathlibNt.SieveTheory.SingularSeries.liuLocalFactor` | 局部奇异级数因子定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuLocalFactor._proof_1` | 局部因子定义的自动生成辅助证明 |
| `MathlibNt.SieveTheory.SingularSeries.liuLocalFactor_eq_correction_mul_base` | 局部因子分解为修正乘通用因子 |
| `MathlibNt.SieveTheory.SingularSeries.liuLocalFactor_of_dvd` | 素数整除模数时的局部因子公式 |
| `MathlibNt.SieveTheory.SingularSeries.liuSingularSeries` | 外部归一化的奇异级数定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos` | 奇异级数正性 |
| `MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct` | 通用奇异级数无限乘积定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuUniversalProductTruncated` | 通用乘积的有限截断定义 |
| `MathlibNt.SieveTheory.SingularSeries.liuUniversalProductTruncated_pos` | 有限截断正性 |
| `MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_le_liuSingularSeries` | 奇异级数的统一下界 |
| `MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_nonneg` | 通用乘积非负 |
| `MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_pos` | 通用乘积严格为正 |
| `MathlibNt.SieveTheory.SingularSeries.multipliable_one_add_liuBaseDeviation` | 通用无限乘积收敛 |
| `MathlibNt.SieveTheory.SingularSeries.one_add_liuBaseDeviation_eq_baseFactor` | 通用 Euler 因子的等价公式 |
| `MathlibNt.SieveTheory.SingularSeries.one_add_liuBaseDeviation_le_one` | 通用 Euler 因子上界 |
| `MathlibNt.SieveTheory.SingularSeries.one_add_liuBaseDeviation_pos` | 通用 Euler 因子正性 |
| `MathlibNt.SieveTheory.SingularSeries.tendsto_liuUniversalProductTruncated` | 有限截断趋于无限乘积 |

## 未使用的其他项目结论

声明闭包没有 `Goldbach.one_plus_one_nine`、其存在/计数/下界变体、Chen 1+2 结论，也没有三素数定理。与独立模块审计交叉检查后，1+1.9 主结论模块及其数值系数/积分证书模块甚至没有进入当前模块导入闭包；独立的 `liu-wang-ternary-goldbach-lean` 三素数工程也不在源根或 Lake 依赖中。

导入闭包中确有与 `LiLiu` 名称有关的通用前置模块 `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean`，但该模块没有任何声明进入本次 839 条实际外部声明集合。不能因共享仓库或名称相近，就将这些基础工具描述为调用 1+1.9 结论。

这里排除的是其他项目的数值证书作为证明输入。普通精确算术及本项目自身的有限计算仍然可能出现在证明中；本次全部范围的公理集合已单独核查。

## 可复核材料

- `DeclarationAudit.lean`：Lean 环境导出程序；在工程目录运行 `flock /tmp/liliu-build.lock lake env lean ../work/publication/declaration-audit/DeclarationAudit.lean`。
- `declaration-graph.json`：完整逐声明图（约 95 MB）。
- `analyze.py`：对三个主结果、102 条审阅集合和完整公共库做可达闭包分析。
- `summary.json`：每个范围的计数、实际模块、公理集合。
- `theorem_1_1.json`、`theorem_1_2.json`、`primePair_consequence.json`、`reviewed_102.json`、`public_library.json`：完整外部声明列表、直接边界引用、每个外部声明的实际引用路径。
- 各 `*-external-declarations.tsv`：便于人工查看的逐条名称、所属模块、声明类型与私有标记。
- `reviewed-requiring-mertens.json`：102 条中真正依赖 Mertens 的声明列表。
- `imported-modules.json`：独立的环境模块导入列表，共 11,731 个；它与证明常量依赖图是不同的材料。
