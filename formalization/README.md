# Li–Liu Goldbach16：证明工程

这是从已经逐项审阅的陈述稿开始的实际Lean证明工程。原文件作为不可变参考保存在`reference/Reviewed.lean`；原中文对照页面仍是审阅快照，不能用其`全部sorry`标识描述本工程的新进度。

[查看当前证明进展及中文／Lean对照](progress.html) · [机器公理台账](proof-status.json) · [102条声明类型保真检查](reviewed-types.json)

基线的102个待证声明目前：**102个已消除传递的sorryAx，0个证明体已经写完但传递依赖仍未证明，0个仍是直接占位。** 另有新增辅助结果；计入全部公共lemma/theorem后，完全无sorryAx依赖的结果共1354个。辅助结果没有当作新增的论文命名定理。

## 当前主结论的状态

经原TeX逐项审阅的102条定理（正文及附录）全部通过Lean传递公理核验。常数与h的量词次序、GRH和S/R条件没有改变；171个原定义也保持不变。这里完成的是论文原有条件结论的形式化。

- `theorem_1_1`：kernel_closed。本地待证依赖：无。
- `theorem_1_2`：kernel_closed。本地待证依赖：无。
- `primePair_consequence`：kernel_closed。本地待证依赖：无。

## 已闭合的原审阅声明

- [interiorLine_memLp](LiLiuGoldbach/Definitions.lean)（第12行）。
- [boundaryTraces_exist](LiLiuGoldbach/Definitions.lean)（第28行）。
- [proposition_6_5_components_spec](LiLiuGoldbach/Proofs/ArithmeticComponentOperators.lean)（第108行）。
- [lemma_A_3_balance](LiLiuGoldbach/Proofs/BalanceBounds.lean)（第36行）。
- [lemma_A_3_width_ratio](LiLiuGoldbach/Proofs/BalanceBounds.lean)（第95行）。
- [proposition_A_4_baseline_product](LiLiuGoldbach/Proofs/BaselineEuler.lean)（第123行）。
- [lemma_4_2](LiLiuGoldbach/Proofs/BetaIdentity.lean)（第219行）。
- [lemma_4_1](LiLiuGoldbach/Proofs/BetaIntegrals.lean)（第172行）。
- [lemma_4_1_absolute_convergence](LiLiuGoldbach/Proofs/BetaIntegrals.lean)（第183行）。
- [lemma_4_1_signed_model](LiLiuGoldbach/Proofs/BetaIntegrals.lean)（第195行）。
- [lemma_4_2_meromorphic](LiLiuGoldbach/Proofs/BetaMeromorphic.lean)（第129行）。
- [proposition_3_2](LiLiuGoldbach/Proofs/CharacterAnalytic.lean)（第108行）。
- [lemma_6_4](LiLiuGoldbach/Proofs/CharacterAverage.lean)（第82行）。
- [proposition_3_2_joint_meromorphic](LiLiuGoldbach/Proofs/CharacterJoint.lean)（第55行）。
- [lemma_3_4_paired_zero_sum](LiLiuGoldbach/Proofs/CharacterSeries.lean)（第63行）。
- [lemma_3_4](LiLiuGoldbach/Proofs/CharacterZeroExpansion.lean)（第53行）。
- [lemma_3_4_normal_convergence](LiLiuGoldbach/Proofs/CharacterZeroShiftNormal.lean)（第26行）。
- [lemma_6_4_zero_poisson_convergence](LiLiuGoldbach/Proofs/CharacterZeroSummability.lean)（第122行）。
- [lemma_3_1_odd_orthogonality](LiLiuGoldbach/Proofs/Characters.lean)（第58行）。
- [lemma_3_1](LiLiuGoldbach/Proofs/Characters.lean)（第360行）。
- [lemma_4_3_density_convergence](LiLiuGoldbach/Proofs/DensityConvergence.lean)（第75行）。
- [lemma_4_3_euler_product_convergence](LiLiuGoldbach/Proofs/DensityEuler.lean)（第146行）。
- [lemma_4_3](LiLiuGoldbach/Proofs/DensityEulerIdentity.lean)（第98行）。
- [theorem_6_1](LiLiuGoldbach/Proofs/DictionaryApplication.lean)（第34行）。
- [singularSeries_eq_existing](LiLiuGoldbach/Proofs/Elementary.lean)（第10行）。
- [proposition_B_5](LiLiuGoldbach/Proofs/FiniteExperimentSpectrum.lean)（第141行）。
- [lemma_3_3](LiLiuGoldbach/Proofs/HadamardLimit.lean)（第110行）。
- [proposition_5_3](LiLiuGoldbach/Proofs/HardyArithmeticTheorems.lean)（第33行）。
- [proposition_5_4_kernel_pairing](LiLiuGoldbach/Proofs/HardyArithmeticTheorems.lean)（第47行）。
- [proposition_5_3_kernel_integrability](LiLiuGoldbach/Proofs/HardyArithmeticTheorems.lean)（第55行）。
- [proposition_5_4](LiLiuGoldbach/Proofs/HardyArithmeticTheorems.lean)（第66行）。
- [proposition_5_4_fixed_contour](LiLiuGoldbach/Proofs/HardyArithmeticTheorems.lean)（第79行）。
- [lemma_5_2](LiLiuGoldbach/Proofs/HardyConverse.lean)（第43行）。
- [proposition_5_4_exact_norm](LiLiuGoldbach/Proofs/HardyReproducing.lean)（第138行）。
- [lemma_5_2_representation_spec](LiLiuGoldbach/Proofs/HardyTraceAlgebra.lean)（第123行）。
- [lemma_5_2_closed_trace_space](LiLiuGoldbach/Proofs/HardyTraceAlgebra.lean)（第181行）。
- [lemma_5_2_boundary_inner](LiLiuGoldbach/Proofs/HardyTraceAlgebra.lean)（第198行）。
- [proposition_3_2_finite_rank](LiLiuGoldbach/Proofs/KernelAlgebra.lean)（第106行）。
- [proposition_5_1](LiLiuGoldbach/Proofs/KernelRegularity.lean)（第95行）。
- [proposition_5_1_fueter_equation](LiLiuGoldbach/Proofs/KernelRegularity.lean)（第144行）。
- [theorem_7_1_uniform](LiLiuGoldbach/Proofs/Main.lean)（第16行）。
- [theorem_1_1](LiLiuGoldbach/Proofs/Main.lean)（第56行）。
- [theorem_1_2](LiLiuGoldbach/Proofs/Main.lean)（第98行）。
- [lemma_7_1](LiLiuGoldbach/Proofs/MellinCharacterShift.lean)（第107行）。
- [lemma_7_1_absolute_convergence](LiLiuGoldbach/Proofs/MellinCharacterShift.lean)（第153行）。
- [lemma_7_2](LiLiuGoldbach/Proofs/MellinModelDouble.lean)（第66行）。
- [lemma_7_2_absolute_convergence](LiLiuGoldbach/Proofs/MellinModelDouble.lean)（第77行）。
- [lemma_3_5](LiLiuGoldbach/Proofs/MellinMoment.lean)（第97行）。
- [lemma_3_5_absolute_convergence](LiLiuGoldbach/Proofs/MellinMomentComplete.lean)（第10行）。
- [lemma_3_5_small_sigma](LiLiuGoldbach/Proofs/MellinMomentComplete.lean)（第21行）。
- [proposition_7_3](LiLiuGoldbach/Proofs/MellinResidual.lean)（第89行）。
- [proposition_7_3_absolute_convergence](LiLiuGoldbach/Proofs/MellinResidual.lean)（第98行）。
- [proposition_4_4](LiLiuGoldbach/Proofs/ModelContinuation.lean)（第88行）。
- [proposition_A_4](LiLiuGoldbach/Proofs/PoleObstruction.lean)（第11行）。
- [primePair_consequence](LiLiuGoldbach/Proofs/PrimePairs.lean)（第13行）。
- [lemma_7_5](LiLiuGoldbach/Proofs/QuadraticEstimates.lean)（第37行）。
- [lemma_7_5_asymptotic](LiLiuGoldbach/Proofs/QuadraticEstimates.lean)（第74行）。
- [proposition_7_4](LiLiuGoldbach/Proofs/QuadraticFunctional.lean)（第11行）。
- [theorem_7_1](LiLiuGoldbach/Proofs/QuadraticIdentity.lean)（第120行）。
- [proposition_6_5](LiLiuGoldbach/Proofs/QuantitativeBounds.lean)（第23行）。
- [lemma_A_3_absolute_operator_bound](LiLiuGoldbach/Proofs/QuantitativeBounds.lean)（第42行）。
- [lemma_A_3](LiLiuGoldbach/Proofs/QuantitativeBounds.lean)（第53行）。
- [theorem_6_2](LiLiuGoldbach/Proofs/QuantitativeBounds.lean)（第108行）。
- [proposition_4_5](LiLiuGoldbach/Proofs/ResidualAnalytic.lean)（第85行）。
- [lemma_4_1_local_density](LiLiuGoldbach/Proofs/SingularDensity.lean)（第63行）。
- [theorem_1_2_hypothesisR_implies_S](LiLiuGoldbach/Proofs/SpectralAlgebra.lean)（第12行）。
- [theorem_6_1_width_comparison](LiLiuGoldbach/Proofs/SpectralAlgebra.lean)（第24行）。
- [proposition_6_3_factor_central_order](LiLiuGoldbach/Proofs/SpectralAlgebra.lean)（第126行）。
- [proposition_6_2](LiLiuGoldbach/Proofs/SpectralCompletion.lean)（第81行）。
- [proposition_6_1_spectral_choice_independent](LiLiuGoldbach/Proofs/SpectralCompletionChoice.lean)（第104行）。
- [proposition_6_1_square_determinant](LiLiuGoldbach/Proofs/SpectralCompletionDeterminant.lean)（第37行）。
- [proposition_6_1](LiLiuGoldbach/Proofs/SpectralCompletionDeterminant.lean)（第46行）。
- [proposition_6_1_enumeration](LiLiuGoldbach/Proofs/SpectralCompletionIdentities.lean)（第53行）。
- [proposition_6_2_centered_product](LiLiuGoldbach/Proofs/SpectralCompletionIdentities.lean)（第98行）。
- [proposition_6_2_critical_values](LiLiuGoldbach/Proofs/SpectralCompletionIdentities.lean)（第154行）。
- [proposition_6_3_multiplicities](LiLiuGoldbach/Proofs/SpectralCompletionMultiplicities.lean)（第86行）。
- [proposition_6_3_three_cases](LiLiuGoldbach/Proofs/SpectralCompletionZeros.lean)（第91行）。
- [proposition_6_3](LiLiuGoldbach/Proofs/SpectralConsequences.lean)（第33行）。
- [proposition_6_1_all_slices](LiLiuGoldbach/Proofs/SpectralConsequences.lean)（第56行）。
- [proposition_6_1_complex_slice](LiLiuGoldbach/Proofs/SpectralConsequences.lean)（第65行）。
- [proposition_6_5_diagonal_vector_spec](LiLiuGoldbach/Proofs/SpectralDiagonalVector.lean)（第111行）。
- [theorem_6_1_abstract_dictionary](LiLiuGoldbach/Proofs/SpectralDictionary.lean)（第166行）。
- [proposition_5_3_hs_basis_independent](LiLiuGoldbach/Proofs/SpectralHilbertSchmidt.lean)（第52行）。
- [lemma_6_4_poisson_action_spec](LiLiuGoldbach/Proofs/SpectralPoisson.lean)（第29行）。
- [lemma_6_4_perron_residue](LiLiuGoldbach/Proofs/SpectralPoisson.lean)（第43行）。
- [lemma_6_4_poisson_convolution](LiLiuGoldbach/Proofs/SpectralPoissonConvolution.lean)（第172行）。
- [proposition_6_1_positive_fredholm_spec](LiLiuGoldbach/Proofs/SpectralPositiveFredholm.lean)（第17行）。
- [lemma_4_3_uniform](LiLiuGoldbach/Proofs/TotientLogLog.lean)（第170行）。
- [proposition_A_2](LiLiuGoldbach/Proofs/VariableConsequences.lean)（第19行）。
- [proposition_A_1](LiLiuGoldbach/Proofs/VariableQuadratic.lean)（第55行）。
- [proposition_A_2_pointwise](LiLiuGoldbach/Proofs/VariableQuadratic.lean)（第116行）。
- [proposition_A_1_operator_spec](LiLiuGoldbach/Proofs/VariableStripOperators.lean)（第151行）。
- [theorem_1_1_weight_exists](LiLiuGoldbach/Proofs/Weights.lean)（第45行）。
- [lemma_3_5_weight_support](LiLiuGoldbach/Proofs/Weights.lean)（第66行）。
- [lemma_7_2_convolutions](LiLiuGoldbach/Proofs/Weights.lean)（第115行）。
- [proposition_7_4_norm_integrals](LiLiuGoldbach/Proofs/Weights.lean)（第196行）。
- [lemma_B_3](LiLiuGoldbach/Proofs/WideError.lean)（第11行）。
- [lemma_B_3_main_integral](LiLiuGoldbach/Proofs/WideMainIntegral.lean)（第65行）。
- [proposition_B_4](LiLiuGoldbach/Proofs/WideMellinResidual.lean)（第58行）。
- [lemma_B_2](LiLiuGoldbach/Proofs/WideMoments.lean)（第84行）。
- [proposition_B_1](LiLiuGoldbach/Proofs/WidePrimePowerCount.lean)（第143行）。
- [proposition_B_4_weight](LiLiuGoldbach/Proofs/WideWeight.lean)（第163行）。

## 已有证明体但还依赖未证对象／定理


## 并行模块

- `Proofs/Weights.lean`、`WeightNorm.lean`：光滑权、严格正质量、卷积与支集、范数积分和统一界。
- `Proofs/Characters.lean`、`KernelAlgebra.lean`：通用奇特征正交、完整Lemma3.1、有限Gram核与有限秩。
- `Proofs/SpectralAlgebra.lean`、`SpectralProducts.lean`、`SpectralDictionary.lean`：宽度代数、谱坐标与算子范数、复／四元数无穷乘积和零点，以及完整抽象谱字典。DictionaryApplication将其用于原文的Hardy算子。
- `Proofs/LFunctionDomain.lean`：导子GRH与Euler因子保证非本原奇特征的非零性、对数导数解析性及二维核可微性。
- `Proofs/Elementary.lean`、`Asymptotics.lean`：奇异级数的已有项目适配、eventual工具、log函数的可容许性和极限。
- `Proofs/PrimePowers.lean`、`PrimePairs.lean`：忠实于原相关和的坏素数幂质量、显式误差界、计数转换和最终条件推论。
- `Proofs/Main.lean`：原主定理的拼接。解析前置主链已经闭合；剩余的原陈述在`Remaining.lean`中列出。
- `BaseDefinitions.lean`与`Definitions.lean`：171个原定义保持原样。内线L²和边界迹存在性已给出真实证明；Hardy双向表示、闭迹子空间和精确范数均已闭合。

- `Proofs/CharacterSeries.lean`、`CharacterAnalytic.lean`、`CharacterJoint.lean`：完整特征核级数、共轭对称和联合亚纯性。
- `Proofs/Hardy*.lean`：Fourier–Laplace正向表示、真实边界迹、全纯性和精确范数。
- `Proofs/Beta*.lean`：原Beta模型积分、绝对收敛、Gamma恒等式和竖线界。
- `Proofs/Mellin*.lean`、`Quadratic*.lean`：Mellin反演、原矩关系、泛函密度、Riesz表示和完整Prop7.4。
- `Proofs/SpectralCompletion*.lean`、`SpectralPositiveTrace.lean`、`SpectralHilbertSchmidt.lean`：完整谱乘积及对称性、基底无关性和正迹类基础。

## 验证与复现

```sh
lake build
python3 scripts/audit_proofs.py
python3 scripts/check_reviewed_types.py
python3 scripts/check_definitions.py
python3 scripts/write_progress_report.py
python3 scripts/build_progress.py
```

在本目录运行。工具链固定为Lean4.35.0，Mathlib固定为`56a005855ea17e0b0958f73ec801ae140b0a1679`。Lake本地依赖`/home/azureuser/goldbach-lean`，复用其中`LiuSingularSeries`及已安装Mathlib；迁移到其他机器时须在lakefile.toml中调整该项目路径并保留锁定版本。既有两个Goldbach项目的源码未改动。

`scripts/rebuild_remaining.py`会根据当前已经实际实现的原名字重建剩余占位索引。继续并行工作时，先让新模块独立编译，再运行该脚本并整体build，避免同名占位与证明并存。

`reviewed-definitions.json`另外检查171个原定义的实际声明和函数体保持不变；只忽略空白及声明间注释，避免仅靠类型比较漏掉定义被改弱。HTML生成需要Pygments和KaTeX；本机自动复用已装依赖，其他机器可用requirements-review.txt和package.json安装。现成progress.html完全离线，不需要安装这些显示依赖。
`reviewed-types.json`来自Lean内的定义相等检查：把原快照命名空间的常量映射到当前命名空间后，逐一比较102条完整定理类型。它验证没有改动假设、结论与量词；不证明尚未完成的数学内容。

`proof-status.json`中的公理清单由Lean内核环境的`collectAxioms`递归提取。允许的标准基础公理是propext、Classical.choice、Quot.sound；sorryAx单独视为未完成。目前未发现额外的非标准公理。类型保真测试所导入的旧占位只在验证脚本内使用，不由证明工程导入。

## 完成情况

正文及附录A/B的102条原审阅声明全部闭合。附录B.4单独证明了有限C6、宽支集且不对称权的Mellin模型公式，使用原交叉质量积分，而未套用窄支集对称权条件。完整构建、公理依赖、类型/定义保真、离线页面验证见verification.json。
