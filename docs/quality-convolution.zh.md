# 卷积证明、编译热点和导入入口改造

[English](quality-convolution.md) · [JSON](quality-convolution.json)

本轮将主文和附录 B 的 Beta–Mellin 卷积推导集中到 `MellinBetaConvolutionCore`。旧定理名称、参数及完整类型保留；两种权函数条件分别提供可测性、收敛性、竖线可积性和核配对公式。主文外层配对允许任意实部，附录版本保留正实部条件。

Poisson 零点重排显式指定 `Equiv.summable_iff (f := q)`，消除被求和函数的高阶统一热点。平均估计的四次 `nlinarith` 改为只使用当前代数步骤需要的假设。

| 源码规模 | 改造前 | 改造后 |
|---|---:|---:|
| Lean 文件 | 270 | 271 |
| 物理行数 | 30,755 | 30,774 |
| 非空行数 | 28,007 | 28,015 |

保留旧接口的完整陈述及显式分析条件会增加少量行数；共享的是证明体。物理行数包含注释与空行，不含依赖和审计代码。

| 文件独立编译中位数 | 改造前（秒） | 改造后（秒） |
|---|---:|---:|
| `CharacterPoissonAnchor` | 13.33 | 7.95 |
| `CharacterAverageAssembly` | 12.05 | 7.55 |
| `MellinBetaConvolution` | 5.98 | 3.69 |
| `FiniteModelBetaConvolution` | 5.10 | 3.45 |
| `MellinBetaConvolutionCore` | — | 3.74 |

新公共文件也需要编译，其耗时单列；不能把两个入口文件的加速当作整段卷积证明的总加速。各文件测三次，导入使用同一最终编译环境，`LEAN_NUM_THREADS=2`。共享主机可能有其他负载。本轮没有重新测量整库清缓存构建。

| 单个热点定理 heartbeats | 原证明 | 优化后 |
|---|---:|---:|
| `CharacterPoissonAnchor` | 121,226 | 6,641 |
| `CharacterAverageAssembly` | 99,731 | 13,350 |

使用 `#count_heartbeats in` 分别测量 `primitive_poisson_anchor_bound` 和 `lemma_6_4_of_reference_and_comparison`；同一组最终导入下比较原证明和新证明。JSON 包含探针源码和原始输出。

| 入口 | 总模块 | 本地模块 | Mathlib | goldbach 数学模块 |
|---|---:|---:|---:|---:|
| `ConditionalGoldbach` | 6,803 | 271 | 3,801 | 57 |
| `ConditionalGoldbach.Definitions` | 5,469 | 20 | 3,510 | 3 |
| `ConditionalGoldbach.Proofs.Main` | 6,441 | 141 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.PrimePairs` | 6,444 | 144 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.FiniteExperimentSpectrum` | 5,512 | 35 | 3,538 | 3 |

新增公共模块使整库导入由 6,802 增至 6,803；Mathlib 仍为 3,801，goldbach 数学模块仍为同一组 57 个。本表统计实际加载模块，包含隐式 Init；定义与有限谱入口各比显式源码扫描多 151 个 Init 模块。五个入口分别编译独立消费者。禁止依赖、定义入口的证明模块允许列表及模块数上限已接入 `verify_project.py`；详见[导入说明](imports.zh.md)。


本轮额外比较了四个修改模块原有的 29 条声明完整类型，全部保持不变。常规定义、完整类型、公理审计及独立 Comparator 的结果见[当前验证记录](../formalization/verification.json)。

[Baseline sources](quality-convolution-baseline.tar.gz) · [Previous refactor](quality-refactor.md)
