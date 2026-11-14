# 本轮质量改造与性能对比

[English](quality-refactor.md) · [JSON](quality-refactor.json)

定义按 14 个数学主题拆分；纯 Hilbert 空间的谱数据引理单独放入 `SpectralDataAlgebra`；主文和附录 B 共用 `MellinDoubleDiagonal`。两个旧定义入口继续公开导出原来的对象。

Hilbert–Schmidt 基无关性及相关重排证明显式指定 `Equiv.summable_iff` 的被求和函数，避免在 `Summable` 的展开式中进行高阶统一。主文与附录的权函数假设、可积性证明及质量项分别保留。

| 规模 | 改造前 | 改造后 |
|---|---:|---:|
| 主库 Lean 文件 | 254 | 270 |
| 主库物理行数 | 30,678 | 30,755 |
| 主库非空行数 | 27,990 | 28,007 |

| 导入闭包 | 改造前 | 改造后 |
|---|---:|---:|
| `ConditionalGoldbach` | 6,914 | 6,802 |
| `Definitions` | 5,552 | 5,318 |
| `Proofs.HardyBoundary` | 5,300 | 4,730 |
| `Proofs.SpectralCompletionTrace` | 5,554 | 3,986 |
| `Proofs.MellinModelDouble` | 5,593 | 5,365 |
| `Proofs.FiniteModelDouble` | 5,609 | 5,375 |
| 总入口中的 Mathlib 模块 | 3,929 | 3,801 |

Hardy 边界和 Hilbert–Schmidt 迹模块的闭包均不含 `goldbach-lean` 数学模块；完整项目仍使用该固定版本的 57 个数学模块。行数包含注释与空行，不含依赖、审计副本及生成页面。新增模块的导入、命名空间和说明计入总长。

| 计时工作负载 | 改造前（秒） | 改造后（秒） |
|---|---:|---:|
| 总入口加载 | 3.90 | 3.86 |
| 定义总入口加载 | 3.42 | 3.23 |
| Hardy 边界模块加载 | 3.29 | 2.96 |
| Hilbert–Schmidt 迹证明文件 | 9.39 | 2.60 |
| 主文双重 Mellin 文件 | 3.36 | 2.69 |
| 附录 B 双重 Mellin 文件 | 3.23 | 2.69 |
| 主库全量重编译 | 469.20 | 374.90 |

前六行各测三次，取墙钟时间中位数。全量重编译各测一次，仅清除本项目编译 trace，保留依赖缓存；两边均使用 `LEAN_NUM_THREADS=2` 和 `lake --wfail build`。共享主机上的其他构建可能影响墙钟时间。Comparator、报告、下载不计入构建时间。

| 同一导入环境下的证明 heartbeats | 原证明 | 优化后 |
|---|---:|---:|
| `SpectralCompletionTrace` | 77,906 | 1,704 |
| `SpectralHilbertSchmidt` | 82,974 | 6,720 |
| `SpectralRankOneSeries` | 5,598 | 5,594 |

逐个定理使用 `#count_heartbeats in`，分别测量基无关性、伴随算子的双重 Parseval、秩一展开的迹公式。原证明与优化证明均使用最终版本的同一组导入，因此这一项能单独观察证明改写的效果。

验证保留了 171 个原始定义体及 102 个审阅定理的完整类型。103 条独立陈述的完整类型检查、218 项 Lean Comparator 检验及三类故意改坏的对照均通过。详见[当前验证记录](../formalization/verification.json)。

[Baseline sources](quality-baseline.tar.gz) · [Raw measurements and source hashes](quality-refactor.json)
