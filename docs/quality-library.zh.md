# 可复用库接口与质量改造

[English](quality-library.md) · [中文](quality-library.zh.md) · [JSON](quality-library.json)

基线为 `cb16bfc`。本轮完成四处证明热点优化、编译选项清理、分层验证与 CI、离线审阅页压缩、基础导入拆分和可复用分析接口。原有数学定义与定理接口经检查保持一致。

## 源码与依赖

| 指标 | 改造前 | 改造后 |
|---|---:|---:|
| 主库 Lean 文件 | 271 | 275 |
| 含注释与空行的行数 | 30,774 | 30,739 |
| 去注释、空行后的行数 | 27,535 | 27,455 |
| 再去除模块、导入与公开区段行 | 26,335 | 26,241 |
| 文件级编译放宽选项 | 140 | 0 |
| 局部编译放宽选项 | 1 | 0 |
| 公开 tactic 导入 | 26 | 0 |

行数只统计主库，不含依赖、审计副本、工具和 HTML。去注释统计使用支持嵌套注释及字符串的 Lean 词法扫描。80 行净减少主要来自编译选项清理，不能视为数学证明压缩量。

| 导入入口 | 总模块 | 本地 | Mathlib | goldbach 数学模块 |
|---|---:|---:|---:|---:|
| `ConditionalGoldbach` | 6,807 | 275 | 3,801 | 57 |
| `ConditionalGoldbach.Definitions` | 5,472 | 23 | 3,510 | 3 |
| `ConditionalGoldbach.Proofs.Main` | 6,442 | 142 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.PrimePairs` | 6,445 | 145 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.FiniteExperimentSpectrum` | 5,513 | 36 | 3,538 | 3 |
| `ConditionalGoldbach.Definitions.GeometryCore` | 3,577 | 1 | 1,696 | 0 |
| `ConditionalGoldbach.Analysis.L2Fourier` | 4,876 | 1 | 2,939 | 0 |
| `ConditionalGoldbach.Analysis.SpectralData` | 4,136 | 2 | 2,198 | 0 |

整库导入从 6,803 增至 6,807，新增四项均为本地模块。Mathlib 的 3,801 个模块和 goldbach 的 57 个数学模块保持不变；所有依赖固定版本也保持不变。八个独立消费者均通过公开声明、实际导入集合和预算检查，两个分析接口还有使用示例。

## 证明热点

| 定理 | 原 heartbeat | 当前 heartbeat | 减少 |
|---|---:|---:|---:|
| `pole_spectral_obstruction` | 57,987 | 6,204 | 89.3% |
| `LFunction_sub_one_norm_bound` | 53,884 | 2,935 | 94.6% |
| `logDerivative_uniform_bound` | 55,638 | 18,387 | 67.0% |
| `spectralQuaternion_reindexed_compactUniformLimit` | 49,880 | 1,595 | 96.8% |

同机、相同 Lean 与依赖版本、两线程，按定理交替运行改造前后的源码探针。每条定理仅包裹 `#count_heartbeats in`；该计数器会关闭其自身的 heartbeat 限制，因此默认限制下能否构建由另外的 `lake --wfail build` 验证。该完整构建通过，主库无 warning 或 tactic 建议提示；依赖库仍有两条既有 `ring` 信息提示。JSON 保存源码哈希、日志及探针耗时。本轮没有重测空本地产物的全量构建时间。

## 验证与复用

已有编译缓存下，日常七项检查合计 **92.48 秒**；本次完整发布验证的构建、审计和汇总步骤合计 **585.10 秒**，包含独立 Comparator，不含页面生成和打包。两者检查范围不同。日常输出单独保存，原发布记录的哈希逐个确认未变。

完整证据未改变时，`check_project.py --reuse-release` 本次耗时 1.04 秒。主 Comparator 共 384.96 秒，其中内核重验 236.12 秒、两端导出 84.08 秒；沙箱阶段之外的比较、协调等共 59.69 秒。完整重验保留在发布流程中。

全部 102 条原审阅定理、171 个定义体、1,621 个既有公共源码声明接口和 103 条独立完整类型检查通过；Comparator 接受 218 个目标，拒绝三项条件、量词、定义被故意改动的对照。公理审计覆盖 2,974 个本地编译常量，公共定理及辅助结果为 1,400 条。仅允许 `propext`、`Classical.choice`、`Quot.sound`。新增导出主要来自共享分析接口与兼容包装。

接口指纹保留显式参数名、顺序和隐式性，统一 universe 参数名，并去除元数据及匿名参数的编译器卫生作用域。基线指纹来自原提交的独立编译环境。旧导入路径和声明名保留；证明所用 tactic 改为私有导入，下游应显式导入所需 tactic。

`Analysis.L2Fourier` 仅依赖 Mathlib，供 Hardy 内部限制与边界证明共用；`Analysis.SpectralData` 供谱代数与迹证明共用。`GeometryCore` 与 `BoundaryIntegral` 分离，旧 `Geometry` 兼容导出两者。

CI 在 PR 上运行日常检查，在 main 推送和手动触发时运行完整验证、双语浏览器测试、篡改回归和打包。Actions 固定到提交，验证工具和结果也纳入证据哈希；旧证据的复用需要所有绑定输入保持一致。沙箱子进程分阶段计时，保留原有隔离和父进程退出语义。

## 离线审阅页

| 语言 | 原 HTML | 当前 HTML |
|---|---:|---:|
| en | 25.67 MiB | 6.24 MiB |
| zh | 25.71 MiB | 6.26 MiB |

完整源码仅保存一份，以 UTF-16 token 区间重建语法高亮，共享数学说明；首屏仅创建 102 个审阅定理的 DOM。全部 1,638 个声明仍可搜索查看。中英文测试核对逐字源码、公式、深链接、离线无网络和 390 px 移动端；中文标题中的公式也已渲染，快速切换范围不会留下失效的高亮计时器。

[开发与接口指南](development.zh.md) · [导入指南](imports.zh.md) · [当前验证记录](../formalization/verification.json)
