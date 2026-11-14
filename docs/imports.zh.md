# 按用途选择导入入口

[English](imports.md)

根据需要使用以下已有入口；定义和定理陈述与完整主库一致。

| 导入模块 | 可用结果 | 自动检查的边界 |
|---|---|---|
| `ConditionalGoldbach.Proofs.Main` | 定理 1.1、1.2、7.1 的一致估计 | 不加载素数对推论、有限谱实验和 totient/log-log 证明 |
| `ConditionalGoldbach.Proofs.PrimePairs` | 主定理及 `primePair_consequence` | 不加载有限谱实验和 totient/log-log 证明 |
| `ConditionalGoldbach.Proofs.FiniteExperimentSpectrum` | `proposition_B_5` 及有限谱 | 不加载主定理、素数对推论和 totient/log-log 证明模块 |
| `ConditionalGoldbach.Definitions` | 审阅定义，包括 `IsWeight`、`HypothesisS`、`HypothesisR` | 只允许定义所需的四个既有 Hardy 基础证明模块 |
| `ConditionalGoldbach.Definitions.GeometryCore` | 条带几何与尺度参数 | 不加载积分及论文证明模块 |
| `ConditionalGoldbach.Analysis.L2Fourier` | 经典/L² Fourier、缩放与物理归一化 | 只依赖 Mathlib，不加载论文定义与证明 |
| `ConditionalGoldbach.Analysis.SpectralData` | 对角 Hilbert 坐标和范数关系 | 不加载 Hardy 构造与算术证明 |
| `ConditionalGoldbach` | 整篇论文的主库 | 检查四个主要结果的导出和完整导入规模上限 |

例如：

```lean
import ConditionalGoldbach.Proofs.Main

#check @ConditionalGoldbach.theorem_1_1
#check @ConditionalGoldbach.theorem_1_2
```

定义总入口包含 `HardyWeights`、`HardyFourier`、`HardyInterior` 和 `HardyBoundary`，
用于构造实际的 Hardy 空间对象。只需要某个主题的定义时，还可以直接导入
`ConditionalGoldbach.Definitions` 下对应模块。

在 `formalization/` 下构建后运行：

```bash
lake --wfail build
python3 scripts/check_entrypoints.py
```

`verify_project.py` 也会运行此检查。每个独立消费者只导入一个入口，由 Lean 检查公开声明是否可用，
并记录实际加载的模块，包括隐式的 `Init` 前导库。`scripts/entrypoints.json` 规定禁止依赖、定义入口允许的证明模块，以及本地、
Mathlib、goldbach 数学模块和总模块数的上限。修改上限时应说明新增依赖的理由；这些检查不受计时波动影响。
`verification/entrypoints.json` 保存源码哈希、依赖版本、检查策略哈希及完整模块列表。

较窄的导入可减少下游加载量；整篇论文的完整构建仍检查所有主库模块。
实测导入规模和证明耗时见[本轮改造报告](quality-library.zh.md)。

[公开接口约定](development.zh.md)包括独立 L² 消费者示例。仅供证明使用的 tactic 导入为私有，下游应显式导入所需 tactic。
