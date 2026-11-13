# Mathlib 以外的实际依赖

本项目在 Lake 配置中额外固定一个数学工程：[`subfish-zhou/goldbach-lean`](https://github.com/subfish-zhou/goldbach-lean/tree/24490c2ab7787238f816d771c9176411dcbda503)。该仓库也包含 Chen 与 Li–Liu 1+1.9 的形式化，但本项目没有导入那些结论或其数值证书模块，也不依赖独立的三素数定理工程。

这里必须区分三种口径：包依赖、编译时导入的模块、证明表达式实际引用的声明。我们同时遍历了源码导入图与 Lean 环境的声明类型/证明值闭包，二者的模块清单完全一致。

## 编译时加载

本项目直接导入4个非Mathlib数学模块：

| 模块 | 用途 | 本项目导入处 |
|---|---|---|
| `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries` | 奇异级数的定义、正性和欧拉积基础 | `BaseDefinitions.lean` |
| `MathlibNt.SieveTheory.Arithmetic.MertensTheorem` | Mertens乘积估计，进而控制 `N / φ(N)` | `Proofs/TotientLogLog.lean` |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries` | Dirichlet L函数级数及周期抵消估计 | `Proofs/CharacterGrowthFoundation.lean` |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds` | 右半平面增长界 | 同上 |

传递导入后，`goldbach-lean` 中共有 **57个模块、22,284物理行**进入环境；去除空行与注释后为16,684行。这里包含一些通过总入口导入、但最终证明未用到的内容：

| 包内目录 | 导入模块数 | 来源与角色 |
|---|---:|---|
| `MathlibNt` | 10 | 共享数论基础；不等于调用Chen或1+1.9定理 |
| `AnalyticNumberTheory` | 33 | 来源包括 `UyNewNas/analytic-number-theory-lean` 及后续开发 |
| `PrimeNumberTheoremAnd` | 14 | `AlexKontorovich/PrimeNumberTheoremAnd` 的适配闭包，提供素数定理基础 |

上述目录均已打包在同一个固定提交的 `goldbach-lean` 中，不是三个独立的 Lake 下载依赖。原库的来源记录见 [`docs/PROVENANCE.md`](https://github.com/subfish-zhou/goldbach-lean/blob/24490c2ab7787238f816d771c9176411dcbda503/docs/PROVENANCE.md)。PNT移植来源记录的上游提交为 `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`。

此外，PNT源码传递导入了 **LeanArchitect的9个工具模块**。它用于蓝图/声明标记，不是额外的Goldbach数学定理。Lean、Mathlib及其常规工具包没有混入上述57模块的统计。

## 证明真正使用

下表按 Lean 中实际声明的类型和证明值递归追踪；声明数含辅助声明、生成声明与私有声明，不能直接理解为“借用了多少条命名数学定理”。

| 检查范围 | 实际使用的外部数学模块 | 外部声明数 |
|---|---:|---:|
| `theorem_1_1` | 5 | 68 |
| `theorem_1_2` | 5 | 68 |
| `primePair_consequence` | 5 | 72 |
| 原102条审阅声明的合并闭包 | 22 | 839 |
| 整个公共证明库的合并闭包 | 22 | 839 |

三个主结果实际使用的5个模块是：

```text
MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative
```

它们提供奇异级数、Dirichlet L函数、特征周期和与Abel求和分析。三个主结果均未使用Mertens/素数定理链。

原102条审阅声明中，只有 **`lemma_4_3_uniform`** 的依赖闭包使用Mertens与 `MediumPNT`，用于 `N/φ(N) ≪ log log N` 的统一界。**素数定理是关于素数分布的结果，不是三素数定理。**

因此，本项目复用了现有Goldbach工程的基础设施，但没有以1+1.9、Chen或三素数结论作为证明前提。公理审计仍仅出现 `propext`、`Classical.choice`、`Quot.sound`。

## 可核查证据

- [完整模块导入图与来源](../formalization/verification/publication/dependencies-imports.json)
- [声明级计数](../formalization/verification/publication/declaration-audit/summary.json)
- [839条实际外部声明清单](../formalization/verification/publication/declaration-audit/reviewed_102-external-declarations.tsv)
- [逐声明引用路径与详细解释](../formalization/verification/publication/declaration-audit/report.md)

这些材料对应固定提交与已记录的源码哈希。原审计中的本机路径是取证记录；当前构建配置使用可下载的Git依赖。

在完成主库构建后，可在 `formalization` 目录复跑：

```bash
lake env lean verification/publication/declaration-audit/DeclarationAudit.lean
python3 verification/publication/declaration-audit/analyze.py
python3 verification/publication/audit_imports.py
```

完整声明图约95 MB，可由上述命令生成；仓库保留紧凑结果与引用路径，不提交这份可再生的大文件。
