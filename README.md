# Conditional Goldbach in Lean

Li–Liu 论文的条件式 Goldbach 结论及其分析、算子与谱理论准备的 Lean 4 形式化。主结果保留原文的 **GRH 与谱条件 S/R**；这里没有无条件 Goldbach 或黎曼猜想的证明。

仓库名中的 `conditional` 描述数学内容。源码命名空间 `LiLiuGoldbach16` 沿用原始附件 `LiLiuGoldbach16.tex` 的名称；`16` 不是定理的参数。

## 当前范围

- 原论文 38 个命名结论拆成的 **102 条审阅声明**全部证明闭合；1354 个公共定理/辅助结果的传递依赖均未检出 `sorryAx`。
- 主证明库含 **254 个 Lean 文件、29,629 行**，包含注释和空行，不包含依赖库与审计代码。
- 三个独立子任务重新逐条核对原始 TeX。103 项独立命题的完整类型检查通过；真实 Lean comparator 接受 **218 个目标**，涵盖命题、定义体等式、语义桥梁和905计数证书。改变条件、交换量词、替换定义的三个错误对照均被拒绝。
- `N = 30030` 的 **905 个无序素数对**另有使用 `decide +kernel` 的直接枚举证书。

**尚未完成：**附录 B 中特定积分近似的误差证书、由该误差得到具体整数区间的计算，以及有限谱矩阵的具体数值认证。一般误差传递与谱零点条件定理已证明，但不等于这些数值输入已认证。直接枚举905也不替代原文的积分认证路线。

TeX 到 Lean 参考的含义由独立数学审查核对；comparator 验证参考与实际证明一致、定义未被替换以及证明公理符合要求。它本身不解释 TeX。

## 构建

```bash
git clone https://github.com/subfish-zhou/conditional-goldbach-lean.git
cd conditional-goldbach-lean/formalization
lake update
lake exe cache get
lake build
```

需要安装 Lean 的 `elan` 工具链管理器。`lean-toolchain` 固定 Lean 4.35.0，Lake 清单固定全部依赖版本：

| 依赖 | 固定版本 |
|---|---|
| `goldbach-lean` | `24490c2ab7787238f816d771c9176411dcbda503` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

仓库配置使用 Git 依赖，不要求本机存在某个固定路径的其他工程。详细的模块与证明依赖见 [依赖说明](docs/dependencies.md)。

## 阅读与复核

- [独立审计对照页](formalization/verification/independent-audit/report.html)：中文、公式渲染、Lean 高亮、逐项检查与剩余数值任务。下载后可离线用浏览器打开。
- [完整证明对照页](formalization/progress.html)：当前证明源码和传递公理状态。
- [独立审计机器摘要](formalization/verification/independent-audit/summary.json)、[comparator 日志](formalization/verification/independent-audit/comparator.log)、[逐项最终结果](formalization/verification/independent-audit/final-comparison.json)。
- [905 的直接枚举证明](formalization/verification/independent-audit/appendices/NumericCrossCheck.lean)。
- [原始 TeX](outputs/formalization-preparation/LiLiuGoldbach16.tex)。

复跑独立比较器（Linux，需要 `bubblewrap`）：

```bash
python3 formalization/verification/independent-audit/prepare_comparator.py
python3 formalization/verification/independent-audit/run_comparator.py
```

比较器只允许 `propext`、`Classical.choice` 和 `Quot.sound`。审计 `Challenge` 中的 `sorry` 指定待比较的目标；`Solution` 必须给出真正的证明。`reference/Reviewed.lean` 和 `outputs/formalization-preparation/` 是早期陈述审阅快照，允许保留占位，但不由主证明库导入。

如需重新生成与检查 HTML，在 `formalization` 安装 `requirements-review.txt` 与 `package.json` 中的可选依赖，并运行 `npx playwright install chromium`。这些展示工具不参与 Lean 证明。

## 验证记录

既有证明和独立审计记录按验证时的内容保留，部分记录含原机器的绝对路径。发布时仅调整依赖配置与复现工具，数学 Lean 源码的冻结哈希保持不变。新的构建与依赖记录位于 [publication](formalization/verification/publication/)。

计时记录：在共享的8逻辑CPU主机上，以2个Lean工作线程重新编译本项目、复用依赖缓存，耗时15分56秒；无改动复查4.75秒。原形式化工程创建至已验证包生成的文件时间跨度约5小时25分，不含前期论文拆解和后续审计。
