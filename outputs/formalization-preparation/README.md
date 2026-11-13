# Li–Liu 论文的 Lean 陈述审阅包

先打开 [依赖审阅页](dependency-review.html) 查看整篇依赖关系，再打开 `review.html`：中文数学说明与 Lean 源码左右对照，数学公式和语法高亮均可离线显示。原文主声明默认展开，配套陈述可折叠；每个命名条目和定义族显示本轮审计状态。

本轮审计范围为附件全文的 38 个命名条目、121 个定义族，包含附录 A、B。修订后主模块含 102 个定理声明：38 个原文主标签、60 个配套陈述、4 个辅助声明。所有证明都保留 `by sorry`。本轮已取得用户提供的原始 TeX，并完成逐项复核；页面为全部 38 个命名条目、121 个定义族提供可复制的 TeX 原文和行段。

- `dependency-review.html`、`dependency-graph.json`、`dependency-audit.md`：论文证明依赖、Lean声明引用与沿依赖复核（不是已完成的Lean证明图）；全38命名条目和121定义族，所有证明仍为空。
- `LiLiuGoldbach16.lean`：修订后的实际定义与待审陈述。
- `LiLiuGoldbach16.tex`、`tex-index.json`：用户提供的原始源码及 38 个命名环境、3 个假设环境、233 个标签的索引。
- `tex-audit.md`、`tex-audit.json`：本轮 TeX 复核结果；区分中文展示、依赖接口和真实对象表示义务。
- `tex-cross-check.json`：新增正交、Perron、Poisson、A.1 接口的独立复核。
- `semantic-audit.md`：关键问题、数学编码选择及逐项审计索引。
- `semantic-audit.json`：159 项审计台账，含原文子句、Lean 对应、修正与限制。
- `report.md`、`inventory.json`：完整对象映射、依赖、声明名和当前行号。
- `source-audit.json`：当前 PDF/TeX 来源信息，以及上一轮公开检索的历史记录。
- `cross-check.json`：独立交叉复查。
- `verification.json`、`typecheck.log`：源码哈希及类型检查证据。
- `html-verification.json`：数学渲染、复制下载、筛选、左右布局与离线检查结果。

上一轮修正了 `ContDiff ℝ ⊤` 误表示解析阶、A.2 假设量词过强、联合亚纯性缺项，以及若干积分、谱、迹和无穷乘积的有效性义务。原文 6.5 的三个估计均独立显示，右栏用局部 `P`、`D`、`K` 对应。

## 复现类型检查

在 `/home/azureuser/goldbach-lean` 中运行：

```sh
LEAN_NUM_THREADS=2 lake env lean /home/azureuser/Documents/Codex/2026-11-13/files-mentioned-by-the-user-liliugoldbach16/outputs/formalization-preparation/LiLiuGoldbach16.lean
```

Lean 4.35.0；Mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。已检查的合并稿与交付文件逐字节相同，退出码 0，102 条预期 `sorry` 警告。两个现有 Goldbach 项目保持只读。主模块还直接依赖主项目的 `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries`，不能当成任意版本的纯 Mathlib 文件。

## 审阅边界

逐项审计与类型检查均不构成数学等价性或无遗漏的形式证明。共同整分母编码联合亚纯性、加权 L² 与 Hardy 空间的对应、自然数索引谱、专用正迹类 Fredholm 行列式等选择仍需用户审阅，台账已标明。对象的存在性、选择无关性、收敛性以及论文结论本身均未填证明。

原始 TeX 复核修正中文 V/Ψ、η/W/f 与 C_{N,γ} 符号，补充 A.1 可变边界算子的实际核表示、边界 L²、可积性和谱数据存在义务，以及奇特征正交、Perron 留数、Poisson 零参数恒等作用的支持接口。现有源码含 171 个定义声明，归入 121 个定义族。证明局部绑定的范围见 TeX 审计台账，未把每个局部符号都扩成全局接口。

依赖审计修订 9 新增 `theorem_6_1_abstract_dictionary`，归入 Theorem 6.1 的折叠配套声明，补齐附录 A 的可变条带复用。它是从原证明抽出的未证明泛化接口。当前计数为 **102 / 60 / 171**（总定理 / 配套陈述 / 定义声明），完整数学覆盖仍为 **38 + 121**。历史审计哈希保留在各历史记录中，当前源码与日志哈希以 `verification.json` 为准。

依赖图共含146个论文节点、236条工作依赖边，以及273个Lean声明、987条精确声明引用；原文逐条审核记录为189条。最终结果清单区分17项核心、结构性／附录和数值／说明性内容。当前图数据、审计报告和页面验证记录分别见 `dependency-graph.json`、`dependency-audit.json`、`dependency-verification.json`、`dependency-html-verification.json`；抽象字典独立复核见 `abstract-bridge-cross-check.json`。
