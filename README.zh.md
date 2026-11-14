# Conditional Goldbach in Lean

[English](README.md)

Li–Liu 论文条件 Goldbach 结论及其分析、算子和谱理论基础的 Lean 4 形式化。主定理在 **GRH 与谱条件 S/R** 下给出充分大偶数的渐近式，保留原文的常数依赖和量词顺序。

## 当前结果

- 覆盖38个命名结论的 **102条审阅声明**全部证明闭合；传递公理检查覆盖 **1386个公共定理及辅助结果**。
- 主库含271个Lean文件、30,774行，包括注释和空行。
- 独立审阅直接核对原始TeX；103个独立命题通过完整类型检查，比较器接受218个目标，三个故意改动的对照均被拒绝。
- 直接枚举证书使用 `decide +kernel` 证明30030有 **905个无序素数对表示**。

附录B剩余数值工作：特定积分近似的误差证书、由这些输入推出具体整数区间、有限谱矩阵的数值认证。一般误差传播和谱判据已证明；直接枚举与积分认证分别记录。

[本轮改造与性能对比](docs/quality-convolution.zh.md)列出了源码规模、导入闭包和编译、证明耗时。

## 构建

```bash
git clone https://github.com/subfish-zhou/conditional-goldbach-lean.git
cd conditional-goldbach-lean/formalization
lake update
lake exe cache get
lake --wfail build
```

主库使用 Lean 模块系统，公开定义可展开。未使用的证明形参以 `_` 开头。按名字传参时用新拼写，例如 `lemma_3_1_odd_orthogonality` 的 `_hN`。

先安装Lean工具链管理器 `elan`。工具链固定Lean 4.35.0；Git依赖 `goldbach-lean` 固定为 `24490c2ab7787238f816d771c9176411dcbda503`，Mathlib固定为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

[按用途选择导入入口](docs/imports.zh.md)说明主定理、素数对、定义及有限谱消费者的用法与自动检查边界。

## 阅读和验证

- [证明工程](formalization/README.zh.md)与[证明浏览页](formalization/progress.html)。
- [独立审计页](formalization/verification/independent-audit/report.html)、[比较结果](formalization/verification/independent-audit/final-comparison.json)。
- [声明级依赖说明](docs/dependencies.zh.md)。
- [905枚举证书](formalization/verification/independent-audit/appendices/NumericCrossCheck.lean)。
- [原始TeX](outputs/formalization-preparation/conditional-goldbach.tex)与[历史陈述审阅快照](outputs/formalization-preparation/README.md)。

在仓库根目录运行 `python3 formalization/scripts/verify_project.py`，可重新构建并生成完整审计记录。脚本会检查 Lake 依赖是否处在固定版本，记录源码、比较配置和输出的哈希。已有当前构建记录时，也可在 Linux 下用 `bubblewrap` 单独复跑比较器。

```bash
python3 formalization/verification/independent-audit/prepare_comparator.py
python3 formalization/verification/independent-audit/run_comparator.py
python3 formalization/scripts/refresh_audit_summary.py
```

允许公理为 `propext`、`Classical.choice`、`Quot.sound`。数学审阅建立TeX与独立参考的对应，比较器核查参考和实际证明的类型、定义体及公理。审计Challenge的占位指定比较目标，Solution提供证明；主库导入完成的证明模块。

[发布验证目录](formalization/verification/publication/)保存构建和依赖证据。历史记录标注各次检查的测量及哈希，后续源码重命名和文档修改由Git记录。
