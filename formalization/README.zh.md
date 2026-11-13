# Conditional Goldbach：证明工程

[English](README.md) · [证明浏览页](progress.html) · [公理台账](proof-status.json)

原审阅的102条声明全部证明闭合，包含正文及附录A/B。公共定理与辅助结果共1354条。主结论在GRH和谱条件S/R下给出充分大偶数的渐近式，常数与h的量词顺序与原文一致；171个原定义通过定义体检查。

`theorem_1_1`、`theorem_1_2` 和 `primePair_consequence` 的传递证明依赖均已闭合。

附录B待完成特定积分近似的误差认证、具体整数区间的推导，以及有限谱矩阵的数值认证。一般误差传播与谱条件定理已证明；[直接枚举证书](verification/independent-audit/appendices/NumericCrossCheck.lean)给出30030的905个无序素数对。

## 构建与验证

在本目录运行：

```bash
lake update
lake exe cache get
lake build
python3 scripts/audit_proofs.py
python3 scripts/check_reviewed_types.py
python3 scripts/check_definitions.py
python3 scripts/write_progress_report.py
python3 scripts/build_progress.py
```

工具链固定Lean 4.35.0。Lake使用固定提交的Git依赖，详见[依赖说明](../docs/dependencies.zh.md)。HTML生成所需可选依赖列于 `requirements-review.txt` 和 `package.json`；现成页面可离线阅读。

## 验证材料

- `proof-status.json`：Lean递归提取类型与证明中的公理依赖，允许 `propext`、`Classical.choice`、`Quot.sound`。
- `reviewed-types.json`：映射参考命名空间后，核对102条完整定理类型，包括假设、结论和量词。
- `reviewed-definitions.json`：核对171个原定义的声明和函数体。
- `verification.json`：汇总构建与验证记录。
- [独立审计页](verification/independent-audit/report.html)：原始TeX审阅、表示桥梁与比较器结果。

`reference/Reviewed.lean` 保存早期陈述审阅快照。当前主库导入完成的证明模块。完整模块索引及102条声明的源码链接见[英文README](README.md)。
