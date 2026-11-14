# Conditional Goldbach：证明工程

[English](README.md) · [证明浏览页](progress.zh.html) · [公理台账](proof-status.json)

原审阅的 102 条声明中，102 条证明依赖全部闭合，包含正文及附录 A/B。公共定理与辅助结果共 1400 条。主结论在 GRH 和谱条件 S/R 下给出充分大偶数的渐近式，常数与 h 的量词顺序与原文一致；171 个原定义通过定义体检查。

附录 B 的具体积分近似误差、由此推导的整数区间以及有限谱矩阵数值认证仍是独立的数值工作。一般误差传播与谱条件定理已证明；[直接枚举证书](verification/independent-audit/appendices/NumericCrossCheck.lean)给出 30030 的 905 个无序素数对。

## 构建与验证

在本目录运行日常检查：

```bash
python3 scripts/check_project.py
```

完整发布检查包含独立 Comparator、三项负向对照、双语页面测试及验证证据的篡改测试：

```bash
python3 scripts/verify_project.py
python3 scripts/render_verified.py
python3 scripts/test_verification.py
python3 scripts/package_verified.py
```

工具链固定 Lean 4.35.0；依赖与安装见[依赖说明](../docs/dependencies.zh.md)。审阅工具用 `python3 -m pip install -r requirements-review.txt`、`npm ci` 和 `npx playwright install chromium` 安装；现成页面可离线阅读。

[开发与公共接口指南](../docs/development.zh.md)说明两类验证的范围、CI 和接口兼容检查。[按用途选择导入入口](../docs/imports.zh.md)列出独立消费者及其依赖边界。

## 验证材料

- `proof-status.json`：递归检查定理类型与证明的公理依赖，允许 `propext`、`Classical.choice`、`Quot.sound`。
- `reviewed-types.json`：核对 102 条完整定理类型，包括假设、结论和量词。
- `reviewed-definitions.json`：核对 171 个原定义的声明和函数体。
- `verification/public-api.json`：核对 1621 个旧公共声明的类型，包括参数名、顺序和隐式性。
- `verification/entrypoints.json`：独立导入消费者、实际依赖清单和导入上限。
- `verification/proof-policy.json`：检查所有生产模块可达，编译放宽选项仅允许局部作用。
- `verification.json`：汇总构建与验证记录。
- [独立审计页](verification/independent-audit/report.zh.html)：原始 TeX 审阅、表示桥梁与比较器结果。

## 定义与分析层

`GeometryCore` 提供不依赖积分模块的基础几何定义；`BoundaryIntegral` 单独提供边界积分。`Analysis/L2Fourier` 仅依赖 Mathlib，提供 Fourier 与 L² 缩放接口；`Analysis/SpectralData` 提供 Hilbert 空间谱数据引理。旧模块路径和公共定理名保留。`reference/Reviewed.lean` 保留早期陈述审阅快照。完整模块索引及 102 条声明的源码链接见[英文 README](README.md)。
