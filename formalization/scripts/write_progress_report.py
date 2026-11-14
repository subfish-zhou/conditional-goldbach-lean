"""Render both proof-library READMEs from the current axiom ledger."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
status = json.loads((ROOT / 'proof-status.json').read_text())
original = status['original_theorem_counts']
public = status['all_public_theorem_counts']
rows = status['declarations']
closed = [r for r in rows if r['original'] and r['status'] == 'kernel_closed']
pending = [r for r in rows if r['original'] and r['status'] != 'kernel_closed']

parts = [
    '# Conditional Goldbach: proof library', '',
    '[Chinese](README.zh.md) · [Proof explorer](progress.html) · [Axiom ledger](proof-status.json)', '',
    'Lean 4 proofs of the reviewed Li–Liu statements, including the analytic, Hardy-space, operator, and spectral constructions. The main theorems give asymptotics for sufficiently large even integers under GRH and spectral condition S or R, with the original quantifier order and constant dependencies.', '',
    '## Current status', '',
    f'**{original["kernel_closed"]} of 102 reviewed declarations** have complete transitive proof dependencies. '
    f'The ledger records {original["proof_written_dependencies_pending"]} declarations with written proofs and pending dependencies, '
    f'and {original["pending_direct_sorry"]} direct placeholders. '
    f'Across all public theorems and auxiliary results, **{public["kernel_closed"]}** have complete proof dependencies.', '',
    'The 102 reviewed declarations cover the paper\'s 38 named results and their supporting clauses. The review also tracks 171 original definitions.', '',
]
for short in ('theorem_1_1', 'theorem_1_2', 'primePair_consequence'):
    row = next(r for r in rows if r['name'] == 'ConditionalGoldbach.' + short)
    parts.append(f'- `{short}`: `{row["status"]}`.')
parts += [
    '',
    'Remaining numerical work in Appendix B: certify the specified integral approximations and their errors, derive the concrete integer interval from those inputs, and certify the finite spectral matrix numerically. The general error-propagation and spectral-criterion theorems are proved. A separate [direct enumeration certificate](verification/independent-audit/appendices/NumericCrossCheck.lean) establishes 905 unordered prime pairs for 30030.', '',
    '## Build and verify', '',
    'Run from this directory:', '', '```bash',
    'lake update', 'lake exe cache get', 'lake --wfail build',
    'python3 scripts/check_project.py',
    'python3 scripts/check_public_api.py',
    'python3 scripts/check_entrypoints.py',
    'python3 scripts/audit_proofs.py',
    'python3 scripts/check_reviewed_types.py',
    'python3 scripts/check_definitions.py',
    'python3 scripts/write_progress_report.py',
    'python3 scripts/build_progress.py', '```', '',
    'The toolchain is Lean 4.35.0. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`; the `goldbach-lean` Git dependency is pinned in `lakefile.toml` and `lake-manifest.json`. See [dependency details](../docs/dependencies.md).', '',
    'HTML generation uses the optional packages in `requirements-review.txt` and `package.json`. The generated reports work offline.', '',
    'See [choosing an import](../docs/imports.md) for isolated consumers and enforced dependency boundaries.', '',
    'See the [development and public-interface guide](../docs/development.md) for daily checks, the complete release sequence and CI.', '',
    '## Library map', '',
    '| Modules | Content |', '|---|---|',
    '| `Definitions/*.lean` | Reviewed objects split into arithmetic, analytic, Hardy, Hilbert, spectral, and experiment modules |',
    '| `BaseDefinitions.lean`, `Definitions.lean` | Compatibility entry points reexporting the original reviewed definitions |',
    '| `Analysis/L2Fourier.lean` | Mathlib-only Fourier and L² dilation interfaces |',
    '| `Analysis/SpectralData.lean` | Shared Hilbert coordinate and norm identities |',
    '| `Proofs/HardyFourier.lean`, `Proofs/SpectralDataAlgebra.lean` | Compatibility entrypoints for the shared analysis interfaces |',
    '| `Proofs/MellinDoubleDiagonal.lean` | Shared double-Mellin diagonalization and density-factor extraction |',
    '| `Proofs/MellinBetaConvolutionCore.lean` | Shared Beta–Mellin convolution proofs with weight-specific wrappers |',
    '| `Proofs/Weights.lean`, `WeightNorm.lean` | Smooth weights, positive mass, support, convolutions, and norm integrals |',
    '| `Proofs/Characters.lean`, `Character*.lean`, `LFunction*.lean` | Odd-character projection, L-functions, zero expansions, and analytic kernels |',
    '| `Proofs/Beta*.lean`, `Density*.lean` | Beta integrals, meromorphic identities, and singular-density Euler products |',
    '| `Proofs/Hardy*.lean`, `Kernel*.lean` | Fourier–Laplace realization, traces, integral operators, and reproducing kernels |',
    '| `Proofs/Spectral*.lean`, `DictionaryApplication.lean` | Spectral products, trace and determinant identities, zeros, and the spectral dictionary |',
    '| `Proofs/Mellin*.lean`, `Quadratic*.lean` | Inversion, moment identities, Riesz representation, and the exact quadratic identity |',
    '| `Proofs/QuantitativeBounds.lean`, `TotientLogLog.lean` | Uniform operator bounds and singular-series estimates |',
    '| `Proofs/Variable*.lean`, `BalanceBounds.lean`, `PoleObstruction.lean` | Variable strips, boundary balance, and the small-boundary obstruction |',
    '| `Proofs/Wide*.lean`, `FiniteExperimentSpectrum.lean` | Appendix B wide weights, count identities, and finite spectral criteria |',
    '| `Proofs/PrimePowers.lean`, `PrimePairs.lean`, `Main.lean` | Prime-power removal, prime-pair consequence, and main theorem assembly |', '',
    '## Verification evidence', '',
    '- `proof-status.json`: Lean `collectAxioms` follows theorem types and proof values recursively. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.',
    '- `reviewed-types.json`: definitional-equality checks compare all 102 complete theorem types against the statement snapshot, after mapping its namespace.',
    '- `reviewed-definitions.json`: checks the declarations and bodies of the 171 reviewed definitions, ignoring whitespace and comments between declarations.',
    '- `verification/entrypoints.json`: isolated consumer exports, compiled import inventories, and dependency budgets.',
    '- `verification/public-api.json`: all 1621 frozen public declaration types, including binder names, order and implicitness.',
    '- `verification/proof-policy.json`: source reachability and scoped elaboration options.',
    '- `verification.json`: consolidated build and verification records.',
    '- [Independent source audit](verification/independent-audit/report.html): original-TeX review, representation bridges, and comparator results.', '',
    '`reference/Reviewed.lean` preserves the earlier statement-review snapshot. The main library imports the completed proof modules. Audit challenges use placeholders to specify expected targets; their solutions provide the corresponding proofs.', '',
    '## Completed reviewed declarations', '',
]
for row in closed:
    short = row['name'].split('.')[-1]
    parts.append(f'- [{short}]({row["file"]}#L{row["line"]})')
if pending:
    parts += ['', '## Pending reviewed declarations', '']
    for row in pending:
        deps = ', '.join('`' + name.split('.')[-1] + '`' for name in row['pending_local_dependencies'])
        parts.append(f'- [{row["name"].split(".")[-1]}]({row["file"]}#L{row["line"]}): `{row["status"]}`' + (f'; dependencies: {deps}.' if deps else '.'))
(ROOT / 'README.md').write_text('\n'.join(parts) + '\n')
zh = [
    '# Conditional Goldbach：证明工程', '',
    '[English](README.md) · [证明浏览页](progress.zh.html) · [公理台账](proof-status.json)', '',
    f'原审阅的 102 条声明中，{original["kernel_closed"]} 条证明依赖全部闭合，包含正文及附录 A/B。'
    f'公共定理与辅助结果共 {public["kernel_closed"]} 条。主结论在 GRH 和谱条件 S/R 下给出充分大偶数的渐近式，'
    '常数与 h 的量词顺序与原文一致；171 个原定义通过定义体检查。', '',
    '附录 B 的具体积分近似误差、由此推导的整数区间以及有限谱矩阵数值认证仍是独立的数值工作。'
    '一般误差传播与谱条件定理已证明；'
    '[直接枚举证书](verification/independent-audit/appendices/NumericCrossCheck.lean)给出 30030 的 905 个无序素数对。', '',
    '## 构建与验证', '',
    '在本目录运行日常检查：', '', '```bash', 'python3 scripts/check_project.py', '```', '',
    '完整发布检查包含独立 Comparator、三项负向对照、双语页面测试及验证证据的篡改测试：', '',
    '```bash', 'python3 scripts/verify_project.py', 'python3 scripts/render_verified.py',
    'python3 scripts/test_verification.py', 'python3 scripts/package_verified.py', '```', '',
    '工具链固定 Lean 4.35.0；依赖与安装见[依赖说明](../docs/dependencies.zh.md)。'
    '审阅工具用 `python3 -m pip install -r requirements-review.txt`、`npm ci` 和 '
    '`npx playwright install chromium` 安装；现成页面可离线阅读。', '',
    '[开发与公共接口指南](../docs/development.zh.md)说明两类验证的范围、CI 和接口兼容检查。'
    '[按用途选择导入入口](../docs/imports.zh.md)列出独立消费者及其依赖边界。', '',
    '## 验证材料', '',
    '- `proof-status.json`：递归检查定理类型与证明的公理依赖，允许 `propext`、`Classical.choice`、`Quot.sound`。',
    '- `reviewed-types.json`：核对 102 条完整定理类型，包括假设、结论和量词。',
    '- `reviewed-definitions.json`：核对 171 个原定义的声明和函数体。',
    '- `verification/public-api.json`：核对 1621 个旧公共声明的类型，包括参数名、顺序和隐式性。',
    '- `verification/entrypoints.json`：独立导入消费者、实际依赖清单和导入上限。',
    '- `verification/proof-policy.json`：检查所有生产模块可达，编译放宽选项仅允许局部作用。',
    '- `verification.json`：汇总构建与验证记录。',
    '- [独立审计页](verification/independent-audit/report.zh.html)：原始 TeX 审阅、表示桥梁与比较器结果。', '',
    '## 定义与分析层', '',
    '`GeometryCore` 提供不依赖积分模块的基础几何定义；`BoundaryIntegral` 单独提供边界积分。'
    '`Analysis/L2Fourier` 仅依赖 Mathlib，提供 Fourier 与 L² 缩放接口；'
    '`Analysis/SpectralData` 提供 Hilbert 空间谱数据引理。旧模块路径和公共定理名保留。'
    '`reference/Reviewed.lean` 保留早期陈述审阅快照。'
    '完整模块索引及 102 条声明的源码链接见[英文 README](README.md)。', '',
]
(ROOT / 'README.zh.md').write_text('\n'.join(zh))
print({'original': original, 'public': public})
