"""Render the English proof-library README from the current axiom ledger."""
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
    'lake update', 'lake exe cache get', 'lake build',
    'python3 scripts/audit_proofs.py',
    'python3 scripts/check_reviewed_types.py',
    'python3 scripts/check_definitions.py',
    'python3 scripts/write_progress_report.py',
    'python3 scripts/build_progress.py', '```', '',
    'The toolchain is Lean 4.35.0. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`; the `goldbach-lean` Git dependency is pinned in `lakefile.toml` and `lake-manifest.json`. See [dependency details](../docs/dependencies.md).', '',
    'HTML generation uses the optional packages in `requirements-review.txt` and `package.json`. The generated reports work offline.', '',
    '## Library map', '',
    '| Modules | Content |', '|---|---|',
    '| `BaseDefinitions.lean`, `Definitions.lean` | Reviewed objects, interior-line L², and boundary-trace existence |',
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
print({'original': original, 'public': public})
