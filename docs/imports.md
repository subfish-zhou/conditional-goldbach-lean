# Choosing an import

[中文](imports.zh.md)

Use one of these existing entrypoints according to the results your file needs.
They preserve the same definitions and theorem statements as the complete library.

| Import | Public results | Boundary checked |
|---|---|---|
| `ConditionalGoldbach.Proofs.Main` | Theorems 1.1, 1.2, and the uniform form of 7.1 | Excludes the prime-pair consequence, finite-spectrum experiment, and totient/log-log proof |
| `ConditionalGoldbach.Proofs.PrimePairs` | Main theorems and `primePair_consequence` | Excludes the finite-spectrum experiment and totient/log-log proof |
| `ConditionalGoldbach.Proofs.FiniteExperimentSpectrum` | `proposition_B_5` and the finite spectrum | Excludes the main-theorem, prime-pair, and totient/log-log proof modules |
| `ConditionalGoldbach.Definitions` | Reviewed definitions, including `IsWeight`, `HypothesisS`, and `HypothesisR` | Allows only the four existing Hardy foundation proof modules needed by the definitions |
| `ConditionalGoldbach.Definitions.GeometryCore` | Strip geometry and scale parameters | Excludes integration and all paper proof modules |
| `ConditionalGoldbach.Analysis.L2Fourier` | Classical/L² Fourier compatibility, dilation, physical normalization | Mathlib only; excludes paper definitions and proofs |
| `ConditionalGoldbach.Analysis.SpectralData` | Diagonal Hilbert coordinate and norm identities | Excludes Hardy constructions and arithmetic proof dependencies |
| `ConditionalGoldbach` | Complete paper library | Checks all four principal result exports and the full import budget |

For example:

```lean
import ConditionalGoldbach.Proofs.Main

#check @ConditionalGoldbach.theorem_1_1
#check @ConditionalGoldbach.theorem_1_2
```

The definition entrypoint includes `HardyWeights`, `HardyFourier`, `HardyInterior`,
and `HardyBoundary`: these support the realized Hardy-space objects. For a more
specific definition, import its module under `ConditionalGoldbach.Definitions`.

Run the consumer checks from `formalization/` after building:

```bash
lake --wfail build
python3 scripts/check_entrypoints.py
```

`verify_project.py` also runs this check. Each consumer imports exactly one entry,
checks the advertised declarations with Lean, and records Lean's actual imported
module inventory, including the implicit `Init` prelude. `scripts/entrypoints.json` defines forbidden dependencies,
the definition entrypoint's proof-module allowlist, and maximum counts for local,
Mathlib, goldbach mathematical, and total modules. Changes to these budgets should
accompany an explanation of the new dependency. They are independent of timing
noise. The result in `verification/entrypoints.json` records the source hashes,
dependency revisions, policy hash, and complete inventories.

Narrow imports reduce what downstream consumers load. Building the complete paper
still checks every production module. See the [refactor measurements](quality-library.md)
for the measured import sizes and proof costs.

The [public-interface guide](development.md) includes a standalone L² consumer and the frozen API contract. Proof-only tactic modules are private imports; import any tactics used by downstream proofs explicitly.
