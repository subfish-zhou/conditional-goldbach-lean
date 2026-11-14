# Mathematical dependencies

[Chinese](dependencies.zh.md)

The project pins [`subfish-zhou/goldbach-lean`](https://github.com/subfish-zhou/goldbach-lean/tree/24490c2ab7787238f816d771c9176411dcbda503) for singular-series and analytic-number-theory foundations. The audit records package dependencies, imported modules, and declarations reached through actual proof terms separately.

## Imported modules

The `ConditionalGoldbach` entry point loads 6,803 modules, including 3,801 from Mathlib. The source scan and Lean's compiled import graph agree on the current closure.

Before the definition split, these counts were 6,914 and 3,929. The Hardy boundary and pure Hilbert–Schmidt trace closures now have no `goldbach-lean` number-theory dependencies. The full project retains the external mathematical dependencies listed below. See the [refactor measurements](quality-convolution.md) for timings, the baseline source snapshot, and measurement details.

Four mathematical modules are imported directly in addition to Mathlib:

| Module | Purpose | Local importer |
|---|---|---|
| `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries` | Singular series, positivity, and Euler products | `Definitions/Arithmetic.lean` |
| `MathlibNt.SieveTheory.Arithmetic.MertensTheorem` | Mertens product estimate and bounds for `N / φ(N)` | `Proofs/TotientLogLog.lean` |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries` | Dirichlet L-series and periodic cancellation estimates | `Proofs/CharacterGrowthFoundation.lean` |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds` | Growth bounds in the right half-plane | `Proofs/CharacterGrowthFoundation.lean` |

The transitive import closure includes **57 mathematical modules and 22,284 physical lines** from `goldbach-lean`, or 16,684 lines after removing comments and blank lines:

| Directory | Modules | Source and role |
|---|---:|---|
| `MathlibNt` | 10 | Shared number-theory foundations |
| `AnalyticNumberTheory` | 33 | Foundations from `UyNewNas/analytic-number-theory-lean` and subsequent development |
| `PrimeNumberTheoremAnd` | 14 | Adapted prime-number-theorem foundations from `AlexKontorovich/PrimeNumberTheoremAnd` |

All three directories are bundled in the pinned `goldbach-lean` revision. Its [provenance record](https://github.com/subfish-zhou/goldbach-lean/blob/24490c2ab7787238f816d771c9176411dcbda503/docs/PROVENANCE.md) identifies the upstream PNT revision as `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`.

The PNT sources also import nine LeanArchitect tooling modules for blueprint and declaration annotations. Lean, Mathlib, and their regular tooling packages are counted separately from the 57 mathematical modules above.

## Declarations used by proofs

The declaration audit recursively follows types and proof or definition values. Counts include auxiliary, generated, and private declarations.

| Roots | External mathematical modules | External declarations |
|---|---:|---:|
| `theorem_1_1` | 5 | 68 |
| `theorem_1_2` | 5 | 68 |
| `primePair_consequence` | 5 | 72 |
| All 102 reviewed declarations | 22 | 839 |
| Entire public proof library | 22 | 839 |

The five modules used by the three main results are:

```text
MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative
```

They provide singular series, Dirichlet L-functions, periodic character sums, and Abel summation. Among the 102 reviewed declarations, **`lemma_4_3_uniform`** alone reaches the Mertens and `MediumPNT` chain, for the uniform estimate `N/φ(N) ≪ log log N`.

The recorded proof closures use `propext`, `Classical.choice`, and `Quot.sound`.

## Evidence and reproduction

- [Complete import graph and provenance](../formalization/verification/publication/dependencies-imports.json)
- [Declaration counts](../formalization/verification/publication/declaration-audit/summary.json)
- [All 839 external declarations](../formalization/verification/publication/declaration-audit/reviewed_102-external-declarations.tsv)
- [Declaration paths and detailed report](../formalization/verification/publication/declaration-audit/report.md)

After building the main library, run from `formalization`:

```bash
lake env lean verification/publication/declaration-audit/DeclarationAudit.lean
python3 verification/publication/declaration-audit/analyze.py
python3 verification/publication/audit_imports.py
```

The complete declaration graph is approximately 95 MB and is reproducible with these commands. The repository stores compact results and reference paths. Historical evidence records the source hashes and local paths used for its collection.
