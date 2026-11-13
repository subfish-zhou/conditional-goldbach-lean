# External declaration dependency audit

[Detailed Chinese report](report.zh.md)

This audit traces the declarations actually referenced by proof terms. The project uses singular-series and Dirichlet L-function foundations from the pinned `goldbach-lean` package. Across the full reviewed library, `lemma_4_3_uniform` additionally uses the Mertens product lower bound and its prime-number-theorem dependencies.

Recorded environment: Lean **v4.35.0**, `goldbach-lean` revision **24490c2ab7787238f816d771c9176411dcbda503**. Historical source hashes are in `source-hashes.json`; graph hashes, collection time, and counting conventions are in `metadata.json`.

## Method and counts

`DeclarationAudit.lean` loads `ConditionalGoldbach`, follows declaration types and proof or definition values, including opaque values, and adds constructors for inductive types. Lean's module metadata identifies each declaration's source. The recorded traversal reached **90,420 declarations**, resolving every referenced constant.

The public-library roots are **2,869 nonprivate declarations**, including Lean-generated helpers. Checking all **2,938 local declarations**, including private declarations, produced the same external dependency set. The 102 reviewed roots come from `reviewed-types.json`.

| Roots | External declarations | External modules | Direct external targets |
|---|---:|---:|---:|
| `theorem_1_1` | 68 | 5 | 20 |
| `theorem_1_2` | 68 | 5 | 20 |
| `primePair_consequence` | 72 | 5 | 22 |
| All 102 reviewed declarations | 839 | 22 | 30 |
| Public proof library | 839 | 22 | 30 |
| Complete local library, including private declarations | 839 | 22 | 30 |

These external counts cover the mathematical source directories in `goldbach-lean`. Lean, Mathlib, and general tooling are counted separately. Every audited scope has axiom set `{Classical.choice, Quot.sound, propext}`.

## Main-result dependencies

| External module | Theorems 1.1 / 1.2 | Prime-pair consequence | Role |
|---|---:|---:|---|
| `MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries` | 23 | 27 | Singular series, Euler factors, convergence, positivity, and bounds |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries` | 27 | 27 | Ordered L-series, tail estimates, and equality with L-functions |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation` | 9 | 9 | Abel summation and complex-power variation |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative` | 7 | 7 | Periodic character sums, partial-sum bounds, and finite Abel identities |
| `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds` | 2 | 2 | Integral-comparison bounds for real power series |

`LFunction_polynomial_bound` uses the ordered-series interfaces to establish `‖L(s,χ)‖ ≤ q (1 + ‖s‖/Re(s))`. `LFunction_sub_one_norm_bound` uses `tsum_nat_rpow_neg_le` for the right half-plane. The singular-series normalization is `singularSeries N = 2 * liuSingularSeries N`. The prime-pair consequence also uses the uniform positive lower bound from `liuUniversalProduct`.

## Mertens and PNT path

Among the 102 reviewed declarations, `ConditionalGoldbach.lemma_4_3_uniform` is the root reaching this chain:

```text
ConditionalGoldbach.lemma_4_3_uniform
→ ConditionalGoldbach.totient_ratio_loglog_bound
→ ConditionalGoldbach.totient_ratio_loglog_large
→ MathlibNt.SieveTheory.MertensTheorem.primeProduct_lower_bound
→ MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order
→ MathlibNt.SieveTheory.MertensTheorem.mertens_second_theorem
→ AnalyticNumberTheory.Mertens.mertensSecond_nat
→ AnalyticNumberTheory.Mertens.mertensSecond_isBigO
→ AnalyticNumberTheory.Mertens.mertensSecond_eventually
→ AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_endpoint_error
→ AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_error
→ AnalyticNumberTheory.PrimeDistribution.chebyshevPsi_medium_error
→ MediumPNT
```

The lower bound `c/log m ≤ ∏p≤m(1−1/p)` yields `N/φ(N) ≪ log log N`. The external `MediumPNT` theorem states `ψ(x)=x+O(x exp(−c(log x)^(1/10)))`.

The [839-declaration listing](reviewed_102-external-declarations.tsv) records every external declaration and its module. `reviewed_102.json` and `public_library.json` also give direct boundary references and complete reference paths. The direct local-to-external boundary consists of 30 target constants.

## Reproduce

After building the project, run from `formalization`:

```bash
lake env lean verification/publication/declaration-audit/DeclarationAudit.lean
python3 verification/publication/declaration-audit/analyze.py
```

| Artifact | Contents |
|---|---|
| `declaration-graph.json` | Reproducible full declaration graph, approximately 95 MB |
| `summary.json` | Counts, actual modules, and axioms for each root set |
| `theorem_1_1.json`, `theorem_1_2.json`, `primePair_consequence.json` | Main-result closures and reference paths |
| `reviewed_102.json`, `public_library.json` | Combined closures and direct boundary targets |
| `*-external-declarations.tsv` | Declaration names, modules, types, and private flags |
| `reviewed-requiring-mertens.json` | Reviewed declarations reaching Mertens |
| `imported-modules.json` | Independently collected module import list: 11,731 modules in the recorded environment |
