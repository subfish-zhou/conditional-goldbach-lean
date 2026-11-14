# Convolution proofs, elaboration hotspots, and import entrypoints

[中文](quality-convolution.zh.md) · [JSON](quality-convolution.json)

The main text and Appendix B now share the Beta–Mellin convolution argument in `MellinBetaConvolutionCore`. Existing theorem names, parameters, and complete types are preserved. Each weight class supplies its own measurability, convergence, vertical integrability, and kernel-pairing results. Main-text outer pairing remains valid at every real part; the finite-weight version retains its positive-real-part assumption.

Poisson zero reindexing specifies `Equiv.summable_iff (f := q)`, avoiding higher-order unification of the summand. Four `nlinarith` calls in the averaged estimate now use only the inequalities required for their algebraic steps.

| Production source size | Before | After |
|---|---:|---:|
| Lean files | 270 | 271 |
| Physical lines | 30,755 | 30,774 |
| Nonblank lines | 28,007 | 28,015 |

Explicit analytic assumptions and the complete statements of compatibility wrappers add a small number of lines; proof bodies are shared. Physical lines include comments and blanks, excluding dependencies and audit code.

| Individual-file elaboration median | Before (s) | After (s) |
|---|---:|---:|
| `CharacterPoissonAnchor` | 13.33 | 7.95 |
| `CharacterAverageAssembly` | 12.05 | 7.55 |
| `MellinBetaConvolution` | 5.98 | 3.69 |
| `FiniteModelBetaConvolution` | 5.10 | 3.45 |
| `MellinBetaConvolutionCore` | — | 3.74 |

The new shared core also needs elaboration and is measured separately. Wrapper speedups alone do not represent total convolution-build savings. Each file is measured three times against the same final compiled import environment, with `LEAN_NUM_THREADS=2`. Other workloads on this shared host can affect wall time. A full cache-cleared project rebuild was not remeasured in this round.

| Hotspot theorem heartbeats | Original | Optimized |
|---|---:|---:|
| `CharacterPoissonAnchor` | 121,226 | 6,641 |
| `CharacterAverageAssembly` | 99,731 | 13,350 |

The paired `#count_heartbeats in` probes measure `primitive_poisson_anchor_bound` and `lemma_6_4_of_reference_and_comparison` under identical final imports. JSON includes both probe sources and their raw output.

| Entrypoint | Total modules | Local modules | Mathlib | goldbach math modules |
|---|---:|---:|---:|---:|
| `ConditionalGoldbach` | 6,803 | 271 | 3,801 | 57 |
| `ConditionalGoldbach.Definitions` | 5,469 | 20 | 3,510 | 3 |
| `ConditionalGoldbach.Proofs.Main` | 6,441 | 141 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.PrimePairs` | 6,444 | 144 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.FiniteExperimentSpectrum` | 5,512 | 35 | 3,538 | 3 |

The shared local module increases the full closure from 6,802 to 6,803. Mathlib remains at 3,801 modules and the same 57 goldbach mathematical modules remain imported. Counts include the implicit Init prelude; the definition and finite-spectrum entries each have 151 more Init modules than their explicit-source closure. Each of the five entrypoints has an independently compiled consumer. Forbidden imports, the definition entrypoint’s proof-module allowlist, and module-count budgets are enforced by `verify_project.py`; see [choosing an import](imports.md).


An additional full-type comparison covers all 29 original declarations in the four edited modules; all are preserved. Definition, reviewed-type, transitive-axiom, and independent Comparator results are recorded in the [current verification record](../formalization/verification.json).

[Baseline sources](quality-convolution-baseline.tar.gz) · [Previous refactor](quality-refactor.md)
