# Definition, Hilbert–Schmidt, and Mellin refactor

[中文](quality-refactor.zh.md) · [JSON](quality-refactor.json)

Definitions are split into 14 mathematical topics. `SpectralDataAlgebra` holds Hilbert-space coordinate lemmas, and `MellinDoubleDiagonal` supplies the common main-text and Appendix B integral argument. Both original definition entry points continue to reexport the reviewed objects.

Hilbert–Schmidt and related reindexing proofs specify the summand of `Equiv.summable_iff` explicitly, avoiding higher-order unification through `Summable`. Each double-Mellin caller retains its original weight assumptions, integrability proof, and mass term.

| Size | Before | After |
|---|---:|---:|
| Production Lean files | 254 | 270 |
| Production physical lines | 30,678 | 30,755 |
| Production nonblank lines | 27,990 | 28,007 |

| Import closure | Before | After |
|---|---:|---:|
| `ConditionalGoldbach` | 6,914 | 6,802 |
| `Definitions` | 5,552 | 5,318 |
| `Proofs.HardyBoundary` | 5,300 | 4,730 |
| `Proofs.SpectralCompletionTrace` | 5,554 | 3,986 |
| `Proofs.MellinModelDouble` | 5,593 | 5,365 |
| `Proofs.FiniteModelDouble` | 5,609 | 5,375 |
| Mathlib modules in the full entry point | 3,929 | 3,801 |

The Hardy boundary and Hilbert–Schmidt trace closures contain no `goldbach-lean` mathematical modules. The full project still imports 57 such modules at the pinned revision. Physical lines include comments and blanks, excluding dependencies, audit copies, and generated pages; module headers and documentation count toward the total.

| Timed workload | Before (s) | After (s) |
|---|---:|---:|
| Full entry point | 3.90 | 3.86 |
| Definition entry point | 3.42 | 3.23 |
| Hardy boundary consumer | 3.29 | 2.96 |
| Hilbert–Schmidt trace file | 9.39 | 2.60 |
| Main-text double Mellin file | 3.36 | 2.69 |
| Appendix B double Mellin file | 3.23 | 2.69 |
| Full production rebuild | 469.20 | 374.90 |

The first six workloads report the median wall time of three runs. Full rebuilds are single measurements after removing only project build traces while retaining dependency caches. Both use `LEAN_NUM_THREADS=2` and `lake --wfail build`. Other builds on this shared host can affect wall time. Comparator runs, reporting, and downloads are excluded.

| Proof heartbeats under identical imports | Original | Optimized |
|---|---:|---:|
| `SpectralCompletionTrace` | 77,906 | 1,704 |
| `SpectralHilbertSchmidt` | 82,974 | 6,720 |
| `SpectralRankOneSeries` | 5,598 | 5,594 |

The paired `#count_heartbeats in` checks measure basis independence, double Parseval for the adjoint, and the rank-one trace formula. Each original/optimized pair uses the same final imports, isolating proof elaboration from import changes.

Verification preserves all 171 reviewed definition bodies and the full types of 102 reviewed theorems. The 103 independently stated full types, 218 Lean Comparator targets, and three rejection controls pass. See the [current verification record](../formalization/verification.json).

[Baseline sources](quality-baseline.tar.gz) · [Raw measurements and source hashes](quality-refactor.json)
