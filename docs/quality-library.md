# Reusable interfaces and library-quality improvements

[English](quality-library.md) · [中文](quality-library.zh.md) · [JSON](quality-library.json)

The baseline is `cb16bfc`. This round implements four proof-hotspot improvements, elaboration-option cleanup, development/release verification and CI, a compact offline explorer, foundational import separation, and reusable analysis interfaces. The checked mathematical definitions and existing declaration interfaces are preserved.

## Source and dependencies

| Metric | Before | After |
|---|---:|---:|
| Production Lean files | 271 | 275 |
| Physical lines | 30,774 | 30,739 |
| Noncomment, nonblank lines | 27,535 | 27,455 |
| Also excluding module/import/public-section lines | 26,335 | 26,241 |
| File-wide elaboration overrides | 140 | 0 |
| Scoped elaboration overrides | 1 | 0 |
| Public tactic imports | 26 | 0 |

Counts cover production Lean sources only, excluding dependencies, audit copies, tools and HTML. The comment lexer handles nested comments and strings. The net reduction of 80 code lines largely reflects option cleanup, not a proof-only reduction.

| Entrypoint | Total modules | Local | Mathlib | goldbach mathematics |
|---|---:|---:|---:|---:|
| `ConditionalGoldbach` | 6,807 | 275 | 3,801 | 57 |
| `ConditionalGoldbach.Definitions` | 5,472 | 23 | 3,510 | 3 |
| `ConditionalGoldbach.Proofs.Main` | 6,442 | 142 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.PrimePairs` | 6,445 | 145 | 3,615 | 16 |
| `ConditionalGoldbach.Proofs.FiniteExperimentSpectrum` | 5,513 | 36 | 3,538 | 3 |
| `ConditionalGoldbach.Definitions.GeometryCore` | 3,577 | 1 | 1,696 | 0 |
| `ConditionalGoldbach.Analysis.L2Fourier` | 4,876 | 1 | 2,939 | 0 |
| `ConditionalGoldbach.Analysis.SpectralData` | 4,136 | 2 | 2,198 | 0 |

The complete import count changes from 6,803 to 6,807; the four additions are local modules. Mathlib remains at 3,801 and goldbach at 57 mathematical modules, with unchanged dependency pins. Eight isolated consumers pass export, compiled-inventory and budget checks; the two analysis interfaces also compile usage examples.

## Proof hotspots

| Theorem | Before heartbeats | After heartbeats | Reduction |
|---|---:|---:|---:|
| `pole_spectral_obstruction` | 57,987 | 6,204 | 89.3% |
| `LFunction_sub_one_norm_bound` | 53,884 | 2,935 | 94.6% |
| `logDerivative_uniform_bound` | 55,638 | 18,387 | 67.0% |
| `spectralQuaternion_reindexed_compactUniformLimit` | 49,880 | 1,595 | 96.8% |

Paired probes alternate baseline/current sources on the same host, pinned Lean and dependencies, with two threads. Each selected declaration is wrapped in `#count_heartbeats in`. The counter disables its own heartbeat limit, so default-budget success is established separately by the successful `lake --wfail build`. Production sources have no warnings or tactic suggestions; the dependency library retains two existing `ring` informational messages. JSON records source hashes, logs and probe timings. Empty-local-output rebuild timing was not repeated in this round.

## Verification and reuse

With existing compilation artifacts, the seven development checks total **92.48 seconds**. Build, audit and summary steps in the full release run total **585.10 seconds**, including the independent Comparator and excluding rendering/packaging. These workflows have different scopes. Development output is isolated; the existing release-record hashes were individually checked unchanged.

With unchanged complete evidence, `check_project.py --reuse-release` takes 1.04 seconds in this run. The main Comparator takes 384.96 seconds: kernel rechecking uses 236.12 seconds and the two exports 84.08 seconds; comparison, coordination and other time outside sandbox phases total 59.69 seconds. Full rechecking remains part of release verification.

Checks pass for all 102 reviewed theorem types, 171 definition bodies, 1,621 existing public source interfaces, and 103 independently restated full types. Comparator accepts 218 targets and rejects the three condition/quantifier/definition mutations. The axiom audit covers 2,974 local compiled constants and 1,400 public results, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Additional exports mainly expose shared analysis facts and compatibility wrappers.

Interface fingerprints preserve explicit binder names, order and implicitness, normalize universe names, and erase metadata and compiler-generated binder hygiene scopes. Baseline fingerprints come from the original commit’s separate compiled environment. Existing import paths and declaration names remain available; proof tactics are private imports, so downstream proofs should import their own tactics.

`Analysis.L2Fourier` depends only on Mathlib and serves both Hardy interior restrictions and boundary proofs. `Analysis.SpectralData` serves spectral algebra and trace proofs. `GeometryCore` is separated from `BoundaryIntegral`, while the existing `Geometry` entrypoint reexports both.

CI runs development checks on PRs and the full verification, bilingual browser tests, tamper regressions and packaging on main pushes/manual dispatch. Actions are pinned by commit. Verification tools and outputs are hash-bound; reuse requires every bound input to match. Sandbox subprocess timing preserves isolation and parent-death behavior.

## Offline explorer

| Language | Before HTML | After HTML |
|---|---:|---:|
| en | 25.67 MiB | 6.24 MiB |
| zh | 25.71 MiB | 6.26 MiB |

Source is stored once, highlighting is reconstructed from UTF-16 token intervals, and mathematical summaries are shared. Initial DOM contains only the 102 reviewed declarations; all 1,638 declarations remain searchable. Both languages pass exact-source, mathematics, deep-link, offline/no-network and 390 px mobile checks. Chinese title formulas are rendered, and scope changes are safe while jump-highlight timers are pending.

[Development and API guide](development.md) · [Import guide](imports.md) · [Current verification record](../formalization/verification.json)
