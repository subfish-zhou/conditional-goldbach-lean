# Comparison with the previous GitHub release

[中文](release-comparison.zh.md) · [Raw measurements](release-comparison.json)

The baseline is GitHub `main` before the push, [`14c132a`](https://github.com/subfish-zhou/conditional-goldbach-lean/tree/14c132a382c52f89d2403ff7ba9397a0432bc1d3). The refactored code is [`8aa8312`](https://github.com/subfish-zhou/conditional-goldbach-lean/tree/8aa8312001a626be4933ef156438d074bd90a672). This comparison covers the cumulative changes.

## Source and dependency size

| Metric | GitHub baseline | Refactored code | Change |
|---|---:|---:|---:|
| Production Lean files | 254 | 271 | +17 |
| Physical lines | 29,629 | 30,774 | +1,145 |
| Nonblank lines, comments retained | 27,451 | 28,015 | +564 |
| Noncomment, nonblank lines | 27,005 | 27,535 | +530 |
| Also excluding module/import/public-section lines | 26,276 | 26,335 | +59 |
| Imported modules | 11,731 | 6,803 | -4,928 |
| Mathlib modules | 8,625 | 3,801 | -4,824 |
| goldbach mathematical modules | 57 | 57 | +0 |

Noncomment, nonblank source grows by 530 lines (about 1.96%). Of these, 471 are module declarations, imports, or public-section boundaries; excluding those leaves a net increase of 59 lines. This second metric still includes definitions, statements, namespaces, and options, so it is not a proof-only count. Production counts exclude dependencies, audit copies, JSON, HTML, scripts, and historical artifacts. The comment lexer handles nested block comments and preserves comment markers inside strings.

The full imported-module count falls by about 42.01%, and Mathlib modules by about 55.93%. The set of 57 goldbach mathematical modules and all dependency revisions are unchanged. Import counts are cross-checked against the compiled environments.

## Compilation and diagnostics

| Workload | GitHub baseline | Refactored code |
|---|---:|---:|
| Full production rebuild | 1018.12 s | 395.10 s |
| Import-only consumer, median of three | 6.02 s | 3.90 s |
| Import-process peak RSS, median | 6.93 GiB | 4.36 GiB |
| Production warning diagnostics | 400 | 0 |
| Of which: legacy-module warnings | 28 | 0 |
| Other production warnings | 372 | 0 |

The measured full-rebuild wall time falls by **61.2%**. Both isolated directories start with empty local build outputs and reuse identical pinned dependency artifacts. Builds run sequentially with `LEAN_NUM_THREADS=2 lake build`, recording one successful full build per version; import probes run three times each. An earlier refactored-code build exhausted temporary disk space and is excluded; its replacement starts again with empty local outputs. Background activity on this shared host can affect wall time. Downloads, Comparator runs, audits, reporting, and packaging are excluded. The current version also passes `lake --wfail build`.

[Baseline build log](release-before-build.log) · [Refactored build log](release-after-build.log)

## Formalization quality

- **Mathematical coverage is preserved.** All 102 reviewed declarations remain closed, with 171 original definition bodies preserved. The 103 independent full-type checks, 218 Comparator targets, and three rejection controls pass. Fourteen source/reference files, including the original TeX and reviewed snapshot, are byte-identical to the baseline.
- **The audit covers more declarations.** Lean module ownership and source ranges replace discovery by text and name prefixes. The audit now covers 2,965 local compiled constants, including private and generated declarations, with no additional axioms or admissions. The public-result count rises from 1,354 to 1,386: 17 were already present but omitted by the old scanner, and 15 are new auxiliary lemmas.
- **Dependency boundaries are explicit.** Definitions are split into 14 topics using the Lean module system and explicit public exports. Five consumer entrypoints enforce advertised exports, forbidden imports, and module-count budgets.
- **Proof maintenance is simpler.** Mellin contour shifts, double integrals, and Beta–Mellin convolutions share arguments. Named interfaces expose spectral data and the corrected counting identity. Ineffective tactics, redundant simp arguments, and unused-parameter warnings are removed.
- **Hotspot changes are measured.** Hilbert–Schmidt and Poisson reindexing specify summands explicitly; averaged estimates constrain nonlinear arithmetic search. The two preceding reports contain paired theorem heartbeats and local timings; those stage-specific timings are distinct from this GitHub-baseline rebuild comparison.
- **Evidence is traceable.** Build inputs, Comparator settings, policies, sources, and outputs are bound by hashes. Copied evidence is checked independently of filesystem mtimes, and deliberate alterations are rejected.

Compatibility: some unused binder names change from forms such as `hN` to `_hN`, so named-argument callers may need adjustment. The root no longer implicitly loads all of Mathlib; downstream files using additional Mathlib declarations should import the relevant modules explicitly. Mathematical hypotheses are retained.

[Definition/HS/Mellin refactor](quality-refactor.md) · [Convolution/hotspot refactor](quality-convolution.md) · [Import guide](imports.md)
