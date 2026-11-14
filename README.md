# Conditional Goldbach in Lean

[Chinese](README.zh.md)

A Lean 4 formalization of the Li–Liu paper's conditional Goldbach results and their analytic, operator, and spectral foundations. The main theorems give asymptotics for sufficiently large even integers under **GRH and spectral condition S or R**, with the paper's quantifier order and constant dependencies.

## Results

- All **102 reviewed declarations**, covering the paper's 38 named results, have complete proofs. The transitive axiom audit covers **1,386 public theorems and auxiliary results**.
- The main library contains **271 Lean files and 30,774 lines**, including comments and blank lines, excluding dependencies and audit code.
- Three independent reviews checked the original TeX. All **103 independently stated propositions** passed full type checks; the Lean comparator accepted **218 targets**, including propositions, definition equalities, representation bridges, and the counting certificate. Three deliberately altered controls were rejected.
- A direct enumeration certificate proves that **30030 has 905 unordered prime-pair representations**, using `decide +kernel`.

The remaining numerical work in Appendix B consists of certifying the specified integral approximations and their errors, deriving the stated integer interval from those certified inputs, and certifying the finite spectral matrix numerically. General error propagation and spectral criteria are proved. The direct count and the integral certificate are separate verification tasks.

## Build

```bash
git clone https://github.com/subfish-zhou/conditional-goldbach-lean.git
cd conditional-goldbach-lean/formalization
lake update
lake exe cache get
lake --wfail build
```

Install the `elan` Lean toolchain manager first. `lean-toolchain` pins Lean 4.35.0; the Lake manifest pins the dependencies:

| Dependency | Revision |
|---|---|
| `goldbach-lean` | `24490c2ab7787238f816d771c9176411dcbda503` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The package uses Git dependencies. See [dependency details](docs/dependencies.md) for imported modules and declarations actually used by proofs.

The proof library uses Lean's module system and preserves unfolding for its public definitions. Unused proof parameters have a leading `_`. If you pass an affected parameter by name, use its new spelling, such as `_hN` in `lemma_3_1_odd_orthogonality`.

See the [latest refactor measurements](docs/quality-convolution.md) for source size, import closures, and build/proof timing comparisons.

See [choosing an import](docs/imports.md) for main-theorem, prime-pair, definition, and finite-spectrum consumers with checked import boundaries.

## Read and verify

- [Independent audit](formalization/verification/independent-audit/report.html): source comparisons, mechanical checks, and numerical tasks.
- [Proof explorer](formalization/progress.html): current proof sources and transitive axiom status.
- [Proof library](formalization/README.md): modules, checked declarations, and verification commands.
- [Audit summary](formalization/verification/independent-audit/summary.json), [comparator log](formalization/verification/independent-audit/comparator.log), and [individual comparison results](formalization/verification/independent-audit/final-comparison.json).
- [Direct counting proof](formalization/verification/independent-audit/appendices/NumericCrossCheck.lean).
- [Original TeX](outputs/formalization-preparation/conditional-goldbach.tex) and [statement-review snapshot](outputs/formalization-preparation/README.md).

To reproduce the build, proof and dependency audits, full comparator run, and machine summaries from the repository root on Linux with `bubblewrap` installed:

```bash
python3 formalization/scripts/verify_project.py
```

Then render and browser-check both report languages before running `update_verification.py` and `package_verified.py`. The runner checks the Lake dependency checkouts against the pinned revisions and records the source, comparator configuration, and audit output hashes. The report checks use these hashes so the evidence can be verified after copying or extracting it.

To rerun the independent comparator using the current build records:

```bash
python3 formalization/verification/independent-audit/prepare_comparator.py
python3 formalization/verification/independent-audit/run_comparator.py
python3 formalization/scripts/refresh_audit_summary.py
```

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Audit `Challenge` files specify comparison targets using placeholders; the corresponding `Solution` files supply proofs. `reference/Reviewed.lean` and `outputs/formalization-preparation/` preserve the earlier statement-review stage. The main library imports the completed proof modules.

Mathematical review connects the TeX to the independent Lean reference. The comparator then checks that reference against actual theorem types, definition bodies, and proof axioms.

The HTML reports work offline. To regenerate and check them, install the optional dependencies in `formalization/requirements-review.txt` and `formalization/package.json`, then run `npx playwright install chromium` from `formalization`.

## Verification records

The [publication records](formalization/verification/publication/) contain build, import, and declaration audits. Historical reports retain the measurements and hashes recorded at the time of each check. The [naming migration record](formalization/verification/naming-migration.json) links the Git snapshots before and after the rename.

The [pre-rename clean-build record](https://github.com/subfish-zhou/conditional-goldbach-lean/blob/8e2f641b8625cf58ae53ab5a836d30193b9c1c30/formalization/verification/independent-audit/build-project-clean.json) records a shared host with eight logical CPUs and two Lean worker threads: **15 minutes 56 seconds** for the project with dependency caches reused; **4.75 seconds** for an [unchanged rebuild](https://github.com/subfish-zhou/conditional-goldbach-lean/blob/8e2f641b8625cf58ae53ab5a836d30193b9c1c30/formalization/verification/independent-audit/build-warm.json). The file timestamps from initial proof-project creation to the verified package span approximately **5 hours 25 minutes**, excluding preparation and later audits.
