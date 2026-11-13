# Statement-review snapshot

The type checks and source hashes recorded here belong to the **pre-rename review snapshot**. Current theorem-type checks are in [reviewed-types.json](../../formalization/reviewed-types.json); [naming-migration.json](../../formalization/verification/naming-migration.json) records the original Git blobs and before/after hashes. [snapshot-migration.json](snapshot-migration.json) records the current snapshot's byte-for-byte match to the Reviewed reference and the unchanged TeX hash.

[Chinese](README.zh.md) · [Current proof library](../../formalization/README.md)

This directory preserves revision 9 of the statement-review stage. It covers the original TeX's **38 named results and 121 definition families**, including Appendices A and B. The Lean snapshot contains **102 theorem statements** (38 principal statements, 60 supporting statements, and 4 auxiliary statements) and **171 definition declarations**. Its proofs use `by sorry`; the completed implementations live in `formalization`.

Start with the [dependency review](dependency-review.html) and [source comparison](review.html). Both work offline and provide rendered formulas, Lean highlighting, and original TeX excerpts.

| Files | Contents |
|---|---|
| `conditional-goldbach.lean` | Reviewed definitions and theorem statements |
| `conditional-goldbach.tex`, `tex-index.json` | Original source and index of 38 named environments, 3 hypothesis environments, and 233 labels |
| `dependency-review.html`, `dependency-graph.json`, `dependency-audit.md` | Paper dependencies, Lean declaration references, and dependency review |
| `tex-audit.md`, `tex-audit.json`, `tex-cross-check.json` | TeX review and checks of added representation interfaces |
| `semantic-audit.md`, `semantic-audit.json` | Mathematical encoding decisions and the 159-entry review ledger |
| `report.md`, `inventory.json` | Object map, declaration inventory, and source locations |
| `source-audit.json`, `cross-check.json` | Source provenance and independent review |
| `verification.json` | Pre-rename source hashes and historical type-check record |
| `html-verification.json`, `dependency-html-verification.json` | Offline display and interaction checks |

The dependency graph contains 146 paper nodes and 236 working dependency edges, plus 273 Lean declarations and 987 exact declaration references. The paper review records 189 dependencies. Theorem 6.1's supporting statement `theorem_6_1_abstract_dictionary` provides a common spectral interface for fixed and variable strips.

## Recheck the snapshot

After installing the project's pinned dependencies, run from `formalization`:

```bash
lake env lean ../outputs/formalization-preparation/conditional-goldbach.lean
```

The recorded environment is Lean 4.35.0 with Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The historical type check exited successfully with 102 expected placeholder warnings.

The review records five principal encoding choices: common entire denominators for joint meromorphy; weighted Fourier–Laplace L² models of Hardy spaces; countable Hilbert bases for Hilbert–Schmidt operators and spectra; specialized positive trace-class Fredholm determinants; and a shared complex entire function for quaternionic slices and multiplicities. The [independent audit](../../formalization/verification/independent-audit/report.html) documents their later representation checks.
