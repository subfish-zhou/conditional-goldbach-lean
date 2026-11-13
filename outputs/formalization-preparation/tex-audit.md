# Original TeX review: revision 8 snapshot

The type checks and source hashes recorded here belong to the **pre-rename review snapshot**. Current theorem-type checks are in [reviewed-types.json](../../formalization/reviewed-types.json); [naming-migration.json](../../formalization/verification/naming-migration.json) records the original Git blobs and before/after hashes. [snapshot-migration.json](snapshot-migration.json) records the current snapshot's byte-for-byte match to the Reviewed reference and the unchanged TeX hash.

[Detailed Chinese record](tex-audit.zh.md) · [Item-by-item ledger](tex-audit.json)

The review checked **38 named results and 121 core definition families** against the original TeX, including section assumptions, quantifiers, constant dependencies, formulas, and valid domains. The source index contains 3 hypothesis environments and 233 labels.

| Review classification | Named results | Definition families |
|---|---:|---:|
| Statement or definition matched | 32 | 109 |
| Display notation corrected | 3 | 7 |
| Supporting proof interface added | 2 | 3 |
| Object representation obligation added | 1 | 2 |

These counts classify affected entries; one issue can affect several entries.

The principal additions were Appendix A.1's variable-boundary representation and spectral-existence obligations, the general odd-character projection, the Perron residue, and the Poisson action's zero-parameter identity and positive-parameter normalization and convolution. Display corrections distinguished `V` from `Ψ`, restored `η/W/f`, and used the original coefficient `C_{N,γ}`.

The five encoding choices documented in [semantic-audit.md](semantic-audit.md) concern joint meromorphy, Hardy realization, countable Hilbert bases, positive trace-class Fredholm determinants, and quaternionic slices.

At this revision the merged snapshot had **101 theorem statements and 171 definition declarations**. The type check succeeded with placeholder proofs; revision 9 subsequently added the abstract spectral dictionary, bringing the theorem count to 102. The [independent interface check](tex-cross-check.json) and [verification record](verification.json) preserve the evidence.

The TeX attachment omitted `X30030-heatmap.pdf` and `X30030-zeros.pdf`. A local typeset copy used figure placeholders for numbering and had 62 pages; the supplied PDF had 63. PDF page references use the supplied PDF. An auxiliary long-token sequence comparison reported approximately 99.87% agreement, with differences due to mathematical glyphs, layout, and extraction order.

The original TeX SHA-256 was `0d36bddbed7c6a74a36c7b87a469fdc96f4b4692aa5c95a2890a1c4f5f59b125`. The ledger records local notation and the scope of later contour and energy estimates separately from the 121 core definition families.
