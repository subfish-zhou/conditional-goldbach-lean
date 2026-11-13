"""Render the English appendix report without changing audit inputs or status data."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
rows = json.loads((ROOT / 'comparison.json').read_text())
definitions = json.loads((ROOT / 'definitions-comparison.json').read_text())
families = json.loads((ROOT / 'definition-families.json').read_text())
numerics = json.loads((ROOT / 'uncovered-numerics.json').read_text())
numerical_text = json.loads((ROOT.parents[2] / 'reference/audit-numerics-en.json').read_text())

INTRO = "# Independent audit of Appendices A and B\n\n[Detailed Chinese report](audit-report.zh.md) · [Proposition comparisons](comparison.json) · [Definition comparisons](definitions-comparison.json)\n\nOriginal TeX lines **3931–4599** were checked against the current implementation. The audit covers **18 complete propositions**: 9 named results, 8 reviewed supporting statements, and `variable_uniform_spectral_bound`. It covers **32 definition families** through **48 independently reconstructed definition bodies**, including two auxiliary definitions for A.3.\n\nThe checked statement clusters preserve the source hypotheses, quantifier order, coefficients, and definitions. Specific numerical inputs are listed separately below.\n\n## Appendix A\n\n| Statement | Checked mathematical content |\n|---|---|\n| A.1 | Fix `c > 0`; assume even `N ≥ 4`, `N > exp(10c)`, and GRH. The variable-strip quadratic identity and pointwise estimates retain these conditions. The norm asymptotic has constants depending on `φ,c`, with `c` fixed before `N → ∞`. |\n| A.1 operator supplement | The variable-boundary kernel representation, boundary L², action integrability, and square-summable spectrum are conclusions under the same assumptions. |\n| A.2 | The R/norm and zero-free-width/norm equivalences preserve the open half-space, `0 < η < 1/2`, and admissible S width `≤ 1/4`. Constants for the arithmetic errors precede `h`. |\n| A.2 pointwise supplement | `∀φ,c ∃C>0 ∀N ∀h` expresses a constant independent of `h`. |\n| `variable_uniform_spectral_bound` | `∀c>0 ∃C≥1,c0>0 ∃N0 ∀` sufficiently large even `N`; no `φ` or `h` parameter occurs. It supplies width `c0 S(N)/(N log N)`. |\n| A.3 | `Qα ≍φ N^(2α)` uniformly for `0 < α < 1/10`; the absolute operator bound is `C((log N)² + α⁻²)`. |\n| A.3 absolute bound | `∃C>0 ∃N0 ∀N ∀α`, with no weight parameter. |\n| A.3 balance | For fixed `φ,C`, constants are uniform in admissible `N,c` and give `QαMα ≍φ (log N)²e^(2c)(1+c⁻²)`. |\n| A.3 widths | The ratio of the two actual admissible widths has order `h²(log N)⁴/S(N)² · e^(4c)(1+c⁻²)²`. Positive scales and the inverse-width domains are retained. |\n| A.4 | With `N` and a chosen zero ordinate `γ` fixed, `liminf(c→0+) c‖TN,c‖ ≥ 2 C_N,γ log N/(1+γ²) > 0`. The coefficient averages squared analytic multiplicities. The small-`c` domain gives `‖T‖ ≥ z/c`, failure of R, and `η ≤ δ²c²/(3z²)`. |\n| A.4 Euler supplement | The regular Euler product is analytic near zero and satisfies `S(N)RN(0)=1`, for even `N≥4`. |\n\nThe A.2 baseline width is the width supplied by the proved norm bound. A.4's lower-limit statement is expressed by `∀ε>0 ∃c0>0 ∀0<c<c0`, with `N,γ` fixed outside these quantifiers.\n\n## Appendix B\n\nThroughout the experiment, `N=30030`, `A=16`, and `L=1000`.\n\n| Statement | Checked mathematical content |\n|---|---|\n| B.1 | The `C⁶` symmetric cutoff, the actual wide weight, and `rG=NJ/2−Cpp/2+E`. The prime-power correction sums ordered pairs with at least one exponent ≥2 and divides by the product of exponents; the final formula divides this correction by 2. |\n| B.2 | Absolute convergence and `Iχ=−Σaₙχ(n)`, with all 5760 characters. `J=Σχχ(−1)|Iχ|²/5760` and `D=Σχ|Iχ|²/5760`. The logarithmic derivative is evaluated on the `3/2` line. |\n| B.3 | For arbitrary approximations and a certified RMS error `ε≥0`, `|J−Ĵ|≤2√D̂ ε+ε²`, and the exact integer count lies in the resulting closed interval. |\n| B.3 main identity | `A=NS cf/2` and `rG=A−NB/2−Cpp/2+E`, with `cf=∫₀¹ f(u)f(1−u)du`. |\n| B.4 | Under GRH, `B=⟨TvW,vW⟩`; the functional is integrable, bounded, linear, and represented by the actual Riesz vector. |\n| B.4 weight supplement | The wide weight has `C⁶` regularity and compact support in `(0,1)`. The model uses its cross mass `∫f(u)f(1−u)du`. |\n| B.5 | The matrix has 2562 nodes: 1281 on each boundary, from `−40` to `40` in steps of `1/16`, with endpoint half-weights. The matrix is `√wi E(si,conj sj)/((1+si)(1+conj sj)) √wj`. Its real spectrum is tied to a unitary diagonalization and its norm is the induced complex Euclidean norm. Under the stated GRH context, `‖C‖≤δ` implies every zero has real part `1/2`. |\n\nThe finite matrix product is\n\n`det(I−4q(1−q)C²/δ²) = ∏j(1−4λj²q(1−q)/δ²)`.\n\n"
EVIDENCE = '\n`Reference.lean` reconstructs the propositions and appendix-specific formulas. All **48 `rfl` definition bridges** and **18 complete proposition assignments** compiled successfully. `definition-families.json` maps all 32 families. The independent review checks the mathematical correspondence from TeX; the consolidated [comparator results](../final-comparison.json) check the Lean reference against the implementation.\n'


def cell(value):
    return str(value).replace('|', '\\|').replace('\n', ' ')


def tex_range(value):
    if isinstance(value, list):
        return '–'.join(str(x) for x in value)
    return str(value)


parts = [INTRO.rstrip(), '', '## Numerical claims and remaining certificates', '',
         'The general identities and criteria above are proved. The following table uses the current numerical audit ledger.', '',
         '| TeX lines | Reported computation | Certificate status |',
         '|---|---|---|']
for row in numerics:
    english = numerical_text[row['id']]
    parts.append('| ' + tex_range(row['tex_lines']) + ' | ' + cell(english['claim']) + ' | ' + cell(english['scope']) + ' |')
parts += ['', '## Comparison targets', '',
          f'The current mappings contain **{len(rows)} propositions**, **{len(definitions)} definition bodies**, and **{len(families)} definition families**.', '',
          '| Proposition | Original TeX lines |', '|---|---|']
for row in rows:
    parts.append('| `' + row['actual'] + '` | ' + tex_range(row['tex_lines']) + ' |')
parts += ['', 'The complete definition targets and family mapping are in [definitions-comparison.json](definitions-comparison.json) and [definition-families.json](definition-families.json).', '',
          '## Evidence', '', EVIDENCE.strip()]
(ROOT / 'audit-report.md').write_text('\n'.join(parts) + '\n')
print({'propositions': len(rows), 'definition_bodies': len(definitions),
       'definition_families': len(families), 'numerical_entries': len(numerics)})
