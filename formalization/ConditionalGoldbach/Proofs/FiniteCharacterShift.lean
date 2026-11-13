import ConditionalGoldbach.Proofs.FiniteMellinProjection
import ConditionalGoldbach.Proofs.MellinCharacterShift

/-! Character Mellin contour shifts requiring only four derivatives. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma finite_mellin_character_uniform_bound (N : ℕ) (hN : 4 ≤ N) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 4 f) (l r : ℝ) (hsupp : Function.support f ⊆ Icc l r)
    (lo A : ℝ) (hlo : 0<lo) (hlo1 : lo≤1) (hA : 0 ≤ A) (g : ℂ → ℂ)
    (hg : ∀ x ∈ Icc lo 1, ∀ t : ℝ,
      ‖g (line x t)‖ ≤ A * Real.log (N * (|t| + 2)) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc lo 1, ∀ t : ℝ,
      ‖(N : ℂ) ^ (line x t) * mellin (fun u => (f u:ℂ)) (line x t) * g (line x t)‖ ≤
        C * (1 + |t|)⁻¹ ^ 2 := by
  obtain ⟨B, hB, hb⟩ := compact_mellin_finite_decay 4 f hf l r hsupp lo 1 hlo hlo1
  refine ⟨(N : ℝ) * B * (4 * A * (N : ℝ) ^ 2), by positivity, ?_⟩
  intro x hx t
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNpow : ‖(N : ℂ) ^ (line x t)‖ ≤ N := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    have hline : (line x t).re = x := by simp [line]
    rw [hline]
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hx.2
  have hm : ‖mellin (fun u => (f u:ℂ)) (line x t)‖ ≤ B * (1 + |t|)⁻¹ ^ 4 := by
    simpa only [line, add_re, ofReal_re, mul_re, ofReal_im, I_re,
      I_im, mul_zero, zero_mul, sub_self, add_zero, add_im, mul_im, mul_one,
      zero_add] using hb (line x t) (by simpa [line] using hx)
  have hg' : ‖g (line x t)‖ ≤ (4 * A * (N : ℝ) ^ 2) * (1 + |t|) ^ 2 := by
    have h := (hg x hx t).trans (mul_le_mul_of_nonneg_left (log_square_polynomial_bound N hN t) hA)
    convert h using 1 <;> ring
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((N : ℝ) * (B * (1 + |t|)⁻¹ ^ 4)) *
        ((4 * A * (N : ℝ) ^ 2) * (1 + |t|) ^ 2) :=
      mul_le_mul (mul_le_mul hNpow hm (norm_nonneg _) hNpos.le) hg'
        (norm_nonneg _) (by positivity)
    _ = _ := by
      have ht : (1 + |t|) ≠ 0 := by positivity
      field_simp
      <;> ring


lemma finite_character_mellin_shift {N : ℕ} [NeZero N] (hN4 : 4≤N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ∈oddCharacters N)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (l r : ℝ) (hsupp : Function.support f ⊆ Icc l r)
    (σ : ℝ) (hσ : 0<σ) (hσ1 : σ≤1) :
    Integrable (fun t : ℝ => (N:ℂ)^(line σ t)*mellin (fun u => (f u:ℂ)) (line σ t)*logDerivative χ (line σ t)) ∧
    verticalMellin σ (fun s => (N:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s)=
      verticalMellin 1 (fun s => (N:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s) := by
  obtain ⟨A,hA,hlog⟩ := logDerivative_uniform_bound σ 1 hσ hσ1
  have hg := hlog N inferInstance hN4 hGRH χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2)
  obtain ⟨C,hC,hbound⟩ := finite_mellin_character_uniform_bound N hN4 f hf l r hsupp σ A hσ hσ1 hA.le (logDerivative χ) hg
  let F : ℂ → ℂ := fun s => (N:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s
  have hNz : (N:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hd : ∀z : ℂ, z.re∈Icc σ 1 → DifferentiableAt ℂ F z := by
    intro z hz
    have hz0 := hσ.trans_le hz.1
    exact ((differentiableAt_id.const_cpow (Or.inl hNz)).mul
      (compact_mellin_regular f hf.continuous l r hsupp z hz0).2).mul
        (odd_logDerivative_analyticAt_of_GRH hGRH χ hχ hz0).differentiableAt
  have hcF : Continuous (fun t : ℝ => F (line σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hd _ (by simpa [line] using (show σ∈Icc σ 1 from ⟨le_rfl,hσ1⟩))).continuousAt.comp
      (f := fun t : ℝ => line σ t) (by unfold line; fun_prop)
  have hi := integrable_of_uniform_vertical_decay F σ C hcF (hbound σ ⟨le_rfl,hσ1⟩)
  exact ⟨hi,verticalMellin_eq_of_uniform_decay F σ 1 C hσ1 hd hi
    (finite_character_mellin_initial_integrable χ f (hf.of_le (by norm_num)) l r hsupp 1 (by norm_num)) hbound⟩

end ConditionalGoldbach
