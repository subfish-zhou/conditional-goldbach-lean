import LiLiuGoldbach.Proofs.Characters

/-!
# Algebraic properties of the character kernel

These finite Gram arguments make no assumptions about the zeros of L-functions.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable conductorNeZero

lemma characterKernel_gram (N : ℕ) [NeZero N] (s z : ℂ) :
    characterKernel N s (conj z) =
      (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N,
        logDerivative χ s * conj (logDerivative χ z) := by
  simp [characterKernel]

lemma characterKernel_hermitian (N : ℕ) [NeZero N] :
    HermitianKernel (fun s z => characterKernel N s (conj z)) := by
  intro s z
  simp only [characterKernel_gram, map_mul, map_sum, starRingEnd_self_apply]
  have htwo : conj (2 : ℂ) = (2 : ℂ) := by
    exact Complex.conj_ofReal 2
  have hscale : conj (2 / (N.totient : ℂ)) = 2 / N.totient := by
    simp only [map_div₀, htwo, map_natCast]
  rw [hscale]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  ring

/-- Every finite complex Gram kernel with nonnegative real scale is positive. -/
lemma finite_gram_positive {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ)
    (c : ℝ) (hc : 0 ≤ c) :
    PositiveKernel (fun z w => (c : ℂ) * ∑ k ∈ s, g k z * conj (g k w)) := by
  intro n points coefficients
  have hsq (k : ι) :
      (∑ i : Fin n, ∑ j : Fin n,
        coefficients i * conj (coefficients j) * (g k (points i) * conj (g k (points j)))) =
      (‖∑ i : Fin n, coefficients i * g k (points i)‖ ^ 2 : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq :
      (∑ i : Fin n, ∑ j : Fin n, coefficients i * conj (coefficients j) *
        ((c : ℂ) * ∑ k ∈ s, g k (points i) * conj (g k (points j)))) =
      (c : ℂ) * ∑ k ∈ s, (‖∑ i : Fin n, coefficients i * g k (points i)‖ ^ 2 : ℝ) := by
    simp only [Complex.ofReal_sum]
    simp_rw [← hsq]
    calc
      _ = (c : ℂ) * ∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ s,
          coefficients i * conj (coefficients j) * (g k (points i) * conj (g k (points j))) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        congr 1
        simp_rw [Finset.sum_comm (s := Finset.univ) (t := s)]
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ]
  apply mul_nonneg hc
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma characterKernel_positive (N : ℕ) [NeZero N] :
    PositiveKernel (fun s z => characterKernel N s (conj z)) := by
  have h := finite_gram_positive (oddCharacters N) (fun χ => logDerivative χ)
    (2 / (N.totient : ℝ)) (by positivity)
  simpa only [characterKernel_gram, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast] using h

/-- The character-kernel sections lie in the finite span of logarithmic derivatives. -/
lemma characterKernel_sections_le (N : ℕ) [NeZero N] :
    Submodule.span ℂ (Set.range (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z))) ≤
      Submodule.span ℂ (Set.range (fun χ : Character N => logDerivative χ)) := by
  apply Submodule.span_le.mpr
  rintro f ⟨z, rfl⟩
  have heq : (fun s : ℂ => characterKernel N s (conj z)) =
      ∑ χ ∈ oddCharacters N,
        ((2 / (N.totient : ℂ)) * conj (logDerivative χ z)) • logDerivative χ := by
    ext s
    simp only [characterKernel_gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  change (fun s : ℂ => characterKernel N s (conj z)) ∈ _
  rw [heq]
  apply Submodule.sum_mem
  intro χ _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨χ, rfl⟩

theorem proposition_3_2_finite_rank (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) := by
  let : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun χ : Character N => logDerivative χ))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le (characterKernel_sections_le N)

/-- Evaluating the odd projector at `(1,1)` counts exactly half the characters. -/
lemma oddCharacters_card (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) :
    (oddCharacters N).card = N.totient / 2 := by
  have hneg : (1 : ZMod N) ≠ -1 := by
    intro h
    have hh := ZMod.neg_one_eq_one_iff.mp h.symm
    omega
  have hp := lemma_3_1_odd_orthogonality N hN hN4 1 1
  simp [hneg] at hp
  have htot : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N.totient)
  field_simp at hp
  have hcard : 2 * (oddCharacters N).card = N.totient := by exact_mod_cast hp
  omega

/-- The numerical rank bound is controlled by odd characters, not all characters. -/
lemma characterKernel_rank_le (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) ≤ N.totient / 2 := by
  classical
  let S : Finset (ℂ → ℂ) := (oddCharacters N).image (fun χ => logDerivative χ)
  have hle : Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z))) ≤
      Submodule.span ℂ (S : Set (ℂ → ℂ)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨z, rfl⟩
    have heq : (fun s : ℂ => characterKernel N s (conj z)) =
        ∑ χ ∈ oddCharacters N,
          ((2 / (N.totient : ℂ)) * conj (logDerivative χ z)) • logDerivative χ := by
      ext s
      simp only [characterKernel_gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    change (fun s : ℂ => characterKernel N s (conj z)) ∈ _
    rw [heq]
    apply Submodule.sum_mem
    intro χ hχ
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨χ, hχ, rfl⟩
  calc
    _ ≤ Module.finrank ℂ (Submodule.span ℂ (S : Set (ℂ → ℂ))) := Submodule.finrank_mono hle
    _ ≤ S.card := finrank_span_finset_le_card S
    _ ≤ (oddCharacters N).card := Finset.card_image_le
    _ = N.totient / 2 := oddCharacters_card N hN hN4

end LiLiuGoldbach16
