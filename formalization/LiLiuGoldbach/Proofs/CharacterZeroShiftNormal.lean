import LiLiuGoldbach.Proofs.CharacterZeroNormal
import LiLiuGoldbach.Proofs.CompletedLZeros

/-! The exact shifted zero-resolvent convergence under GRH. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace LiLiuGoldbach16

lemma NormallySummableOn.comp {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : ι → Y → ℂ} {U : Set Y} (hf : NormallySummableOn f U)
    (T : X → Y) (hT : Continuous T) {V : Set X} (hTU : MapsTo T V U) :
    NormallySummableOn (fun i x => f i (T x)) V := by
  intro K hK hKV
  have hh := hf (T '' K) (hK.image hT) (by
    rintro y ⟨x,hx,rfl⟩
    exact hTU (hKV hx))
  have he (i : ι) : {r : ℝ | ∃ y ∈ T '' K, r = ‖f i y‖} =
      {r : ℝ | ∃ x ∈ K, r = ‖f i (T x)‖} := by
    ext r
    simp
  simpa only [he] using hh

attribute [local instance] conductorNeZero in
theorem lemma_3_4_normal_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) :
    NormallySummableOn (fun p : ZeroIndex χ.primitiveCharacter => fun s : ℂ =>
      1 / (s - p.val.1.im * I) - 1 / (3 / 2 - p.val.1.im * I))
      {s | 0 < s.re} := by
  have hχn := primitiveCharacter_ne_one_of_ne_one χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2)
  have hf := primitive_zero_difference_normallySummable χ.primitiveCharacter hχn χ.primitiveCharacter_isPrimitive
  let T : ℂ → ℂ × ℂ := fun s => (1/2+s,2)
  have hT : Continuous T := by fun_prop
  have hmaps : MapsTo T {s | 0<s.re}
      {u | completedL χ.primitiveCharacter u.1 ≠ 0 ∧ completedL χ.primitiveCharacter u.2 ≠ 0} := by
    intro s hs
    constructor
    · intro hz
      have hzero := ((completedL_eq_zero_iff χ.primitiveCharacter hχn χ.primitiveCharacter_isPrimitive _).mp hz).2.2
      exact primitive_LFunction_ne_zero_of_GRH hGRH χ.conductor_dvd_level χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive hχn (by change 1/2 < (1/2+s).re; norm_num; exact hs) hzero
    · intro hz
      have hzero := ((completedL_eq_zero_iff χ.primitiveCharacter hχn χ.primitiveCharacter_isPrimitive _).mp hz).2.1
      change (2 : ℂ).re < 1 at hzero
      norm_num at hzero
  have hh := hf.comp T hT hmaps
  have he : (fun p : ZeroIndex χ.primitiveCharacter => fun s : ℂ =>
        1 / ((T s).1-p.val.1)-1 / ((T s).2-p.val.1)) =
      (fun p : ZeroIndex χ.primitiveCharacter => fun s : ℂ =>
        1 / (s-p.val.1.im*I)-1 / (3/2-p.val.1.im*I)) := by
    funext p s
    have hre := hGRH χ.conductor inferInstance χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive p.val.1 p.property.1 p.property.2.1 p.property.2.2.1
    have hp : p.val.1 = (1/2 : ℂ)+(p.val.1.im : ℂ)*I := by
      apply Complex.ext <;> simp [hre]
    dsimp [T]
    conv_lhs => rw [hp]
    congr 2 <;> ring
  rw [he] at hh
  exact hh

end LiLiuGoldbach16
