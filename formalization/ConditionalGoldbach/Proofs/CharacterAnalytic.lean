module

public import Mathlib.Analysis.Meromorphic.Basic
public import ConditionalGoldbach.Proofs.CharacterSeries
public import ConditionalGoldbach.Proofs.KernelAlgebra
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Global conjugation and meromorphy of the character kernel. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

lemma star_character_ne_one {N : ℕ} (χ : Character N) (hχ : χ ≠ 1) : star χ ≠ 1 := by
  intro h
  apply hχ
  simpa using congrArg star h

lemma LFunction_star_eq_conj {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1) :
    (star χ).LFunction = fun s => conj (χ.LFunction (conj s)) := by
  have hL : Differentiable ℂ (star χ).LFunction :=
    DirichletCharacter.differentiable_LFunction (star_character_ne_one χ hχ)
  have hC : Differentiable ℂ (fun s => conj (χ.LFunction (conj s))) := by
    intro s
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiable_LFunction hχ (conj s)).conj_conj
  apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (fun z _ => hL.analyticAt z) (fun z _ => hC.analyticAt z) (z₀ := 2)
  have hu : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hu] with s hs
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs,
    DirichletCharacter.LFunction_eq_LSeries _ (by simpa using hs)]
  unfold LSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp [LSeries.term, hn, MulChar.star_apply, RCLike.star_def, conj_natCast_cpow]

lemma logDerivative_star_eq_conj {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1) (s : ℂ) :
    logDerivative (star χ) s = conj (logDerivative χ (conj s)) := by
  have hf : (star χ).LFunction = conj ∘ χ.LFunction ∘ conj := LFunction_star_eq_conj χ hχ
  unfold logDerivative
  rw [hf, deriv_conj_conj]
  simp [Function.comp_def, map_div₀, show conj (2 : ℂ) = 2 from Complex.conj_ofReal 2]

lemma logDerivative_meromorphic {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1) :
    MeromorphicOn (logDerivative χ) Set.univ := by
  intro s _
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hshift : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + z) s := analyticAt_const.add analyticAt_id
  exact (((hL.deriv.analyticAt _).comp hshift).meromorphicAt).fun_div
    (((hL.analyticAt _).comp hshift).meromorphicAt)

lemma star_mem_oddCharacters {N : ℕ} [NeZero N] (χ : Character N) :
    star χ ∈ oddCharacters N ↔ χ ∈ oddCharacters N := by
  simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and, MulChar.star_apply]
  constructor
  · intro h
    have h' := congrArg star h
    simpa using h'
  · intro h
    simp [h]

lemma characterKernel_eq_star_sum (N : ℕ) [NeZero N] (s z : ℂ) :
    characterKernel N s z = (2 / (N.totient : ℂ)) *
      ∑ χ ∈ oddCharacters N, logDerivative χ s * logDerivative (star χ) z := by
  unfold characterKernel
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [logDerivative_star_eq_conj χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2)]

lemma characterKernel_symmetric (N : ℕ) [NeZero N] (s z : ℂ) :
    characterKernel N s z = characterKernel N z s := by
  rw [characterKernel_eq_star_sum, characterKernel_eq_star_sum]
  congr 1
  apply Finset.sum_bij (fun χ _ => star χ)
  · intro χ hχ
    exact (star_mem_oddCharacters χ).2 hχ
  · intro a ha b hb hab
    simpa using congrArg star hab
  · intro χ hχ
    exact ⟨star χ, (star_mem_oddCharacters χ).2 hχ, by simp⟩
  · intro χ hχ
    simp [mul_comm]

lemma characterKernel_conjugation (N : ℕ) [NeZero N] (s z : ℂ) :
    conj (characterKernel N s z) = characterKernel N (conj s) (conj z) := by
  calc
    conj (characterKernel N s z) = characterKernel N (conj z) (conj s) := by
      simpa using congrArg conj (characterKernel_hermitian N s (conj z))
    _ = _ := characterKernel_symmetric N _ _

lemma characterKernel_meromorphic_left (N : ℕ) [NeZero N] (z : ℂ) :
    MeromorphicOn (fun s => characterKernel N s z) Set.univ := by
  intro s _
  unfold characterKernel
  apply (MeromorphicAt.const _ _).fun_mul
  apply MeromorphicAt.fun_sum
  intro χ hχ
  exact (logDerivative_meromorphic χ (odd_character_ne_one χ
    (Finset.mem_filter.mp hχ).2) s (Set.mem_univ s)).fun_mul (MeromorphicAt.const _ _)

lemma characterKernel_meromorphic_right (N : ℕ) [NeZero N] (s : ℂ) :
    MeromorphicOn (fun z => characterKernel N s z) Set.univ := by
  simpa only [characterKernel_symmetric N s] using characterKernel_meromorphic_left N s

theorem proposition_3_2 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) :
    (∀ s z : ℂ, 1 / 2 < s.re → 1 / 2 < z.re →
      Summable (fun p : ℕ × ℕ => ‖arithmeticExpansionTerm N p.1 p.2 s z‖) ∧
      characterKernel N s z = ∑' p : ℕ × ℕ, arithmeticExpansionTerm N p.1 p.2 s z) ∧
    (∀ z, MeromorphicOn (fun s => characterKernel N s z) Set.univ) ∧
    (∀ s, MeromorphicOn (fun z => characterKernel N s z) Set.univ) ∧
    (GRH N → DifferentiableOn ℂ (fun p : ℂ × ℂ => characterKernel N p.1 p.2)
      {p | 0 < p.1.re ∧ 0 < p.2.re}) ∧
    (∀ s z, characterKernel N s z = characterKernel N z s ∧
      conj (characterKernel N s z) = characterKernel N (conj s) (conj z)) ∧
    PositiveKernel (fun s z => characterKernel N s (conj z)) ∧
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) ≤ N.totient / 2 := by
  exact ⟨fun s z hs hz => characterKernel_dirichlet_expansion N hN hN4 s z hs hz,
    characterKernel_meromorphic_left N, characterKernel_meromorphic_right N,
    fun hGRH => characterKernel_differentiableOn_of_GRH hGRH,
    fun s z => ⟨characterKernel_symmetric N s z, characterKernel_conjugation N s z⟩,
    characterKernel_positive N, characterKernel_rank_le N hN hN4⟩

end ConditionalGoldbach
