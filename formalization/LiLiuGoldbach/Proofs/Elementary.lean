import LiLiuGoldbach.Definitions

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable conductorNeZero

theorem singularSeries_eq_existing (N : ℕ) :
    singularSeries N = 2 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N := rfl

theorem singularSeries_pos (N : ℕ) : 0 < singularSeries N := by
  exact mul_pos (by norm_num) (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N)

theorem singularSeries_uniform_lower (N : ℕ) : 2 * C2 ≤ singularSeries N := by
  exact mul_le_mul_of_nonneg_left
    (MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_le_liuSingularSeries N) (by norm_num)

theorem C2_pos : 0 < C2 := MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_pos

theorem EvenEventually.mono {P Q : ℕ → Prop} (hP : EvenEventually P)
    (hPQ : ∀ N, P N → Q N) : EvenEventually Q := by
  obtain ⟨n, hn⟩ := hP
  exact ⟨n, fun N hN he => hPQ N (hn N hN he)⟩

theorem EvenEventually.and {P Q : ℕ → Prop} (hP : EvenEventually P)
    (hQ : EvenEventually Q) : EvenEventually (fun N => P N ∧ Q N) := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  exact ⟨max p q, fun N hN he =>
    ⟨hp N (le_trans (le_max_left _ _) hN) he,
      hq N (le_trans (le_max_right _ _) hN) he⟩⟩

theorem EvenEventually.of_forall {P : ℕ → Prop} (h : ∀ N, P N) : EvenEventually P :=
  ⟨0, fun N _ _ => h N⟩

theorem evenEventually_large : EvenEventually (fun N => Real.exp 10 < (N : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp 10)
  exact ⟨n, fun N hN _ => lt_of_lt_of_le hn (by exact_mod_cast hN)⟩

theorem large_parameters {N : ℕ} (hlarge : Real.exp 10 < (N : ℝ)) :
    4 ≤ N ∧ 0 < Real.log (N : ℝ) ∧ alpha N < beta := by
  have hten : (10 : ℝ) < Real.log (N : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 10) hlarge
    simpa using h
  have hexp : (11 : ℝ) ≤ Real.exp 10 := by simpa only [show (10 : ℝ) + 1 = 11 by norm_num] using Real.add_one_le_exp (10 : ℝ)
  have hN4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  refine ⟨hN4, by linarith, ?_⟩
  dsimp [alpha, beta]
  exact (div_lt_div_iff₀ (by linarith : (0 : ℝ) < Real.log N) (by norm_num : (0 : ℝ) < 8)).2 (by linarith)

end LiLiuGoldbach16
