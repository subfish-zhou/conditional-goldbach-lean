import LiLiuGoldbach.Proofs.SpectralCompletionUniform

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem spectralPartialQuaternionReindexed_map (N : ℕ) (T : H →L[ℂ] H)
    (e : ℕ ≃ ℕ) (f : ℂ →ₐ[ℝ] Quaternion ℝ) (q : ℂ) (k : ℕ) :
    spectralPartialQuaternionReindexed N T e (f q) k =
      f (∏ j ∈ Finset.range k,
        (1 - (4 * eigenvalues T (e j) ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))) := by
  induction k with
  | zero => simp [spectralPartialQuaternionReindexed]
  | succ k ih =>
    have hrec : spectralPartialQuaternionReindexed N T e (f q) (k + 1) =
        spectralPartialQuaternionReindexed N T e (f q) k *
        (1 - (4 * eigenvalues T (e k) ^ 2 / spectralScale N ^ 2 : ℝ) * f q * (1 - f q)) := by
      simp [spectralPartialQuaternionReindexed, List.range_succ, List.foldl_append]
    rw [hrec, ih, Finset.prod_range_succ, map_mul]
    congr 1
    rw [← spectralFactor_map]
    simp only [Quaternion.coe_mul_eq_smul, Algebra.smul_mul_assoc]

theorem spectralQuaternion_reindexed_compactUniformLimit (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (e : ℕ ≃ ℕ) :
    CompactUniformLimit (fun k q => spectralPartialQuaternionReindexed N T e q k)
      (spectralQuaternion N T) := by
  intro K hK ε hε
  obtain ⟨B, _, hKB⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hu := spectralComplex_hasProdUniformlyOn N T hT
    (Metric.closedBall 0 B) (isCompact_closedBall 0 B)
  have he : HasProdUniformlyOn (fun j (q : ℂ) =>
      1 - (4 * eigenvalues T (e j) ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))
      (spectralComplex N T) (Metric.closedBall 0 B) := by
    exact (e.hasProd_iff).2 hu
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.1 he.tendstoUniformlyOn_finsetRange) ε hε)
  refine ⟨n₀, fun n hn q hq => ?_⟩
  obtain ⟨f, z, rfl⟩ := quaternion_exists_complex_slice q
  have hz : z ∈ Metric.closedBall 0 B := by
    have := hKB hq
    simpa only [Metric.mem_closedBall, dist_zero_right, quaternion_algHom_norm] using this
  have hh := hn₀ n hn z hz
  dsimp only
  rw [spectralPartialQuaternionReindexed_map, spectralQuaternion_apply_algHom N T hT,
    ← map_sub, quaternion_algHom_norm]
  simpa only [dist_eq_norm, norm_sub_rev] using hh

theorem proposition_6_1_enumeration (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (e : ℕ ≃ ℕ) :
    CompactUniformLimit (fun k q =>
      spectralPartialQuaternionReindexed N (residualOperator ha N) e q k)
      (spectralQuaternion N (residualOperator ha N)) ∧
    (∀ q : ℂ, (∏' j : ℕ,
      (1 - (4 * eigenvalues (residualOperator ha N) (e j) ^ 2 / spectralScale N ^ 2 : ℝ) *
        q * (1 - q))) = spectralComplex N (residualOperator ha N) q) := by
  have hT := (proposition_5_3 N hN hlarge hGRH ha).2.2.2.2.2.1
  refine ⟨spectralQuaternion_reindexed_compactUniformLimit N _ hT e, ?_⟩
  intro q
  unfold spectralComplex
  exact e.tprod_eq (fun j => 1 - (4 * eigenvalues (residualOperator ha N) j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))

theorem quaternion_centered_factor (a : ℝ) (ξ : Quaternion ℝ) :
    1 - (4 * a) • (((1 / 2 : Quaternion ℝ) + ξ) * (1 - (1 / 2 + ξ))) =
      1 - (a : Quaternion ℝ) + (4 * a : ℝ) * ξ ^ 2 := by
  have hhalf : (1 / 2 : Quaternion ℝ) = ((1 / 2 : ℝ) : Quaternion ℝ) := by
    rw [Quaternion.coe_div]; rfl
  rw [hhalf]
  ext <;> simp [pow_two, -Quaternion.coe_div, -Quaternion.coe_inv] <;> ring

theorem spectralPartialQuaternion_centered (N : ℕ) (T : H →L[ℂ] H)
    (ξ : Quaternion ℝ) (k : ℕ) :
    spectralPartialQuaternion N T (1 / 2 + ξ) k = centeredSpectralPartial N T ξ k := by
  have hf (j : ℕ) :
      1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) •
        (((1 / 2 : Quaternion ℝ) + ξ) * (1 - (1 / 2 + ξ))) =
      1 - (eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) +
        (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * ξ ^ 2 := by
    simpa only [mul_div_assoc] using
      quaternion_centered_factor (eigenvalues T j ^ 2 / spectralScale N ^ 2) ξ
  simp only [spectralPartialQuaternion, centeredSpectralPartial, hf]

theorem spectralQuaternion_centered_compactUniformLimit (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) :
    CompactUniformLimit (fun k ξ => centeredSpectralPartial N T ξ k)
      (fun ξ => spectralQuaternion N T (1 / 2 + ξ)) := by
  intro K hK ε hε
  have hc : Continuous (fun ξ : Quaternion ℝ => 1 / 2 + ξ) := continuous_const.add continuous_id
  obtain ⟨n₀, hn₀⟩ := spectralQuaternion_compactUniformLimit N T hT _ (hK.image hc) ε hε
  refine ⟨n₀, fun n hn ξ hξ => ?_⟩
  simpa only [spectralPartialQuaternion_centered] using hn₀ n hn (1 / 2 + ξ) ⟨ξ, hξ, rfl⟩

theorem proposition_6_2_centered_product (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    CompactUniformLimit (fun k ξ => centeredSpectralPartial N (residualOperator ha N) ξ k)
      (fun ξ => spectralQuaternion N (residualOperator ha N) (1 / 2 + ξ)) := by
  have hT := (proposition_5_3 N hN hlarge hGRH ha).2.2.2.2.2.1
  exact spectralQuaternion_centered_compactUniformLimit N _ hT

/-- The critical-hyperplane product is real and independent of the imaginary unit. -/
theorem spectralQuaternion_critical_values (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (J : Quaternion ℝ) (hJre : J.re = 0)
    (hJnorm : ‖J‖ = 1) (t : ℝ) :
    Multipliable (fun j : ℕ => (1 - eigenvalues T j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2) : ℝ)) ∧
    spectralQuaternion N T ((1 / 2 : Quaternion ℝ) + t • J) =
      ((∏' j : ℕ, (1 - eigenvalues T j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2)) : ℝ) : Quaternion ℝ) := by
  have hnormSq : Quaternion.normSq J = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hJnorm]; norm_num
  have hJsq : J * J = -1 := by
    have := (Quaternion.sq_eq_neg_normSq (a := J)).2 hJre
    simpa only [hnormSq, pow_two, Quaternion.coe_one] using this
  let f := Complex.liftAux J hJsq
  let z : ℂ := ⟨1 / 2, t⟩
  have hfz : f z = (1 / 2 : Quaternion ℝ) + t • J := by
    change ((1 / 2 : ℝ) : Quaternion ℝ) + t • J = _
    rw [Quaternion.coe_div]; rfl
  have hz : z * (1 - z) = ((1 + 4 * t ^ 2) / 4 : ℝ) := by
    apply Complex.ext
    · change (z * (1 - z)).re = (1 + 4 * t ^ 2) / 4
      simp [z]
      <;> ring
    · change (z * (1 - z)).im = 0
      simp [z]
      <;> ring
  have hs := (((eigenvalues_square_summable T hT).mul_right
    (spectralScale N ^ 2)⁻¹).mul_right (1 + 4 * t ^ 2)).neg
  have hm : Multipliable (fun j : ℕ => (1 - eigenvalues T j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2) : ℝ)) := by
    simpa only [sub_eq_add_neg, div_eq_mul_inv] using Real.multipliable_one_add_of_summable hs
  refine ⟨hm, ?_⟩
  have hmap := hm.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  change ((∏' j : ℕ, (1 - eigenvalues T j ^ 2 / spectralScale N ^ 2 * (1 + 4 * t ^ 2)) : ℝ) : ℂ) =
    ∏' j : ℕ, ((1 - eigenvalues T j ^ 2 / spectralScale N ^ 2 * (1 + 4 * t ^ 2) : ℝ) : ℂ) at hmap
  have hp : spectralComplex N T z =
      ((∏' j : ℕ, (1 - eigenvalues T j ^ 2 / spectralScale N ^ 2 * (1 + 4 * t ^ 2)) : ℝ) : ℂ) := by
    rw [hmap]
    apply tprod_congr
    intro j
    change 1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * z * (1 - z) = _
    rw [mul_assoc, hz]
    push_cast
    ring
  rw [← hfz, spectralQuaternion_apply_algHom N T hT, hp]
  exact f.commutes _

theorem proposition_6_2_critical_values (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta)
    (J : Quaternion ℝ) (hJre : J.re = 0) (hJnorm : ‖J‖ = 1) (t : ℝ) :
    Multipliable (fun j : ℕ => (1 - eigenvalues (residualOperator ha N) j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2) : ℝ)) ∧
    spectralQuaternion N (residualOperator ha N) ((1 / 2 : Quaternion ℝ) + t • J) =
      ((∏' j : ℕ, (1 - eigenvalues (residualOperator ha N) j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2)) : ℝ) : Quaternion ℝ) := by
  have hT := (proposition_5_3 N hN hlarge hGRH ha).2.2.2.2.2.1
  exact spectralQuaternion_critical_values N _ hT J hJre hJnorm t

end LiLiuGoldbach16
