import ConditionalGoldbach.Proofs.CharacterZeroExpansion

/-! Actual principal parts of logarithmic derivatives, with their multiplicities retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace ConditionalGoldbach

lemma logDeriv_principal_part {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c)
    (n : ℤ) (hn : meromorphicOrderAt f c = n) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h c ∧
      logDeriv f =ᶠ[𝓝[≠] c] fun z => (n:ℂ)/(z-c)+h z := by
  obtain ⟨g,hg,hg0,he⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  refine ⟨logDeriv g,hg.deriv.div hg hg0,?_⟩
  have hge : ∀ᶠ z in 𝓝 c, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hde := logDeriv_congr_nhdsNE he
  filter_upwards [hde,hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hge.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with z hz hgz hgn hzc
  have hsub : z-c ≠ 0 := sub_ne_zero.mpr hzc
  rw [hz]
  change logDeriv (fun z => (z-c)^n*g z) z = _
  rw [logDeriv_fun_mul (f := fun z => (z-c)^n) (g := g) z (zpow_ne_zero _ hsub) hgn
    ((differentiableAt_id.sub_const c).zpow (Or.inl hsub)) hgz.differentiableAt,
    logDeriv_fun_zpow ((hasDerivAt_id' z).differentiableAt.sub_const c)]
  rw [logDeriv_apply,((hasDerivAt_id' z).sub_const c).deriv]
  ring

lemma logDeriv_residue_tendsto {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c)
    (n : ℤ) (hn : meromorphicOrderAt f c = n) :
    Tendsto (fun z => (z-c)*logDeriv f z) (𝓝[≠] c) (𝓝 (n:ℂ)) := by
  obtain ⟨h,hh,he⟩ := logDeriv_principal_part hf n hn
  have hlim : Tendsto (fun z => (n:ℂ)+(z-c)*h z) (𝓝[≠] c) (𝓝 (n:ℂ)) := by
    simpa using (tendsto_const_nhds.add ((tendsto_id.sub_const c).mul hh.continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [he,eventually_mem_nhdsWithin] with z hz hzc
  rw [hz]
  have hsub : z-c ≠ 0 := sub_ne_zero.mpr hzc
  field_simp

lemma deriv_logDeriv_double_pole_tendsto {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c)
    (n : ℤ) (hn : meromorphicOrderAt f c = n) :
    Tendsto (fun z => (z-c)^2*deriv (logDeriv f) z) (𝓝[≠] c) (𝓝 (-(n:ℂ))) := by
  obtain ⟨h,hh,he⟩ := logDeriv_principal_part hf n hn
  have hde := he.nhdsNE_deriv
  have hlim : Tendsto (fun z => -(n:ℂ)+(z-c)^2*deriv h z) (𝓝[≠] c) (𝓝 (-(n:ℂ))) := by
    simpa using (tendsto_const_nhds.add (((tendsto_id.sub_const c).pow 2).mul hh.deriv.continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [hde,hh.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z hz hhz hzc
  have hsub : z-c ≠ 0 := sub_ne_zero.mpr hzc
  have hd := ((hasDerivAt_const z (n:ℂ)).div ((hasDerivAt_id' z).sub_const c) hsub).add hhz.differentiableAt.hasDerivAt
  change HasDerivAt (fun w : ℂ => (n:ℂ)/(w-c)+h w) _ z at hd
  rw [hz,hd.deriv]
  field_simp
  ring

lemma LFunction_analyticOrder_ne_top {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction univ := fun z _ => (χ.differentiable_LFunction hχ).analyticAt z
  apply ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 2) (by trivial) (by trivial)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)))]
  simp

lemma LFunction_orderNat_pos_of_zero {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1)
    {ρ : ℂ} (hz : χ.LFunction ρ = 0) : 0 < analyticOrderNatAt χ.LFunction ρ := by
  have hn := LFunction_analyticOrder_ne_top χ hχ ρ
  have ha := (χ.differentiable_LFunction hχ).analyticAt ρ
  by_contra h
  have h0 : analyticOrderNatAt χ.LFunction ρ = 0 := Nat.eq_zero_of_not_pos h
  have hc : analyticOrderAt χ.LFunction ρ = 0 := by rw [← Nat.cast_analyticOrderNatAt hn,h0]; rfl
  exact ((analyticOrderAt_eq_zero.mp hc).resolve_left (not_not_intro ha)) hz

lemma poleCoefficient_pos {N : ℕ} [NeZero N] (γ : ℝ)
    (hzero : ∃ χ ∈ oddCharacters N, χ.LFunction (line (1/2) γ) = 0) :
    0 < poleCoefficient N γ := by
  obtain ⟨χ,hχ,hz⟩ := hzero
  have hm := LFunction_orderNat_pos_of_zero χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) hz
  have hmR : (0:ℝ) < analyticOrderNatAt χ.LFunction (line (1/2) γ) := by exact_mod_cast hm
  unfold poleCoefficient
  apply mul_pos (div_pos (by norm_num) (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)))
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨χ,hχ,sq_pos_of_pos hmR⟩

end ConditionalGoldbach
