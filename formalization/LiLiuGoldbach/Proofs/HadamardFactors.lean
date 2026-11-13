import LiLiuGoldbach.Proofs.HadamardLog
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-! Finite removal of zeros with an actual entire quotient, including removable point values. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter MeromorphicOn
namespace LiLiuGoldbach16

lemma entire_order_ne_top (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (z : ℂ) :
    meromorphicOrderAt f z ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  exact ha.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial
    (by rw [(hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]; simp)

lemma entire_factorized_quotient (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (D : ℂ → ℤ) (hfin : D.HasFiniteSupport) (hD : ∀ z, 0 ≤ D z)
    (hord : ∀ z, (D z : WithTop ℤ) ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z, f z = (∏ᶠ u, (·-u)^D u) z * g z) ∧
      (∀ z, meromorphicOrderAt g z = meromorphicOrderAt f z - (D z : WithTop ℤ)) := by
  let P : ℂ → ℂ := ∏ᶠ u, (·-u)^D u
  have hP : Differentiable ℂ P := fun z => (Function.FactorizedRational.analyticAt (hD z)).differentiableAt
  have hPf (z : ℂ) : meromorphicOrderAt P z ≠ ⊤ := Function.FactorizedRational.meromorphicOrderAt_ne_top D
  have hPo (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq D hfin
  have hmero : MeromorphicOn (f/P) univ :=
    fun z _ => (hf.analyticAt z).meromorphicAt.div (hP.analyticAt z).meromorphicAt
  let g : ℂ → ℂ := toMeromorphicNFOn (f/P) univ
  have hgNF : MeromorphicNFOn g univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hgo (z : ℂ) : meromorphicOrderAt g z = meromorphicOrderAt f z - (D z : WithTop ℤ) := by
    rw [show g = toMeromorphicNFOn (f/P) univ from rfl,
      meromorphicOrderAt_toMeromorphicNFOn hmero (mem_univ z),
      meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hP.analyticAt z).meromorphicAt,hPo]
  have hg : Differentiable ℂ g := by
    intro z
    apply AnalyticAt.differentiableAt
    apply (hgNF (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [hgo]
    have hz := hord z
    lift meromorphicOrderAt f z to ℤ using entire_order_ne_top f hf hf0 z with n hn
    norm_cast at hz ⊢
    omega
  refine ⟨g,hg,?_,hgo⟩
  intro z
  have he : (fun w => P w*g w) =ᶠ[𝓝[≠] z] f := by
    filter_upwards [hmero.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z),
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hP.analyticAt z).meromorphicAt).mp (hPf z)] with w hw hn
    change g w = f w/P w at hw
    rw [hw]
    field_simp
  have h1 : Tendsto (fun w => P w*g w) (𝓝[≠] z) (𝓝 (P z*g z)) :=
    ((hP.continuous.continuousAt).mul hg.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun w => P w*g w) (𝓝[≠] z) (𝓝 (f z)) :=
    (hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm
  exact (tendsto_nhds_unique h1 h2).symm

lemma factorizedRational_eq_prod (D : ℂ → ℤ) (hfin : D.HasFiniteSupport) :
    (∏ᶠ u, (·-u)^D u) = ∏ u ∈ hfin.toFinset, (·-u)^D u := by
  apply finprod_eq_prod_of_mulSupport_subset
  rw [Function.FactorizedRational.mulSupport]
  intro z hz
  exact hfin.mem_toFinset.mpr hz

lemma factorizedRational_logDeriv (D : ℂ → ℤ) (hfin : D.HasFiniteSupport)
    (hD : ∀ u, 0 ≤ D u) (z : ℂ) (hz : (∏ᶠ u, (·-u)^D u) z ≠ 0) :
    logDeriv (∏ᶠ u, (·-u)^D u) z = ∑ u ∈ hfin.toFinset, (D u : ℂ)/(z-u) := by
  rw [factorizedRational_eq_prod D hfin] at hz ⊢
  have hn : ∀ u ∈ hfin.toFinset, ((·-u)^D u) z ≠ 0 := by
    simpa only [Finset.prod_apply,Finset.prod_ne_zero_iff] using hz
  rw [logDeriv_prod hn (fun u _ =>
    ((analyticAt_id.sub analyticAt_const).fun_zpow_nonneg (hD u)).differentiableAt)]
  apply Finset.sum_congr rfl
  intro u hu
  change logDeriv (fun z : ℂ => (z-u)^D u) z = _
  rw [logDeriv_fun_zpow (show DifferentiableAt ℂ (fun z : ℂ => z-u) z from differentiableAt_id.sub_const u) (D u),logDeriv_apply,
    show deriv (fun z : ℂ => z-u) z = 1 by simpa only [id_eq] using ((hasDerivAt_id z).sub_const u).deriv]
  ring

lemma factorizedRational_norm_lower (D : ℂ → ℤ) (hfin : D.HasFiniteSupport)
    (hD : ∀ u, 0 ≤ D u) (r : ℝ) (hsupport : ∀ u ∈ D.support, ‖u‖ ≤ r)
    (z : ℂ) (hz : 2*r ≤ ‖z‖) :
    ‖(∏ᶠ u, (·-u)^D u) 0‖ ≤ ‖(∏ᶠ u, (·-u)^D u) z‖ := by
  rw [factorizedRational_eq_prod D hfin]
  simp only [Finset.prod_apply,norm_prod,Pi.pow_apply,norm_zpow,zero_sub,norm_neg]
  apply Finset.prod_le_prod₀
  · intro u hu; positivity
  intro u hu
  apply zpow_le_zpow_left₀ (hD u) (norm_nonneg _)
  have hh := norm_add_le (z-u) u
  rw [sub_add_cancel] at hh
  have huR := hsupport u (hfin.mem_toFinset.mp hu)
  linarith

end LiLiuGoldbach16
