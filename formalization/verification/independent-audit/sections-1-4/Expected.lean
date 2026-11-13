import LiLiuGoldbach

/-!
Independent TeX audit, sections 1--4.  This file was reconstructed from the
TeX formulas and their quantifier scopes, not from reference/Reviewed.lean.
The `expect_*` declarations are propositions, not assumed theorems.
Names from LiLiuGoldbach16 not rebuilt below are audited in coverage.json;
using their names does not by itself certify their intended mathematical meaning.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex LiLiuGoldbach16
namespace TexAudit14
attribute [local instance] Classical.propDecidable conductorNeZero

-- TeX 151--164: compact support follows from containment in the compact interval.
def Weight (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.support φ ⊆ Icc (1 / 3) (2 / 3) ∧
  (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, φ u = φ (1 - u)) ∧ φ ≠ 0
def Mass (φ : ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, φ u ^ 2
def Goldbach (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then
      mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
    else 0
-- TeX 182--185: all primitive conductors dividing N, not only odd characters.
def GRHExpected (N : ℕ) : Prop :=
  ∀ d : ℕ, ∀ (_ : NeZero d), d ∣ N → ∀ χ : DirichletCharacter ℂ d,
    χ.IsPrimitive → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      χ.LFunction ρ = 0 → ρ.re = 1 / 2
-- TeX 345--346: every asymptotic is along even integers.
def EventuallyEven (P : ℕ → Prop) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, Even N → P N
def TendsToInfinityEven (h : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, EventuallyEven (fun N => B ≤ h N)
def AsymptoticEven (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → EventuallyEven (fun N => |f N / g N - 1| < ε)
def Width (N : ℕ) (h : ℕ → ℝ) : ℝ :=
  h N ^ 2 * Real.log N ^ 3 / (N * singularSeries N)
def Admissible (h : ℕ → ℝ) : Prop :=
  (∀ N, Even N → 4 ≤ N → 0 < h N) ∧ TendsToInfinityEven h ∧
  EventuallyEven (fun N => Width N h ≤ 1 / 4)
def S (h : ℕ → ℝ) : Prop := Admissible h ∧ EventuallyEven (fun N => GRHExpected N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta),
    ∀ q : Quaternion ℝ, 1 - Width N h < q.re →
      spectralQuaternion N (@residualOperator (alpha N) ha N _hN) q ≠ 0)
def R : Prop := EventuallyEven (fun N => GRHExpected N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta),
    ∀ q : Quaternion ℝ,
      spectralQuaternion N (@residualOperator (alpha N) ha N _hN) q = 0 → q.re = 1 / 2)
def Scale (N : ℕ) : ℝ :=
  Real.sqrt (singularSeries N / N) * Real.rpow (Real.log N) (3 / 2)
def PrimeCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime ∧
    (N : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ 2 * N / 3)).card
def BetaRegion : Set (ℂ × ℂ) :=
  {p | p.1.re < 1 / 2 ∧ p.2.re < 1 / 2 ∧ 0 < (p.1 + p.2).re}
def Omega : Set (ℂ × ℂ) :=
  {p | 0 < p.1.re ∧ p.1.re < 3 / 2 ∧ 0 < p.2.re ∧ p.2.re < 3 / 2}
def BetaSigned (s z : ℂ) : ℂ :=
  betaIntegral (1 / 2 - s) (s + z) + betaIntegral (1 / 2 - z) (s + z) -
    betaIntegral (1 / 2 - s) (1 / 2 - z)
def GammaRatio (s : ℂ) : ℂ :=
  Gamma ((3 / 2 - s) / 2) / Gamma ((3 / 2 + s) / 2)
def DensityProduct (N : ℕ) (w : ℂ) : ℂ :=
  ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
    1 + (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 1
def ContinuedDensity (N : ℕ) (w : ℂ) : ℂ :=
  singularSeries N * riemannZeta w * DensityProduct N w
def Model (N : ℕ) (s z : ℂ) : ℂ :=
  (N : ℂ) ^ (-(s + z)) * ContinuedDensity N (s + z) * BetaSigned s z
def ContinuedModel (N : ℕ) (s z : ℂ) : ℂ :=
  singularSeries N * ((Real.pi : ℂ) / N) ^ (s + z) *
    DensityProduct N (s + z) * riemannZeta (1 - s - z) * GammaRatio s * GammaRatio z
def Residual (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  characterKernel N s z - diagonalSeries N (s + z) - ContinuedModel N s z

-- Adapter to the existing project's normalization. Its actual Euler-product
-- meaning is independently expanded in Bridges.singular_series_formula.
def expect_singularSeries_eq_existing : Prop := ∀ N : ℕ,
  singularSeries N = 2 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N

-- TeX 289--298. C precedes h; the eventual cutoff may follow h.
def expect_theorem_1_1 : Prop := ∀ φ : ℝ → ℝ, Weight φ →
  ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ → ℝ,
    EventuallyEven GRHExpected → S h →
    EventuallyEven (fun N => |Goldbach N φ - Mass φ * singularSeries N| ≤
      C * singularSeries N / h N) ∧
    AsymptoticEven (fun N => Goldbach N φ) (fun N => Mass φ * singularSeries N)
def expect_theorem_1_1_weight_exists : Prop := ∃ φ : ℝ → ℝ, Weight φ
-- TeX 315--323.
def expect_theorem_1_2 : Prop := ∀ φ : ℝ → ℝ, Weight φ →
  EventuallyEven GRHExpected → R →
  ∃ C : ℝ, 0 < C ∧ EventuallyEven (fun N =>
    |Goldbach N φ - Mass φ * singularSeries N| ≤ C * Scale N)
def expect_theorem_1_2_hypothesisR_implies_S : Prop :=
  R → ∀ h : ℕ → ℝ, Admissible h → S h
-- TeX 325--328. Counting the first prime counts ordered pairs (p,N-p).
def expect_primePair_consequence : Prop := ∀ φ : ℝ → ℝ, Weight φ →
  EventuallyEven GRHExpected → (R ∨ ∃ h, S h) →
  ∃ C : ℝ, 0 < C ∧ EventuallyEven (fun N =>
    C * singularSeries N * N / Real.log N ^ 2 ≤ (PrimeCount N : ℝ))
-- TeX 1090--1100.
def expect_lemma_3_1 : Prop := ∀ φ : ℝ → ℝ, Weight φ →
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
    Goldbach N φ = diagonalMoment N φ - characterMoment N φ ∧
    0 ≤ characterMoment N φ ∧ characterMoment N φ ≤ diagonalMoment N φ ∧
    diagonalMoment N φ ≤ C * Real.log N
def expect_lemma_3_1_odd_orthogonality : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → ∀ n m : ℕ,
    (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N, χ n * conj (χ m) =
      if Nat.Coprime (n * m) N then
        (if (n : ZMod N) = m then (1 : ℂ) else 0) -
          (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)
      else 0
-- TeX 1180--1200; joint meromorphy is separately checked below.
def expect_proposition_3_2 : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
    (∀ s z : ℂ, 1 / 2 < s.re → 1 / 2 < z.re →
      Summable (fun p : ℕ × ℕ => ‖arithmeticExpansionTerm N p.1 p.2 s z‖) ∧
      characterKernel N s z = ∑' p : ℕ × ℕ, arithmeticExpansionTerm N p.1 p.2 s z) ∧
    (∀ z, MeromorphicOn (fun s => characterKernel N s z) Set.univ) ∧
    (∀ s, MeromorphicOn (fun z => characterKernel N s z) Set.univ) ∧
    (GRHExpected N → DifferentiableOn ℂ (fun p : ℂ × ℂ => characterKernel N p.1 p.2)
      {p | 0 < p.1.re ∧ 0 < p.2.re}) ∧
    (∀ s z, characterKernel N s z = characterKernel N z s ∧
      conj (characterKernel N s z) = characterKernel N (conj s) (conj z)) ∧
    PositiveKernel (fun s z => characterKernel N s (conj z)) ∧
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) ≤ N.totient / 2
def expect_proposition_3_2_finite_rank : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z))))
def expect_proposition_3_2_joint_meromorphic : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
    let B : ℂ × ℂ → ℂ := fun p => ∏ χ ∈ oddCharacters N,
      χ.LFunction (1 / 2 + p.1) * χ.LFunction (1 / 2 + p.2)
    Differentiable ℂ B ∧ B ≠ 0 ∧
    (∃ A : ℂ × ℂ → ℂ, Differentiable ℂ A ∧
      ∀ p : ℂ × ℂ, B p ≠ 0 → characterKernel N p.1 p.2 = A p / B p) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => characterKernel N p.1 p.2)
      {p | ∀ χ ∈ oddCharacters N,
        χ.LFunction (1 / 2 + p.1) ≠ 0 ∧ χ.LFunction (1 / 2 + p.2) ≠ 0}
-- TeX 1247--1260: uniform constant before conductor and character; zeros counted with multiplicity.
def expect_lemma_3_3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ (_ : NeZero d), ∀ χ : Character d,
    χ.IsPrimitive → χ (-1) = -1 →
    (∀ u u₀ : ℂ, completedL χ u ≠ 0 → completedL χ u₀ ≠ 0 →
      deriv (completedL χ) u / completedL χ u -
        deriv (completedL χ) u₀ / completedL χ u₀ = zeroDifference χ u u₀) ∧
    NormallySummableOn (fun p : ZeroIndex χ => fun u : ℂ × ℂ =>
      1 / (u.1 - p.val.1) - 1 / (u.2 - p.val.1))
      {u | completedL χ u.1 ≠ 0 ∧ completedL χ u.2 ≠ 0} ∧
    (∀ t, (zeroWindow χ t).Finite ∧
      ((zeroWindow χ t).ncard : ℝ) ≤ C * Real.log (d * (|t| + 2)))
-- TeX 1274--1290. The same C works for N, χ, t; only the fixed interval is outside C.
def expect_lemma_3_4 : Prop := ∀ δ M : ℝ, 0 < δ → δ ≤ M →
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), 4 ≤ N → Even N → GRHExpected N →
    ∀ χ ∈ oddCharacters N,
    (∀ s : ℂ, 0 < s.re → logDerivative χ s =
      zeroDifference χ.primitiveCharacter (1 / 2 + s) 2 +
      deriv χ.LFunction 2 / χ.LFunction 2 -
      (deriv Gamma (3 / 4 + s / 2) / Gamma (3 / 4 + s / 2) -
        deriv Gamma (3 / 2) / Gamma (3 / 2)) / 2 +
      eulerCorrection χ (1 / 2 + s) - eulerCorrection χ 2) ∧
    (∀ σ ∈ Icc δ M, ∀ t : ℝ,
      ‖logDerivative χ (line σ t)‖ ≤ C * Real.log (N * (|t| + 2)) ^ 2)
def expect_lemma_3_4_normal_convergence : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRHExpected N →
    ∀ χ : Character N, χ ∈ oddCharacters N →
    NormallySummableOn (fun p : ZeroIndex χ.primitiveCharacter => fun s : ℂ =>
      1 / (s - p.val.1.im * I) - 1 / (3 / 2 - p.val.1.im * I)) {s | 0 < s.re}
def expect_lemma_3_4_paired_zero_sum : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRHExpected N →
    ∀ χ : Character N, χ ∈ oddCharacters N → ∀ s : ℂ, 0 < s.re →
      zeroDifference χ.primitiveCharacter (1 / 2 + s) 2 = pairedZeroSum χ s
-- TeX 1365--1380: large contour unconditional, small contour conditional, signed families and support.
def expect_lemma_3_5 : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → ∀ φ : ℝ → ℝ, Weight φ →
    ∀ σ : ℝ, 1 / 2 < σ →
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) ∧
    ∀ n m : ℕ, 0 < n → 0 < m → n ≠ m →
      (((n : ZMod N) = m) ↔
        (∃ k : ℕ, 0 < k ∧ m = n + k * N) ∨ (∃ k : ℕ, 0 < k ∧ n = m + k * N)) ∧
      (((n : ZMod N) = -(m : ZMod N)) ↔ ∃ k : ℕ, 0 < k ∧ n + m = k * N)
def expect_lemma_3_5_absolute_convergence : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → ∀ φ : ℝ → ℝ, Weight φ →
    ∀ σ : ℝ, (1 / 2 < σ ∨ (GRHExpected N ∧ 0 < σ ∧ σ ≤ 1 / 9)) →
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) * mellinWeight φ (line σ p.1) *
        mellinWeight φ (line σ p.2) * characterKernel N (line σ p.1) (line σ p.2))
def expect_lemma_3_5_small_sigma : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRHExpected N →
    ∀ φ : ℝ → ℝ, Weight φ → ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 →
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z))
def expect_lemma_3_5_weight_support : Prop :=
  ∀ N : ℕ, 0 < N → ∀ φ : ℝ → ℝ, Weight φ → ∀ n m k : ℕ,
    φ ((n : ℝ) / N) ≠ 0 → φ ((m : ℝ) / N) ≠ 0 →
    ¬positiveDifferenceFamily N n m k ∧ ¬negativeDifferenceFamily N n m k ∧
    (sumFamily N n m k ↔ k = 1 ∧ n + m = N)
-- TeX 1480--1497.
def expect_lemma_4_1 : Prop := ∀ h : ℝ, 0 < h → ∀ s z : ℂ, (s, z) ∈ BetaRegion →
  (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)) =
    (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (s + z) ∧
  (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - z) * (x + h : ℂ) ^ (-1 / 2 - s)) =
    (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - z) (s + z) ∧
  (∫ x in Ioo (0 : ℝ) h, (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)) =
    (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (1 / 2 - z)
def expect_lemma_4_1_absolute_convergence : Prop :=
  ∀ h : ℝ, 0 < h → ∀ s z : ℂ, (s, z) ∈ BetaRegion →
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (x + h : ℂ) ^ (-1 / 2 - z)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - z) *
      (x + h : ℂ) ^ (-1 / 2 - s)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (h - x : ℂ) ^ (-1 / 2 - z)) (Ioo 0 h)
def expect_lemma_4_1_signed_model : Prop :=
  ∀ h : ℝ, 0 < h → ∀ s z : ℂ, (s, z) ∈ BetaRegion →
    let I₁ := ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)
    let I₂ := ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - z) * (x + h : ℂ) ^ (-1 / 2 - s)
    let I₃ := ∫ x in Ioo (0 : ℝ) h, (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)
    I₁ + I₂ - I₃ = (h : ℂ) ^ (-(s + z)) * BetaSigned s z ∧
    ∀ N k : ℕ, Even N → 4 ≤ N → 0 < k → h = (k * N : ℕ) →
      (singularSeries (k * N) : ℂ) * (I₁ + I₂ - I₃) =
        singularSeries (k * N) * (h : ℂ) ^ (-(s + z)) * BetaSigned s z
def expect_lemma_4_1_local_density : Prop :=
  ∀ h : ℕ, Even h → 0 < h →
    (∏' p : ℕ, if p.Prime then localDensityFactor p h else 1) = singularSeries h
-- TeX 1538--1551. The bound lives on an integral domain; meromorphic extension is separate.
def expect_lemma_4_2 : Prop := ∀ s z : ℂ, (s, z) ∈ BetaRegion →
  BetaSigned s z = (2 : ℂ) ^ (1 - (s + z)) * Gamma (s + z) *
    Complex.cos (Real.pi * (s + z) / 2) * GammaRatio s * GammaRatio z ∧
  (∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 → s.re = σ → z.re = σ →
    ‖BetaSigned s z‖ ≤ ‖2 * betaIntegral (1 / 2 - σ) (2 * σ) +
      betaIntegral (1 / 2 - σ) (1 / 2 - σ)‖)
def expect_lemma_4_2_meromorphic : Prop :=
  ∃ A B : ℂ × ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧ B ≠ 0 ∧
    ∀ p : ℂ × ℂ, B p ≠ 0 →
      betaGamma (1 / 2 - p.1) (p.1 + p.2) +
        betaGamma (1 / 2 - p.2) (p.1 + p.2) -
        betaGamma (1 / 2 - p.1) (1 / 2 - p.2) = A p / B p ∧
      (2 : ℂ) ^ (1 - (p.1 + p.2)) * Gamma (p.1 + p.2) *
        Complex.cos (Real.pi * (p.1 + p.2) / 2) *
        GammaRatio p.1 * GammaRatio p.2 = A p / B p
-- TeX 1611--1630. Holomorphy off 1, absolute density convergence and uniform estimates are split.
def expect_lemma_4_3 : Prop := ∀ N : ℕ, Even N → 4 ≤ N →
  (∀ w : ℂ, 0 < w.re → Summable (fun n : ℕ =>
    if 0 < n ∧ Nat.Coprime n N then ‖(mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + w)‖ else 0)) ∧
  (∀ w : ℂ, 1 < w.re → densitySeries N w = ContinuedDensity N w) ∧
  MeromorphicOn (ContinuedDensity N) {w | 0 < w.re} ∧
  Tendsto (fun w : ℂ => (w - 1) * ContinuedDensity N w) (𝓝[≠] 1) (𝓝 ((N : ℂ) / N.totient)) ∧
  1 < singularSeries N ∧ C2 * N / N.totient ≤ singularSeries N ∧
  singularSeries N ≤ (N : ℝ) / N.totient
def expect_lemma_4_3_uniform : Prop := ∀ lo hi : ℝ, 0 < lo → lo < hi →
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Even N → 4 ≤ N →
    (∀ w : ℂ, w.re ∈ Icc lo hi → 1 ≤ |w.im| →
      ‖ContinuedDensity N w‖ ≤ C * (N : ℝ) / N.totient * (1 + |w.im|)) ∧
    (N : ℝ) / N.totient ≤ C * Real.log (Real.log N)
def expect_lemma_4_3_density_convergence : Prop := ∀ N : ℕ, Even N → 4 ≤ N →
  (∀ w : ℂ, 1 < w.re → Summable (fun k : ℕ =>
    if 0 < k then ‖(singularSeries (k * N) : ℂ) / (k : ℂ) ^ w‖ else 0)) ∧
  DifferentiableOn ℂ (ContinuedDensity N) {w | 0 < w.re ∧ w ≠ 1}
def expect_lemma_4_3_euler_product_convergence : Prop := ∀ N : ℕ, Even N → 4 ≤ N →
  NormallySummableOn (fun p : ℕ => fun w : ℂ =>
    if p.Prime ∧ 2 < p ∧ ¬p ∣ N then (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 0)
    {w | 0 < w.re} ∧
  (∀ w : ℂ, 0 < w.re → Multipliable (fun p : ℕ =>
    if p.Prime ∧ 2 < p ∧ ¬p ∣ N then 1 + (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 1)) ∧
  DifferentiableOn ℂ (DensityProduct N) {w | 0 < w.re} ∧
  DifferentiableOn ℂ (diagonalSeries N) {w | 0 < w.re}
-- TeX 1704--1710 and 1760--1768.
def expect_proposition_4_4 : Prop := ∀ N : ℕ, Even N → 4 ≤ N →
  (∀ s z : ℂ, (s, z) ∈ BetaRegion → Model N s z = ContinuedModel N s z) ∧
  DifferentiableOn ℂ (fun p : ℂ × ℂ => ContinuedModel N p.1 p.2) Omega
def expect_proposition_4_5 : Prop :=
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRHExpected N →
    DifferentiableOn ℂ (fun p : ℂ × ℂ => Residual N p.1 p.2) Omega ∧
    (∀ s z : ℂ, Residual N s z = Residual N z s ∧
      conj (Residual N s z) = Residual N (conj s) (conj z)) ∧
    HermitianKernel (fun s z => Residual N s (conj z))

end TexAudit14
