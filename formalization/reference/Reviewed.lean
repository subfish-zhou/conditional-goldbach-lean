import Mathlib
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
Statement preparation for Li–Liu, ConditionalGoldbach.pdf (63 pages).
All proof bodies are deliberately `sorry` for the author's review.
Existence lemmas used to define analytic objects are also review obligations.
No theorem here is claimed proved. Existing project sources are read-only.
- Mathematical inner products in the PDF are linear in the first argument.
  `paperInner u v = inner v u` converts Mathlib's convention.
- `HardySpace` uses the weighted Fourier–Laplace realization of Lemma 5.2.
  The equivalence with the raw holomorphic definition is an explicit obligation.
- Totalized choices return zero outside their specified existence domains.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex

namespace ConditionalGoldbach

attribute [local instance] Classical.propDecidable

abbrev Character (N : ℕ) := DirichletCharacter ℂ N

local instance conductorNeZero {N : ℕ} [NeZero N] (χ : Character N) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
abbrev mangoldt := ArithmeticFunction.vonMangoldt
abbrev prime (n : ℕ) := Nat.Prime n

def IsWeight (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.support φ ⊆ Icc (1 / 3) (2 / 3) ∧
  (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, φ u = φ (1 - u)) ∧ φ ≠ 0

def companion (φ : ℝ → ℝ) (u : ℝ) : ℝ := Real.sqrt u * φ u

def derivativeWeight (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  companion φ u - u * deriv (companion φ) u

def weightMass (φ : ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, φ u ^ 2

def C2 : ℝ := MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct

def singularSeries (N : ℕ) : ℝ :=
  2 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N

/-- Existing source normalization to review against the paper's factor 2. -/
theorem singularSeries_eq_existing (N : ℕ) :
    singularSeries N = 2 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N := by sorry

def goldbach (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then
      mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
    else 0

def diagonalMoment (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    if Nat.Coprime n N then (mangoldt n) ^ 2 * φ (n / N) ^ 2 else 0

def oddCharacters (N : ℕ) [NeZero N] : Finset (Character N) :=
  Finset.univ.filter (fun χ => χ (-1) = -1)

def characterPolynomial {N : ℕ} (χ : Character N) (φ : ℝ → ℝ) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    (mangoldt n : ℂ) * χ n * (φ (n / N) : ℂ)

def characterMoment (N : ℕ) [NeZero N] (φ : ℝ → ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N, ‖characterPolynomial χ φ‖ ^ 2

def GRH (N : ℕ) : Prop :=
  ∀ d : ℕ, ∀ (_ : NeZero d), d ∣ N → ∀ χ : Character d, χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1 / 2

def logDerivative {N : ℕ} [NeZero N] (χ : Character N) (s : ℂ) : ℂ :=
  deriv χ.LFunction (1 / 2 + s) / χ.LFunction (1 / 2 + s)

def characterKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    logDerivative χ s * conj (logDerivative χ (conj z))

def diagonalSeries (N : ℕ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, if 0 < n ∧ Nat.Coprime n N then
    (mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + w) else 0

def densitySeries (N : ℕ) (w : ℂ) : ℂ :=
  ∑' k : ℕ, if 0 < k then (singularSeries (k * N) : ℂ) / (k : ℂ) ^ w else 0

def densityEulerProduct (N : ℕ) (w : ℂ) : ℂ :=
  ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
    1 + (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 1

def continuedDensity (N : ℕ) (w : ℂ) : ℂ :=
  singularSeries N * riemannZeta w * densityEulerProduct N w

def betaKernel (s z : ℂ) : ℂ :=
  betaIntegral (1 / 2 - s) (s + z) + betaIntegral (1 / 2 - z) (s + z) -
    betaIntegral (1 / 2 - s) (1 / 2 - z)

def gammaQuotient (s : ℂ) : ℂ :=
  Gamma ((3 / 2 - s) / 2) / Gamma ((3 / 2 + s) / 2)

def betaModel (N : ℕ) (s z : ℂ) : ℂ :=
  (N : ℂ) ^ (-(s + z)) * continuedDensity N (s + z) * betaKernel s z

def continuedModel (N : ℕ) (s z : ℂ) : ℂ :=
  singularSeries N * ((Real.pi : ℂ) / N) ^ (s + z) *
    densityEulerProduct N (s + z) * riemannZeta (1 - s - z) *
    gammaQuotient s * gammaQuotient z

def residual (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  characterKernel N s z - diagonalSeries N (s + z) - continuedModel N s z

def analyticDomain : Set (ℂ × ℂ) :=
  {p | 0 < p.1.re ∧ p.1.re < 3 / 2 ∧ 0 < p.2.re ∧ p.2.re < 3 / 2}

def betaDomain : Set (ℂ × ℂ) :=
  {p | p.1.re < 1 / 2 ∧ p.2.re < 1 / 2 ∧ 0 < (p.1 + p.2).re}

def alpha (N : ℕ) (c : ℝ := 1) : ℝ := c / Real.log N

def beta : ℝ := 1 / 8

def sigmaStar : ℝ := 1 / 9

def width (a : ℝ) : ℝ := beta - a

def strip (a b : ℝ) : Set ℂ := {s | a < s.re ∧ s.re < b}

def line (x t : ℝ) : ℂ := (x : ℂ) + t * I

def boundaryIntegral (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t : ℝ, f (line a t)) + ∫ t : ℝ, f (line b t)

def mellinWeight (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun u => (companion φ u : ℂ)) s

/-- Oriented vertical integral divided by 2πi, written in the height coordinate. -/
def verticalMellin (σ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, f (line σ t)

def residualIntegral (N : ℕ) [NeZero N] (φ : ℝ → ℝ) (σ : ℝ) : ℂ :=
  verticalMellin σ (fun s => verticalMellin σ (fun z =>
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * residual N s z))

def differenceConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), φ u * φ (u + y)

def sumConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), φ u * φ (y - u)

def signedConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * differenceConvolution φ y - sumConvolution φ y

def hardyWeight (a b τ : ℝ) : ℝ := Real.exp (2 * a * τ) + Real.exp (2 * b * τ)

def hardyMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ))

abbrev HardySpace (a b : ℝ) := Lp ℂ 2 (hardyMeasure a b)

def fourierLaplace {a b : ℝ} (ψ : HardySpace a b) (s : ℂ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * ∫ τ : ℝ, ψ τ * Complex.exp (s * τ)

def IsRawHardy (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (strip a b) ∧
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < (b - a) / 2 →
      Integrable (fun t : ℝ => ‖f (line (a + ε) t)‖ ^ 2 +
        ‖f (line (b - ε) t)‖ ^ 2) ∧
      (∫ t : ℝ, ‖f (line (a + ε) t)‖ ^ 2 + ‖f (line (b - ε) t)‖ ^ 2) ≤ C

/-- Raw Hardy norm squared, with the two boundary terms paired as in (5.1). -/
def rawHardyNormSq (a b : ℝ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ ε : ℝ, 0 < ε ∧ ε < (b - a) / 2 ∧
    r = ∫ t : ℝ, ‖f (line (a + ε) t)‖ ^ 2 + ‖f (line (b - ε) t)‖ ^ 2}

theorem interiorLine_memLp {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Ioo a b) (ψ : HardySpace a b) :
    MemLp (fun t : ℝ => fourierLaplace ψ (line x t)) 2 volume := by sorry

def interiorLine {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (x : ℝ) (hx : x ∈ Ioo a b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (interiorLine_memLp hab hx ψ).toLp _

/-- Boundary traces are defined through L2 limits, including the limit's side. -/
def IsBoundaryTrace {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (left right : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  Tendsto (fun x : Ioo a b => interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 left) ∧
  Tendsto (fun x : Ioo a b => interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 right)

theorem boundaryTraces_exist {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    ∃ p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ),
      IsBoundaryTrace hab ψ p.1 p.2 := by sorry

def boundaryTraces {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :=
  Classical.choose (boundaryTraces_exist hab ψ)

def paperInner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : H) : ℂ := inner ℂ v u

def weightedKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  residual N s (conj z) / ((1 + s) * (1 + conj z))

def kernelAction {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (h : HardySpace a beta) (s : ℂ) : ℂ :=
  (∫ t : ℝ, K s (line a t) * (boundaryTraces ha h).1 t) +
  ∫ t : ℝ, K s (line beta t) * (boundaryTraces ha h).2 t

def RepresentsKernel {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (T : HardySpace a beta →L[ℂ] HardySpace a beta) : Prop :=
  ∀ h s, s ∈ strip a beta → fourierLaplace (T h) s = kernelAction ha N K h s

/-- Concrete integral-kernel operator, totalized by zero if no bounded realization exists. -/
def kernelOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) : HardySpace a beta →L[ℂ] HardySpace a beta :=
  if h : ∃ T, RepresentsKernel ha N K T then Classical.choose h else 0

def residualOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (weightedKernel N)

def arithmeticOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (fun s z => characterKernel N s (conj z) / ((1 + s) * (1 + conj z)))

def diagonalOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (fun s z => diagonalSeries N (s + conj z) / ((1 + s) * (1 + conj z)))

def modelOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (fun s z => continuedModel N s (conj z) / ((1 + s) * (1 + conj z)))

/-- Countably infinite Hilbert-space model used for Hardy spaces. Finite matrices in B.5
are handled separately. The index ℕ here is deliberate, not a general library API. -/
def IsHilbertSchmidt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => ‖T (b j)‖ ^ 2)

def hsNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : ℝ :=
  if h : ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => ‖T (b j)‖ ^ 2)
  then Real.sqrt (∑' j, ‖T ((Classical.choose h) j)‖ ^ 2) else 0

def IsPositiveTraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  T.IsSymmetric ∧ (∀ x, 0 ≤ (paperInner (T x) x).re) ∧
  ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => (paperInner (T (b j)) (b j)).re)

def positiveTrace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : ℝ :=
  if h : ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => (paperInner (T (b j)) (b j)).re)
  then ∑' j, (paperInner (T ((Classical.choose h) j)) ((Classical.choose h) j)).re else 0

/-- Full eigenbasis includes zero eigenvalues, so multiplicities are fixed by a basis. -/
structure SpectralData {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) where
  basis : HilbertBasis ℕ ℂ H
  values : ℕ → ℝ
  diagonal : ∀ j, T (basis j) = (values j : ℂ) • basis j
  squareSummable : Summable (fun j => values j ^ 2)

def eigenvalues {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : ℕ → ℝ :=
  if h : Nonempty (SpectralData T) then (Classical.choice h).values else 0

def spectralScale (N : ℕ) : ℝ :=
  Real.sqrt (singularSeries N / N) * Real.rpow (Real.log N) (3 / 2)

def spectralComplex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (q : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))

def spectralPartialQuaternion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (q : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun z j =>
    z * (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) • (q * (1 - q)))) 1

def spectralQuaternion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (q : Quaternion ℝ) : Quaternion ℝ :=
  if h : ∃ y, Tendsto (spectralPartialQuaternion N T q) atTop (𝓝 y)
  then Classical.choose h else 0

def RealizationValid (N : ℕ) (a : ℝ) : Prop :=
  Even N ∧ 4 ≤ N ∧ GRH N ∧ 0 < a ∧ a < 1 / 10

def normFunctional (N : ℕ) (φ : ℝ → ℝ) (a : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in Ioi (0 : ℝ),
    Real.rpow (N * u) (2 * a) * derivativeWeight φ u ^ 2 /
      (1 + Real.rpow (N * u) (-2 * (beta - a))) / u

def weightEnergy (φ : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in Ioi (0 : ℝ), derivativeWeight φ u ^ 2 / u

def functionalValue {a : ℝ} (N : ℕ) (φ : ℝ → ℝ) (σ : ℝ)
    (h : HardySpace a beta) : ℂ :=
  verticalMellin σ (fun s => (N : ℂ) ^ s * mellinWeight φ s * (1 + s) * fourierLaplace h s)

def rieszVector {a : ℝ} (N : ℕ) (φ : ℝ → ℝ) : HardySpace a beta :=
  if h : ∃ v : HardySpace a beta, ∀ f,
      functionalValue N φ sigmaStar f = paperInner f v
  then Classical.choose h else 0

def evaluationVector {a b : ℝ} (s : ℂ) : HardySpace a b :=
  if h : ∃ v : HardySpace a b, ∀ f, fourierLaplace f s = paperInner f v
  then Classical.choose h else 0

def pointDistance (a b : ℝ) (s : ℂ) : ℝ := min (s.re - a) (b - s.re)

def reproducingKernel (a b : ℝ) (s z : ℂ) : ℂ :=
  (4 * ((b - a : ℝ) : ℂ))⁻¹ /
    Complex.sin ((Real.pi : ℂ) * (s + conj z - 2 * a) / (2 * (b - a : ℝ)))

def zeroFreeWidth (N : ℕ) (h : ℕ → ℝ) : ℝ :=
  h N ^ 2 * Real.log N ^ 3 / (N * singularSeries N)

def EvenEventually (P : ℕ → Prop) : Prop := ∃ N₀ : ℕ, ∀ N ≥ N₀, Even N → P N

def EvenTendstoInfinity (h : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, EvenEventually (fun N => B ≤ h N)

def IsAdmissible (h : ℕ → ℝ) : Prop :=
  (∀ N, Even N → 4 ≤ N → 0 < h N) ∧ EvenTendstoInfinity h ∧
  EvenEventually (fun N => zeroFreeWidth N h ≤ 1 / 4)

/-- Totalized scalar width condition at arbitrary left endpoint. -/
def SpectralR (N : ℕ) [NeZero N] (a : ℝ) (ha : a < beta) : Prop :=
  ∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 → q.re = 1 / 2

def SpectralZeroFree (N : ℕ) [NeZero N] (a : ℝ) (ha : a < beta) (η : ℝ) : Prop :=
  ∀ q : Quaternion ℝ, 1 - η < q.re → spectralQuaternion N (residualOperator ha N) q ≠ 0

/-- Hypotheses preserve GRH(N) as an implication in the eventual spectral condition. -/
def HypothesisR : Prop := EvenEventually (fun N => GRH N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta), @SpectralR N _hN (alpha N) ha)

def HypothesisS (h : ℕ → ℝ) : Prop := IsAdmissible h ∧ EvenEventually (fun N => GRH N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta),
    @SpectralZeroFree N _hN (alpha N) ha (zeroFreeWidth N h))

def PrimePairCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime ∧
    (N : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ 2 * N / 3)).card

/-- Nontrivial zero index with multiplicity, using Mathlib's analytic order. -/
def ZeroIndex {d : ℕ} [NeZero d] (χ : Character d) :=
  {p : ℂ × ℕ // 0 < p.1.re ∧ p.1.re < 1 ∧ χ.LFunction p.1 = 0 ∧
    p.2 < analyticOrderNatAt χ.LFunction p.1}

def completedL {d : ℕ} [NeZero d] (χ : Character d) (u : ℂ) : ℂ :=
  (d : ℂ) ^ ((u + 1) / 2) * χ.completedLFunction u

def zeroDifference {d : ℕ} [NeZero d] (χ : Character d) (u u₀ : ℂ) : ℂ :=
  ∑' p : ZeroIndex χ, (1 / (u - p.val.1) - 1 / (u₀ - p.val.1))

def eulerCorrection {N : ℕ} [NeZero N] (χ : Character N) (u : ℂ) : ℂ :=
  ∑ p ∈ N.primeFactors, if ¬p ∣ χ.conductor then
    χ.primitiveCharacter p * (Real.log p : ℂ) /
      ((p : ℂ) ^ u - χ.primitiveCharacter p) else 0

def zeroPoisson {N : ℕ} [NeZero N] (χ : Character N) (x t : ℝ) : ℝ :=
  ∑' p : ZeroIndex χ.primitiveCharacter, x / (x ^ 2 + (t - p.val.1.im) ^ 2)

def averagedLogDerivative (N : ℕ) [NeZero N] (σ : ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    ∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)

/-- Absolute locally uniform convergence criterion used for zero expansions. -/
def NormallySummableOn {ι X : Type*} [TopologicalSpace X]
    (f : ι → X → ℂ) (U : Set X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ U →
    (∀ i, BddAbove {r : ℝ | ∃ x ∈ K, r = ‖f i x‖}) ∧
    Summable (fun i => sSup {r : ℝ | ∃ x ∈ K, r = ‖f i x‖})

def HermitianKernel (K : ℂ → ℂ → ℂ) : Prop := ∀ s z, K s z = conj (K z s)

def PositiveKernel (K : ℂ → ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∀ points coefficients : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, coefficients i * conj (coefficients j) * K (points i) (points j)).re

def BoundaryKernelSquareIntegral (a b : ℝ) (K : ℂ → ℂ → ℂ) : ℝ :=
  ∑ x ∈ ({a, b} : Finset ℝ), ∑ y ∈ ({a, b} : Finset ℝ),
    ∫ t : ℝ, ∫ u : ℝ, ‖K (line x t) (line y u)‖ ^ 2

def IntrinsicEntire (F : Quaternion ℝ → Quaternion ℝ) : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ z, f (conj z) = conj (f z)) ∧
    ∀ J : Quaternion ℝ, J.re = 0 → J ^ 2 = -1 → ∀ z : ℂ,
      F ((z.re : Quaternion ℝ) + z.im • J) = (f z).re + (f z).im • J

def CompactUniformLimit {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    (f : ℕ → X → Y) (g : X → Y) : Prop :=
  ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ n₀, ∀ n ≥ n₀, ∀ x ∈ K, ‖f n x - g x‖ < ε

def EvenAsymptotic (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → EvenEventually (fun N => |f N / g N - 1| < ε)

def spectralWidthFromBound (N : ℕ) (M : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - spectralScale N ^ 2 / M ^ 2)) / 2

-- Section 1. Quantifier order keeps C independent of the prescribed h.
/-- Nonvacuity obligation: the paper requires a nonzero smooth compactly supported weight.
The smooth order is the inner top in ℕ∞, not the analytic top in ℕ∞ω. -/
theorem theorem_1_1_weight_exists : ∃ φ : ℝ → ℝ, IsWeight φ := by sorry

theorem theorem_1_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ → ℝ,
      EvenEventually GRH → HypothesisS h →
      EvenEventually (fun N => |goldbach N φ - weightMass φ * singularSeries N| ≤
        C * singularSeries N / h N) ∧
      EvenAsymptotic (fun N => goldbach N φ) (fun N => weightMass φ * singularSeries N) := by sorry

theorem theorem_1_2 (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (hGRH : EvenEventually GRH) (hR : HypothesisR) :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N) := by sorry

/-- The implication stated immediately after Hypothesis R, before Theorem 1.2. -/
theorem theorem_1_2_hypothesisR_implies_S (hR : HypothesisR)
    (h : ℕ → ℝ) (hh : IsAdmissible h) : HypothesisS h := by sorry

/-- Unnumbered prime-pair consequence following Theorems 1.1 and 1.2. -/
theorem primePair_consequence (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (hGRH : EvenEventually GRH) (hSpectral : HypothesisR ∨ ∃ h, HypothesisS h) :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      C * singularSeries N * N / Real.log N ^ 2 ≤ (PrimePairCount N : ℝ)) := by sorry

-- Section 3.
theorem lemma_3_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : NeZero N), Even N → 4 ≤ N →
      goldbach N φ = diagonalMoment N φ - characterMoment N φ ∧
      0 ≤ characterMoment N φ ∧ characterMoment N φ ≤ diagonalMoment N φ ∧
      diagonalMoment N φ ≤ C * Real.log N := by sorry

/-- The odd-character projector (gb:orthogonality), the direct dependency of the
finite projection. All characters, including imprimitive ones, are retained;
zero extension at nonunits is expressed by the coprimality condition. -/
theorem lemma_3_1_odd_orthogonality (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (n m : ℕ) :
    (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N, χ n * conj (χ m) =
      if Nat.Coprime (n * m) N then
        (if (n : ZMod N) = m then (1 : ℂ) else 0) -
          (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)
      else 0 := by sorry

def arithmeticExpansionTerm (N n m : ℕ) (s z : ℂ) : ℂ :=
  if 0 < n ∧ 0 < m ∧ Nat.Coprime (n * m) N then
    (mangoldt n : ℂ) * mangoldt m / ((n : ℂ) ^ (1 / 2 + s) * (m : ℂ) ^ (1 / 2 + z)) *
      ((if (n : ZMod N) = m then 1 else 0) -
        (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)) else 0

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
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) ≤ N.totient / 2 := by sorry

def zeroWindow {d : ℕ} [NeZero d] (χ : Character d) (t : ℝ) : Set (ZeroIndex χ) :=
  {p | t ≤ p.val.1.im ∧ p.val.1.im < t + 1}

theorem lemma_3_3 : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ (_ : NeZero d), ∀ χ : Character d,
    χ.IsPrimitive → χ (-1) = -1 →
    (∀ u u₀ : ℂ, completedL χ u ≠ 0 → completedL χ u₀ ≠ 0 →
      deriv (completedL χ) u / completedL χ u -
        deriv (completedL χ) u₀ / completedL χ u₀ = zeroDifference χ u u₀) ∧
    NormallySummableOn (fun p : ZeroIndex χ => fun u : ℂ × ℂ =>
      1 / (u.1 - p.val.1) - 1 / (u.2 - p.val.1))
      {u | completedL χ u.1 ≠ 0 ∧ completedL χ u.2 ≠ 0} ∧
    (∀ t, (zeroWindow χ t).Finite ∧
      ((zeroWindow χ t).ncard : ℝ) ≤ C * Real.log (d * (|t| + 2))) := by sorry

theorem lemma_3_4 (δ M : ℝ) (hδ : 0 < δ) (hM : δ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), 4 ≤ N → Even N → GRH N →
      ∀ χ ∈ oddCharacters N,
      (∀ s : ℂ, 0 < s.re → logDerivative χ s =
        zeroDifference χ.primitiveCharacter (1 / 2 + s) 2 +
        deriv χ.LFunction 2 / χ.LFunction 2 -
        (deriv Gamma (3 / 4 + s / 2) / Gamma (3 / 4 + s / 2) -
          deriv Gamma (3 / 2) / Gamma (3 / 2)) / 2 +
        eulerCorrection χ (1 / 2 + s) - eulerCorrection χ 2) ∧
      (∀ σ ∈ Icc δ M, ∀ t : ℝ,
        ‖logDerivative χ (line σ t)‖ ≤ C * Real.log (N * (|t| + 2)) ^ 2) := by sorry

theorem lemma_3_5 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) ∧
    ∀ n m : ℕ, 0 < n → 0 < m → n ≠ m →
      (((n : ZMod N) = m) ↔
        (∃ k : ℕ, 0 < k ∧ m = n + k * N) ∨ (∃ k : ℕ, 0 < k ∧ n = m + k * N)) ∧
      (((n : ZMod N) = -(m : ZMod N)) ↔ ∃ k : ℕ, 0 < k ∧ n + m = k * N) := by sorry

-- Section 4.
theorem lemma_4_1 (h : ℝ) (hh : 0 < h) (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (s + z) ∧
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - z) * (x + h : ℂ) ^ (-1 / 2 - s)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - z) (s + z) ∧
    (∫ x in Ioo (0 : ℝ) h, (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (1 / 2 - z) := by sorry

theorem lemma_4_2 (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    betaKernel s z = (2 : ℂ) ^ (1 - (s + z)) * Gamma (s + z) *
      Complex.cos (Real.pi * (s + z) / 2) * gammaQuotient s * gammaQuotient z ∧
    (∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 → s.re = σ → z.re = σ →
      ‖betaKernel s z‖ ≤ ‖2 * betaIntegral (1 / 2 - σ) (2 * σ) +
        betaIntegral (1 / 2 - σ) (1 / 2 - σ)‖) := by sorry

theorem lemma_4_3 (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∀ w : ℂ, 0 < w.re → Summable (fun n : ℕ =>
      if 0 < n ∧ Nat.Coprime n N then ‖(mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + w)‖ else 0)) ∧
    (∀ w : ℂ, 1 < w.re → densitySeries N w = continuedDensity N w) ∧
    MeromorphicOn (continuedDensity N) {w | 0 < w.re} ∧
    Tendsto (fun w : ℂ => (w - 1) * continuedDensity N w) (𝓝[≠] 1) (𝓝 ((N : ℂ) / N.totient)) ∧
    1 < singularSeries N ∧ C2 * N / N.totient ≤ singularSeries N ∧
    singularSeries N ≤ (N : ℝ) / N.totient := by sorry

/-- Uniform part (4.6) and the final totient bound of Lemma 4.3. -/
theorem lemma_4_3_uniform (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Even N → 4 ≤ N →
      (∀ w : ℂ, w.re ∈ Icc lo hi → 1 ≤ |w.im| →
        ‖continuedDensity N w‖ ≤ C * (N : ℝ) / N.totient * (1 + |w.im|)) ∧
      (N : ℝ) / N.totient ≤ C * Real.log (Real.log N) := by sorry

theorem proposition_4_4 (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∀ s z : ℂ, (s, z) ∈ betaDomain → betaModel N s z = continuedModel N s z) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => continuedModel N p.1 p.2) analyticDomain := by sorry

theorem proposition_4_5 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => residual N p.1 p.2) analyticDomain ∧
    (∀ s z : ℂ, residual N s z = residual N z s ∧
      conj (residual N s z) = residual N (conj s) (conj z)) ∧
    HermitianKernel (fun s z => residual N s (conj z)) := by sorry

-- Section 5.
def wirtingerBar (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (deriv (fun x : ℝ => f (s + x)) 0 + I * deriv (fun y : ℝ => f (s + y * I)) 0) / 2

def wirtinger (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (deriv (fun x : ℝ => f (s + x)) 0 - I * deriv (fun y : ℝ => f (s + y * I)) 0) / 2

theorem proposition_5_1 (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) :
    HermitianKernel (weightedKernel N) ∧
    HermitianKernel (fun s z => residual N s (conj z)) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2)) analyticDomain ∧
    (∃ U : Set (ℂ × ℂ), IsOpen U ∧
      {p | alpha N ≤ p.1.re ∧ p.1.re ≤ beta ∧
        alpha N ≤ p.2.re ∧ p.2.re ≤ beta} ⊆ U ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => residual N p.1 p.2) U ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2)) U) ∧
    (∀ s z : ℂ, (s, conj z) ∈ analyticDomain →
      wirtingerBar (fun w => residual N w (conj z)) s = 0 ∧
      wirtinger (fun w => residual N s (conj w)) z = 0) ∧
    1 / 90 < sigmaStar - alpha N ∧ beta - sigmaStar = 1 / 72 := by sorry

theorem lemma_5_2 (a b : ℝ) (hab : a < b) :
    (∀ ψ : HardySpace a b, IsRawHardy a b (fourierLaplace ψ) ∧
      rawHardyNormSq a b (fourierLaplace ψ) = ‖ψ‖ ^ 2 ∧
      ‖ψ‖ ^ 2 = ‖(boundaryTraces hab ψ).1‖ ^ 2 + ‖(boundaryTraces hab ψ).2‖ ^ 2) ∧
    (∀ f : ℂ → ℂ, IsRawHardy a b f →
      ∃! ψ : HardySpace a b, ∀ s ∈ strip a b, fourierLaplace ψ s = f s) := by sorry

theorem proposition_5_3 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (∀ x ∈ ({alpha N, beta} : Finset ℝ), ∀ y ∈ ({alpha N, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
    IsHilbertSchmidt (residualOperator ha N) ∧ Nonempty (SpectralData (residualOperator ha N)) ∧
    (∑' j, eigenvalues (residualOperator ha N) j ^ 2) = hsNorm (residualOperator ha N) ^ 2 ∧
    hsNorm (residualOperator ha N) ^ 2 = BoundaryKernelSquareIntegral (alpha N) beta (weightedKernel N) ∧
    ‖residualOperator ha N‖ = sSup (Set.range (fun j => |eigenvalues (residualOperator ha N) j|)) ∧
    (residualOperator ha N ≠ 0 → ∃ j, |eigenvalues (residualOperator ha N) j| = ‖residualOperator ha N‖) := by sorry

theorem proposition_5_4 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (s z : ℂ) (hs : s ∈ strip (alpha N) beta) (hz : z ∈ strip (alpha N) beta) :
    (∀ h : HardySpace (alpha N) beta, fourierLaplace h s = paperInner h (evaluationVector s)) ∧
    fourierLaplace (evaluationVector z : HardySpace (alpha N) beta) s = reproducingKernel (alpha N) beta s z ∧
    ‖(evaluationVector s : HardySpace (alpha N) beta)‖ ^ 2 ≤ 1 / (8 * pointDistance (alpha N) beta s) ∧
    ‖residual N s (conj z)‖ ≤ ‖residualOperator ha N‖ * ‖1 + s‖ * ‖1 + z‖ /
      (8 * Real.sqrt (pointDistance (alpha N) beta s * pointDistance (alpha N) beta z)) := by sorry

-- Section 6.
/-- The spectral definition of the Fredholm determinant for a positive trace-class
operator A. Its intended domain is `IsPositiveTraceClass A`; convergence and spectral
validity are conclusions of `proposition_6_1_positive_fredholm_spec` below. This is a
paper-specific interface, not a claimed Mathlib general Fredholm determinant API. -/
def positiveFredholmDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (t : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - t * (eigenvalues A j : ℂ))

def fredholmSquareDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (t : ℂ) : ℂ :=
  positiveFredholmDet (T.comp T) t

theorem proposition_6_1 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    CompactUniformLimit (fun k q => spectralPartialQuaternion N (residualOperator ha N) q k)
      (spectralQuaternion N (residualOperator ha N)) ∧
    IntrinsicEntire (spectralQuaternion N (residualOperator ha N)) ∧
    (∀ q : ℂ, Multipliable (fun j : ℕ =>
      1 - (4 * eigenvalues (residualOperator ha N) j ^ 2 / spectralScale N ^ 2 : ℝ) *
        q * (1 - q))) ∧
    IsPositiveTraceClass ((residualOperator ha N).comp (residualOperator ha N)) ∧
    positiveTrace ((residualOperator ha N).comp (residualOperator ha N)) =
      hsNorm (residualOperator ha N) ^ 2 ∧
    (∀ q : ℂ, spectralComplex N (residualOperator ha N) q =
      fredholmSquareDet (residualOperator ha N) (4 / spectralScale N ^ 2 * q * (1 - q))) := by sorry

theorem proposition_6_2 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    let X := spectralQuaternion N (residualOperator ha N)
    X 0 = 1 ∧ X 1 = 1 ∧ (∀ q, X (1 - q) = X q) ∧
    (∀ q, X (star q) = star (X q)) ∧ (∀ q, X (1 - star q) = star (X q)) ∧
    (∀ ξ, X (1 / 2 + ξ) = X (1 / 2 - ξ)) ∧
    (∀ x : ℝ, x ∉ Ioo 0 1 → 1 ≤ (X x).re) := by sorry

theorem proposition_6_3 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 ↔
      ∃ j : ℕ, eigenvalues (residualOperator ha N) j ≠ 0 ∧
        q * (1 - q) = (spectralScale N ^ 2 /
          (4 * eigenvalues (residualOperator ha N) j ^ 2) : ℝ)) ∧
    (∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 →
      q.re ≠ 1 / 2 → q = (q.re : Quaternion ℝ) ∧ q.re ∈ Ioo 0 1) ∧
    (∀ x : ℝ, spectralQuaternion N (residualOperator ha N) x = 0 → x ∈ Ioo 0 1) ∧
    Set.Finite {j | spectralScale N < |eigenvalues (residualOperator ha N) j|} := by sorry

theorem theorem_6_1 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (SpectralR N (alpha N) ha ↔ ‖residualOperator ha N‖ ≤ spectralScale N) ∧
    (∀ η : ℝ, 0 < η → η < 1 / 2 →
      (SpectralZeroFree N (alpha N) ha η ↔
        ‖residualOperator ha N‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η))))) ∧
    (∀ M : ℝ, spectralScale N < M → ‖residualOperator ha N‖ ≤ M →
      0 < spectralWidthFromBound N M ∧ spectralWidthFromBound N M < 1 / 2 ∧
      SpectralZeroFree N (alpha N) ha (spectralWidthFromBound N M)) := by sorry

theorem theorem_6_2 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    EvenEventually (fun N => ∀ (_ : NeZero N) (ha : alpha N < beta), GRH N →
      IsHilbertSchmidt (residualOperator ha N) ∧
      ‖residualOperator ha N‖ ≤ hsNorm (residualOperator ha N) ∧
      hsNorm (residualOperator ha N) ≤ C * Real.log N ^ 2 ∧
      SpectralZeroFree N (alpha N) ha (c * singularSeries N / (N * Real.log N))) := by sorry

theorem lemma_6_4 : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ σ : ℝ, 0 < σ → σ ≤ beta →
      (∀ χ ∈ oddCharacters N,
        Integrable (fun t : ℝ => ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2))) ∧
      averagedLogDerivative N σ ≤ C * (Real.log N ^ 2 + σ⁻¹ ^ 2) := by sorry

theorem proposition_6_5 : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
      let α := alpha N
      let P := arithmeticOperator ha N
      let D := diagonalOperator ha N
      let K := modelOperator ha N
      IsPositiveTraceClass P ∧ IsPositiveTraceClass D ∧ IsHilbertSchmidt K ∧
      (hsNorm P ≤ positiveTrace P ∧
        positiveTrace P ≤ C * (Real.log N ^ 2 + α⁻¹ ^ 2)) ∧
      (hsNorm D ≤ positiveTrace D ∧ positiveTrace D ≤ C * α⁻¹ ^ 2) ∧
      hsNorm K ≤ C * α⁻¹ ^ 2 := by sorry

/-- The three components in Proposition 6.5 realize the stated boundary kernels.
Integrability and the residual decomposition exclude the fallback-zero branches
of the totalized kernel-operator definitions from standing in for these claims. -/
theorem proposition_6_5_components_spec (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    let α := alpha N
    let P := arithmeticOperator ha N
    let D := diagonalOperator ha N
    let K := modelOperator ha N
    let κP := fun s z : ℂ =>
      characterKernel N s (conj z) / ((1 + s) * (1 + conj z))
    let κD := fun s z : ℂ =>
      diagonalSeries N (s + conj z) / ((1 + s) * (1 + conj z))
    let κK := fun s z : ℂ =>
      continuedModel N s (conj z) / ((1 + s) * (1 + conj z))
    RepresentsKernel ha N κP P ∧
    RepresentsKernel ha N κD D ∧
    RepresentsKernel ha N κK K ∧
    (∀ κ ∈ ([κP, κD, κK] : List (ℂ → ℂ → ℂ)),
      ∀ (h : HardySpace α beta) (s : ℂ), s ∈ strip α beta →
        Integrable (fun t : ℝ => κ s (line α t) * (boundaryTraces ha h).1 t) ∧
        Integrable (fun t : ℝ => κ s (line beta t) * (boundaryTraces ha h).2 t)) ∧
    residualOperator ha N = P - D - K := by sorry

-- Section 7.
theorem lemma_7_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ σ u : ℝ, 0 < u → (companion φ u : ℂ) =
      verticalMellin σ (fun s => mellinWeight φ s * (u : ℂ) ^ (-s))) ∧
    (∀ lo hi : ℝ, lo ≤ hi → ∃ C : ℝ, 0 < C ∧
      ∀ σ ∈ Icc lo hi, ∀ t : ℝ, ‖mellinWeight φ (line σ t)‖ ≤ C * (1 + |t|)⁻¹ ^ 6) ∧
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
      ∀ χ ∈ oddCharacters N, ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 →
        characterPolynomial χ φ = -verticalMellin σ (fun s =>
          (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s)) := by sorry

theorem lemma_7_2 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * diagonalSeries N (s + z))) =
        diagonalMoment N φ ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s + z) * betaKernel s z)) =
        -(weightMass φ * singularSeries N : ℝ) := by sorry

theorem proposition_7_3 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    residualIntegral N φ σ = (weightMass φ * singularSeries N - goldbach N φ : ℝ) := by sorry

theorem proposition_7_4 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ N : ℕ, Even N → Real.exp 10 < (N : ℝ) →
      (∀ σ ∈ Ioo (alpha N) beta,
        (∀ h : HardySpace (alpha N) beta,
          Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
            (1 + line σ t) * fourierLaplace h (line σ t)) ∧
          functionalValue N φ σ h = paperInner h (rieszVector N φ)) ∧
        ∃ ℓ : HardySpace (alpha N) beta →L[ℂ] ℂ,
          (∀ h, ℓ h = functionalValue N φ σ h) ∧
          ‖ℓ‖ ^ 2 = normFunctional N φ (alpha N)) ∧
      ‖(rieszVector N φ : HardySpace (alpha N) beta)‖ ^ 2 = normFunctional N φ (alpha N) ∧
      normFunctional N φ (alpha N) ≤ Real.exp 2 * weightEnergy φ) ∧
    (∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |normFunctional N φ (alpha N) - Real.exp 2 * weightEnergy φ| ≤ C / Real.log N)) := by sorry

theorem theorem_7_1 (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (ha : alpha N < beta) :
    (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
      paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) ∧
    |weightMass φ * singularSeries N - goldbach N φ| ≤
      normFunctional N φ (alpha N) * ‖residualOperator ha N‖ := by sorry

theorem lemma_7_5 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
      Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
      ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → SpectralZeroFree N (alpha N) ha η →
      |goldbach N φ - weightMass φ * singularSeries N| / (weightMass φ * singularSeries N) ≤
        C * Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) := by sorry

-- Appendix A.
theorem proposition_A_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) (c : ℝ) (hc : 0 < c) :
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → Real.exp (10 * c) < (N : ℝ) → GRH N →
      alpha N c < 1 / 10 ∧ 1 / 40 < width (alpha N c) ∧
      1 / 90 < sigmaStar - alpha N c ∧ beta - sigmaStar = 1 / 72 ∧
      (∀ σ ∈ Ioo (alpha N c) beta,
        (∀ h : HardySpace (alpha N c) beta,
          Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
            (1 + line σ t) * fourierLaplace h (line σ t)) ∧
          functionalValue N φ σ h = paperInner h (rieszVector N φ)) ∧
        ∃ ℓ : HardySpace (alpha N c) beta →L[ℂ] ℂ,
          (∀ h, ℓ h = functionalValue N φ σ h) ∧
          ‖ℓ‖ ^ 2 = normFunctional N φ (alpha N c)) ∧
      ‖(rieszVector N φ : HardySpace (alpha N c) beta)‖ ^ 2 = normFunctional N φ (alpha N c) ∧
      (∀ ha : alpha N c < beta,
        IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
        IsHilbertSchmidt (residualOperator ha N) ∧
        (∀ s z : ℂ, s ∈ strip (alpha N c) beta → z ∈ strip (alpha N c) beta →
          ‖residual N s (conj z)‖ ≤ ‖residualOperator ha N‖ * ‖1 + s‖ * ‖1 + z‖ /
            (8 * Real.sqrt (pointDistance (alpha N c) beta s * pointDistance (alpha N c) beta z))) ∧
        (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
          paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) ∧
        |weightMass φ * singularSeries N - goldbach N φ| ≤
          normFunctional N φ (alpha N c) * ‖residualOperator ha N‖) ∧
      normFunctional N φ (alpha N c) ≤ Real.exp (2 * c) * weightEnergy φ) ∧
    (∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |normFunctional N φ (alpha N c) - Real.exp (2 * c) * weightEnergy φ| ≤ C / Real.log N)) := by sorry

def HypothesisRAt (c : ℝ) : Prop := EvenEventually (fun N => GRH N →
  ∀ (_ : NeZero N) (ha : alpha N c < beta), SpectralR N (alpha N c) ha)

def HypothesisSAt (c : ℝ) (h : ℕ → ℝ) : Prop := IsAdmissible h ∧
  EvenEventually (fun N => GRH N → ∀ (_ : NeZero N) (ha : alpha N c < beta),
    SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h))

theorem proposition_A_2 (φ : ℝ → ℝ) (hφ : IsWeight φ) (c : ℝ) (hc : 0 < c) :
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → Real.exp (10 * c) < (N : ℝ) → GRH N →
      ∀ ha : alpha N c < beta,
      (SpectralR N (alpha N c) ha ↔ ‖residualOperator ha N‖ ≤ spectralScale N) ∧
      (∀ η : ℝ, 0 < η → η < 1 / 2 → (SpectralZeroFree N (alpha N c) ha η ↔
        ‖residualOperator ha N‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η))))) ∧
      (∀ h : ℕ → ℝ, 0 < h N → 0 < zeroFreeWidth N h → zeroFreeWidth N h ≤ 1 / 4 →
        (SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h) ↔
          ‖residualOperator ha N‖ ≤ singularSeries N / (2 * h N * Real.sqrt (1 - zeroFreeWidth N h))))) ∧
    (∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
      EvenEventually (fun N => ∀ (_ : NeZero N) (ha : alpha N c < beta), GRH N →
        ‖residualOperator ha N‖ ≤ C * Real.log N ^ 2 ∧
        SpectralZeroFree N (alpha N c) ha (c₀ * singularSeries N / (N * Real.log N))) ∧
      (∀ h : ℕ → ℝ, HypothesisSAt c h →
        EvenEventually (fun N => GRH N →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * singularSeries N / h N)) ∧
      (HypothesisRAt c →
        EvenEventually (fun N => GRH N →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N))) := by sorry

def baselineBound (C : ℝ) (N : ℕ) (a : ℝ) : ℝ := C * (Real.log N ^ 2 + a⁻¹ ^ 2)

def balanceFactor (c : ℝ) : ℝ := Real.exp (2 * c) * (1 + c⁻¹ ^ 2)

theorem lemma_A_3 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∃ C L U : ℝ, 0 < C ∧ 0 < L ∧ 0 < U ∧
      EvenEventually (fun N => ∀ (_ : NeZero N), GRH N → ∀ a : ℝ, 0 < a → a < 1 / 10 →
        L * Real.rpow N (2 * a) ≤ normFunctional N φ a ∧
        normFunctional N φ a ≤ U * Real.rpow N (2 * a) ∧
        ∀ ha : a < beta, ‖residualOperator ha N‖ ≤ baselineBound C N a)) ∧
    Tendsto balanceFactor (nhdsWithin 0 (Ioi 0)) atTop ∧ Tendsto balanceFactor atTop atTop := by sorry

def poleCoefficient (N : ℕ) [NeZero N] (γ : ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    (analyticOrderNatAt χ.LFunction (line (1 / 2) γ) : ℝ) ^ 2

theorem proposition_A_4 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (γ : ℝ)
    (hzero : ∃ χ ∈ oddCharacters N, χ.LFunction (line (1 / 2) γ) = 0) :
    0 < poleCoefficient N γ ∧
    (∀ ε : ℝ, 0 < ε → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ →
      ∀ ha : alpha N c < beta,
        2 * poleCoefficient N γ * Real.log N / (1 + γ ^ 2) - ε ≤ c * ‖residualOperator ha N‖) ∧
    (∃ z c₀ : ℝ, 0 < z ∧ 0 < c₀ ∧ c₀ ≤ Real.log N / 24 ∧
      ∀ c : ℝ, 0 < c → c < c₀ → ∀ ha : alpha N c < beta,
        z / c ≤ ‖residualOperator ha N‖ ∧ ¬SpectralR N (alpha N c) ha ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → SpectralZeroFree N (alpha N c) ha η →
          η ≤ spectralScale N ^ 2 * c ^ 2 / (3 * z ^ 2)) := by sorry

-- Appendix B. All arithmetic objects here use the fixed integer 30030.
abbrev experimentN : ℕ := 30030

def cutoffPolynomial (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
    ∑ j ∈ Finset.Icc 7 13, (Nat.choose 13 j : ℝ) * t ^ j * (1 - t) ^ (13 - j)

def wideCutoff (x : ℝ) : ℝ :=
  cutoffPolynomial ((x - 16) / (1000 - 16)) *
    cutoffPolynomial ((experimentN - x - 16) / (1000 - 16))

def wideCompanion (u : ℝ) : ℝ :=
  if u ∈ Ioo (16 / experimentN : ℝ) (1 - 16 / experimentN : ℝ) then
    Real.sqrt (1 - u) * wideCutoff (experimentN * u) /
      Real.sqrt (Real.log (experimentN * u) * Real.log (experimentN * (1 - u))) else 0

def wideWeight (u : ℝ) : ℝ := wideCompanion u / Real.sqrt u

def wideCorrelation : ℝ := goldbach experimentN wideWeight

def unorderedPrimePairs : ℕ := ((Finset.range (experimentN + 1)).filter
  (fun p => p.Prime ∧ (experimentN - p).Prime ∧ p ≤ experimentN - p)).card

def edgeCorrection : ℝ := ∑ p ∈ Finset.range 1000,
  if p.Prime ∧ (experimentN - p).Prime ∧ p ≤ experimentN - p
  then 1 - wideCutoff p ^ 2 else 0

def primePowerCorrection : ℝ :=
  ∑ p ∈ Finset.range (experimentN + 1), ∑ q ∈ Finset.range (experimentN + 1),
    ∑ k ∈ Finset.range (experimentN + 1), ∑ l ∈ Finset.range (experimentN + 1),
      if p.Prime ∧ q.Prime ∧ 0 < k ∧ 0 < l ∧ 2 ≤ max k l ∧
        p ^ k + q ^ l = experimentN ∧ Nat.Coprime (p * q) experimentN
      then wideCutoff (p ^ k) ^ 2 / (k * l : ℕ) else 0

def countingCoefficient (n : ℕ) : ℝ := mangoldt n / Real.sqrt n * wideCompanion (n / experimentN)

def countingIntegral (χ : Character experimentN) : ℂ :=
  verticalMellin 1 (fun s => (experimentN : ℂ) ^ s *
    mellin (fun u => (wideCompanion u : ℂ)) s * logDerivative χ s)

def diagonalCountingMoment : ℝ := ∑ n ∈ Finset.range experimentN,
  if Nat.Coprime n experimentN then countingCoefficient n ^ 2 else 0

def approxSignedMoment (Ihat : Character experimentN → ℂ) : ℝ :=
  (5760 : ℝ)⁻¹ * (∑ χ : Character experimentN, (χ (-1)).re * ‖Ihat χ‖ ^ 2)

def approxDiagonalMoment (Ihat : Character experimentN → ℂ) : ℝ :=
  (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN, ‖Ihat χ‖ ^ 2

def wideModelMass : ℝ := ∫ u in (0 : ℝ)..1, wideWeight u * wideWeight (1 - u)

def wideResidual : ℝ := wideModelMass * singularSeries experimentN - wideCorrelation

def approxPrimeCount (Ihat : Character experimentN → ℂ) : ℝ :=
  (experimentN : ℝ) / 2 * approxSignedMoment Ihat - primePowerCorrection / 2 + edgeCorrection

def countError (Ihat : Character experimentN → ℂ) (ε : ℝ) : ℝ :=
  (experimentN : ℝ) / 2 * (2 * Real.sqrt (approxDiagonalMoment Ihat) * ε + ε ^ 2)

theorem proposition_B_1 :
    ContDiff ℝ 6 wideCutoff ∧ (∀ x : ℝ, wideCutoff x = wideCutoff (experimentN - x)) ∧
    (∀ x ∈ Icc (1000 : ℝ) (experimentN - 1000), wideCutoff x = 1) ∧
    (∀ u ∈ Ioo (16 / experimentN : ℝ) (1 - 16 / experimentN : ℝ),
      wideWeight u * wideWeight (1 - u) = wideCutoff (experimentN * u) ^ 2 /
        (Real.log (experimentN * u) * Real.log (experimentN * (1 - u)))) ∧
    (unorderedPrimePairs : ℝ) = (experimentN : ℝ) / 2 * wideCorrelation - primePowerCorrection / 2 + edgeCorrection := by sorry

theorem lemma_B_2 :
    (∀ χ : Character experimentN,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line 1 t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line 1 t) * logDerivative χ (line 1 t)) ∧
      countingIntegral χ = -∑ n ∈ Finset.range experimentN, (countingCoefficient n : ℂ) * χ n) ∧
    wideCorrelation = approxSignedMoment countingIntegral ∧
    diagonalCountingMoment = approxDiagonalMoment countingIntegral := by sorry

theorem lemma_B_3 (Ihat : Character experimentN → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN, ‖countingIntegral χ - Ihat χ‖ ^ 2 ≤ ε ^ 2) :
    |wideCorrelation - approxSignedMoment Ihat| ≤
      2 * Real.sqrt (approxDiagonalMoment Ihat) * ε + ε ^ 2 ∧
    |(unorderedPrimePairs : ℝ) - approxPrimeCount Ihat| ≤ countError Ihat ε ∧
    (unorderedPrimePairs : ℝ) ∈
      Icc (approxPrimeCount Ihat - countError Ihat ε) (approxPrimeCount Ihat + countError Ihat ε) ∩
        Set.range (fun k : ℤ => (k : ℝ)) := by sorry

def wideFunctional {a : ℝ} (h : HardySpace a beta) : ℂ :=
  verticalMellin sigmaStar (fun s => (experimentN : ℂ) ^ s *
    mellin (fun u => (wideCompanion u : ℂ)) s * (1 + s) * fourierLaplace h s)

def wideRieszVector : HardySpace (alpha experimentN) beta :=
  if h : ∃ v : HardySpace (alpha experimentN) beta, ∀ f, wideFunctional f = paperInner f v
  then Classical.choose h else 0

theorem proposition_B_4 (hGRH : GRH experimentN) (ha : alpha experimentN < beta) :
    (∀ h : HardySpace (alpha experimentN) beta,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line sigmaStar t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line sigmaStar t) *
        (1 + line sigmaStar t) * fourierLaplace h (line sigmaStar t)) ∧
      wideFunctional h = paperInner h wideRieszVector) ∧
    (∃ ℓ : HardySpace (alpha experimentN) beta →L[ℂ] ℂ, ∀ h, ℓ h = wideFunctional h) ∧
    (wideResidual : ℂ) = paperInner (residualOperator ha experimentN wideRieszVector) wideRieszVector := by sorry

def spectralNode (i : Fin 2562) : ℂ :=
  line (if i.val < 1281 then alpha experimentN else beta) (((i.val % 1281 : ℕ) : ℝ) / 16 - 40)

def trapezoidWeight (i : Fin 2562) : ℝ :=
  (1 / 16) * if i.val % 1281 = 0 ∨ i.val % 1281 = 1280 then 1 / 2 else 1

def finiteSpectralMatrix : Matrix (Fin 2562) (Fin 2562) ℂ :=
  fun i j => (Real.sqrt (trapezoidWeight i) : ℂ) *
    weightedKernel experimentN (spectralNode i) (spectralNode j) * Real.sqrt (trapezoidWeight j)

def finiteSpectralFunction (q : ℂ) : ℂ :=
  Matrix.det (1 - (4 * q * (1 - q) / spectralScale experimentN ^ 2) •
    (finiteSpectralMatrix * finiteSpectralMatrix))

/-- Matrix eigenvalue list is linked to a unitary eigenbasis, with multiplicity. -/
def IsFiniteSpectrum (ev : Fin 2562 → ℝ) : Prop :=
  ∃ U : Matrix (Fin 2562) (Fin 2562) ℂ,
    star U * U = 1 ∧ U * star U = 1 ∧
    finiteSpectralMatrix = U * Matrix.diagonal (fun i => (ev i : ℂ)) * star U

def finiteEigenvalues : Fin 2562 → ℝ :=
  if h : ∃ ev, IsFiniteSpectrum ev then Classical.choose h else 0

def finiteMatrixOpNorm : ℝ :=
  sSup {r : ℝ | ∃ x : EuclideanSpace ℂ (Fin 2562), ‖x‖ = 1 ∧
    r = ‖(WithLp.toLp 2 (finiteSpectralMatrix.mulVec (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin 2562))‖}

theorem proposition_B_5 (hGRH : GRH experimentN) :
    IsFiniteSpectrum finiteEigenvalues ∧
    (∀ q : ℂ, finiteSpectralFunction q =
      ∏ j : Fin 2562, (1 - (4 * finiteEigenvalues j ^ 2 / spectralScale experimentN ^ 2 : ℝ) * q * (1 - q))) ∧
    (∀ q : ℂ, finiteSpectralFunction (1 - q) = finiteSpectralFunction q) ∧
    (finiteMatrixOpNorm ≤ spectralScale experimentN →
      ∀ q : ℂ, finiteSpectralFunction q = 0 → q.re = 1 / 2) := by sorry

end ConditionalGoldbach

/-!
Auxiliary definitions used in the paper's proofs and appendices.
All are part of this single review module and contain their actual formulas.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

/-- Full meromorphic Gamma-quotient form; equality to the integral has domain hypotheses. -/
def betaGamma (u v : ℂ) : ℂ := Gamma u * Gamma v / Gamma (u + v)

/-- Both boundary components are retained as a disjoint union, even for arbitrary endpoints. -/
abbrev BoundaryParameter := Bool × ℝ

def boundaryPoint (a b : ℝ) (p : BoundaryParameter) : ℂ :=
  line (if p.1 then b else a) p.2

def boundaryMeasure : Measure BoundaryParameter :=
  Measure.prod Measure.count (volume : Measure ℝ)

def positiveDifferenceFamily (N n m k : ℕ) : Prop :=
  0 < k ∧ m = n + k * N

def negativeDifferenceFamily (N n m k : ℕ) : Prop :=
  0 < k ∧ n = m + k * N

def sumFamily (N n m k : ℕ) : Prop :=
  0 < k ∧ n + m = k * N

/-- (3.6), with the inducing primitive character's zero set. -/
def pairedZeroSum {N : ℕ} [NeZero N] (χ : Character N) (s : ℂ) : ℂ :=
  ∑' p : ZeroIndex χ.primitiveCharacter,
    (1 / (s - p.val.1.im * I) - 1 / (3 / 2 - p.val.1.im * I))

def zeroMultiplicity {N : ℕ} [NeZero N] (χ : Character N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt χ.LFunction ρ

def spectralRootParameter (N : ℕ) (μ : ℝ) : ℝ :=
  spectralScale N ^ 2 / μ ^ 2

def quaternionSlice (J : Quaternion ℝ) : Set (Quaternion ℝ) :=
  {q | ∃ x y : ℝ, q = (x : Quaternion ℝ) + y • J}

def complexQuaternion (z : ℂ) : Quaternion ℝ := ⟨z.re, z.im, 0, 0⟩

/-- The paper's stated coordinate convention ∂sbar + j∂z on a complex-valued F. -/
def fueterOperator (F : ℂ → ℂ → ℂ) (s z : ℂ) : Quaternion ℝ :=
  complexQuaternion (wirtingerBar (fun u => F u z) s) +
    (⟨0, 0, 1, 0⟩ : Quaternion ℝ) * complexQuaternion (wirtinger (F s) z)

def referenceLine (N : ℕ) : ℝ := 2 / Real.log N

def perronCutoff (N : ℕ) : ℝ := (N : ℝ) / 2

/-- Smoothed cutoff from §6.4.1; the analytic assertions use X > 1. -/
def smoothedPerronWeight (X : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ Real.sqrt X then 1
  else if (n : ℝ) ≤ X then Real.log (X / n) / Real.log (Real.sqrt X)
  else 0

def smoothedDirichletPolynomial {N : ℕ} (χ : Character N) (X : ℝ) (u : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
    (mangoldt n : ℂ) * χ n * (n : ℂ) ^ (-u) * smoothedPerronWeight X n

def smoothedPerronKernel (X : ℝ) (v : ℂ) : ℂ :=
  ((X : ℂ) ^ v - (Real.sqrt X : ℂ) ^ v) / (v ^ 2 * Real.log (Real.sqrt X))

def logDerivativeEnergy {N : ℕ} [NeZero N] (χ : Character N) (σ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)

/-- Real-line Poisson kernel; analytic uses require a > 0. -/
def poissonKernelReal (a t : ℝ) : ℝ := a / (Real.pi * (a ^ 2 + t ^ 2))

def realConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, f u * g (t - u)

/-- Poisson action on the closed parameter range: at zero the paper means the
identity, not convolution with the totalized scalar kernel `poissonKernelReal 0`.
Analytic statements use only nonnegative parameters. -/
def poissonAction (ℓ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  if ℓ = 0 then f else realConvolution (poissonKernelReal ℓ) f

def diagonalVector (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) ^ (-s) / (1 + s)

def weightIntegral (φ : ℝ → ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), φ u

def functionalIntegrand (N : ℕ) (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ s * mellinWeight φ s * (1 + s)

/-- The available uniform majorant in §6.5 and Lemma A.3. -/
def availableNormMajorant (C : ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  C * (Real.log N ^ 2 + a ^ (-2 : ℤ))

/-- Euler product R_N in the fixed-modulus obstruction, Appendix A.4. -/
def baselineProductR (N : ℕ) (w : ℂ) : ℂ :=
  (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-1 - w))) *
  ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
    1 + (2 * (p : ℂ) ^ (-w) - (p : ℂ) ^ (-2 * w)) / ((p : ℂ) * ((p : ℂ) - 2))
  else 1

def wideMainIntegral : ℝ := singularSeries experimentN *
  ∫ x in (16 : ℝ)..((experimentN : ℝ) / 2),
    wideCutoff x ^ 2 / (Real.log x * Real.log ((experimentN : ℝ) - x))

def HasMomentError (Ihat : Character experimentN → ℂ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN,
    ‖countingIntegral χ - Ihat χ‖ ^ 2 ≤ ε ^ 2

end ConditionalGoldbach

/-!
Supplementary clauses of named statements. These are proof-free review stubs.
Labels are kept in the names so that subordinate clauses are not silently lost.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

/-- The finite-dimensionality assertion is essential: `finrank` alone is zero
for an infinite-dimensional space and would not express a finite rank bound. -/
theorem proposition_3_2_finite_rank (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) := by sorry

theorem lemma_3_4_normal_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) :
    NormallySummableOn (fun p : ZeroIndex χ.primitiveCharacter => fun s : ℂ =>
      1 / (s - p.val.1.im * I) - 1 / (3 / 2 - p.val.1.im * I))
      {s | 0 < s.re} := by sorry

/-- Absolute convergence on the initial contours and on the GRH-shifted ones. -/
theorem lemma_3_5_absolute_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 1 / 2 < σ ∨ (GRH N ∧ 0 < σ ∧ σ ≤ 1 / 9)) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        characterKernel N (line σ p.1) (line σ p.2)) := by sorry

theorem lemma_3_5_small_sigma (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) := by sorry

theorem lemma_3_5_weight_support (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (n m k : ℕ)
    (hn : φ ((n : ℝ) / N) ≠ 0) (hm : φ ((m : ℝ) / N) ≠ 0) :
    ¬positiveDifferenceFamily N n m k ∧
    ¬negativeDifferenceFamily N n m k ∧
    (sumFamily N n m k ↔ k = 1 ∧ n + m = N) := by sorry

theorem lemma_4_1_absolute_convergence (h : ℝ) (hh : 0 < h)
    (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (x + h : ℂ) ^ (-1 / 2 - z)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - z) *
      (x + h : ℂ) ^ (-1 / 2 - s)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (h - x : ℂ) ^ (-1 / 2 - z)) (Ioo 0 h) := by sorry

theorem lemma_4_3_density_convergence (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∀ w : ℂ, 1 < w.re → Summable (fun k : ℕ =>
      if 0 < k then ‖(singularSeries (k * N) : ℂ) / (k : ℂ) ^ w‖ else 0)) ∧
    DifferentiableOn ℂ (continuedDensity N) {w | 0 < w.re ∧ w ≠ 1} := by sorry

theorem lemma_5_2_closed_trace_space (a b : ℝ) (hab : a < b) :
    IsClosed (Set.range (fun ψ : HardySpace a b => boundaryTraces hab ψ)) := by sorry

theorem proposition_5_4_exact_norm (a b : ℝ) (hab : a < b)
    (s : ℂ) (hs : s ∈ strip a b) :
    ‖(evaluationVector s : HardySpace a b)‖ ^ 2 =
      1 / (4 * (b - a) * Real.sin (Real.pi * (s.re - a) / (b - a))) := by sorry

/-- Re-enumeration is stated on the quaternion partial products, where
commutativity cannot be silently delegated to the ambient quaternion ring. -/
def spectralPartialQuaternionReindexed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (N : ℕ) (T : H →L[ℂ] H)
    (e : ℕ ≃ ℕ) (q : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun acc j =>
    acc * (1 - (4 * eigenvalues T (e j) ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))) 1

theorem proposition_6_1_enumeration (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (e : ℕ ≃ ℕ) :
    CompactUniformLimit (fun k q =>
      spectralPartialQuaternionReindexed N (residualOperator ha N) e q k)
      (spectralQuaternion N (residualOperator ha N)) ∧
    (∀ q : ℂ, (∏' j : ℕ,
      (1 - (4 * eigenvalues (residualOperator ha N) (e j) ^ 2 / spectralScale N ^ 2 : ℝ) *
        q * (1 - q))) = spectralComplex N (residualOperator ha N) q) := by sorry

theorem proposition_6_1_complex_slice (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (q : ℂ) :
    spectralQuaternion N (residualOperator ha N) (complexQuaternion q) =
      complexQuaternion (spectralComplex N (residualOperator ha N) q) := by sorry

def centeredSpectralPartial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (N : ℕ) (T : H →L[ℂ] H)
    (ξ : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun acc j => acc *
    (1 - (eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) +
      (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * ξ ^ 2)) 1

theorem proposition_6_2_centered_product (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    CompactUniformLimit (fun k ξ => centeredSpectralPartial N (residualOperator ha N) ξ k)
      (fun ξ => spectralQuaternion N (residualOperator ha N) (1 / 2 + ξ)) := by sorry

theorem proposition_6_2_critical_values (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta)
    (J : Quaternion ℝ) (hJre : J.re = 0) (hJnorm : ‖J‖ = 1) (t : ℝ) :
    Multipliable (fun j : ℕ => (1 - eigenvalues (residualOperator ha N) j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2) : ℝ)) ∧
    spectralQuaternion N (residualOperator ha N) ((1 / 2 : Quaternion ℝ) + t • J) =
      ((∏' j : ℕ, (1 - eigenvalues (residualOperator ha N) j ^ 2 /
        spectralScale N ^ 2 * (1 + 4 * t ^ 2)) : ℝ) : Quaternion ℝ) := by sorry

/-- Three disjoint root cases: a nonreal sphere, a central double factor root,
and an exceptional pair of real roots. -/
theorem proposition_6_3_three_cases (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (q : Quaternion ℝ) :
    spectralQuaternion N (residualOperator ha N) q = 0 ↔
      ∃ j : ℕ, eigenvalues (residualOperator ha N) j ≠ 0 ∧
        let d := spectralRootParameter N (eigenvalues (residualOperator ha N) j)
        (1 < d ∧ q.re = 1 / 2 ∧ ‖q - (q.re : Quaternion ℝ)‖ = Real.sqrt (d - 1) / 2) ∨
        (d = 1 ∧ q = 1 / 2) ∨
        (0 < d ∧ d < 1 ∧
          (q = ((1 / 2 - Real.sqrt (1 - d) / 2 : ℝ) : Quaternion ℝ) ∨
           q = ((1 / 2 + Real.sqrt (1 - d) / 2 : ℝ) : Quaternion ℝ))) := by sorry

theorem proposition_6_3_factor_central_order (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (j : ℕ)
    (hμ : eigenvalues (residualOperator ha N) j ≠ 0)
    (hd : spectralRootParameter N (eigenvalues (residualOperator ha N) j) = 1) :
    analyticOrderNatAt (fun q : ℂ =>
      1 - (4 * eigenvalues (residualOperator ha N) j ^ 2 / spectralScale N ^ 2 : ℝ) *
        q * (1 - q)) (1 / 2) = 2 := by sorry

theorem proposition_6_3_multiplicities (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (∀ q : ℂ, analyticOrderNatAt (spectralComplex N (residualOperator ha N)) q =
      analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (1 - q)) ∧
    (∀ q : ℂ, analyticOrderNatAt (spectralComplex N (residualOperator ha N)) q =
      analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (conj q)) ∧
    Even (analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (1 / 2)) ∧
    (∀ q u : Quaternion ℝ, ‖u‖ = 1 →
      spectralQuaternion N (residualOperator ha N) q = 0 →
      spectralQuaternion N (residualOperator ha N) (u * q * star u) = 0) := by sorry

/-! Semantic audit supplements. All proofs remain explicit review obligations. -/

theorem proposition_5_1_fueter_equation (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (s z : ℂ)
    (hsz : (s, conj z) ∈ analyticDomain) :
    fueterOperator (fun u v => residual N u (conj v)) s z = 0 := by sorry

theorem lemma_5_2_representation_spec (a b : ℝ) (hab : a < b) :
    (∀ ψ : HardySpace a b,
      (∀ s ∈ strip a b, Integrable (fun τ : ℝ => ψ τ * Complex.exp (s * τ))) ∧
      IsBoundaryTrace hab ψ (boundaryTraces hab ψ).1 (boundaryTraces hab ψ).2 ∧
      Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * hardyWeight a b τ) ∧
      ‖ψ‖ ^ 2 = ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * hardyWeight a b τ) ∧
    (∀ ψ χ : HardySpace a b, ∀ s ∈ strip a b,
      fourierLaplace (ψ + χ) s = fourierLaplace ψ s + fourierLaplace χ s) ∧
    (∀ c : ℂ, ∀ ψ : HardySpace a b, ∀ s ∈ strip a b,
      fourierLaplace (c • ψ) s = c * fourierLaplace ψ s) ∧
    (∀ ψ χ : HardySpace a b,
      boundaryTraces hab (ψ + χ) = boundaryTraces hab ψ + boundaryTraces hab χ) ∧
    (∀ c : ℂ, ∀ ψ : HardySpace a b,
      boundaryTraces hab (c • ψ) = c • boundaryTraces hab ψ) ∧
    (∀ ψ χ : HardySpace a b, ‖ψ - χ‖ ^ 2 =
      ‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖ ^ 2 +
      ‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖ ^ 2) := by sorry

theorem proposition_5_3_kernel_integrability (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    ∀ (h : HardySpace (alpha N) beta) (s : ℂ), s ∈ strip (alpha N) beta →
      Integrable (fun t : ℝ => weightedKernel N s (line (alpha N) t) *
        (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => weightedKernel N s (line beta t) *
        (boundaryTraces ha h).2 t) := by sorry

/-- Validity of the chosen HS norm, including independence of the Hilbert basis. -/
theorem proposition_5_3_hs_basis_independent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ℕ ℂ H) :
    Summable (fun j => ‖T (b j)‖ ^ 2) ∧
    hsNorm T ^ 2 = ∑' j, ‖T (b j)‖ ^ 2 := by sorry

theorem proposition_5_4_kernel_pairing (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (s z : ℂ) (hs : s ∈ strip (alpha N) beta) (hz : z ∈ strip (alpha N) beta) :
    weightedKernel N s z =
      paperInner (residualOperator ha N (evaluationVector z)) (evaluationVector s) := by sorry

theorem proposition_5_4_fixed_contour : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
      ∀ ha : alpha N < beta, ∀ v t : ℝ,
        ‖residual N (line sigmaStar v) (line sigmaStar t)‖ ≤
          C * ‖residualOperator ha N‖ * (1 + |v| + |t|) ^ 2 := by sorry

/-- The positive trace-class spectral determinant is based on A's own spectrum.
The summability, nonnegative spectrum and determinant convergence are conclusions,
not additional hypotheses imposed on any original paper theorem. -/
theorem proposition_6_1_positive_fredholm_spec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H)
    (hA : IsPositiveTraceClass A) :
    IsCompactOperator A ∧ IsHilbertSchmidt A ∧ Nonempty (SpectralData A) ∧
    (∀ j, 0 ≤ eigenvalues A j) ∧ Summable (eigenvalues A) ∧
    positiveTrace A = ∑' j, eigenvalues A j ∧
    (∀ b : HilbertBasis ℕ ℂ H,
      Summable (fun j => (paperInner (A (b j)) (b j)).re) ∧
      positiveTrace A = ∑' j, (paperInner (A (b j)) (b j)).re) ∧
    (∀ t : ℂ, Multipliable (fun j : ℕ => 1 - t * (eigenvalues A j : ℂ))) := by sorry

theorem proposition_6_1_square_determinant (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    let T := residualOperator ha N
    Nonempty (SpectralData (T.comp T)) ∧
    positiveTrace (T.comp T) = ∑' j, eigenvalues T j ^ 2 ∧
    (∀ t : ℂ, Multipliable (fun j : ℕ => 1 - t * (eigenvalues T j : ℂ) ^ 2) ∧
      fredholmSquareDet T t = ∏' j : ℕ, (1 - t * (eigenvalues T j : ℂ) ^ 2)) := by sorry

theorem proposition_6_1_all_slices (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (J : Quaternion ℝ) (hJre : J.re = 0) (hJsq : J ^ 2 = -1) (z : ℂ) :
    spectralQuaternion N (residualOperator ha N) ((z.re : Quaternion ℝ) + z.im • J) =
      ((spectralComplex N (residualOperator ha N) z).re : Quaternion ℝ) +
        (spectralComplex N (residualOperator ha N) z).im • J := by sorry

/-- A different diagonalizing Hilbert basis must give the same spectral product. -/
theorem proposition_6_1_spectral_choice_independent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (d₁ d₂ : SpectralData T) (t : ℂ) :
    (∏' j : ℕ, (1 - t * (d₁.values j : ℂ) ^ 2)) =
      ∏' j : ℕ, (1 - t * (d₂.values j : ℂ) ^ 2) := by sorry

/-- Hardy-space realization of the diagonal vector in the proof of Proposition 6.5.
Outside the stated strip/n range this is only a totalized choice. -/
def diagonalHardyVector {a : ℝ} (n : ℕ) : HardySpace a beta :=
  if h : ∃ d : HardySpace a beta, ∀ s ∈ strip a beta,
      fourierLaplace d s = diagonalVector n s
  then Classical.choose h else 0

theorem proposition_6_5_diagonal_vector_spec (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (ha : alpha N < beta) (n : ℕ) (hn : 1 ≤ n) :
    let d : HardySpace (alpha N) beta := diagonalHardyVector n
    (∀ s ∈ strip (alpha N) beta, fourierLaplace d s = diagonalVector n s) ∧
    ((boundaryTraces ha d).1 =ᵐ[volume] fun t : ℝ => diagonalVector n (line (alpha N) t)) ∧
    ((boundaryTraces ha d).2 =ᵐ[volume] fun t : ℝ => diagonalVector n (line beta t)) ∧
    ‖d‖ ^ 2 = Real.pi * (Real.rpow n (-2 * alpha N) / (1 + alpha N) +
      Real.rpow n (-2 * beta) / (1 + beta)) ∧
    (∀ h : HardySpace (alpha N) beta,
      InnerProductSpace.rankOne ℂ d d h = paperInner h d • d) := by sorry

theorem lemma_6_4_zero_poisson_convergence (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (x t : ℝ) (hx : 0 < x) :
    Summable (fun p : ZeroIndex χ.primitiveCharacter =>
      x / (x ^ 2 + (t - p.val.1.im) ^ 2)) := by sorry

/-- The smoothed Perron kernel has residue 1 at zero. Its totalized value at zero
is not used for this meromorphic statement (source TeX lines 2735--2737). -/
theorem lemma_6_4_perron_residue (X : ℝ) (hX : 1 < X) :
    MeromorphicOn (smoothedPerronKernel X) Set.univ ∧
    Tendsto (fun v : ℂ => v * smoothedPerronKernel X v)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by sorry

/-- Normalization is for a strictly positive kernel parameter; the zero-parameter
identity belongs to the action, not to the ordinary kernel function. -/
theorem lemma_6_4_poisson_action_spec :
    (∀ f : ℝ → ℝ, poissonAction 0 f = f) ∧
    ∀ ℓ : ℝ, 0 < ℓ →
      Integrable (poissonKernelReal ℓ) ∧
      (∀ t : ℝ, 0 ≤ poissonKernelReal ℓ t) ∧
      (∫ t : ℝ, poissonKernelReal ℓ t) = 1 ∧
      ∀ f : ℝ → ℝ,
        poissonAction ℓ f = realConvolution (poissonKernelReal ℓ) f := by sorry

/-- The convolution and comparison used to transfer the weighted boundary energy.
This states the positive-parameter calculation; ℓ=0 is handled by poissonAction. -/
theorem lemma_6_4_poisson_convolution (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ) :
    Integrable (fun u : ℝ => poissonKernelReal 1 u * poissonKernelReal ℓ (t - u)) ∧
    realConvolution (poissonKernelReal 1) (poissonKernelReal ℓ) t =
      poissonKernelReal (1 + ℓ) t ∧
    poissonKernelReal (1 + ℓ) t ≤ (1 + ℓ) * poissonKernelReal 1 t := by sorry


theorem lemma_7_2_absolute_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        diagonalSeries N (line σ p.1 + line σ p.2)) ∧
    Integrable (fun p : ℝ × ℝ =>
      mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        continuedDensity N (line σ p.1 + line σ p.2) *
        betaKernel (line σ p.1) (line σ p.2)) := by sorry

theorem proposition_7_3_absolute_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        residual N (line σ p.1) (line σ p.2)) := by sorry

end ConditionalGoldbach


namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

/-- Appendix A.3, the two-sided balance and the corresponding width gain. -/
theorem lemma_A_3_balance (φ : ℝ → ℝ) (hφ : IsWeight φ) (C : ℝ) (hC : 0 < C) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ EvenEventually (fun N =>
      ∀ c : ℝ, 0 < c → alpha N c < 1 / 10 →
        L * Real.log N ^ 2 * balanceFactor c ≤
          normFunctional N φ (alpha N c) * baselineBound C N (alpha N c) ∧
        normFunctional N φ (alpha N c) * baselineBound C N (alpha N c) ≤
          U * Real.log N ^ 2 * balanceFactor c ∧
        ∀ h : ℕ → ℝ, 0 < h N →
          L ^ 2 * h N ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2 ≤
            h N ^ 2 * (normFunctional N φ (alpha N c) * baselineBound C N (alpha N c)) ^ 2 /
              singularSeries N ^ 2 ∧
          h N ^ 2 * (normFunctional N φ (alpha N c) * baselineBound C N (alpha N c)) ^ 2 /
              singularSeries N ^ 2 ≤
            U ^ 2 * h N ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2) := by sorry

/-- Raw Hardy boundary data also preserve the paper's inner product convention. -/
theorem lemma_5_2_boundary_inner (a b : ℝ) (hab : a < b) (h g : HardySpace a b) :
    paperInner h g =
      (∫ t : ℝ, (boundaryTraces hab h).1 t * conj ((boundaryTraces hab g).1 t)) +
      ∫ t : ℝ, (boundaryTraces hab h).2 t * conj ((boundaryTraces hab g).2 t) := by sorry

/-- The original local prime-density factor in Lemma 4.1. -/
def localDensityFactor (p h : ℕ) : ℝ :=
  (1 - (if p ∣ h then 1 else 2) / (p : ℝ)) / (1 - (p : ℝ)⁻¹) ^ 2

theorem lemma_4_1_local_density (h : ℕ) (hh : Even h) (hpos : 0 < h) :
    (∏' p : ℕ, if p.Prime then localDensityFactor p h else 1) = singularSeries h := by sorry

/-- Both sides represent the same meromorphic function on C²: a common quotient
of entire functions with denominator not identically zero. Values of totalized Gamma
at poles are not mistaken for values of the meromorphic germ. This statement has
no caller-supplied Gamma nonvanishing assumptions. -/
theorem lemma_4_2_meromorphic :
    ∃ A B : ℂ × ℂ → ℂ,
      Differentiable ℂ A ∧ Differentiable ℂ B ∧ B ≠ 0 ∧
      ∀ p : ℂ × ℂ, B p ≠ 0 →
        betaGamma (1 / 2 - p.1) (p.1 + p.2) +
          betaGamma (1 / 2 - p.2) (p.1 + p.2) -
          betaGamma (1 / 2 - p.1) (1 / 2 - p.2) = A p / B p ∧
        (2 : ℂ) ^ (1 - (p.1 + p.2)) * Gamma (p.1 + p.2) *
          Complex.cos (Real.pi * (p.1 + p.2) / 2) *
          gammaQuotient p.1 * gammaQuotient p.2 = A p / B p := by sorry

/-- Joint meromorphic continuation, with an explicit common entire denominator.
Its zeros are precisely the permitted zero loci of the individual odd L-functions.
Mathlib's one-variable MeromorphicOn alone does not express this C² assertion. -/
theorem proposition_3_2_joint_meromorphic (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) :
    let B : ℂ × ℂ → ℂ := fun p => ∏ χ ∈ oddCharacters N,
      χ.LFunction (1 / 2 + p.1) * χ.LFunction (1 / 2 + p.2)
    Differentiable ℂ B ∧ B ≠ 0 ∧
    (∃ A : ℂ × ℂ → ℂ, Differentiable ℂ A ∧
      ∀ p : ℂ × ℂ, B p ≠ 0 → characterKernel N p.1 p.2 = A p / B p) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => characterKernel N p.1 p.2)
      {p | ∀ χ ∈ oddCharacters N,
        χ.LFunction (1 / 2 + p.1) ≠ 0 ∧ χ.LFunction (1 / 2 + p.2) ≠ 0} := by sorry

/-- Connect the literal paired-ordinate notation (3.6) to the zero-index form (3.8). -/
theorem lemma_3_4_paired_zero_sum (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (s : ℂ) (hs : 0 < s.re) :
    zeroDifference χ.primitiveCharacter (1 / 2 + s) 2 = pairedZeroSum χ s := by sorry

/-- The signed continuous model retains the +,+,- signs and the common density.
The three separate integral identities and their integrability are stated above. -/
theorem lemma_4_1_signed_model (h : ℝ) (hh : 0 < h)
    (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    let I₁ := ∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)
    let I₂ := ∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (-1 / 2 - z) * (x + h : ℂ) ^ (-1 / 2 - s)
    let I₃ := ∫ x in Ioo (0 : ℝ) h,
      (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)
    I₁ + I₂ - I₃ = (h : ℂ) ^ (-(s + z)) * betaKernel s z ∧
    ∀ N k : ℕ, Even N → 4 ≤ N → 0 < k → h = (k * N : ℕ) →
      (singularSeries (k * N) : ℂ) * (I₁ + I₂ - I₃) =
        singularSeries (k * N) * (h : ℂ) ^ (-(s + z)) * betaKernel s z := by sorry

/-- Convergence obligations for the actual tprod, and holomorphy on its stated domain.
These prevent a totalized product or tsum from standing in for a convergent expression. -/
theorem lemma_4_3_euler_product_convergence (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    NormallySummableOn (fun p : ℕ => fun w : ℂ =>
      if p.Prime ∧ 2 < p ∧ ¬p ∣ N then (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 0)
      {w | 0 < w.re} ∧
    (∀ w : ℂ, 0 < w.re → Multipliable (fun p : ℕ =>
      if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
        1 + (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 1)) ∧
    DifferentiableOn ℂ (densityEulerProduct N) {w | 0 < w.re} ∧
    DifferentiableOn ℂ (diagonalSeries N) {w | 0 < w.re} := by sorry

/-- Abstract zero--norm dictionary extracted from the proof of Theorem 6.1.
A real diagonal Hilbert basis with square-summable values suffices; compactness,
selfadjointness and Hilbert--Schmidt membership follow from these data.
This bridge also applies to Appendix A's moving-strip realization. Its existence
and positive scale are conclusions of earlier paper results, not extra assumptions
on the original Appendix A statements. The proof remains a review obligation. -/
theorem theorem_6_1_abstract_dictionary {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (hδ : 0 < spectralScale N) :
    ((∀ q : Quaternion ℝ, spectralQuaternion N T q = 0 → q.re = 1 / 2) ↔
      ‖T‖ ≤ spectralScale N) ∧
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ((∀ q : Quaternion ℝ, 1 - η < q.re → spectralQuaternion N T q ≠ 0) ↔
        ‖T‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η)))) := by sorry

/-- Quantitative comparison in Theorem 6.1 for the width obtained from a norm bound. -/
theorem theorem_6_1_width_comparison (N : ℕ) (M : ℝ)
    (hδ : 0 < spectralScale N) (hM : spectralScale N < M) :
    spectralScale N ^ 2 / (4 * M ^ 2) ≤ spectralWidthFromBound N M ∧
      spectralWidthFromBound N M ≤ spectralScale N ^ 2 / (2 * M ^ 2) := by sorry

/-- The weight-dependent uniform bound stated at the end of Theorem 7.1. -/
theorem theorem_7_1_uniform (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (ha : alpha N < beta) :
    |weightMass φ * singularSeries N - goldbach N φ| ≤
      Real.exp 2 * weightEnergy φ * ‖residualOperator ha N‖ := by sorry

/-- The ratio in Lemma A.3 expressed using actual admissible zero-free widths.
The required norm is the one supplied by the Cauchy--Schwarz error bound. -/
theorem lemma_A_3_width_ratio (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (C : ℝ) (hC : 0 < C) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ EvenEventually (fun N =>
      ∀ c h : ℝ, 0 < c → alpha N c < 1 / 10 → 0 < h →
        let requiredNorm := singularSeries N / (h * normFunctional N φ (alpha N c))
        let suppliedNorm := baselineBound C N (alpha N c)
        let requiredWidth := spectralWidthFromBound N requiredNorm
        let suppliedWidth := spectralWidthFromBound N suppliedNorm
        0 < spectralScale N → spectralScale N < requiredNorm →
        spectralScale N < suppliedNorm → requiredWidth ≤ 1 / 4 →
        suppliedWidth ≤ 1 / 4 →
          L * h ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2 ≤
            requiredWidth / suppliedWidth ∧
          requiredWidth / suppliedWidth ≤
            U * h ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2) := by sorry

end ConditionalGoldbach


namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

/-- Lemma 7.1: both inversion integrals are absolutely convergent; the double
character identity is also stated here so (7.2) and (7.3) remain together. -/
theorem lemma_7_1_absolute_convergence (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ σ u : ℝ, 0 < u → Integrable (fun t : ℝ =>
      mellinWeight φ (line σ t) * (u : ℂ) ^ (-line σ t))) ∧
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
      ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 →
        (∀ χ ∈ oddCharacters N, Integrable (fun t : ℝ =>
          (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) * logDerivative χ (line σ t))) ∧
        Integrable (fun p : ℝ × ℝ =>
          (N : ℂ) ^ (line σ p.1 + line σ p.2) * mellinWeight φ (line σ p.1) *
            mellinWeight φ (line σ p.2) * characterKernel N (line σ p.1) (line σ p.2)) ∧
        (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
          (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z))) := by sorry

/-- Equation (7.4): the positive-half-line implementation agrees with the paper's
finite interval because the weight is zero outside its positive support. -/
theorem lemma_7_2_convolutions (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ y : ℝ,
      IntegrableOn (fun u : ℝ => φ u * φ (u + y)) (Ioi 0) ∧
      IntegrableOn (fun u : ℝ => φ u * φ (y - u)) (Ioi 0) ∧
      sumConvolution φ y = ∫ u in (0 : ℝ)..y, φ u * φ (y - u)) ∧
    sumConvolution φ 1 = weightMass φ ∧ IntegrableOn φ (Ioi 0) := by sorry

/-- The numerical integral defining Q is not used via the default value of a
nonintegrable Bochner integral. This holds for every real a when N is positive. -/
theorem proposition_7_4_norm_integrals (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (a : ℝ) :
    IntegrableOn (fun u : ℝ => derivativeWeight φ u ^ 2 / u) (Ioi 0) ∧
    IntegrableOn (fun u : ℝ =>
      Real.rpow (N * u) (2 * a) * derivativeWeight φ u ^ 2 /
        (1 + Real.rpow (N * u) (-2 * (beta - a))) / u) (Ioi 0) := by sorry

/-- The asymptotic criterion (7.20) in uniform epsilon form. It applies along any
sequence of even moduli satisfying the hypotheses, without assuming GRH elsewhere. -/
theorem lemma_7_5_asymptotic (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
        ∀ ha : alpha N < beta, ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
          SpectralZeroFree N (alpha N) ha η →
          B ≤ N * η * singularSeries N / Real.log N ^ 3 →
          |goldbach N φ / (weightMass φ * singularSeries N) - 1| < ε := by sorry

/-- Appendix A.2: the arithmetic estimates are local in N and their constant
is chosen before the width h. No assertion of GRH for other moduli is needed. -/
theorem proposition_A_2_pointwise (φ : ℝ → ℝ) (hφ : IsWeight φ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
      Real.exp (10 * c) < (N : ℝ) → GRH N → ∀ ha : alpha N c < beta,
        (∀ h : ℕ → ℝ, 0 < h N → 0 < zeroFreeWidth N h → zeroFreeWidth N h ≤ 1 / 4 →
          SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h) →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * singularSeries N / h N) ∧
        (SpectralR N (alpha N c) ha →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N) := by sorry

/-- The constant in Lemma A.3 is absolute: no weight parameter precedes it.
The threshold is likewise independent of the moving left boundary a. -/
theorem lemma_A_3_absolute_operator_bound :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N => ∀ (_ : NeZero N), GRH N →
      ∀ a : ℝ, 0 < a → a < 1 / 10 → ∀ ha : a < beta,
        ‖residualOperator ha N‖ ≤ baselineBound C N a) := by sorry

/-- The Euler product introduced in the proof of A.4 has its analytic meaning
near zero; outside this domain the totalized product carries no such assertion. -/
theorem proposition_A_4_baseline_product (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε →
      Multipliable (fun p : ℕ => if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
        1 + (2 * (p : ℂ) ^ (-w) - (p : ℂ) ^ (-2 * w)) / ((p : ℂ) * ((p : ℂ) - 2))
        else 1) ∧ DifferentiableAt ℂ (baselineProductR N) w) ∧
    (singularSeries N : ℂ) * baselineProductR N 0 = 1 := by sorry

/-- Appendix B.3, the defining identity relating the main integral to c_f,
and its exact residual decomposition. Numerical quadrature is not assumed. -/
theorem lemma_B_3_main_integral :
    wideMainIntegral = (experimentN : ℝ) * singularSeries experimentN * wideModelMass / 2 ∧
    (unorderedPrimePairs : ℝ) = wideMainIntegral - (experimentN : ℝ) / 2 * wideResidual -
      primePowerCorrection / 2 + edgeCorrection := by sorry

/-- The wide weight is not an IsWeight weight: its support is much larger.
These are its own regularity and compact-support obligations used in B.4. -/
theorem proposition_B_4_weight :
    ContDiff ℝ 6 wideWeight ∧ HasCompactSupport wideWeight ∧
    Function.support wideWeight ⊆ Ioo (0 : ℝ) 1 ∧
    IntervalIntegrable (fun u : ℝ => wideWeight u * wideWeight (1 - u)) volume 0 1 ∧
    IntervalIntegrable (fun x : ℝ => wideCutoff x ^ 2 /
      (Real.log x * Real.log ((experimentN : ℝ) - x))) volume 16 ((experimentN : ℝ) / 2) := by sorry

/-- Appendix A.1 reuses the actual kernel realization at the moving boundary.
The fixed-alpha statement in Section 5 does not by itself validate this choice.
These are conclusions on the original domain, never extra caller assumptions. -/
theorem proposition_A_1_operator_spec (N : ℕ) [NeZero N] (hN : Even N)
    (hN4 : 4 ≤ N) (c : ℝ) (hc : 0 < c) (hlarge : Real.exp (10 * c) < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N c < beta) :
    (∀ x ∈ ({alpha N c, beta} : Finset ℝ), ∀ y ∈ ({alpha N c, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    Nonempty (SpectralData (residualOperator ha N)) ∧
    (∀ (h : HardySpace (alpha N c) beta) (s : ℂ), s ∈ strip (alpha N c) beta →
      Integrable (fun t : ℝ => weightedKernel N s (line (alpha N c) t) *
        (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => weightedKernel N s (line beta t) *
        (boundaryTraces ha h).2 t)) := by sorry


end ConditionalGoldbach
