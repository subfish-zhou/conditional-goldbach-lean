import LiLiuGoldbach.BaseDefinitions
import LiLiuGoldbach.Proofs.HardyBoundary

/-! Audited definitions, with interior-line square-integrability and both boundary traces proved. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
attribute [local instance] conductorNeZero
theorem interiorLine_memLp {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Ioo a b) (ψ : HardySpace a b) :
    MemLp (fun t : ℝ => fourierLaplace ψ (line x t)) 2 volume := by
  exact hardy_interiorLine_memLp hab hx ψ

def interiorLine {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (x : ℝ) (hx : x ∈ Ioo a b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (interiorLine_memLp hab hx ψ).toLp _

def IsBoundaryTrace {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (left right : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  Tendsto (fun x : Ioo a b => interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 left) ∧
  Tendsto (fun x : Ioo a b => interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 right)

theorem boundaryTraces_exist {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    ∃ p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ),
      IsBoundaryTrace hab ψ p.1 p.2 := by
  simpa only [IsBoundaryTrace, interiorLine] using hardy_boundaryTraces_exist hab ψ

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

def SpectralR (N : ℕ) [NeZero N] (a : ℝ) (ha : a < beta) : Prop :=
  ∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 → q.re = 1 / 2

def SpectralZeroFree (N : ℕ) [NeZero N] (a : ℝ) (ha : a < beta) (η : ℝ) : Prop :=
  ∀ q : Quaternion ℝ, 1 - η < q.re → spectralQuaternion N (residualOperator ha N) q ≠ 0

def HypothesisR : Prop := EvenEventually (fun N => GRH N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta), @SpectralR N _hN (alpha N) ha)

def HypothesisS (h : ℕ → ℝ) : Prop := IsAdmissible h ∧ EvenEventually (fun N => GRH N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta),
    @SpectralZeroFree N _hN (alpha N) ha (zeroFreeWidth N h))

def PrimePairCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime ∧
    (N : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ 2 * N / 3)).card

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

def arithmeticExpansionTerm (N n m : ℕ) (s z : ℂ) : ℂ :=
  if 0 < n ∧ 0 < m ∧ Nat.Coprime (n * m) N then
    (mangoldt n : ℂ) * mangoldt m / ((n : ℂ) ^ (1 / 2 + s) * (m : ℂ) ^ (1 / 2 + z)) *
      ((if (n : ZMod N) = m then 1 else 0) -
        (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)) else 0

def zeroWindow {d : ℕ} [NeZero d] (χ : Character d) (t : ℝ) : Set (ZeroIndex χ) :=
  {p | t ≤ p.val.1.im ∧ p.val.1.im < t + 1}

def wirtingerBar (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (deriv (fun x : ℝ => f (s + x)) 0 + I * deriv (fun y : ℝ => f (s + y * I)) 0) / 2

def wirtinger (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (deriv (fun x : ℝ => f (s + x)) 0 - I * deriv (fun y : ℝ => f (s + y * I)) 0) / 2

def positiveFredholmDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (t : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - t * (eigenvalues A j : ℂ))

def fredholmSquareDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (t : ℂ) : ℂ :=
  positiveFredholmDet (T.comp T) t

def HypothesisRAt (c : ℝ) : Prop := EvenEventually (fun N => GRH N →
  ∀ (_ : NeZero N) (ha : alpha N c < beta), SpectralR N (alpha N c) ha)

def HypothesisSAt (c : ℝ) (h : ℕ → ℝ) : Prop := IsAdmissible h ∧
  EvenEventually (fun N => GRH N → ∀ (_ : NeZero N) (ha : alpha N c < beta),
    SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h))

def baselineBound (C : ℝ) (N : ℕ) (a : ℝ) : ℝ := C * (Real.log N ^ 2 + a⁻¹ ^ 2)

def balanceFactor (c : ℝ) : ℝ := Real.exp (2 * c) * (1 + c⁻¹ ^ 2)

def poleCoefficient (N : ℕ) [NeZero N] (γ : ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    (analyticOrderNatAt χ.LFunction (line (1 / 2) γ) : ℝ) ^ 2

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

def wideFunctional {a : ℝ} (h : HardySpace a beta) : ℂ :=
  verticalMellin sigmaStar (fun s => (experimentN : ℂ) ^ s *
    mellin (fun u => (wideCompanion u : ℂ)) s * (1 + s) * fourierLaplace h s)

def wideRieszVector : HardySpace (alpha experimentN) beta :=
  if h : ∃ v : HardySpace (alpha experimentN) beta, ∀ f, wideFunctional f = paperInner f v
  then Classical.choose h else 0

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

def IsFiniteSpectrum (ev : Fin 2562 → ℝ) : Prop :=
  ∃ U : Matrix (Fin 2562) (Fin 2562) ℂ,
    star U * U = 1 ∧ U * star U = 1 ∧
    finiteSpectralMatrix = U * Matrix.diagonal (fun i => (ev i : ℂ)) * star U

def finiteEigenvalues : Fin 2562 → ℝ :=
  if h : ∃ ev, IsFiniteSpectrum ev then Classical.choose h else 0

def finiteMatrixOpNorm : ℝ :=
  sSup {r : ℝ | ∃ x : EuclideanSpace ℂ (Fin 2562), ‖x‖ = 1 ∧
    r = ‖(WithLp.toLp 2 (finiteSpectralMatrix.mulVec (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin 2562))‖}

def betaGamma (u v : ℂ) : ℂ := Gamma u * Gamma v / Gamma (u + v)

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

def fueterOperator (F : ℂ → ℂ → ℂ) (s z : ℂ) : Quaternion ℝ :=
  complexQuaternion (wirtingerBar (fun u => F u z) s) +
    (⟨0, 0, 1, 0⟩ : Quaternion ℝ) * complexQuaternion (wirtinger (F s) z)

def referenceLine (N : ℕ) : ℝ := 2 / Real.log N

def perronCutoff (N : ℕ) : ℝ := (N : ℝ) / 2

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

def poissonKernelReal (a t : ℝ) : ℝ := a / (Real.pi * (a ^ 2 + t ^ 2))

def realConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, f u * g (t - u)

def poissonAction (ℓ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  if ℓ = 0 then f else realConvolution (poissonKernelReal ℓ) f

def diagonalVector (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) ^ (-s) / (1 + s)

def weightIntegral (φ : ℝ → ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), φ u

def functionalIntegrand (N : ℕ) (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ s * mellinWeight φ s * (1 + s)

def availableNormMajorant (C : ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  C * (Real.log N ^ 2 + a ^ (-2 : ℤ))

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

def spectralPartialQuaternionReindexed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (N : ℕ) (T : H →L[ℂ] H)
    (e : ℕ ≃ ℕ) (q : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun acc j =>
    acc * (1 - (4 * eigenvalues T (e j) ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))) 1

def centeredSpectralPartial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (N : ℕ) (T : H →L[ℂ] H)
    (ξ : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun acc j => acc *
    (1 - (eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) +
      (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * ξ ^ 2)) 1

def diagonalHardyVector {a : ℝ} (n : ℕ) : HardySpace a beta :=
  if h : ∃ d : HardySpace a beta, ∀ s ∈ strip a beta,
      fourierLaplace d s = diagonalVector n s
  then Classical.choose h else 0

def localDensityFactor (p h : ℕ) : ℝ :=
  (1 - (if p ∣ h then 1 else 2) / (p : ℝ)) / (1 - (p : ℝ)⁻¹) ^ 2

end LiLiuGoldbach16
