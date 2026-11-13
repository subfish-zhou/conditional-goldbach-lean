import ConditionalGoldbach

/-!
Independent statement reference for Li--Liu, Appendices A and B.
Read from TeX lines 3931--4599 and reconciled against the live declarations.
These are propositions as DATA, not proofs or axioms. Shared analytic objects
retain their live names; the definition rows explicitly record that boundary.
No previous Reviewed.lean file is used by this file or its construction.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex ConditionalGoldbach
namespace TexAuditAB
attribute [local instance] Classical.propDecidable

-- A: boundary parameter, fixed-c quantifiers, and fixed-modulus poles.
def boundaryParameter (N : ℕ) (c : ℝ) : ℝ := c / Real.log N
def eventualR (c : ℝ) : Prop := EvenEventually (fun N => GRH N →
  ∀ (_ : NeZero N) (ha : alpha N c < beta), SpectralR N (alpha N c) ha)
def eventualS (c : ℝ) (h : ℕ → ℝ) : Prop := IsAdmissible h ∧
  EvenEventually (fun N => GRH N → ∀ (_ : NeZero N) (ha : alpha N c < beta),
    SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h))
def poleOrder {N : ℕ} [NeZero N] (χ : Character N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt χ.LFunction ρ
def poleMass (N : ℕ) [NeZero N] (γ : ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    (analyticOrderNatAt χ.LFunction (line (1 / 2) γ) : ℝ) ^ 2
def regularEulerFactor (N : ℕ) (w : ℂ) : ℂ :=
  (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-1 - w))) *
  ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
    1 + (2 * (p : ℂ) ^ (-w) - (p : ℂ) ^ (-2 * w)) / ((p : ℂ) * ((p : ℂ) - 2))
  else 1
def operatorMajorant (C : ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  C * (Real.log N ^ 2 + a⁻¹ ^ 2)
def boundaryCost (c : ℝ) : ℝ := Real.exp (2 * c) * (1 + c⁻¹ ^ 2)

-- B: zero-extended C6 weight. W is the companion, f is the wide weight.
def numericalN : ℕ := 30030
def P (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
    ∑ j ∈ Finset.Icc 7 13, (Nat.choose 13 j : ℝ) * t ^ j * (1 - t) ^ (13 - j)
def eta (x : ℝ) : ℝ :=
  P ((x - 16) / (1000 - 16)) * P ((30030 - x - 16) / (1000 - 16))
def W (u : ℝ) : ℝ :=
  if u ∈ Ioo (16 / 30030 : ℝ) (1 - 16 / 30030 : ℝ) then
    Real.sqrt (1 - u) * eta (30030 * u) /
      Real.sqrt (Real.log (30030 * u) * Real.log (30030 * (1 - u))) else 0
def f (u : ℝ) : ℝ := W u / Real.sqrt u
def J : ℝ := goldbach 30030 f
def primePairCount : ℕ := ((Finset.range (30030 + 1)).filter
  (fun p => p.Prime ∧ (30030 - p).Prime ∧ p ≤ 30030 - p)).card
def edge : ℝ := ∑ p ∈ Finset.range 1000,
  if p.Prime ∧ (30030 - p).Prime ∧ p ≤ 30030 - p
  then 1 - eta p ^ 2 else 0
def properPowers : ℝ :=
  ∑ p ∈ Finset.range (30030 + 1), ∑ q ∈ Finset.range (30030 + 1),
    ∑ k ∈ Finset.range (30030 + 1), ∑ l ∈ Finset.range (30030 + 1),
      if p.Prime ∧ q.Prime ∧ 0 < k ∧ 0 < l ∧ 2 ≤ max k l ∧
        p ^ k + q ^ l = 30030 ∧ Nat.Coprime (p * q) 30030
      then eta (p ^ k) ^ 2 / (k * l : ℕ) else 0
def coefficient (n : ℕ) : ℝ := mangoldt n / Real.sqrt n * W (n / 30030)
def integralI (χ : Character 30030) : ℂ :=
  verticalMellin 1 (fun s => (30030 : ℂ) ^ s *
    mellin (fun u => (W u : ℂ)) s * logDerivative χ s)
def diagonalD : ℝ := ∑ n ∈ Finset.range 30030,
  if Nat.Coprime n 30030 then coefficient n ^ 2 else 0
def signedJhat (Ihat : Character 30030 → ℂ) : ℝ :=
  (5760 : ℝ)⁻¹ * (∑ χ : Character 30030, (χ (-1)).re * ‖Ihat χ‖ ^ 2)
def diagonalDhat (Ihat : Character 30030 → ℂ) : ℝ :=
  (5760 : ℝ)⁻¹ * ∑ χ : Character 30030, ‖Ihat χ‖ ^ 2
def crossMass : ℝ := ∫ u in (0 : ℝ)..1, f u * f (1 - u)
def mainIntegral : ℝ := singularSeries 30030 *
  ∫ x in (16 : ℝ)..((30030 : ℝ) / 2),
    eta x ^ 2 / (Real.log x * Real.log ((30030 : ℝ) - x))
def residualB : ℝ := crossMass * singularSeries 30030 - J
def momentError (Ihat : Character 30030 → ℂ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ (5760 : ℝ)⁻¹ * ∑ χ : Character 30030,
    ‖integralI χ - Ihat χ‖ ^ 2 ≤ ε ^ 2
def countCentre (Ihat : Character 30030 → ℂ) : ℝ :=
  (30030 : ℝ) / 2 * signedJhat Ihat - properPowers / 2 + edge
def countRadius (Ihat : Character 30030 → ℂ) (ε : ℝ) : ℝ :=
  (30030 : ℝ) / 2 * (2 * Real.sqrt (diagonalDhat Ihat) * ε + ε ^ 2)
def ellW {a : ℝ} (h : HardySpace a beta) : ℂ :=
  verticalMellin sigmaStar (fun s => (30030 : ℂ) ^ s *
    mellin (fun u => (W u : ℂ)) s * (1 + s) * fourierLaplace h s)
def vectorW : HardySpace (alpha 30030) beta :=
  if h : ∃ v : HardySpace (alpha 30030) beta, ∀ g, ellW g = paperInner g v
  then Classical.choose h else 0
def node (i : Fin 2562) : ℂ :=
  line (if i.val < 1281 then alpha 30030 else beta) (((i.val % 1281 : ℕ) : ℝ) / 16 - 40)
def nodeWeight (i : Fin 2562) : ℝ :=
  (1 / 16) * if i.val % 1281 = 0 ∨ i.val % 1281 = 1280 then 1 / 2 else 1
def matrixC : Matrix (Fin 2562) (Fin 2562) ℂ :=
  fun i j => (Real.sqrt (nodeWeight i) : ℂ) *
    weightedKernel 30030 (node i) (node j) * Real.sqrt (nodeWeight j)
def finiteX (q : ℂ) : ℂ :=
  Matrix.det (1 - (4 * q * (1 - q) / spectralScale 30030 ^ 2) • (matrixC * matrixC))
def finiteSpectrum (ev : Fin 2562 → ℝ) : Prop :=
  ∃ U : Matrix (Fin 2562) (Fin 2562) ℂ,
    star U * U = 1 ∧ U * star U = 1 ∧
    matrixC = U * Matrix.diagonal (fun i => (ev i : ℂ)) * star U
def eigenvalueList : Fin 2562 → ℝ :=
  if h : ∃ ev, finiteSpectrum ev then Classical.choose h else 0
def matrixNorm : ℝ :=
  sSup {r : ℝ | ∃ x : EuclideanSpace ℂ (Fin 2562), ‖x‖ = 1 ∧
    r = ‖(WithLp.toLp 2 (matrixC.mulVec (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin 2562))‖}

-- A.1: fixed φ,c; C and N0 may depend on these, never on N.
def A1 : Prop := ∀ (φ : ℝ → ℝ), IsWeight φ → ∀ c : ℝ, 0 < c →
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
      |normFunctional N φ (alpha N c) - Real.exp (2 * c) * weightEnergy φ| ≤ C / Real.log N))

def A1_operator : Prop := ∀ (N : ℕ) [NeZero N], Even N → 4 ≤ N →
  ∀ c : ℝ, 0 < c → Real.exp (10 * c) < (N : ℝ) → GRH N → ∀ ha : alpha N c < beta,
    (∀ x ∈ ({alpha N c, beta} : Finset ℝ), ∀ y ∈ ({alpha N c, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    Nonempty (SpectralData (residualOperator ha N)) ∧
    (∀ (h : HardySpace (alpha N c) beta) (s : ℂ), s ∈ strip (alpha N c) beta →
      Integrable (fun t : ℝ => weightedKernel N s (line (alpha N c) t) *
        (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => weightedKernel N s (line beta t) * (boundaryTraces ha h).2 t))

-- A.2: the ∃C is outside ∀h. N0 is inside EvenEventually and may depend on h.
def A2 : Prop := ∀ (φ : ℝ → ℝ), IsWeight φ → ∀ c : ℝ, 0 < c →
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
      (HypothesisRAt c → EvenEventually (fun N => GRH N →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N)))

def A2_pointwise : Prop := ∀ (φ : ℝ → ℝ), IsWeight φ → ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
      Real.exp (10 * c) < (N : ℝ) → GRH N → ∀ ha : alpha N c < beta,
        (∀ h : ℕ → ℝ, 0 < h N → 0 < zeroFreeWidth N h → zeroFreeWidth N h ≤ 1 / 4 →
          SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h) →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * singularSeries N / h N) ∧
        (SpectralR N (alpha N c) ha →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N)

-- Separately required: the operator/GRH-width constants do not depend on φ.
def A2_uniform : Prop := ∀ c : ℝ, 0 < c →
    ∃ C c₀ : ℝ, 1 ≤ C ∧ 0 < c₀ ∧ EvenEventually (fun N =>
      ∀ (_ : NeZero N) (ha : alpha N c < beta), GRH N →
        IsHilbertSchmidt (residualOperator ha N) ∧
        ‖residualOperator ha N‖ ≤ hsNorm (residualOperator ha N) ∧
        hsNorm (residualOperator ha N) ≤ C * Real.log N ^ 2 ∧
        SpectralZeroFree N (alpha N c) ha (c₀ * singularSeries N / (N * Real.log N)))

def A3 : Prop := ∀ (φ : ℝ → ℝ), IsWeight φ →
    (∃ C L U : ℝ, 0 < C ∧ 0 < L ∧ 0 < U ∧
      EvenEventually (fun N => ∀ (_ : NeZero N), GRH N → ∀ a : ℝ, 0 < a → a < 1 / 10 →
        L * Real.rpow N (2 * a) ≤ normFunctional N φ a ∧
        normFunctional N φ a ≤ U * Real.rpow N (2 * a) ∧
        ∀ ha : a < beta, ‖residualOperator ha N‖ ≤ baselineBound C N a)) ∧
    Tendsto balanceFactor (nhdsWithin 0 (Ioi 0)) atTop ∧ Tendsto balanceFactor atTop atTop

def A3_absolute : Prop :=
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N => ∀ (_ : NeZero N), GRH N →
      ∀ a : ℝ, 0 < a → a < 1 / 10 → ∀ ha : a < beta,
        ‖residualOperator ha N‖ ≤ baselineBound C N a)

def A3_balance : Prop := ∀ (φ : ℝ → ℝ), IsWeight φ → ∀ C : ℝ, 0 < C →
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
            U ^ 2 * h N ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2)

def A3_widths : Prop := ∀ (φ : ℝ → ℝ), IsWeight φ → ∀ C : ℝ, 0 < C →
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ EvenEventually (fun N =>
      ∀ c h : ℝ, 0 < c → alpha N c < 1 / 10 → 0 < h →
        let requiredNorm := singularSeries N / (h * normFunctional N φ (alpha N c))
        let suppliedNorm := baselineBound C N (alpha N c)
        let requiredWidth := spectralWidthFromBound N requiredNorm
        let suppliedWidth := spectralWidthFromBound N suppliedNorm
        0 < spectralScale N → spectralScale N < requiredNorm →
        spectralScale N < suppliedNorm → requiredWidth ≤ 1 / 4 → suppliedWidth ≤ 1 / 4 →
          L * h ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2 ≤
            requiredWidth / suppliedWidth ∧
          requiredWidth / suppliedWidth ≤
            U * h ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2)

def A4 : Prop := ∀ (N : ℕ) [NeZero N], Even N → 4 ≤ N → GRH N → ∀ γ : ℝ,
    (∃ χ ∈ oddCharacters N, χ.LFunction (line (1 / 2) γ) = 0) →
    0 < poleCoefficient N γ ∧
    (∀ ε : ℝ, 0 < ε → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ →
      ∀ ha : alpha N c < beta,
        2 * poleCoefficient N γ * Real.log N / (1 + γ ^ 2) - ε ≤ c * ‖residualOperator ha N‖) ∧
    (∃ z c₀ : ℝ, 0 < z ∧ 0 < c₀ ∧ c₀ ≤ Real.log N / 24 ∧
      ∀ c : ℝ, 0 < c → c < c₀ → ∀ ha : alpha N c < beta,
        z / c ≤ ‖residualOperator ha N‖ ∧ ¬SpectralR N (alpha N c) ha ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → SpectralZeroFree N (alpha N c) ha η →
          η ≤ spectralScale N ^ 2 * c ^ 2 / (3 * z ^ 2))

def A4_regular : Prop := ∀ N : ℕ, Even N → 4 ≤ N →
    (∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε →
      Multipliable (fun p : ℕ => if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
        1 + (2 * (p : ℂ) ^ (-w) - (p : ℂ) ^ (-2 * w)) / ((p : ℂ) * ((p : ℂ) - 2))
        else 1) ∧ DifferentiableAt ℂ (baselineProductR N) w) ∧
    (singularSeries N : ℂ) * baselineProductR N 0 = 1

def B1 : Prop :=
    ContDiff ℝ 6 wideCutoff ∧ (∀ x : ℝ, wideCutoff x = wideCutoff (experimentN - x)) ∧
    (∀ x ∈ Icc (1000 : ℝ) (experimentN - 1000), wideCutoff x = 1) ∧
    (∀ u ∈ Ioo (16 / experimentN : ℝ) (1 - 16 / experimentN : ℝ),
      wideWeight u * wideWeight (1 - u) = wideCutoff (experimentN * u) ^ 2 /
        (Real.log (experimentN * u) * Real.log (experimentN * (1 - u)))) ∧
    (unorderedPrimePairs : ℝ) = (experimentN : ℝ) / 2 * wideCorrelation - primePowerCorrection / 2 + edgeCorrection

def B2 : Prop :=
    (∀ χ : Character experimentN,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line 1 t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line 1 t) * logDerivative χ (line 1 t)) ∧
      countingIntegral χ = -∑ n ∈ Finset.range experimentN, (countingCoefficient n : ℂ) * χ n) ∧
    wideCorrelation = approxSignedMoment countingIntegral ∧
    diagonalCountingMoment = approxDiagonalMoment countingIntegral

def B3 : Prop := ∀ (Ihat : Character experimentN → ℂ) (ε : ℝ), 0 ≤ ε →
    (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN, ‖countingIntegral χ - Ihat χ‖ ^ 2 ≤ ε ^ 2 →
    |wideCorrelation - approxSignedMoment Ihat| ≤
      2 * Real.sqrt (approxDiagonalMoment Ihat) * ε + ε ^ 2 ∧
    |(unorderedPrimePairs : ℝ) - approxPrimeCount Ihat| ≤ countError Ihat ε ∧
    (unorderedPrimePairs : ℝ) ∈
      Icc (approxPrimeCount Ihat - countError Ihat ε) (approxPrimeCount Ihat + countError Ihat ε) ∩
        Set.range (fun k : ℤ => (k : ℝ))

def B3_main : Prop :=
    wideMainIntegral = (experimentN : ℝ) * singularSeries experimentN * wideModelMass / 2 ∧
    (unorderedPrimePairs : ℝ) = wideMainIntegral - (experimentN : ℝ) / 2 * wideResidual -
      primePowerCorrection / 2 + edgeCorrection

def B4 : Prop := GRH experimentN → ∀ ha : alpha experimentN < beta,
    (∀ h : HardySpace (alpha experimentN) beta,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line sigmaStar t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line sigmaStar t) *
        (1 + line sigmaStar t) * fourierLaplace h (line sigmaStar t)) ∧
      wideFunctional h = paperInner h wideRieszVector) ∧
    (∃ ℓ : HardySpace (alpha experimentN) beta →L[ℂ] ℂ, ∀ h, ℓ h = wideFunctional h) ∧
    (wideResidual : ℂ) = paperInner (residualOperator ha experimentN wideRieszVector) wideRieszVector

def B4_weight : Prop :=
    ContDiff ℝ 6 wideWeight ∧ HasCompactSupport wideWeight ∧
    Function.support wideWeight ⊆ Ioo (0 : ℝ) 1 ∧
    IntervalIntegrable (fun u : ℝ => wideWeight u * wideWeight (1 - u)) volume 0 1 ∧
    IntervalIntegrable (fun x : ℝ => wideCutoff x ^ 2 /
      (Real.log x * Real.log ((experimentN : ℝ) - x))) volume 16 ((experimentN : ℝ) / 2)

def B5 : Prop := GRH experimentN →
    IsFiniteSpectrum finiteEigenvalues ∧
    (∀ q : ℂ, finiteSpectralFunction q =
      ∏ j : Fin 2562, (1 - (4 * finiteEigenvalues j ^ 2 / spectralScale experimentN ^ 2 : ℝ) * q * (1 - q))) ∧
    (∀ q : ℂ, finiteSpectralFunction (1 - q) = finiteSpectralFunction q) ∧
    (finiteMatrixOpNorm ≤ spectralScale experimentN →
      ∀ q : ℂ, finiteSpectralFunction q = 0 → q.re = 1 / 2)

end TexAuditAB

-- BEGIN GENERATED DEFINITION BRIDGES

namespace TexAuditAB
theorem bridge_boundaryParameter : @TexAuditAB.boundaryParameter = @ConditionalGoldbach.alpha := rfl
theorem bridge_eventualR : @TexAuditAB.eventualR = @ConditionalGoldbach.HypothesisRAt := rfl
theorem bridge_eventualS : @TexAuditAB.eventualS = @ConditionalGoldbach.HypothesisSAt := rfl
theorem bridge_poleOrder : @TexAuditAB.poleOrder = @ConditionalGoldbach.zeroMultiplicity := rfl
theorem bridge_poleMass : @TexAuditAB.poleMass = @ConditionalGoldbach.poleCoefficient := rfl
theorem bridge_regularEulerFactor : @TexAuditAB.regularEulerFactor = @ConditionalGoldbach.baselineProductR := rfl
theorem bridge_operatorMajorant : @TexAuditAB.operatorMajorant = @ConditionalGoldbach.baselineBound := rfl
theorem bridge_boundaryCost : @TexAuditAB.boundaryCost = @ConditionalGoldbach.balanceFactor := rfl
theorem bridge_numericalN : @TexAuditAB.numericalN = @ConditionalGoldbach.experimentN := rfl
theorem bridge_P : @TexAuditAB.P = @ConditionalGoldbach.cutoffPolynomial := rfl
theorem bridge_eta : @TexAuditAB.eta = @ConditionalGoldbach.wideCutoff := rfl
theorem bridge_W : @TexAuditAB.W = @ConditionalGoldbach.wideCompanion := rfl
theorem bridge_f : @TexAuditAB.f = @ConditionalGoldbach.wideWeight := rfl
theorem bridge_J : @TexAuditAB.J = @ConditionalGoldbach.wideCorrelation := rfl
theorem bridge_primePairCount : @TexAuditAB.primePairCount = @ConditionalGoldbach.unorderedPrimePairs := rfl
theorem bridge_edge : @TexAuditAB.edge = @ConditionalGoldbach.edgeCorrection := rfl
theorem bridge_properPowers : @TexAuditAB.properPowers = @ConditionalGoldbach.primePowerCorrection := rfl
theorem bridge_coefficient : @TexAuditAB.coefficient = @ConditionalGoldbach.countingCoefficient := rfl
theorem bridge_integralI : @TexAuditAB.integralI = @ConditionalGoldbach.countingIntegral := rfl
theorem bridge_diagonalD : @TexAuditAB.diagonalD = @ConditionalGoldbach.diagonalCountingMoment := rfl
theorem bridge_signedJhat : @TexAuditAB.signedJhat = @ConditionalGoldbach.approxSignedMoment := rfl
theorem bridge_diagonalDhat : @TexAuditAB.diagonalDhat = @ConditionalGoldbach.approxDiagonalMoment := rfl
theorem bridge_crossMass : @TexAuditAB.crossMass = @ConditionalGoldbach.wideModelMass := rfl
theorem bridge_mainIntegral : @TexAuditAB.mainIntegral = @ConditionalGoldbach.wideMainIntegral := rfl
theorem bridge_residualB : @TexAuditAB.residualB = @ConditionalGoldbach.wideResidual := rfl
theorem bridge_momentError : @TexAuditAB.momentError = @ConditionalGoldbach.HasMomentError := rfl
theorem bridge_countCentre : @TexAuditAB.countCentre = @ConditionalGoldbach.approxPrimeCount := rfl
theorem bridge_countRadius : @TexAuditAB.countRadius = @ConditionalGoldbach.countError := rfl
theorem bridge_ellW : @TexAuditAB.ellW = @ConditionalGoldbach.wideFunctional := rfl
theorem bridge_vectorW : @TexAuditAB.vectorW = @ConditionalGoldbach.wideRieszVector := rfl
theorem bridge_node : @TexAuditAB.node = @ConditionalGoldbach.spectralNode := rfl
theorem bridge_nodeWeight : @TexAuditAB.nodeWeight = @ConditionalGoldbach.trapezoidWeight := rfl
theorem bridge_matrixC : @TexAuditAB.matrixC = @ConditionalGoldbach.finiteSpectralMatrix := rfl
theorem bridge_finiteX : @TexAuditAB.finiteX = @ConditionalGoldbach.finiteSpectralFunction := rfl
theorem bridge_finiteSpectrum : @TexAuditAB.finiteSpectrum = @ConditionalGoldbach.IsFiniteSpectrum := rfl
theorem bridge_eigenvalueList : @TexAuditAB.eigenvalueList = @ConditionalGoldbach.finiteEigenvalues := rfl
theorem bridge_matrixNorm : @TexAuditAB.matrixNorm = @ConditionalGoldbach.finiteMatrixOpNorm := rfl
end TexAuditAB

-- Full type assignment smoke checks; root also uses the external comparator.
example : TexAuditAB.A1 := @ConditionalGoldbach.proposition_A_1
example : TexAuditAB.A1_operator := @ConditionalGoldbach.proposition_A_1_operator_spec
example : TexAuditAB.A2 := @ConditionalGoldbach.proposition_A_2
example : TexAuditAB.A2_pointwise := @ConditionalGoldbach.proposition_A_2_pointwise
example : TexAuditAB.A2_uniform := @ConditionalGoldbach.variable_uniform_spectral_bound
example : TexAuditAB.A3 := @ConditionalGoldbach.lemma_A_3
example : TexAuditAB.A3_absolute := @ConditionalGoldbach.lemma_A_3_absolute_operator_bound
example : TexAuditAB.A3_balance := @ConditionalGoldbach.lemma_A_3_balance
example : TexAuditAB.A3_widths := @ConditionalGoldbach.lemma_A_3_width_ratio
example : TexAuditAB.A4 := @ConditionalGoldbach.proposition_A_4
example : TexAuditAB.A4_regular := @ConditionalGoldbach.proposition_A_4_baseline_product
example : TexAuditAB.B1 := @ConditionalGoldbach.proposition_B_1
example : TexAuditAB.B2 := @ConditionalGoldbach.lemma_B_2
example : TexAuditAB.B3 := @ConditionalGoldbach.lemma_B_3
example : TexAuditAB.B3_main := @ConditionalGoldbach.lemma_B_3_main_integral
example : TexAuditAB.B4 := @ConditionalGoldbach.proposition_B_4
example : TexAuditAB.B4_weight := @ConditionalGoldbach.proposition_B_4_weight
example : TexAuditAB.B5 := @ConditionalGoldbach.proposition_B_5
