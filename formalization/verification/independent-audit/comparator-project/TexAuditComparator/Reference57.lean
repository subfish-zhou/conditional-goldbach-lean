import LiLiuGoldbach

/-!
Independent reference, derived from LiLiuGoldbach16.tex §§5–7 in this audit.
No old Reviewed.lean or prior audit result is used as mathematical evidence.
`Expected_*` definitions are propositions, not assumed proofs. Definition bridges
check only the independently transcribed formula against the implementation;
mathematical validity of the TeX-to-reference transcription remains a human task.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace TexAudit57
universe u
open LiLiuGoldbach16
attribute [local instance] LiLiuGoldbach16.conductorNeZero

-- TeX 1986–2027: the frequency representation is distinct from the raw Hardy space.
def RawHardy (a b : ℝ) (h : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ h {s | a  <  s.re ∧ s.re  <  b} ∧
  ∃ bound : ℝ, ∀ ε : ℝ, 0  <  ε → ε  <  (b-a)/2 →
    Integrable (fun t : ℝ =>  ‖h ((a+ε : ℝ) + t*I)‖^2 + ‖h ((b-ε : ℝ) + t*I)‖^2) ∧
    (∫ t : ℝ, ‖h ((a+ε : ℝ) + t*I)‖^2 + ‖h ((b-ε : ℝ) + t*I)‖^2)  ≤  bound

def BoundaryWeight (a b τ : ℝ) : ℝ := Real.exp (2*a*τ) + Real.exp (2*b*τ)
abbrev FrequencySpace (a b : ℝ) := Lp ℂ 2
  (volume.withDensity (fun τ : ℝ =>  ENNReal.ofReal (BoundaryWeight a b τ)))
def PW {a b : ℝ} (ψ : FrequencySpace a b) (s : ℂ) : ℂ :=
  (Real.sqrt (2*Real.pi) : ℂ)⁻¹ * ∫ τ : ℝ, ψ τ * Complex.exp (s*τ)
def RawNormSquared (a b : ℝ) (h : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ ε : ℝ, 0  <  ε ∧ ε  <  (b-a)/2 ∧
    r = ∫ t : ℝ, ‖h (line (a+ε) t)‖^2 + ‖h (line (b-ε) t)‖^2}
def TracePair {a b : ℝ} (hab : a  <  b) (ψ : HardySpace a b)
    (left right : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  Tendsto (fun x : Ioo a b =>  interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 left) ∧
  Tendsto (fun x : Ioo a b =>  interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 right)
def WeightedResidual (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  residual N s (conj z) / ((1+s)*(1+conj z))
def Distance (a b : ℝ) (z : ℂ) : ℝ := min (z.re-a) (b-z.re)
def Reproducer (a b : ℝ) (s z : ℂ) : ℂ :=
  (4*((b-a : ℝ) : ℂ))⁻¹ / Complex.sin ((Real.pi : ℂ)*(s+conj z-2*a)/(2*(b-a : ℝ)))

-- TeX 2358–2408: real coefficients, ordinary determinant of T².
def RootRatio (N : ℕ) (μ : ℝ) : ℝ := spectralScale N^2 / μ^2
def Slice (J : Quaternion ℝ) : Set (Quaternion ℝ) :=
  {q | ∃ x y : ℝ, q = (x : Quaternion ℝ) + y • J}
def SliceEntire (F : Quaternion ℝ → Quaternion ℝ) : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ z, f (conj z) = conj (f z)) ∧
    ∀ J : Quaternion ℝ, J.re = 0 → J^2 = -1 → ∀ z : ℂ,
      F ((z.re : Quaternion ℝ) + z.im • J) = (f z).re + (f z).im • J

def ZeroSum {N : ℕ} [NeZero N] (χ : Character N) (x t : ℝ) : ℝ :=
  ∑' ρ : ZeroIndex χ.primitiveCharacter, x / (x^2+(t-ρ.val.1.im)^2)
def Energy {N : ℕ} [NeZero N] (χ : Character N) (σ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖logDerivative χ (line σ t)‖^2/(1+t^2)
def AverageEnergy (N : ℕ) [NeZero N] (σ : ℝ) : ℝ :=
  2/N.totient * ∑ χ ∈ oddCharacters N, Energy χ σ
def ReferenceLine (N : ℕ) : ℝ := 2/Real.log N
def Cutoff (X : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ)  ≤  Real.sqrt X then 1 else
  if (n : ℝ)  ≤  X then Real.log (X/n)/Real.log (Real.sqrt X) else 0
def Perron (X : ℝ) (v : ℂ) : ℂ :=
  ((X : ℂ)^v - (Real.sqrt X : ℂ)^v)/(v^2*Real.log (Real.sqrt X))
def Poisson (x t : ℝ) : ℝ := x/(Real.pi*(x^2+t^2))
def Convolution (f g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u : ℝ, f u*g (t-u)
def DiagonalVector (n : ℕ) (s : ℂ) : ℂ := (n : ℂ)^(-s)/(1+s)

-- TeX 3362–3370 and 3595–3638. J₀'s finite-integral bridge is checked separately.
def Difference (φ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), φ u*φ (u+y)
def SumOnPositiveHalfLine (φ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), φ u*φ (y-u)
def Signed (φ : ℝ → ℝ) (y : ℝ) : ℝ := 2*Difference φ y-SumOnPositiveHalfLine φ y
def V (φ : ℝ → ℝ) (u : ℝ) : ℝ := companion φ u-u*deriv (companion φ) u
def Q (N : ℕ) (φ : ℝ → ℝ) (a : ℝ) : ℝ :=
  (2*Real.pi)⁻¹ * ∫ u in Ioi (0 : ℝ),
    Real.rpow (N*u) (2*a)*V φ u^2/(1+Real.rpow (N*u) (-2*(beta-a)))/u
def EnergyV (φ : ℝ → ℝ) : ℝ := (2*Real.pi)⁻¹ * ∫ u in Ioi (0 : ℝ), V φ u^2/u
def Psi (N : ℕ) (φ : ℝ → ℝ) (s : ℂ) : ℂ := (N : ℂ)^s*mellinWeight φ s*(1+s)

-- Formula-level comparisons. No proof of a target theorem is used here.
theorem raw_hardy_bridge (a b : ℝ) (f : ℂ → ℂ) : RawHardy a b f = IsRawHardy a b f := rfl
theorem raw_norm_bridge (a b : ℝ) (f : ℂ → ℂ) : RawNormSquared a b f = rawHardyNormSq a b f := rfl
theorem pw_bridge {a b : ℝ} (ψ : FrequencySpace a b) (s : ℂ) : PW ψ s = fourierLaplace ψ s := rfl
theorem traces_bridge {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) (l r : Lp ℂ 2 (volume : Measure ℝ)) :
  TracePair hab ψ l r = IsBoundaryTrace hab ψ l r := rfl
theorem kernel_bridge (N : ℕ) [NeZero N] (s z : ℂ) : WeightedResidual N s z = weightedKernel N s z := rfl
theorem reproducer_bridge (a b : ℝ) (s z : ℂ) : Reproducer a b s z = reproducingKernel a b s z := rfl
theorem distance_bridge (a b : ℝ) (s : ℂ) : Distance a b s = pointDistance a b s := rfl
theorem ratio_bridge (N : ℕ) (μ : ℝ) : RootRatio N μ = spectralRootParameter N μ := rfl
theorem slice_bridge (J : Quaternion ℝ) : Slice J = quaternionSlice J := rfl
theorem entire_bridge (F : Quaternion ℝ → Quaternion ℝ) : SliceEntire F = IntrinsicEntire F := rfl
theorem zero_sum_bridge {N : ℕ} [NeZero N] (χ : Character N) (x t : ℝ) : ZeroSum χ x t = zeroPoisson χ x t := rfl
theorem energy_bridge {N : ℕ} [NeZero N] (χ : Character N) (σ : ℝ) : Energy χ σ = logDerivativeEnergy χ σ := rfl
theorem average_bridge (N : ℕ) [NeZero N] (σ : ℝ) : AverageEnergy N σ = averagedLogDerivative N σ := rfl
theorem reference_line_bridge (N : ℕ) : ReferenceLine N = referenceLine N := rfl
theorem cutoff_bridge (X : ℝ) (n : ℕ) : Cutoff X n = smoothedPerronWeight X n := rfl
theorem perron_bridge (X : ℝ) (v : ℂ) : Perron X v = smoothedPerronKernel X v := rfl
theorem poisson_bridge (x t : ℝ) : Poisson x t = poissonKernelReal x t := rfl
theorem convolution_bridge (f g : ℝ → ℝ) (t : ℝ) : Convolution f g t = realConvolution f g t := rfl
theorem diagonal_vector_bridge (n : ℕ) (s : ℂ) : DiagonalVector n s = diagonalVector n s := rfl
theorem difference_bridge (φ : ℝ → ℝ) (y : ℝ) : Difference φ y = differenceConvolution φ y := rfl
theorem sum_bridge (φ : ℝ → ℝ) (y : ℝ) : SumOnPositiveHalfLine φ y = sumConvolution φ y := rfl
theorem signed_bridge (φ : ℝ → ℝ) (y : ℝ) : Signed φ y = signedConvolution φ y := rfl
theorem v_bridge (φ : ℝ → ℝ) (u : ℝ) : V φ u = derivativeWeight φ u := rfl
theorem q_bridge (N : ℕ) (φ : ℝ → ℝ) (a : ℝ) : Q N φ a = normFunctional N φ a := rfl
theorem energy_v_bridge (φ : ℝ → ℝ) : EnergyV φ = weightEnergy φ := rfl
theorem psi_bridge (N : ℕ) (φ : ℝ → ℝ) (s : ℂ) : Psi N φ s = functionalIntegrand N φ s := rfl

-- Main expected statements, with all standing assumptions explicit.
-- TeX 2030–2046: onto, uniqueness, both boundary norms, not an arbitrary boundary pair.
def Expected_5_2 : Prop := ∀ a b : ℝ, ∀ hab : a < b,
  (∀ ψ : HardySpace a b, RawHardy a b (fourierLaplace ψ) ∧
    RawNormSquared a b (fourierLaplace ψ) = ‖ψ‖^2 ∧
    ‖ψ‖^2 = ‖(boundaryTraces hab ψ).1‖^2 + ‖(boundaryTraces hab ψ).2‖^2) ∧
  (∀ f : ℂ → ℂ, RawHardy a b f → ∃! ψ : HardySpace a b,
    ∀ s ∈ strip a b, fourierLaplace ψ s=f s)

-- TeX 2975–2986: C outside N; all three estimates and positivity are essential.
def Expected_6_5 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10  <  (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  let a := alpha N
  let P := arithmeticOperator ha N
  let D := diagonalOperator ha N
  let K := modelOperator ha N
  IsPositiveTraceClass P ∧ IsPositiveTraceClass D ∧ IsHilbertSchmidt K ∧
  (hsNorm P ≤ positiveTrace P ∧ positiveTrace P ≤ C*(Real.log N^2+a⁻¹^2)) ∧
  (hsNorm D ≤ positiveTrace D ∧ positiveTrace D ≤ C*a⁻¹^2) ∧ hsNorm K ≤ C*a⁻¹^2

-- TeX 2655–2664: absolute constant uniform in all moduli and 0 < σ ≤ β.
def Expected_6_4 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10  <  (N : ℝ) → GRH N → ∀ σ : ℝ, 0 < σ → σ ≤ beta →
  (∀ χ ∈ oddCharacters N, Integrable (fun t : ℝ =>  ‖logDerivative χ (line σ t)‖^2/(1+t^2))) ∧
  AverageEnergy N σ  ≤  C*(Real.log N^2+σ⁻¹^2)

-- TeX 2552–2570: the open half-space gives a non-strict operator inequality.
def Expected_6_1_dictionary : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  (SpectralR N (alpha N) ha ↔ ‖residualOperator ha N‖ ≤ spectralScale N) ∧
  (∀ η : ℝ, 0 < η → η < 1/2 → (SpectralZeroFree N (alpha N) ha η ↔
    ‖residualOperator ha N‖ ≤ spectralScale N/(2*Real.sqrt (η*(1-η))))) ∧
  (∀ M : ℝ, spectralScale N < M → ‖residualOperator ha N‖ ≤ M →
    0 < spectralWidthFromBound N M ∧ spectralWidthFromBound N M < 1/2 ∧
    SpectralZeroFree N (alpha N) ha (spectralWidthFromBound N M))

def Expected_6_2_baseline : Prop := ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  EvenEventually (fun N =>  ∀ (_ : NeZero N) (ha : alpha N < beta), GRH N →
    IsHilbertSchmidt (residualOperator ha N) ∧
    ‖residualOperator ha N‖ ≤ hsNorm (residualOperator ha N) ∧
    hsNorm (residualOperator ha N) ≤ C*Real.log N^2 ∧
    SpectralZeroFree N (alpha N) ha (c*singularSeries N/(N*Real.log N)))

-- TeX 3374–3390: no GRH is imposed on the diagonal and model inversion.
def Expected_7_2 : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
  ∀ φ : ℝ → ℝ, IsWeight φ → ∀ σ : ℝ, 0 < σ → σ ≤ 1/9 →
  verticalMellin σ (fun s =>  verticalMellin σ (fun z => 
    (N : ℂ)^(s+z)*mellinWeight φ s*mellinWeight φ z*diagonalSeries N (s+z))) = diagonalMoment N φ ∧
  verticalMellin σ (fun s =>  verticalMellin σ (fun z => 
    mellinWeight φ s*mellinWeight φ z*continuedDensity N (s+z)*betaKernel s z)) =
    -(weightMass φ*singularSeries N : ℝ)

def Expected_7_3 : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
  ∀ φ : ℝ → ℝ, IsWeight φ → ∀ σ : ℝ, 0 < σ → σ ≤ 1/9 →
    residualIntegral N φ σ = (weightMass φ*singularSeries N-goldbach N φ : ℝ)

-- TeX 3710–3722: signed residual before absolute values; first-variable-linear inner product.
def Expected_7_1_quadratic : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ φ : ℝ → ℝ, IsWeight φ → ∀ ha : alpha N < beta,
    (weightMass φ*singularSeries N-goldbach N φ : ℝ) =
      paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) ∧
    |weightMass φ*singularSeries N-goldbach N φ| ≤ Q N φ (alpha N)*‖residualOperator ha N‖

def Expected_7_5 : Prop := ∀ φ : ℝ → ℝ, IsWeight φ → ∃ C : ℝ, 0 < C ∧
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
  ∀ ha : alpha N < beta, ∀ η : ℝ, 0 < η → η ≤ 1/4 → SpectralZeroFree N (alpha N) ha η →
    |goldbach N φ-weightMass φ*singularSeries N|/(weightMass φ*singularSeries N) ≤ 
      C*Real.sqrt (Real.log N^3/(N*η*singularSeries N))

-- Direct type bridges: these certify only reference → actual Lean statement agreement.
theorem check_5_2 : Expected_5_2 := lemma_5_2
theorem check_6_5 : Expected_6_5 := proposition_6_5
theorem check_6_4 : Expected_6_4 := lemma_6_4
theorem check_6_1_dictionary : Expected_6_1_dictionary := theorem_6_1
theorem check_6_2_baseline : Expected_6_2_baseline := theorem_6_2
theorem check_7_2 : Expected_7_2 := lemma_7_2
theorem check_7_3 : Expected_7_3 := proposition_7_3
theorem check_7_1_quadratic : Expected_7_1_quadratic := theorem_7_1
theorem check_7_5 : Expected_7_5 := lemma_7_5

-- TeX 1926–1943: both kernels, an open neighborhood, two vanishing derivatives.
def Expected_5_1 : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N →
  HermitianKernel (WeightedResidual N) ∧
  HermitianKernel (fun s z =>  residual N s (conj z)) ∧
  DifferentiableOn ℂ (fun p : ℂ × ℂ =>  WeightedResidual N p.1 (conj p.2)) analyticDomain ∧
  (∃ U : Set (ℂ × ℂ), IsOpen U ∧
    {p | alpha N ≤ p.1.re ∧ p.1.re ≤ beta ∧ alpha N ≤ p.2.re ∧ p.2.re ≤ beta}⊆U ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ =>  residual N p.1 p.2) U ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ =>  WeightedResidual N p.1 (conj p.2)) U) ∧
  (∀ s z : ℂ, (s,conj z)∈analyticDomain →
    wirtingerBar (fun w =>  residual N w (conj z)) s=0 ∧
    wirtinger (fun w =>  residual N s (conj w)) z=0) ∧
  1/90 < sigmaStar-alpha N ∧ beta-sigmaStar=1/72

-- TeX 2123–2141: the actual boundary integral, L², HS equality and attained norm.
def Expected_5_3 : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  (∀ x∈({alpha N,beta} : Finset ℝ), ∀ y∈({alpha N,beta} : Finset ℝ),
    MemLp (fun p : ℝ×ℝ =>  WeightedResidual N (line x p.1) (line y p.2)) 2 volume) ∧
  RepresentsKernel ha N (WeightedResidual N) (residualOperator ha N) ∧
  IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
  IsHilbertSchmidt (residualOperator ha N) ∧ Nonempty (SpectralData (residualOperator ha N)) ∧
  (∑' j, eigenvalues (residualOperator ha N) j^2)=hsNorm (residualOperator ha N)^2 ∧
  hsNorm (residualOperator ha N)^2=BoundaryKernelSquareIntegral (alpha N) beta (WeightedResidual N) ∧
  ‖residualOperator ha N‖=sSup (Set.range (fun j =>  |eigenvalues (residualOperator ha N) j|)) ∧
  (residualOperator ha N≠0 → ∃ j, |eigenvalues (residualOperator ha N) j|=‖residualOperator ha N‖)

def Expected_5_4 : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  ∀ s z : ℂ, s∈strip (alpha N) beta → z∈strip (alpha N) beta →
  (∀ h : HardySpace (alpha N) beta, fourierLaplace h s=paperInner h (evaluationVector s)) ∧
  fourierLaplace (evaluationVector z : HardySpace (alpha N) beta) s=Reproducer (alpha N) beta s z ∧
  ‖(evaluationVector s : HardySpace (alpha N) beta)‖^2 ≤ 1/(8*Distance (alpha N) beta s) ∧
  ‖residual N s (conj z)‖ ≤ ‖residualOperator ha N‖*‖1+s‖*‖1+z‖/
    (8*Real.sqrt (Distance (alpha N) beta s*Distance (alpha N) beta z))

def Expected_6_1_product : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  CompactUniformLimit (fun k q =>  spectralPartialQuaternion N (residualOperator ha N) q k)
    (spectralQuaternion N (residualOperator ha N)) ∧
  SliceEntire (spectralQuaternion N (residualOperator ha N)) ∧
  (∀ q : ℂ, Multipliable (fun j : ℕ => 
    1-(4*eigenvalues (residualOperator ha N) j^2/spectralScale N^2 : ℝ)*q*(1-q))) ∧
  IsPositiveTraceClass ((residualOperator ha N).comp (residualOperator ha N)) ∧
  positiveTrace ((residualOperator ha N).comp (residualOperator ha N))=hsNorm (residualOperator ha N)^2 ∧
  (∀ q : ℂ, spectralComplex N (residualOperator ha N) q=
    fredholmSquareDet (residualOperator ha N) (4/spectralScale N^2*q*(1-q)))

def Expected_6_2_symmetries : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  let X := spectralQuaternion N (residualOperator ha N)
  X 0=1 ∧ X 1=1 ∧ (∀ q, X (1-q)=X q) ∧
  (∀ q, X (star q)=star (X q)) ∧ (∀ q, X (1-star q)=star (X q)) ∧
  (∀ ξ, X (1/2+ξ)=X (1/2-ξ)) ∧ (∀ x : ℝ, x∉Ioo 0 1 → 1 ≤ (X x).re)

def Expected_6_3_zeros : Prop := ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
  Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  (∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q=0 ↔
    ∃ j : ℕ, eigenvalues (residualOperator ha N) j≠0 ∧
      q*(1-q)=(spectralScale N^2/(4*eigenvalues (residualOperator ha N) j^2) : ℝ)) ∧
  (∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q=0 → q.re≠1/2 →
    q=(q.re : Quaternion ℝ) ∧ q.re∈Ioo 0 1) ∧
  (∀ x : ℝ, spectralQuaternion N (residualOperator ha N) x=0 → x∈Ioo 0 1) ∧
  Set.Finite {j | spectralScale N < |eigenvalues (residualOperator ha N) j| }

def Expected_7_1_mellin : Prop := ∀ φ : ℝ → ℝ, IsWeight φ →
  (∀ σ u : ℝ, 0 < u → (companion φ u : ℂ)=
    verticalMellin σ (fun s =>  mellinWeight φ s*(u : ℂ)^(-s))) ∧
  (∀ lo hi : ℝ, lo ≤ hi → ∃ C : ℝ, 0 < C ∧ ∀ σ∈Icc lo hi, ∀ t : ℝ,
    ‖mellinWeight φ (line σ t)‖ ≤ C*(1+|t|)⁻¹^6) ∧
  (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
    ∀ χ∈oddCharacters N, ∀ σ : ℝ, 0 < σ → σ ≤ 1/9 →
      characterPolynomial χ φ= -verticalMellin σ (fun s => 
        (N : ℂ)^s*mellinWeight φ s*logDerivative χ s))

def Expected_7_4 : Prop := ∀ φ : ℝ → ℝ, IsWeight φ →
  (∀ N : ℕ, Even N → Real.exp 10 < (N : ℝ) →
    (∀ σ∈Ioo (alpha N) beta,
      (∀ h : HardySpace (alpha N) beta,
        Integrable (fun t : ℝ =>  (N : ℂ)^(line σ t)*mellinWeight φ (line σ t)*
          (1+line σ t)*fourierLaplace h (line σ t)) ∧
        functionalValue N φ σ h=paperInner h (rieszVector N φ)) ∧
      ∃ ℓ : HardySpace (alpha N) beta →L[ℂ] ℂ,
        (∀ h, ℓ h=functionalValue N φ σ h) ∧ ‖ℓ‖^2=Q N φ (alpha N)) ∧
    ‖(rieszVector N φ : HardySpace (alpha N) beta)‖^2=Q N φ (alpha N) ∧
    Q N φ (alpha N) ≤ Real.exp 2*EnergyV φ) ∧
  (∃ C : ℝ, 0 < C ∧ EvenEventually (fun N => 
    |Q N φ (alpha N)-Real.exp 2*EnergyV φ| ≤ C/Real.log N))

theorem check_5_1 : Expected_5_1 := proposition_5_1
theorem check_5_3 : Expected_5_3 := proposition_5_3
theorem check_5_4 : Expected_5_4 := proposition_5_4
theorem check_6_1_product : Expected_6_1_product := proposition_6_1
theorem check_6_2_symmetries : Expected_6_2_symmetries := proposition_6_2
theorem check_6_3_zeros : Expected_6_3_zeros := proposition_6_3
theorem check_7_1_mellin : Expected_7_1_mellin := lemma_7_1
theorem check_7_4 : Expected_7_4 := proposition_7_4

-- Supplemental paper clauses. Each predicate was transcribed from the indicated
-- mathematical clause, with the existing representation vocabulary audited above.
def expect_proposition_5_1_fueter_equation : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ s z : ℂ,
  (s,conj z) ∈ analyticDomain → fueterOperator (fun u v => residual N u (conj v)) s z = 0

def expect_lemma_5_2_closed_trace_space : Prop := ∀ a b : ℝ, ∀ hab : a < b,
  IsClosed (Set.range (fun ψ : HardySpace a b => boundaryTraces hab ψ))

def expect_lemma_5_2_representation_spec : Prop := ∀ a b : ℝ, ∀ hab : a < b,
  (∀ ψ : HardySpace a b,
    (∀ s ∈ strip a b, Integrable (fun τ : ℝ => ψ τ * Complex.exp (s*τ))) ∧
    TracePair hab ψ (boundaryTraces hab ψ).1 (boundaryTraces hab ψ).2 ∧
    Integrable (fun τ : ℝ => ‖ψ τ‖^2 * BoundaryWeight a b τ) ∧
    ‖ψ‖^2 = ∫ τ : ℝ, ‖ψ τ‖^2 * BoundaryWeight a b τ) ∧
  (∀ ψ χ : HardySpace a b, ∀ s ∈ strip a b,
    fourierLaplace (ψ+χ) s = fourierLaplace ψ s + fourierLaplace χ s) ∧
  (∀ c : ℂ, ∀ ψ : HardySpace a b, ∀ s ∈ strip a b,
    fourierLaplace (c • ψ) s = c*fourierLaplace ψ s) ∧
  (∀ ψ χ : HardySpace a b, boundaryTraces hab (ψ+χ) = boundaryTraces hab ψ + boundaryTraces hab χ) ∧
  (∀ c : ℂ, ∀ ψ : HardySpace a b, boundaryTraces hab (c • ψ) = c • boundaryTraces hab ψ) ∧
  (∀ ψ χ : HardySpace a b, ‖ψ-χ‖^2 =
    ‖(boundaryTraces hab ψ).1-(boundaryTraces hab χ).1‖^2 +
    ‖(boundaryTraces hab ψ).2-(boundaryTraces hab χ).2‖^2)

def expect_lemma_5_2_boundary_inner : Prop := ∀ a b : ℝ, ∀ hab : a < b,
  ∀ h g : HardySpace a b, paperInner h g =
    (∫ t : ℝ, (boundaryTraces hab h).1 t * conj ((boundaryTraces hab g).1 t)) +
    ∫ t : ℝ, (boundaryTraces hab h).2 t * conj ((boundaryTraces hab g).2 t)

def expect_proposition_5_3_kernel_integrability : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  ∀ h : HardySpace (alpha N) beta, ∀ s ∈ strip (alpha N) beta,
    Integrable (fun t : ℝ => WeightedResidual N s (line (alpha N) t)*(boundaryTraces ha h).1 t) ∧
    Integrable (fun t : ℝ => WeightedResidual N s (line beta t)*(boundaryTraces ha h).2 t)

def expect_proposition_5_3_hs_basis_independent : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ T : H →L[ℂ] H, IsHilbertSchmidt T → ∀ b : HilbertBasis ℕ ℂ H,
    Summable (fun j => ‖T (b j)‖^2) ∧ hsNorm T^2 = ∑' j, ‖T (b j)‖^2

def expect_proposition_5_4_exact_norm : Prop := ∀ a b : ℝ, a < b →
  ∀ s ∈ strip a b, ‖(evaluationVector s : HardySpace a b)‖^2 =
    1/(4*(b-a)*Real.sin (Real.pi*(s.re-a)/(b-a)))

def expect_proposition_5_4_kernel_pairing : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  ∀ s z : ℂ, s ∈ strip (alpha N) beta → z ∈ strip (alpha N) beta →
    WeightedResidual N s z = paperInner (residualOperator ha N (evaluationVector z)) (evaluationVector s)

def expect_proposition_5_4_fixed_contour : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
  ∀ ha : alpha N < beta, ∀ v t : ℝ,
    ‖residual N (line sigmaStar v) (line sigmaStar t)‖ ≤ C*‖residualOperator ha N‖*(1+|v|+|t|)^2

def expect_proposition_6_1_enumeration : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta, ∀ e : ℕ ≃ ℕ,
  CompactUniformLimit (fun k q => spectralPartialQuaternionReindexed N (residualOperator ha N) e q k)
    (spectralQuaternion N (residualOperator ha N)) ∧
  (∀ q : ℂ, (∏' j : ℕ,
    (1-(4*eigenvalues (residualOperator ha N) (e j)^2/spectralScale N^2 : ℝ)*q*(1-q))) =
    spectralComplex N (residualOperator ha N) q)

def expect_proposition_6_1_complex_slice : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta, ∀ q : ℂ,
  spectralQuaternion N (residualOperator ha N) (complexQuaternion q) =
    complexQuaternion (spectralComplex N (residualOperator ha N) q)

def expect_proposition_6_1_all_slices : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  ∀ J : Quaternion ℝ, J.re = 0 → J^2 = -1 → ∀ z : ℂ,
    spectralQuaternion N (residualOperator ha N) ((z.re : Quaternion ℝ)+z.im • J) =
      ((spectralComplex N (residualOperator ha N) z).re : Quaternion ℝ) +
      (spectralComplex N (residualOperator ha N) z).im • J

def expect_proposition_6_1_positive_fredholm_spec : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ A : H →L[ℂ] H, IsPositiveTraceClass A →
  IsCompactOperator A ∧ IsHilbertSchmidt A ∧ Nonempty (SpectralData A) ∧
  (∀ j, 0 ≤ eigenvalues A j) ∧ Summable (eigenvalues A) ∧
  positiveTrace A = ∑' j, eigenvalues A j ∧
  (∀ b : HilbertBasis ℕ ℂ H, Summable (fun j => (paperInner (A (b j)) (b j)).re) ∧
    positiveTrace A = ∑' j, (paperInner (A (b j)) (b j)).re) ∧
  (∀ t : ℂ, Multipliable (fun j : ℕ => 1-t*(eigenvalues A j : ℂ)))

def expect_proposition_6_1_square_determinant : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  let T := residualOperator ha N
  Nonempty (SpectralData (T.comp T)) ∧ positiveTrace (T.comp T) = ∑' j, eigenvalues T j^2 ∧
  (∀ t : ℂ, Multipliable (fun j : ℕ => 1-t*(eigenvalues T j : ℂ)^2) ∧
    fredholmSquareDet T t = ∏' j : ℕ, (1-t*(eigenvalues T j : ℂ)^2))

def expect_proposition_6_1_spectral_choice_independent : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ T : H →L[ℂ] H, ∀ d₁ d₂ : SpectralData T, ∀ t : ℂ,
  (∏' j : ℕ, (1-t*(d₁.values j : ℂ)^2)) = ∏' j : ℕ, (1-t*(d₂.values j : ℂ)^2)

def expect_proposition_6_2_centered_product : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  CompactUniformLimit (fun k ξ => centeredSpectralPartial N (residualOperator ha N) ξ k)
    (fun ξ => spectralQuaternion N (residualOperator ha N) (1/2+ξ))

def expect_proposition_6_2_critical_values : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  ∀ J : Quaternion ℝ, J.re = 0 → ‖J‖ = 1 → ∀ t : ℝ,
  Multipliable (fun j : ℕ => (1-eigenvalues (residualOperator ha N) j^2/
    spectralScale N^2*(1+4*t^2) : ℝ)) ∧
  spectralQuaternion N (residualOperator ha N) ((1/2 : Quaternion ℝ)+t • J) =
    ((∏' j : ℕ, (1-eigenvalues (residualOperator ha N) j^2/spectralScale N^2*(1+4*t^2)) : ℝ) : Quaternion ℝ)

def expect_proposition_6_3_three_cases : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta, ∀ q : Quaternion ℝ,
  spectralQuaternion N (residualOperator ha N) q = 0 ↔
    ∃ j : ℕ, eigenvalues (residualOperator ha N) j ≠ 0 ∧
    let d := RootRatio N (eigenvalues (residualOperator ha N) j)
    (1 < d ∧ q.re = 1/2 ∧ ‖q-(q.re : Quaternion ℝ)‖ = Real.sqrt (d-1)/2) ∨
    (d = 1 ∧ q = 1/2) ∨
    (0 < d ∧ d < 1 ∧ (q = ((1/2-Real.sqrt (1-d)/2 : ℝ) : Quaternion ℝ) ∨
      q = ((1/2+Real.sqrt (1-d)/2 : ℝ) : Quaternion ℝ)))

def expect_proposition_6_3_factor_central_order : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta, ∀ j : ℕ,
  eigenvalues (residualOperator ha N) j ≠ 0 →
  RootRatio N (eigenvalues (residualOperator ha N) j) = 1 →
  analyticOrderNatAt (fun q : ℂ =>
    1-(4*eigenvalues (residualOperator ha N) j^2/spectralScale N^2 : ℝ)*q*(1-q)) (1/2) = 2

def expect_proposition_6_3_multiplicities : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  (∀ q : ℂ, analyticOrderNatAt (spectralComplex N (residualOperator ha N)) q =
    analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (1-q)) ∧
  (∀ q : ℂ, analyticOrderNatAt (spectralComplex N (residualOperator ha N)) q =
    analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (conj q)) ∧
  Even (analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (1/2)) ∧
  (∀ q u : Quaternion ℝ, ‖u‖ = 1 → spectralQuaternion N (residualOperator ha N) q = 0 →
    spectralQuaternion N (residualOperator ha N) (u*q*star u) = 0)

def expect_theorem_6_1_abstract_dictionary : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ N : ℕ, ∀ T : H →L[ℂ] H, Nonempty (SpectralData T) → 0 < spectralScale N →
  ((∀ q : Quaternion ℝ, spectralQuaternion N T q = 0 → q.re = 1/2) ↔ ‖T‖ ≤ spectralScale N) ∧
  ∀ η : ℝ, 0 < η → η < 1/2 →
    ((∀ q : Quaternion ℝ, 1-η < q.re → spectralQuaternion N T q ≠ 0) ↔
      ‖T‖ ≤ spectralScale N/(2*Real.sqrt (η*(1-η))))

def expect_theorem_6_1_width_comparison : Prop := ∀ N : ℕ, ∀ M : ℝ,
  0 < spectralScale N → spectralScale N < M →
  spectralScale N^2/(4*M^2) ≤ spectralWidthFromBound N M ∧
  spectralWidthFromBound N M ≤ spectralScale N^2/(2*M^2)

def expect_lemma_6_4_zero_poisson_convergence : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ χ ∈ oddCharacters N,
  ∀ x t : ℝ, 0 < x → Summable (fun p : ZeroIndex χ.primitiveCharacter => x/(x^2+(t-p.val.1.im)^2))

def expect_lemma_6_4_perron_residue : Prop := ∀ X : ℝ, 1 < X →
  MeromorphicOn (Perron X) Set.univ ∧
  Tendsto (fun v : ℂ => v*Perron X v) (𝓝[≠] (0 : ℂ)) (𝓝 1)

def expect_lemma_6_4_poisson_action_spec : Prop :=
  (∀ f : ℝ → ℝ, poissonAction 0 f = f) ∧ ∀ ℓ : ℝ, 0 < ℓ →
  Integrable (Poisson ℓ) ∧ (∀ t : ℝ, 0 ≤ Poisson ℓ t) ∧ (∫ t : ℝ, Poisson ℓ t) = 1 ∧
  ∀ f : ℝ → ℝ, poissonAction ℓ f = Convolution (Poisson ℓ) f

def expect_lemma_6_4_poisson_convolution : Prop := ∀ ℓ : ℝ, 0 < ℓ → ∀ t : ℝ,
  Integrable (fun u : ℝ => Poisson 1 u*Poisson ℓ (t-u)) ∧
  Convolution (Poisson 1) (Poisson ℓ) t = Poisson (1+ℓ) t ∧
  Poisson (1+ℓ) t ≤ (1+ℓ)*Poisson 1 t

def expect_proposition_6_5_components_spec : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  let a := alpha N
  let P := arithmeticOperator ha N
  let D := diagonalOperator ha N
  let K := modelOperator ha N
  let κP := fun s z : ℂ => characterKernel N s (conj z)/((1+s)*(1+conj z))
  let κD := fun s z : ℂ => diagonalSeries N (s+conj z)/((1+s)*(1+conj z))
  let κK := fun s z : ℂ => continuedModel N s (conj z)/((1+s)*(1+conj z))
  RepresentsKernel ha N κP P ∧ RepresentsKernel ha N κD D ∧ RepresentsKernel ha N κK K ∧
  (∀ κ ∈ ([κP,κD,κK] : List (ℂ → ℂ → ℂ)), ∀ h : HardySpace a beta,
    ∀ s ∈ strip a beta,
    Integrable (fun t : ℝ => κ s (line a t)*(boundaryTraces ha h).1 t) ∧
    Integrable (fun t : ℝ => κ s (line beta t)*(boundaryTraces ha h).2 t)) ∧
  residualOperator ha N = P-D-K

def expect_proposition_6_5_diagonal_vector_spec : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → ∀ ha : alpha N < beta, ∀ n : ℕ, 1 ≤ n →
  let d : HardySpace (alpha N) beta := diagonalHardyVector n
  (∀ s ∈ strip (alpha N) beta, fourierLaplace d s = DiagonalVector n s) ∧
  ((boundaryTraces ha d).1 =ᵐ[volume] fun t : ℝ => DiagonalVector n (line (alpha N) t)) ∧
  ((boundaryTraces ha d).2 =ᵐ[volume] fun t : ℝ => DiagonalVector n (line beta t)) ∧
  ‖d‖^2 = Real.pi*(Real.rpow n (-2*alpha N)/(1+alpha N)+Real.rpow n (-2*beta)/(1+beta)) ∧
  (∀ h : HardySpace (alpha N) beta, InnerProductSpace.rankOne ℂ d d h = paperInner h d • d)

def expect_lemma_7_1_absolute_convergence : Prop := ∀ φ : ℝ → ℝ, IsWeight φ →
  (∀ σ u : ℝ, 0 < u → Integrable (fun t : ℝ => mellinWeight φ (line σ t)*(u : ℂ)^(-line σ t))) ∧
  (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
    ∀ σ : ℝ, 0 < σ → σ ≤ 1/9 →
    (∀ χ ∈ oddCharacters N, Integrable (fun t : ℝ =>
      (N : ℂ)^(line σ t)*mellinWeight φ (line σ t)*logDerivative χ (line σ t))) ∧
    Integrable (fun p : ℝ×ℝ => (N : ℂ)^(line σ p.1+line σ p.2)*mellinWeight φ (line σ p.1)*
      mellinWeight φ (line σ p.2)*characterKernel N (line σ p.1) (line σ p.2)) ∧
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ)^(s+z)*mellinWeight φ s*mellinWeight φ z*characterKernel N s z)))

def expect_lemma_7_2_absolute_convergence : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → 4 ≤ N → ∀ φ : ℝ → ℝ, IsWeight φ → ∀ σ : ℝ, 0 < σ → σ ≤ 1/9 →
  Integrable (fun p : ℝ×ℝ => (N : ℂ)^(line σ p.1+line σ p.2)*mellinWeight φ (line σ p.1)*
    mellinWeight φ (line σ p.2)*diagonalSeries N (line σ p.1+line σ p.2)) ∧
  Integrable (fun p : ℝ×ℝ => mellinWeight φ (line σ p.1)*mellinWeight φ (line σ p.2)*
    continuedDensity N (line σ p.1+line σ p.2)*betaKernel (line σ p.1) (line σ p.2))

def expect_lemma_7_2_convolutions : Prop := ∀ φ : ℝ → ℝ, IsWeight φ →
  (∀ y : ℝ, IntegrableOn (fun u : ℝ => φ u*φ (u+y)) (Ioi 0) ∧
    IntegrableOn (fun u : ℝ => φ u*φ (y-u)) (Ioi 0) ∧
    SumOnPositiveHalfLine φ y = ∫ u in (0 : ℝ)..y, φ u*φ (y-u)) ∧
  SumOnPositiveHalfLine φ 1 = weightMass φ ∧ IntegrableOn φ (Ioi 0)

def expect_proposition_7_3_absolute_convergence : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → 4 ≤ N → GRH N → ∀ φ : ℝ → ℝ, IsWeight φ → ∀ σ : ℝ, 0 < σ → σ ≤ 1/9 →
  Integrable (fun p : ℝ×ℝ => (N : ℂ)^(line σ p.1+line σ p.2)*mellinWeight φ (line σ p.1)*
    mellinWeight φ (line σ p.2)*residual N (line σ p.1) (line σ p.2))

def expect_proposition_7_4_norm_integrals : Prop := ∀ N : ℕ, 0 < N →
  ∀ φ : ℝ → ℝ, IsWeight φ → ∀ a : ℝ,
  IntegrableOn (fun u : ℝ => V φ u^2/u) (Ioi 0) ∧
  IntegrableOn (fun u : ℝ => Real.rpow (N*u) (2*a)*V φ u^2/
    (1+Real.rpow (N*u) (-2*(beta-a)))/u) (Ioi 0)

def expect_theorem_7_1_uniform : Prop := ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ φ : ℝ → ℝ, IsWeight φ →
  ∀ ha : alpha N < beta,
  |weightMass φ*singularSeries N-goldbach N φ| ≤ Real.exp 2*EnergyV φ*‖residualOperator ha N‖

def expect_lemma_7_5_asymptotic : Prop := ∀ φ : ℝ → ℝ, IsWeight φ →
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
  Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
  ∀ η : ℝ, 0 < η → η ≤ 1/4 → SpectralZeroFree N (alpha N) ha η →
    B ≤ N*η*singularSeries N/Real.log N^3 → |goldbach N φ/(weightMass φ*singularSeries N)-1| < ε


-- Supplemental reference-to-implementation type checks.
theorem check_proposition_5_1_fueter_equation : TexAudit57.expect_proposition_5_1_fueter_equation := @LiLiuGoldbach16.proposition_5_1_fueter_equation
theorem check_lemma_5_2_closed_trace_space : TexAudit57.expect_lemma_5_2_closed_trace_space := @LiLiuGoldbach16.lemma_5_2_closed_trace_space
theorem check_lemma_5_2_representation_spec : TexAudit57.expect_lemma_5_2_representation_spec := @LiLiuGoldbach16.lemma_5_2_representation_spec
theorem check_lemma_5_2_boundary_inner : TexAudit57.expect_lemma_5_2_boundary_inner := @LiLiuGoldbach16.lemma_5_2_boundary_inner
theorem check_proposition_5_3_kernel_integrability : TexAudit57.expect_proposition_5_3_kernel_integrability := @LiLiuGoldbach16.proposition_5_3_kernel_integrability
theorem check_proposition_5_3_hs_basis_independent : TexAudit57.expect_proposition_5_3_hs_basis_independent := @LiLiuGoldbach16.proposition_5_3_hs_basis_independent
theorem check_proposition_5_4_exact_norm : TexAudit57.expect_proposition_5_4_exact_norm := @LiLiuGoldbach16.proposition_5_4_exact_norm
theorem check_proposition_5_4_kernel_pairing : TexAudit57.expect_proposition_5_4_kernel_pairing := @LiLiuGoldbach16.proposition_5_4_kernel_pairing
theorem check_proposition_5_4_fixed_contour : TexAudit57.expect_proposition_5_4_fixed_contour := @LiLiuGoldbach16.proposition_5_4_fixed_contour
theorem check_proposition_6_1_enumeration : TexAudit57.expect_proposition_6_1_enumeration := @LiLiuGoldbach16.proposition_6_1_enumeration
theorem check_proposition_6_1_complex_slice : TexAudit57.expect_proposition_6_1_complex_slice := @LiLiuGoldbach16.proposition_6_1_complex_slice
theorem check_proposition_6_1_positive_fredholm_spec : TexAudit57.expect_proposition_6_1_positive_fredholm_spec := @LiLiuGoldbach16.proposition_6_1_positive_fredholm_spec
theorem check_proposition_6_1_square_determinant : TexAudit57.expect_proposition_6_1_square_determinant := @LiLiuGoldbach16.proposition_6_1_square_determinant
theorem check_proposition_6_1_all_slices : TexAudit57.expect_proposition_6_1_all_slices := @LiLiuGoldbach16.proposition_6_1_all_slices
theorem check_proposition_6_1_spectral_choice_independent : TexAudit57.expect_proposition_6_1_spectral_choice_independent := @LiLiuGoldbach16.proposition_6_1_spectral_choice_independent
theorem check_proposition_6_2_centered_product : TexAudit57.expect_proposition_6_2_centered_product := @LiLiuGoldbach16.proposition_6_2_centered_product
theorem check_proposition_6_2_critical_values : TexAudit57.expect_proposition_6_2_critical_values := @LiLiuGoldbach16.proposition_6_2_critical_values
theorem check_proposition_6_3_three_cases : TexAudit57.expect_proposition_6_3_three_cases := @LiLiuGoldbach16.proposition_6_3_three_cases
theorem check_proposition_6_3_factor_central_order : TexAudit57.expect_proposition_6_3_factor_central_order := @LiLiuGoldbach16.proposition_6_3_factor_central_order
theorem check_proposition_6_3_multiplicities : TexAudit57.expect_proposition_6_3_multiplicities := @LiLiuGoldbach16.proposition_6_3_multiplicities
theorem check_theorem_6_1_abstract_dictionary : TexAudit57.expect_theorem_6_1_abstract_dictionary := @LiLiuGoldbach16.theorem_6_1_abstract_dictionary
theorem check_theorem_6_1_width_comparison : TexAudit57.expect_theorem_6_1_width_comparison := @LiLiuGoldbach16.theorem_6_1_width_comparison
theorem check_lemma_6_4_zero_poisson_convergence : TexAudit57.expect_lemma_6_4_zero_poisson_convergence := @LiLiuGoldbach16.lemma_6_4_zero_poisson_convergence
theorem check_lemma_6_4_perron_residue : TexAudit57.expect_lemma_6_4_perron_residue := @LiLiuGoldbach16.lemma_6_4_perron_residue
theorem check_lemma_6_4_poisson_action_spec : TexAudit57.expect_lemma_6_4_poisson_action_spec := @LiLiuGoldbach16.lemma_6_4_poisson_action_spec
theorem check_lemma_6_4_poisson_convolution : TexAudit57.expect_lemma_6_4_poisson_convolution := @LiLiuGoldbach16.lemma_6_4_poisson_convolution
theorem check_proposition_6_5_components_spec : TexAudit57.expect_proposition_6_5_components_spec := @LiLiuGoldbach16.proposition_6_5_components_spec
theorem check_proposition_6_5_diagonal_vector_spec : TexAudit57.expect_proposition_6_5_diagonal_vector_spec := @LiLiuGoldbach16.proposition_6_5_diagonal_vector_spec
theorem check_lemma_7_1_absolute_convergence : TexAudit57.expect_lemma_7_1_absolute_convergence := @LiLiuGoldbach16.lemma_7_1_absolute_convergence
theorem check_lemma_7_2_absolute_convergence : TexAudit57.expect_lemma_7_2_absolute_convergence := @LiLiuGoldbach16.lemma_7_2_absolute_convergence
theorem check_lemma_7_2_convolutions : TexAudit57.expect_lemma_7_2_convolutions := @LiLiuGoldbach16.lemma_7_2_convolutions
theorem check_proposition_7_3_absolute_convergence : TexAudit57.expect_proposition_7_3_absolute_convergence := @LiLiuGoldbach16.proposition_7_3_absolute_convergence
theorem check_proposition_7_4_norm_integrals : TexAudit57.expect_proposition_7_4_norm_integrals := @LiLiuGoldbach16.proposition_7_4_norm_integrals
theorem check_theorem_7_1_uniform : TexAudit57.expect_theorem_7_1_uniform := @LiLiuGoldbach16.theorem_7_1_uniform
theorem check_lemma_7_5_asymptotic : TexAudit57.expect_lemma_7_5_asymptotic := @LiLiuGoldbach16.lemma_7_5_asymptotic

-- Construction obligations implicit in the Fourier–Laplace lemma (TeX 2030–2046).
def expect_interiorLine_memLp : Prop := ∀ {a b x : ℝ}, a < b → x ∈ Ioo a b →
  ∀ ψ : HardySpace a b, MemLp (fun t : ℝ => fourierLaplace ψ (line x t)) 2 volume

def expect_boundaryTraces_exist : Prop := ∀ {a b : ℝ}, ∀ hab : a < b,
  ∀ ψ : HardySpace a b,
  ∃ p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ),
    TracePair hab ψ p.1 p.2

theorem check_interiorLine_memLp : expect_interiorLine_memLp := @LiLiuGoldbach16.interiorLine_memLp
theorem check_boundaryTraces_exist : expect_boundaryTraces_exist := @LiLiuGoldbach16.boundaryTraces_exist

end TexAudit57
