import json, re, hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
texpath = root.parent / 'outputs/formalization-preparation/LiLiuGoldbach16.tex'
tex = texpath.read_text().splitlines()
inventory = json.loads((root / 'reference/inventory.json').read_text())

# The old inventory supplies identifiers ONLY. Original formulas below are read
# directly from the TeX, and actual declaration locations from current sources.
locations = {}
for path in (root / 'LiLiuGoldbach').rglob('*.lean'):
    for line, s in enumerate(path.read_text().splitlines(), 1):
        m = re.match(r'(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|structure|theorem|lemma)\s+(\S+)', s)
        if m:
            locations.setdefault('LiLiuGoldbach16.' + m.group(1), []).append({'file': str(path), 'line': line})

definition_data = '''
weight|151:164|Smooth real nonzero symmetric weight; support in [1/3,2/3], 0≤φ≤1. Compact support omitted syntactically but machine-derived, as is positive mass.|weight_has_required_compact_support
vonMangoldt|333:345|The arithmetic function is mathlib vonMangoldt on naturals; all source sums use positive n; n=0 is harmlessly zero.|
singularSeries|1055:1059|Factor 2 is required. Expanded imported product and finite correction match exactly; even N≥4 is imposed at use sites.|singular_series_formula
twinPrimeConstant|1055:1059|Prime means Nat.Prime; C2 is the product over odd primes with the factor 1−1/(p−1)², not twice that product.|universal_product_formula
goldbachCorrelation|154:167|Natural one-index finite sum parametrizes ordered positive pairs by m=N−n; coprimality is (n(N−n),N)=1. PrimePairCount has correct ordered orientation and both primes in support.|prime_count_members_have_both_support_bounds
weightMass|151:164|Integral φ² from 0 to 1, not integral φ and not unnormalized mass; strict positivity follows from Weight.|weight_has_required_compact_support
GRH|180:185|All primitive Dirichlet L-functions of positive conductor dividing N; not only odd characters. Nontrivial zeros are the open critical-strip zeros; all primitive characters retained.|
spectralScale|229:243|δN=√(S(N)/N)(log N)^(3/2). Noninteger exponent is Real.rpow, not natural truncated exponent.|
spectralProduct|229:247|Quaternion product of 1−4μ²q(1−q)/δ²; local-uniform convergence must justify chosen limit and independence of ordering. Zero-padding requires bridge from full basis to nonzero eigenvalues.|cross:sections-5-7
admissibleH|273:282|h fixed before zero assertion; positive on even N≥4, tends to infinity through evens, width eventually≤1/4. Positivity on irrelevant odd/small arguments is not needed; weak ≥B expresses the same divergence as >B.|
hypothesisWidth|273:281|h²(log N)³/(N S(N)), no missing S factor; upper bound 1/4 eventual, not every N.|
HypothesisS|273:282|Admissibility conjunct plus eventual GRH⇒zero exclusion on open Re q>1−ηN, for all quaternions. Proof parameters NeZero/strip are automatic eventually and cannot make the large-N assertion vacuous.|cross:sections-5-7
HypothesisR|306:313|Eventual conditional GRH assertion, every quaternion zero has real part exactly 1/2. No replacement by complex-only zero condition.|cross:sections-5-7
oddCharacters|373:381|All characters modulo N with χ(−1)=−1, including imprimitive. DirichletCharacter supplies zero at nonunits.|
characterPolynomial|399:406|Current finite sum uses equivalent 1/√N form, truncating at N; source support makes larger indices zero. Algebraic equivalence to Λ(n)/√n·Φ(n/N) has been reviewed; this round has no standalone machine bridge for the two infinite-sum displays.|
companionWeight|403:406|Φ(u)=√u φ(u); total Real.sqrt for u<0 is harmless because weight vanishes there.|
diagonalMoment|391:401|N⁻¹Σ_(n,N)=1 Λ(n)²φ(n/N)²; finite cutoff is justified by weight support. No standalone infinite-to-finite definition bridge is newly supplied.|
characterMoment|391:401|2/φ(N) times sum of squared complex norms over odd characters; normalization and reality unchanged.|
characterKernel|414:428|Two holomorphic variables with conjugation on character only; implemented conj(gχ(conj z)) is bridged to g_(barχ)(z). PositiveKernel alone is weaker than standard positivity, but actual kernel is separately Hermitian. Joint meromorphy and finite-dimensional rank helpers required.|character_kernel_original_formula,character_kernel_full_positive,character_kernel_rank_meaning
mellinWeight|422:426|Mathlib mellin integral has u^(s−1), multiplied by companion weight; positive half-line and complex powers match.|
verticalIntegral|422:426|Parameter s=σ+it converts ds=i dt, hence prefactor 1/(2π), without minus sign; nested integral reproduces (2πi)⁻² orientation.|
signedFamilies|465:479|k is a positive natural and signs are +,+,−. Family predicates allow zero n/m as total relations; actual off-diagonal expansion and weight-support results impose positive n/m or nonzero weight.|
signedBeta|514:518|Three terms B(1/2−s,s+z)+B(1/2−z,s+z)−B(1/2−s,1/2−z). Integral-based betaKernel only used on original betaDomain; Gamma-ratio continuation uses a separately bridged function.|beta_integral_continuation_bridge
betaFunction|1468:1482|Integral beta and Gamma quotient agree where real parts positive. betaDomain is Re s,z<1/2 and Re(s+z)>0, exactly lemma 4.1; no unnecessary positivity of each Re s,z.|beta_integral_continuation_bridge
gammaRatio|1532:1535|Γ((3/2−s)/2)/Γ((3/2+s)/2), numerator and denominator not inverted.|
diagonalSeries|1580:1590|Σ positive coprime n Λ(n)²/n^(1+w); domain Re w>0 is imposed on analytic results. |
densitySeries|1580:1604|Σ_(k≥1) S(kN)/k^w initially Re w>1. ContinuedDensity uses S(N)ζ(w)P_N(w); identity and convergence are separate audited statements, never applying original series below Re w=1.|
densityEulerProduct|1598:1604|Product over prime p>2 not dividing N, factors 1+p^(−w)/(p−2); convergence in Re w>0 supplied by auxiliary statement.|
betaModel|1690:1699|N^(−s−z) times continued density times signed Beta; local factor (1−νp(h)/p)/(1−1/p)² uses ν=1 if p divides h, otherwise 2; separate local-density product theorem.|
continuedBetaModel|1690:1709|S(N)(π/N)^(s+z)P_N(s+z)ζ(1−s−z)X1(s)X1(z), exactly continued expression. No GRH needed.|
residualKernel|1732:1758|Character kernel minus exact diagonal minus continued model. GRH only needed for holomorphy of first term, retained in proposition 4.5.|
analyticDomain|1704:1709|Both real parts strictly between 0 and 3/2; no silent restriction to smaller Hardy strip.|
logarithmicDerivative|1155:1177|L′/L at 1/2+s with positive sign; Dirichlet series for its negative. Uses derivative of actual imprimitive L-function.|
alpha|643:666|Main alpha=1/log N; definition generalizes to c/log N with default c=1. Main theorem and hypothesis use c=1.|
beta|643:666|Right Hardy boundary 1/8.|
sigmaStar|643:666|Interior contour 1/9, with alpha<1/10 to ensure interior.|
stripWidth|643:648|Width is beta−alpha (or beta−a), not half-width.|
hardyStrip|643:666|Open vertical strip a<Re s<b. RealizationValid records even N≥4, GRH, 0<a<1/10; weighted-L² versus raw H² representation requires later bridge.|cross:sections-5-7
boundarySpace|650:663|Two disjoint boundary lines, positive arc length on both, no 1/(2π). Bool×R with counting×Lebesgue and sum of two integrals implements disjoint union.|cross:sections-5-7
hardyInnerProduct|658:663|Paper linear in first slot; mathlib inner is reversed as inner v u. Boundary equality requires trace bridge.|cross:sections-5-7
weightedResidualKernel|668:673|E(s,conj z)/((1+s)(1+conj z)); numerator and denominator conjugations consistent.|
residualOperator|668:685|Current conditional choice falls back to zero if no representing bounded operator; existence, uniqueness, and integral specification must be certified under exact paper assumptions.|cross:sections-5-7
hilbertSchmidt|674:685|Square-sum over a countable orthonormal basis implements Hilbert–Schmidt for the infinite-dimensional separable Hardy space. As a generic predicate it excludes finite-dimensional spaces; scope is actual Hardy space.|cross:sections-5-7
eigenvalueFamily|674:685|Full real diagonal eigenbasis with square-summable values includes zeros; source lists nonzero eigenvalues with multiplicity. Need existence and zero-padding/order independence rather than trusting default zero family.|cross:sections-5-7
weightFunctional|691:701|Positive vertical Mellin normalization N^s PhiTilde(s)(1+s)h(s); valid interior contour and contour independence supplied in later results.|cross:sections-5-7
rieszVector|992:999|Chosen vector must satisfy ell(h)=paperInner h v, plus norm. Default zero branch is legitimate only after existence proof.|cross:sections-5-7
functionalNormSq|965:988|Exactly (2π)⁻¹ integral (Nu)^(2a)V²/(1+(Nu)^(−2(beta−a))) du/u. WeightEnergy is same without N-dependent factor. Identification with squared functional norm is a theorem.|cross:sections-5-7
spectralR|895:904|Pointwise all quaternion zeros on Re q=1/2; dictionary to norm≤δ requires spectral construction.|cross:sections-5-7
zeroFreeWidth|794:816|Pointwise open zero-free half-space Re q>1−η; boundary zeros allowed. Width restrictions imposed on dictionary theorem, not predicate itself.|cross:sections-5-7
widthFromNorm|812:818|η(M)=(1−sqrt(1−δ²/M²))/2; M>δ necessary at use sites, predicate total outside intended range.|
residualIntegral|945:959|Two upward contours with N^(s+z), both Mellin weights, residual and normalization; sign is cφS−G. Contour independence follows from exact identity.|cross:sections-5-7
derivativeWeight|971:987|V=Φ−uΦ′; real square equals |V|². No derivative of φ alone.|
completedLFunction|1240:1244|Entire completed odd L-function rather than total Gamma-times-L at poles. Machine bridge verifies entire extension, positive-half-plane normalization, zero set, and multiplicities.|completed_function_meaning
nontrivialZeros|1247:1259|Subtype of (rho,j), 0<Re rho<1, L(rho)=0, j<analyticOrderNatAt. Counted with multiplicity, not set of distinct zeros. Completed normalization has equal analytic order.|completed_function_meaning
zeroCount|1247:1259|Half-open t≤Im rho<t+1 window, ncard with a separately stated finiteness conjunct, and constant uniform in conductor/character.|
pairedZeroSum|1262:1288|Difference of resolvents at s and 3/2, summed over primitive induced zeros with multiplicity; GRH bridge replaces rho by 1/2+iγ. Normal summability controls absolute local uniform convergence.|
eulerCorrection|1262:1288|Finite primes dividing N but not inducing conductor, χ*(p) log p/(p^u−χ*(p)); both e(1/2+s) and subtract e(2) retained.|
'''
defs = {}
for line in definition_data.strip().splitlines():
    label, span, remainder = line.split('|', 2)
    note, bridges = remainder.rsplit('|', 1)
    a,b = map(int,span.split(':'))
    defs[label] = {'tex_lines':[a,b], 'semantic_assessment':note,
      'bridges':bridges.split(',') if bridges else [],
      'status':'reviewed_cross_section_bridge_required' if bridges.startswith('cross:') else 'reviewed_no_substantive_mismatch',
      'quantifier_scope':'Only the stated physical domain is compared; Lean total values outside it do not represent extra TeX claims.'}

statement_ranges = {
 'singularSeries_eq_existing':(1055,1059),
 'theorem_1_1':(289,298), 'theorem_1_1_weight_exists':(151,154),
 'theorem_1_2':(315,323), 'theorem_1_2_hypothesisR_implies_S':(306,313),
 'primePair_consequence':(325,328), 'lemma_3_1':(1090,1100),
 'lemma_3_1_odd_orthogonality':(1102,1117), 'proposition_3_2':(1180,1200),
 'proposition_3_2_finite_rank':(1198,1199), 'proposition_3_2_joint_meromorphic':(1190,1193),
 'lemma_3_3':(1247,1260), 'lemma_3_4':(1274,1290),
 'lemma_3_4_normal_convergence':(1274,1276), 'lemma_3_4_paired_zero_sum':(1262,1283),
 'lemma_3_5':(1365,1380), 'lemma_3_5_absolute_convergence':(1365,1402),
 'lemma_3_5_small_sigma':(1365,1376), 'lemma_3_5_weight_support':(1377,1409),
 'lemma_4_1':(1480,1497), 'lemma_4_1_absolute_convergence':(1480,1492),
 'lemma_4_1_signed_model':(1493,1497), 'lemma_4_1_local_density':(1499,1513),
 'lemma_4_2':(1538,1551), 'lemma_4_2_meromorphic':(1545,1551),
 'lemma_4_3':(1611,1630), 'lemma_4_3_uniform':(1619,1628),
 'lemma_4_3_density_convergence':(1580,1618), 'lemma_4_3_euler_product_convergence':(1642,1648),
 'proposition_4_4':(1704,1710), 'proposition_4_5':(1760,1768)
}
expected = re.findall(r'^def expect_(\w+)', (out/'Expected.lean').read_text(), re.M)
assert set(expected) == set(statement_ranges), set(expected)^set(statement_ranges)
comparisons = []
for name in expected:
    a,b = statement_ranges[name]
    comparisons.append({'expected':'TexAudit14.expect_'+name, 'actual':'LiLiuGoldbach16.'+name,
      'tex_lines':[a,b], 'label':name})
(out/'comparison.json').write_text(json.dumps(comparisons,ensure_ascii=False,indent=2)+'\n')

selected = [d for d in inventory['definitions'] if str(d['section']).split('.')[0] in ['1','2','3','4']]
assert {d['label'] for d in selected} == set(defs)
rows=[]
for d in selected:
    info = defs[d['label']]
    a,b = info['tex_lines']
    rows.append({'label':d['label'],'section':d['section'],'kind':'definition_family',
      **info,'original_tex':'\n'.join(tex[a-1:b]),
      'lean_declarations':[{'name':name,'current_locations':locations.get(name,[])}
        for name in d['actual_lean_declarations']]})
named = [s for s in inventory['statements'] if str(s['section']) in ['1','3','4']]
for s in named:
    names=[n.split('.')[-1] for n in s['actual_lean_declarations']]
    spans=[statement_ranges[n] for n in names]
    a,b=min(x[0] for x in spans),max(x[1] for x in spans)
    rows.append({'label':s['label'],'section':s['section'],'kind':'named_statement',
      'tex_lines':[a,b],'original_tex':'\n'.join(tex[a-1:b]),
      'status':'independently_reconstructed_pending_root_comparator',
      'lean_declarations':[{'name':n,'current_locations':locations.get(n,[])}
        for n in s['actual_lean_declarations']],
      'expected_props':['TexAudit14.expect_'+n for n in names],
      'quantifier_review':'See Expected.lean for exact full reconstruction. No paper conclusion is added as an assumption; only source context hypotheses occur.',
      'semantic_assessment':{
        'Theorem 1.1':'C is chosen after φ and before h. Both GRH and S remain eventual on even N; eventual threshold may depend on h. Relative asymptotic is included.',
        'Theorem 1.2':'GRH and R remain explicit eventual assumptions. Error is δN with correct S(N), N and log exponent. R⇒S helper covers every admissible h.',
        'Lemma 3.1':'Unconditional identity for every even N≥4, signs and normalization preserved; one Cφ for all N.',
        'Proposition 3.2':'Must combine three declarations: core expansion/GRH holomorphy/symmetry/positive real part/finrank bound; finite-dimensional helper prevents finrank=0 loophole; joint-meromorphic helper supplies genuinely two-variable quotient.',
        'Lemma 3.3':'No GRH assumed; primitive odd character; all zero multiplicities retained; C uniform over conductor and character. completedL bridge rules out Gamma-pole artifact.',
        'Lemma 3.4':'Compact-strip endpoints precede constant C; N, character and vertical height follow C. All Euler corrections present. Normal convergence and GRH resolvent conversion supplied by two helpers.',
        'Lemma 3.5':'Main declaration alone would miss small contours and support exclusion; all four declarations together cover unconditional σ>1/2, GRH 0<σ≤1/9, absolute convergence and signed-family elimination.',
        'Lemma 4.1':'All three absolutely convergent integrals and signed local-density combination; exact original domain allows one negative real part, provided sum positive. Local density separately derived.',
        'Lemma 4.2':'Core integral-domain factorization alone would not cover meromorphic identity; helper uses Gamma quotient and common entire quotient. Norm on real Beta bound is harmless only with nonnegative-real bridge.',
        'Lemma 4.3':'Four declarations jointly cover diagonal/density convergence, Euler product, meromorphic continuation, holomorphy off 1, residue, strict S>1, totient bounds and N-uniform vertical growth. Nonzero residue N/totient(N) makes pole simple.',
        'Proposition 4.4':'Unconditional continuation identity on initial Beta domain and holomorphy on full Omega; source N even≥4 retained.',
        'Proposition 4.5':'GRH is explicit and applies to all primitive dividing conductors. Residual has exact subtraction, holomorphy on Omega, symmetry and Hermitian conjugated kernel.'
      }[s['label']]})

summary={'source':str(texpath),'source_sha256':hashlib.sha256(texpath.read_bytes()).hexdigest(),
  'independence':'Original TeX and current source types read directly. Existing inventory only locates labels/names; old Reviewed.lean and old audit verdicts are not evidence.',
  'counts':{'named_statements':len(named),'definition_families':len(selected),
    'independent_expected_statement_props':len(expected),'prime_pair_consequence_extra':1,
    'individual_definition_declarations':sum(len(x['actual_lean_declarations']) for x in selected)},
  'mechanical_scope':'Root performs actual Lean comparator and full-type defeq; this report separately assesses TeX semantics. Definitions not independently reconstructed or linked by Bridges.lean retain semantic-review-only status.',
  'findings':[
    {'severity':'medium_definition_contract','id':'14-POS','finding':'PositiveKernel by itself only asserts nonnegative real part; it is not a generic PSD-kernel definition.','impact':'No missing conclusion for proposition 3.2 once characterKernel_hermitian is included.','resolution':'Bridges.lean character_kernel_full_positive'},
    {'severity':'medium_type_encoding','id':'14-RANK','finding':'A finite Module.finrank bound alone does not exclude infinite dimension.','impact':'Core proposition_3_2 needs its finite_rank auxiliary.','resolution':'Bridges.lean character_kernel_rank_meaning'},
    {'severity':'medium_totalization','id':'14-COMP','finding':'completedL must be entire continuation, not pointwise Gamma times L at trivial zeros.','impact':'Hadamard/zero-index semantics require matching entire function and multiplicity.','resolution':'Bridges.lean completed_function_meaning'},
    {'severity':'cross_section_pending','id':'14-CHOICE','finding':'Conditional choices for kernelOperator, eigenvalues, spectralQuaternion and rieszVector have default zero branches.','impact':'Equivalence to TeX needs existence/specification/uniqueness/ordering theorems under GRH and large N.','resolution':'Cross-section reviewer 5–7 must supply machinery; cannot mark definitions correct from nominal matching alone.'},
    {'severity':'manual_bridge_limit','id':'14-FINITE','finding':'Character polynomial and diagonal moment use finite sums; TeX displays sums over all positive integers.','impact':'Support truncation and change Λ/√n·Φ(n/N)=Λφ/√N were semantically checked, but no new standalone bridge in this audit.','resolution':'Do not claim universal mechanical TeX-to-definition equivalence; current proof finite projection is separately checked.'}],
  'rows':rows}
(out/'coverage.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(summary['counts'],ensure_ascii=False))
