from pathlib import Path
import json,re,hashlib
D=Path(__file__).parent
root=Path.cwd()
comparisons=json.loads((D/'comparison.json').read_text())
# These notes were written after a fresh direct reading of the TeX and current sources.
notes={
'proposition_5_1':('1926-1943','残差及带权核Hermitian；闭带邻域联合全纯；两Wirtinger导数为0；1/90与1/72距离。','两核、邻域、Fueter分量及严格左距离俱全；analyticDomain比闭带所需域大，无减弱。'),
'proposition_5_1_fueter_equation':('1918-1940','(∂s̄+j∂z)E(s,z̄)=0。','真实ℝ导数定义Wirtinger，嵌入ℍ后左乘j；并非把regular定义成True。'),
'lemma_5_2':('1986-2046','原始全纯+配对竖线L²上确界Hardy空间与加权L²的唯一满射等距。','正向RawHardy、精确范数、两条迹范数；反向∃!ψ，故频域编码没有用整个边界L²替代Hardy子空间。'),
'lemma_5_2_closed_trace_space':('2030-2046','迹映射的像为闭子空间。','闭像断言成立；线性由representation_spec给出，不能只把IsClosed单独读作子空间。'),
'lemma_5_2_representation_spec':('2003-2046','Fourier–Laplace真可积、L²边界极限、加权范数公式、线性与迹等距。','含两边Lp拓扑极限及加权积分可积；不是未证明的边界默认值。'),
'lemma_5_2_boundary_inner':('2036-2045','⟨h,g⟩=∫hα ḡα+∫hβ ḡβ，dt不含2π。','paperInner交换mathlib内积参数，使第一变量线性；两项正弧长，无归一化缺失。'),
'proposition_5_3':('2123-2141','积分算子、L²核、自伴紧HS、Σμ²=HS²=双边界核积分、谱范数及非零最大值。','全部合取齐全；SpectralData给真Hilbert基与特征关系；0特征值补齐基不改Σμ²/乘积。'),
'proposition_5_3_kernel_integrability':('2123-2128;2189-2201','每个Hardy向量与每个内点的两条边界积分均绝对可积。','排除Lean总积分在不可积时默认0的偷换；前提仅站立条件及内点。'),
'proposition_5_3_hs_basis_independent':('2133-2139','HS²=Σj‖T bj‖²，任意可数Hilbert基。','先有IsHilbertSchmidt，再对任意b；保证hsNorm的选择不影响数值。泛型Type u保留。'),
'proposition_5_4':('2226-2253','再生公式、1/(4Δ)csc、范数≤1/(8d)、E≤‖T‖|1+s||1+z|/(8√dsdz)。','内点条件、常数8、第二变量共轭均正确；精确范数与固定线界见补充。'),
'proposition_5_4_exact_norm':('2234-2241','‖ks‖²=1/[4(b−a)sin(π(Re s−a)/(b−a))]。','推广到任意a<b，和原式等价；非只给上界。'),
'proposition_5_4_kernel_pairing':('2280-2283','带权E(s,z̄)=⟨T kz,ks⟩。','参数顺序与第一变量线性的约定正确，未仅用范数界代替等式。'),
'proposition_5_4_fixed_contour':('2246-2253','固定σ*=1/9上|E|≪‖T‖(1+|v|+|t|)²。','∃C置于∀N前；第二Mellin变量无共轭是原文最终固定线形式。'),
'proposition_6_1':('2388-2409','ℍ局部一致乘积、intrinsic entire、T²正迹类、trace=HS²、复切片普通Fredholm行列式。','系数4/δ²、q(1−q)、T²均在；顺序/谱选择独立性由补充覆盖。'),
'proposition_6_1_enumeration':('2395-2397','任意ℕ置换后同一局部一致极限与复乘积。','∀e:ℕ≃ℕ，非仅某个排列。含0的基索引与原非零谱乘积差别由单位因子解释。'),
'proposition_6_1_complex_slice':('2404-2408','标准ℂ切片的ℍ函数等于复谱乘积嵌入。','显式complexQuaternion桥梁，不只给两个互不联系的函数。'),
'proposition_6_1_positive_fredholm_spec':('2376-2403','正迹类给非负可和谱、真compact/HS及任意基trace；行列式乘积可乘。','为choice定义提供存在、谱联系和基独立桥梁；∑非负本征值真实可和。'),
'proposition_6_1_square_determinant':('2399-2408','T²谱存在，trace(T²)=Σμ²，det(Id−tT²)=∏(1−tμ²)。','平方算子的任意选定谱确实连接原T的平方谱；不是按名字直接把行列式重定义为结论。'),
'proposition_6_1_all_slices':('2364-2374;2395-2397','每个纯虚单位J上由同一复全纯函数延伸。','J.re=0且J²=−1正是纯虚单位条件；所有J与z全称。'),
'proposition_6_1_spectral_choice_independent':('2395-2397','对T任意两份正交特征基资料，平方谱乘积相同。','单纯索引置换之外，补足Classical.choice谱选择的独立性。'),
'proposition_6_2':('2443-2476','X(0)=X(1)=1；反射、共轭、超平面反射；中心偶性；实x∉(0,1)时X(x)≥1。','归一化均为1；四元数star是共轭；实值性由切片性质而非仅Re界独自保证。'),
'proposition_6_2_centered_product':('2459-2465','X(1/2+ξ)=∏(1−μ²/δ²+4μ²ξ²/δ²)。','有限乘积局部一致收敛到中心函数，系数与符号正确。'),
'proposition_6_2_critical_values':('2466-2475','X(1/2+It)=∏(1−μ²(1+4t²)/δ²)∈ℝ，与I无关。','实乘积及实数到ℍ嵌入精确；∀单位纯虚I，右端不含I。'),
'proposition_6_3':('2493-2511','零点恰来自非零谱因子；非临界零点实且在(0,1)；例外谱索引有限。','↔排除无因子零点的无限积新零点；并非只证单向。'),
'proposition_6_3_three_cases':('2493-2505','d>1球面、d=1中心、0<d<1两实根。','三个区间、1/2、平方根/2与非零μ条件齐全；中心重数由另一补充给出。'),
'proposition_6_3_factor_central_order':('2501-2504','d=1时单个因子的中心零点恰二重。','analyticOrderNatAt=2，不是仅Even。'),
'proposition_6_3_multiplicities':('2506-2511','反射与共轭保持复切片重数，中心阶偶数，单位四元数共轭保零球。','X(0)=1及entire排除identically-zero时analyticOrderNatAt默认值的歧义。'),
 'theorem_6_1':('2552-2570','R⇔‖T‖≤δ；0<η<1/2时开半空间无零⇔‖T‖≤δ/[2√η(1−η)]；M界给η(M)。','开放半空间、非严格范数上界与严格η范围均保留；M>δ及‖T‖≤M齐全。'),
 'theorem_6_1_abstract_dictionary':('2552-2562','任意真实可和平方谱资料的两项谱字典。','Nonempty SpectralData含真基、对角化、平方可和；δ>0显式，不是任意虚构序列。'),
 'theorem_6_1_width_comparison':('2563-2570;2591-2599','δ²/(4M²)≤η(M)≤δ²/(2M²)。','δ>0,M>δ；给出原≍更具体的绝对常数，范围比η≤1/4更强。'),
 'theorem_6_2':('2616-2629','最终偶N满足GRH时‖T‖≤HS≪log²N且零区宽度≍S/(NlogN)。','∃正C,c在EvenEventually外；选择宽度精确cS/(NlogN)，隐含常数与阈值统一。'),
 'lemma_6_4':('2655-2664','所有0<σ≤β的奇字符均方平均≪log²N+σ⁻²。','绝对C位于N、σ外；奇字符包括非本原字符；每项积分可积明示。'),
 'lemma_6_4_zero_poisson_convergence':('2668-2678','Qχ(x,t)对所有非平凡零点按重数绝对收敛。','ZeroIndex primitiveCharacter包含解析零点重数；x>0，无额外零间距假设。'),
 'lemma_6_4_perron_residue':('2722-2735','(X^v−sqrt(X)^v)/(v²log sqrt X)在0的留数1。','X>1；亚纯与lim vK(v)=1，而非错误双极点/导数留数。'),
 'lemma_6_4_poisson_action_spec':('2912-2929','Pℓ非负、总质量1、可积；ℓ=0作用恒等，ℓ>0为卷积。','零参数没有直接套总函数P0=0；明确分支实现原文约定。'),
 'lemma_6_4_poisson_convolution':('2923-2929','P1*Pℓ=P1+ℓ≤(1+ℓ)P1。','ℓ>0；卷积真可积；常数1+ℓ未遗漏。'),
 'proposition_6_5':('2975-2986','P,D正迹类；HS(P)≤trace(P)≪log²N+α⁻²；HS(D)≤trace(D)≪α⁻²；HS(K)≪α⁻²。','三组全部保留，∃C在∀N外；变量α扩展还由ComponentNormBounds.component_bounds_of_average的∀a证实。'),
 'proposition_6_5_components_spec':('2965-2986;3030-3039','三分量均代表自己的边界核且T=P−D−K。','三个算子各有RepresentsKernel与每个内点/向量的绝对可积；符号顺序正确。'),
 'proposition_6_5_diagonal_vector_spec':('3007-3018','dn(s)=n^(−s)/(1+s)的Hardy向量、边界、π范数公式、rankOne约定。','n≥1避开n=0；无GRH是强于原站立条件，纯分析结论合理；rankOne h=⟨h,d⟩d。'),
 'lemma_7_1':('3266-3297','Mellin反演、紧σ区间均匀六次衰减、奇字符积分带负号。','反演∀σ，字符式0<σ≤1/9且GRH，φ全条件；平均双积分见absolute_convergence补充。'),
 'lemma_7_1_absolute_convergence':('3282-3297','一重反演、字符积分、字符矩双积分真可积；P(N)等于双积分。','原主lemma拆开的第二等式在本补充存在；两负号已抵消。'),
 'lemma_7_2':('3374-3390','对角积分=D(N)，Beta积分=−cφS(N)。','无GRH符合TeX；N^(s+z)仅留在对角项，模型中抵消；负号正确。'),
 'lemma_7_2_absolute_convergence':('3374-3390','对角和Beta两项在ℝ²绝对可积。','非仅迭代积分可积，Fubini使用条件完整。'),
 'lemma_7_2_convolutions':('3362-3370','C0,J0可积；J0全正半轴写法等于∫0^y；J0(1)=cφ。','support与对称性由IsWeight输入；全正半轴定义转换不是默认承认。'),
 'proposition_7_3':('3523-3531','rσ=cφS−G，任意0<σ≤1/9。','保留符号及GRH，右侧无σ蕴含轮廓独立。'),
 'proposition_7_3_absolute_convergence':('3523-3527','残差双Mellin积分绝对可积。','ℝ² Integrable排除默认积分值偷换。'),
 'proposition_7_4':('3595-3638','内轮廓无关连续泛函；Riesz范数=Q显式积分≤e²EV；Q=e²EV+Oφ(1/logN)。','∀内σ不只固定1/9；CLM、Riesz等式、精确平方范数、统一界、余项全部保留。GRH未加是纯泛函结论更强。'),
 'proposition_7_4_norm_integrals':('3623-3638','V²/u与Q积分真可积。','N>0、任意实a给更强纯分析结论；在目标域无假设缺口。'),
 'theorem_7_1':('3710-3722','cφS−G=⟨Tv,v⟩，|残差|≤Q‖T‖。','精确有符号等式与常数因子；不是仅不等式；统一≪由uniform补充。'),
 'theorem_7_1_uniform':('3710-3722','|cφS−G|≤e²EV‖T‖。','明确仅依赖φ的常数，实现原≪φ并对全部许可N统一。'),
 'lemma_7_5':('3781-3795','相对误差≪φ sqrt(log³N/(NηS))。','C在∀N、η前；分母cφS；0<η≤1/4和零区假设保留。'),
 'lemma_7_5_asymptotic':('3790-3795','NηS/log³N→∞蕴含相对渐近。','以∀ε∃B∀合格N,η的统一阈值形式实现，比任意单条趋∞序列足够且更强；未变成仅存在子序列。'),
 'interiorLine_memLp':('2005-2016;2050-2062','所有内竖线的Fourier–Laplace限制属于L²。','a<b、a<x<b；对任意频域ψ，无预先假设其像可积的循环。'),
 'boundaryTraces_exist':('1995-2001;2030-2046;2063-2070','每个Hardy向量两端都有L²拓扑极限。','∃(left,right)同时满足两端comap nhdsWithin极限；不是无来源任选边界函数。'),
}
conds={
'5':'算术应用固定偶N>e^10且GRH(N)；通用Hardy结论只需a<b，内点需a<Re(s)<b。NeZero N与ha可由大小条件推出。',
'6':'算术谱结论固定偶N>e^10且GRH(N)；泛型谱结论显式真SpectralData/正迹类；宽度0<η<1/2，M>δ。均匀常数先于N量化。',
'7':'φ光滑、支撑[1/3,2/3]、0≤φ≤1、对称非零；Mellin N≥4偶、0<σ≤1/9；涉及字符残差需GRH；Hardy构造N>e^10。'}
rows=[]
all_sources=list((root/'LiLiuGoldbach').rglob('*.lean'))
for c in comparisons:
 n=c['actual'].split('.')[-1];tex,formula,note=notes[n]
 locs=[]
 for p in all_sources:
  st=p.read_text()
  m=re.search(r'^theorem '+re.escape(n)+r'(?=\s|\{)',st,re.M)
  if m:
   if n=='lemma_7_2_convolutions' and p.name!='Weights.lean':continue
   locs.append({'file':str(p.relative_to(root)), 'line':st[:m.start()].count('\n')+1})
 assert len(locs)==1,(n,locs)
 section=n.split('_')[1] if n not in ['interiorLine_memLp','boundaryTraces_exist'] else '5'
 quant='逐一核对原TeX的全称范围、存在常数位置与前置条件；无发现实质弱化。'
 if 'asymptotic' in n:quant='∀φ,∀ε>0,∃B>0,∀N,η满足假设；B只可依φ,ε，不能依N,η。'
 if n in ['proposition_6_5','lemma_6_4','theorem_6_2','proposition_5_4_fixed_contour']:quant='∃正绝对常数置于∀N和其他变参数之前；无固定N依赖常数偷换。'
 rows.append({**c,'tex_lines_directly_reviewed':tex,'formula_or_clause':formula,'standing_and_implicit_conditions':conds[section],'quantifier_review':quant,'actual_source':locs[0],'semantic_assessment':'consistent_after_stated_representation_bridges','semantic_note':note,'reference_to_actual_check':'Lean proof assignment compiled successfully; independent comparator run owned by root','tex_to_reference_check':'human semantic transcription, not machine-certified'})
(D/'statement-matrix.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')

# Definition families: raw formulas and bridge obligations reviewed from the TeX.
defnotes={
'hardyFunction':('1986-2046','全纯且配对竖线平方积分上确界有限。','frequency L²不等同于任意边界对；RawHardy↔唯一Fourier–Laplace像由lemma5.2，闭迹子空间及线性/内积补充齐全。','raw_hardy_bridge; pw_bridge; check_5_2; check_lemma_5_2_representation_spec'),
'hardyNormSq':('1989-1994','sup_(0<ε<(b−a)/2)∫(|h(a+ε+it)|²+|h(b−ε+it)|²)dt。','sSup只在RawHardy与a<b域解释；可积性明示而非总积分退化。','raw_norm_bridge; check_5_2'),
'boundaryTrace':('1995-2001;2030-2046','hα,hβ是Lp空间内一侧极限。','IsBoundaryTrace是实际Lp拓扑Tendsto；boundaryTraces由已证exists选择；interiorLine由已证MemLp构造。','traces_bridge; check_boundaryTraces_exist; check_interiorLine_memLp'),
'hilbertSchmidtNorm':('2133-2141','HS²=Σ‖T ej‖²=Σμ²=四个边界产品积分。','hsNorm选择可数Hilbert基；basis-independent与算术谱/核等式均证明。此编码限定ℕ基，不宣称覆盖任意非可分/有限维空间。','check_proposition_5_3_hs_basis_independent; check_5_3'),
'fueterOperator':('1918-1940','∂s̄+j∂z，s,z∈ℂ，ℍ坐标s+zj。','Wirtinger以真实实变量导数定义；复数嵌入与左乘j顺序正确；F=E(s,z̄)。','check_proposition_5_1_fueter_equation'),
'hardyWeight':('2003-2007','exp(2aτ)+exp(2bτ)。','两条边界均带权；withDensity使用ENNReal.ofReal，权严格正无截断语义改变。','BoundaryWeight; pw_bridge'),
'fourierLaplace':('2005-2016','(2π)^−1/2∫ψ(τ)e^(sτ)dτ。','内点真可积有独立证明；Fourier约定、sqrt(2π)系数正确。','pw_bridge; check_interiorLine_memLp'),
'evaluationVector':('2213-2241','h(s)=⟨h,ks⟩，ks(z)=(4Δ)^−1csc(π(z+s̄−2a)/(2Δ))。','choose/else0仅作全域扩充；每个内点评价存在、再生式、精确范数已证明。','reproducer_bridge; check_5_4; check_proposition_5_4_exact_norm'),
'boundaryDistance':('2234-2241','min(Re s−a,b−Re s)。','仅在内点用故正；精确min没有换成固定常数。','distance_bridge'),
'sliceRegular':('2369-2374','所有复切片同一实系数entire函数且保共轭。','IntrinsicEntire=存在entire复f且f(z̄)=f(z)̄、所有J映射同一f。与实Taylor系数的数学等价在此作语义审阅，未另声称Lean已解析原文power-series措辞。','entire_bridge; check_6_1_product; check_proposition_6_1_all_slices'),
'quaternionSlice':('2364-2367','C_J={x+yJ:x,y∈ℝ}；J纯虚单位。','set构造自身不约束J，使用处有J.re=0,J²=−1（或范数1）条件。','slice_bridge; check_proposition_6_1_all_slices'),
'traceClass':('2376-2386','正紧A的非负特征值可和。','predicate使用对称、全向量非负二次型、某正交基对角可和；positive_fredholm_spec证明compact、可和谱及等迹，故在所用可数Hilbert空间语义一致。','check_proposition_6_1_positive_fredholm_spec'),
'trace':('2399-2403;3019-3034','正算子的trace=非负谱和，且与基无关。','positiveTrace选择基求和，域外默认0；域内任意基/本征值和等式已证明。','check_proposition_6_1_positive_fredholm_spec; check_proposition_6_1_square_determinant'),
'fredholmDeterminant':('2376-2386;2404-2408','普通det(Id−tA)=∏(1−t aj)，用于A=T²。','definition通过A本身真实谱，不是裸输入μ；平方谱桥梁与可乘性保留。','check_proposition_6_1_square_determinant; check_proposition_6_1_positive_fredholm_spec'),
'spectralRootParameter':('2493-2505','dj=δ²/μj²，μj≠0。','ratio函数全域定义但零分类明确非零μ；不使用除零默认值制造根。','ratio_bridge; check_proposition_6_3_three_cases'),
'averagedLogDerivativeEnergy':('2655-2664;2843-2859','Eχ(σ)=∫|gχ(σ+it)|²/(1+t²)，平均2/φ(N)Σodd。','除数、奇字符家族、height权均相同；可积性在lemma6.4。','energy_bridge; average_bridge; check_6_4'),
'poissonZeroSum':('2668-2678','Σprimitive zeros x/(x²+(t−γ)²)，按重数。','ZeroIndex含解析重数；primitiveCharacter及GRH先行，非仅distinct根。','zero_sum_bridge; check_lemma_6_4_zero_poisson_convergence'),
'referenceLine':('2631-2637','2/logN。','可在β右侧，不能误套Hardy内点前提；平均导数证明允许≤1/5参考线。','reference_line_bridge'),
'smoothedPerronWeight':('2722-2745','X=N/2,x=sqrtX；w=1(n≤x),log(X/n)/logx(x<n≤X),0(n>X)。','端点n=X权为0；K(v)=(X^v−x^v)/(v²logx)简单极点留数1。','cutoff_bridge; perron_bridge; check_lemma_6_4_perron_residue'),
'smoothedDirichletPolynomial':('2722-2727','Σn≤X Λ(n)χ(n)n^(−u)wX(n)。','Finset.range(floorX+1)包括截止端点，n=0和n=1由Λ=0贡献0，与正整数和等价。','direct formula review'),
'poissonKernel':('2912-2929','Pℓ(t)=ℓ/[π(ℓ²+t²)]；ℓ=0作用恒等。','realConvolution是∫f(u)g(t−u)；poissonAction的0分支单独定义且已证，未误用P0=0。','poisson_bridge; convolution_bridge; check_lemma_6_4_poisson_action_spec'),
'characterOperator':('2965-3006','P的核P_N(s,z̄)/[(1+s)(1+z̄)]。','积分表示/绝对可积/正迹类与trace界齐全；kernelOperator选择分支有构造义务。','check_proposition_6_5_components_spec; check_6_5'),
'diagonalOperator':('2965-2986;3007-3034','D的核D_N(s+z̄)/[(1+s)(1+z̄)]。','实际Hardy算子、迹类及范数界，与rankOne原式一致。','check_proposition_6_5_components_spec; check_6_5'),
'betaOperator':('2965-2986;3034-3039','K的核continuedModel(s,z̄)/[(1+s)(1+z̄)]。','正迹类未错误要求于K；只断言HS，上界Cα⁻²；T=P−D−K。','check_proposition_6_5_components_spec; check_6_5'),
'diagonalVector':('3007-3018','dn=n^(−s)/(1+s)，范数π[n^(−2α)/(1+α)+n^(−2β)/(1+β)]。','n≥1；定义Hardy向量choose后已有表达式和真实Lp边界证明。','diagonal_vector_bridge; check_proposition_6_5_diagonal_vector_spec'),
'rankOneOperator':('3016-3034','h↦⟨h,dn⟩dn，内积第一变量线性。','旧locator suggested rankOneOperator并非实际项目声明；真实对应Mathlib InnerProductSpace.rankOne，补充定理显式证应用公式。此为定位元数据差异，不是缺定义。','check_proposition_6_5_diagonal_vector_spec'),
'differenceConvolution':('3362-3368','C0(y)=∫0∞φ(u)φ(u+y)du。','Ioi 0积分，与端点0测度无关；定义公式一致。','difference_bridge'),
'sumConvolution':('3362-3368','J0(y)=∫0^yφ(u)φ(y−u)du。','实际先全正半轴；因φ支撑正半轴才等于有限积分，lemma7.2_convolutions显式完成桥梁。不能作为对任意φ的rfl等式。','sum_bridge; check_lemma_7_2_convolutions'),
'signedConvolution':('3362-3370','H0=2C0−J0。','系数2及负号正确；原J0(1)=cφ与H0(1)=−cφ区别保留。','signed_bridge'),
'weightIntegral':('3451-3458','a0=∫0∞φ(u)du。','不是cφ=∫φ²；pole cancellation与sampled H0(1)分开。','direct formula review; check_lemma_7_2_convolutions'),
'functionalIntegrand':('3724-3730','ΨN(s)=N^s MellinΦ(s)(1+s)。','用Φ=sqrtuφ而非φ；(1+s)未丢；与Riesz Bochner公式共轭约定一致。','psi_bridge'),
'availableNormMajorant':('3147-3184','C(log²N+α⁻²)，Qα≍φN^(2α)，x=αlogN时e^(2x)(1+x⁻²)。','可变a的共同C由component_bounds_of_average见证；整次负幂与倒数平方在a>0相等；Appendix A完整结论由另审计者负责。','direct formula review; ComponentNormBounds.component_bounds_of_average'),
}
inv=json.load(open(root/'reference/inventory.json'))
defrows=[]
for item in inv['definitions']:
 if str(item.get('section','')).split('.')[0] not in ['5','6','7']:continue
 name=item['label'];tex,formula,note,bridges=defnotes[name]
 actual=item.get('actual_lean_declarations') or ['InnerProductSpace.rankOne']
 if name=='rankOneOperator': actual=['InnerProductSpace.rankOne','LiLiuGoldbach16.proposition_6_5_diagonal_vector_spec']
 defrows.append(dict(label=name,section=item['section'],tex_lines_directly_reviewed=tex,formula=formula,actual_declarations=actual,semantic_assessment='consistent_on_paper_domain_with_noted_bridges',semantic_note=note,independent_reference_or_bridge=bridges,tex_to_reference_check='human semantic transcription, not machine-certified'))
assert len(defrows)==32
(D/'definition-matrix.json').write_text(json.dumps(defrows,ensure_ascii=False,indent=2)+'\n')
# A readable exhaustive table, in addition to structured records.
lines=['# 第5–7节独立TeX语义核对表','', '本文只使用本轮直接读取的原TeX和当前Lean定义/类型；旧inventory只提供定位。TeX→参考的语义判断是人工审阅；参考→实际的类型检验是Lean机械结果，不能混同。','', '## 命名结论与审阅辅助条目（54项）','', '|条目|TeX行|原文条款/条件|量词与语义判断|当前声明位置|','|---|---|---|---|---|']
for r in rows:
 lines.append('|'+r['actual'].split('.')[-1]+'|'+r['tex_lines_directly_reviewed']+'|'+r['formula_or_clause'].replace('|','\\|')+'|'+r['semantic_note'].replace('|','\\|')+'|'+r['actual_source']['file']+':'+str(r['actual_source']['line'])+'|')
lines+=['','## 定义族（32项）','','|定义|TeX行|原式|语义/桥梁检查|','|---|---|---|---|']
for r in defrows:lines.append('|'+r['label']+'|'+r['tex_lines_directly_reviewed']+'|'+r['formula'].replace('|','\\|')+'|'+r['semantic_note'].replace('|','\\|')+'；'+r['independent_reference_or_bridge']+'|')
(D/'semantic-matrix.md').write_text('\n'.join(lines)+'\n')
print('Wrote',len(rows),'statement rows and',len(defrows),'definition rows.')
