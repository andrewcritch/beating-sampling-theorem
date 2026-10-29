import BstLean.Part43Defs

/-!
# Part 43: the small ball from Fradelizi (Lemma SB)

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`.

Proof route.
* Integrate the coefficients of a polynomial with continuous-function coefficients to express
  `V(Z) = Var_μ 𝒫(Z)` as a nonnegative polynomial of total degree at most `2k`.
* Apply `FradeliziGauss` at `t = 3` and let `c` decrease to zero. The nonzero probability is zero
  or one. Apply this to each translated polynomial; Gaussian full support excludes the zero
  alternative for a nonconstant polynomial. Continuous tails then give a positive `1/e` quantile.
* Prove the closed-form integral for `Ch` with an exponential-polynomial antiderivative. The
  layer-cake formula and polynomial change of variables give `E V ≤ C_{2k} M_V`.
* Apply the rescaled Fradelizi inequality below the quantile and compare its threshold with
  `t_sb E V` to obtain the required strict sublevel bound.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

private lemma variance_nonneg (μ : Measure (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) : 0 ≤ varU μ f := by
  exact integral_nonneg fun x => sq_nonneg _

private lemma variance_mean_nonneg (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) :
    0 ≤ ∫ Z, varU μ (Pcal (d := d) k T Z) ∂stdGauss (CoefIdxD n d) := by
  exact integral_nonneg fun Z => variance_nonneg μ _

private lemma smallball_zero_mean (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (p : ℝ) (hzero :
      (∫ Z, varU μ (Pcal (d := d) k T Z) ∂stdGauss (CoefIdxD n d)) = 0) :
    stdGauss (CoefIdxD n d) {Z | varU μ (Pcal k T Z) <
      tsb k p * ∫ Z', varU μ (Pcal k T Z') ∂stdGauss (CoefIdxD n d)} ≤
        ENNReal.ofReal p := by
  have hempty : {Z | varU μ (Pcal (d := d) k T Z) <
      tsb k p * ∫ Z', varU μ (Pcal k T Z') ∂stdGauss (CoefIdxD n d)} = ∅ := by
    ext Z
    simp only [hzero, mul_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (variance_nonneg μ _)
  rw [hempty, measure_empty]
  exact bot_le

private lemma map_polynomial (x : Fin n → ℝ) (a : Fin n) :
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, mapMD Z x a = MvPolynomial.eval Z P) ∧ P.totalDegree ≤ 1 := by
  classical
  let Q (i : ℕ) (β : Sym (Fin n) i) : MvPolynomial (CoefIdxD n d) ℝ :=
    if hi : i < d + 1 then
      MvPolynomial.C (BstLean.Part36.monoVal x β.1) *
        MvPolynomial.X ⟨⟨i, hi⟩, (β, a)⟩ else 0
  refine ⟨∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i, Q i β, ?_, ?_⟩
  · intro Z
    simp only [mapMD, MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro β hβ
    have hi' : i < d + 1 := Finset.mem_range.mp hi
    simp only [Q, BstLean.Part36.coefD, dif_pos hi', MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact mul_comm _ _
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    apply MvPolynomial.totalDegree_finsetSum_le
    intro β hβ
    dsimp [Q]
    split_ifs
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl]
    · simp

private lemma Pcal_polynomial (k : ℕ) (T : Tens n) (x : Fin n → ℝ) :
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, Pcal k T Z x = MvPolynomial.eval Z P) ∧ P.totalDegree ≤ k := by
  classical
  choose L hL hdeg using (map_polynomial (d := d) x)
  let Q (j : ℕ) : MvPolynomial (CoefIdxD n d) ℝ :=
    MvPolynomial.C ((Real.sqrt (DD n d) ^ j)⁻¹) *
      ∑ w : Fin j → Fin n, MvPolynomial.C (T j w) * ∏ t, L (w t)
  refine ⟨∑ j ∈ Finset.Icc 1 k, Q j, ?_, ?_⟩
  · intro Z
    simp only [Q, Pcal, uJ, contr, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_prod]
    simp_rw [← hL]
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_eq_mul_inv, mul_comm]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply le_trans (MvPolynomial.totalDegree_mul _ _)
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
    apply Finset.sup_le
    intro w hw
    apply le_trans (MvPolynomial.totalDegree_mul _ _)
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply le_trans (MvPolynomial.totalDegree_finsetProd _ _)
    calc
      ∑ t : Fin j, (L (w t)).totalDegree ≤ ∑ _t : Fin j, 1 :=
        Finset.sum_le_sum fun t ht => hdeg (w t)
      _ = j := by simp
      _ ≤ k := (Finset.mem_Icc.mp hj).2

private lemma sphere_cont_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ := by
  let := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private abbrev JointPoly (n d : ℕ) :=
  MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)

private noncomputable def jointEval (P : JointPoly n d)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z P

private lemma joint_integral_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (P : JointPoly n d) :
    ∃ Q : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, (∫ x, jointEval P Z x ∂μ) = MvPolynomial.eval Z Q) ∧
      Q.totalDegree ≤ P.totalDegree := by
  classical
  refine ⟨∑ e ∈ P.support, MvPolynomial.monomial e (∫ x, P.coeff e x ∂μ), ?_, ?_⟩
  · intro Z
    have hE (x) : jointEval P Z x =
        ∑ e ∈ P.support, P.coeff e x * e.prod (fun i a => Z i ^ a) := by
      conv_lhs => unfold jointEval; rw [P.as_sum]
      simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
        Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
    simp_rw [hE]
    rw [integral_finsetSum _ (fun e _ =>
      (sphere_cont_integrable hμ (P.coeff e).continuous).mul_const _)]
    simp only [integral_mul_const, map_sum, MvPolynomial.eval_monomial]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro e he
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)

private lemma continuous_mono (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) := by
  exact continuous_multiset_prod s (fun i _ => continuous_apply i)

private noncomputable def mapJoint (a : Fin n) : JointPoly n d :=
  ∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then MvPolynomial.X ⟨⟨i, h⟩, (β, a)⟩ else 0) *
      MvPolynomial.C ⟨fun x => BstLean.Part36.monoVal x β.1, continuous_mono β.1⟩

private lemma mapJoint_eval (a : Fin n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (mapJoint a) Z x = mapMD Z x a := by
  classical
  unfold mapJoint jointEval mapMD BstLean.Part36.coefD
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i < d + 1 := Finset.mem_range.mp hi
  simp [h]

private lemma mapJoint_degree (a : Fin n) :
    (mapJoint (d := d) a).totalDegree ≤ 1 := by
  classical
  unfold mapJoint
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply MvPolynomial.totalDegree_finsetSum_le
  intro β hβ
  apply (MvPolynomial.totalDegree_mul _ _).trans
  split_ifs <;> simp

private noncomputable def pJoint (k : ℕ) (T : Tens n) : JointPoly n d :=
  ∑ j ∈ Finset.Icc 1 k, (∑ w : Fin j → Fin n,
    MvPolynomial.C (ContinuousMap.const _ (T j w)) * ∏ t, mapJoint (w t)) *
      MvPolynomial.C (ContinuousMap.const _ ((Real.sqrt (DD n d) ^ j)⁻¹))

private lemma pJoint_eval (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (pJoint (d := d) k T) Z x = Pcal k T Z x := by
  classical
  simp [pJoint, jointEval, Pcal, uJ, contr, div_eq_mul_inv,
    show ∀ a, MvPolynomial.eval₂
      ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z (mapJoint a) =
        mapMD Z x a from fun a => mapJoint_eval a Z x]

private lemma pJoint_degree (k : ℕ) (T : Tens n) :
    (pJoint (d := d) k T).totalDegree ≤ k := by
  classical
  unfold pJoint
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, add_zero]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro w hw
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ t : Fin j, (mapJoint (d := d) (w t)).totalDegree ≤ ∑ _t : Fin j, 1 :=
      Finset.sum_le_sum fun t ht => mapJoint_degree _
    _ = j := by simp
    _ ≤ k := (Finset.mem_Icc.mp hj).2

private lemma jointEval_continuous (P : JointPoly n d) (Z : CoefIdxD n d → ℝ) :
    Continuous (jointEval P Z) := by
  classical
  have he : jointEval P Z = fun x =>
      ∑ e ∈ P.support, P.coeff e x * e.prod (fun i a => Z i ^ a) := by
    funext x
    conv_lhs => unfold jointEval; rw [P.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  rw [he]
  exact continuous_finsetSum _ fun e he => (P.coeff e).continuous.mul continuous_const

private lemma variance_expansion {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (f : (Fin n → ℝ) → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    varU μ f = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  let := hμ.prob
  unfold varU
  have he (x) : (f x - ∫ y, f y ∂μ) ^ 2 =
      f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x + (∫ y, f y ∂μ) ^ 2 := by ring
  simp_rw [he]
  have hi : Integrable (fun x => f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x) μ :=
    hf2.sub (hf.const_mul (2 * ∫ y, f y ∂μ))
  rw [integral_add hi (integrable_const ((∫ y, f y ∂μ) ^ 2)),
    integral_sub hf2 (hf.const_mul (2 * ∫ y, f y ∂μ)), integral_const_mul, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  ring

private lemma variance_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (T : Tens n) :
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, varU μ (Pcal k T Z) = MvPolynomial.eval Z P) ∧ P.totalDegree ≤ 2 * k := by
  classical
  obtain ⟨Q, hQ, hQdeg⟩ := joint_integral_polynomial hμ (pJoint (d := d) k T)
  obtain ⟨R, hR, hRdeg⟩ := joint_integral_polynomial hμ ((pJoint (d := d) k T) ^ 2)
  refine ⟨R + MvPolynomial.C (-1) * Q ^ 2, ?_, ?_⟩
  · intro Z
    have hcont : Continuous (Pcal (d := d) k T Z) := by
      rw [← show jointEval (pJoint k T) Z = Pcal (d := d) k T Z from
        funext (pJoint_eval k T Z)]
      exact jointEval_continuous (pJoint k T) Z
    rw [variance_expansion hμ _ (sphere_cont_integrable hμ hcont)
      (sphere_cont_integrable hμ (hcont.pow 2))]
    have hQ' := hQ Z
    simp only [pJoint_eval] at hQ'
    have hR' := hR Z
    simp only [jointEval, map_pow] at hR'
    change (∫ x, jointEval (pJoint k T) Z x ^ 2 ∂μ) = _ at hR'
    simp only [pJoint_eval] at hR'
    rw [hQ', hR']
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_pow]
    ring
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact hRdeg.trans ((MvPolynomial.totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left 2 (pJoint_degree k T)))
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left 2 (hQdeg.trans (pJoint_degree k T)))

private lemma gaussian_polynomial_integrable {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z P) (stdGauss ι) := by
  classical
  rw [P.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (μ := ProbabilityTheory.gaussianReal 0 1)
      (by simp) (e i))).const_mul _

private lemma mapMD_zero (x : Fin n → ℝ) (a : Fin n) :
    mapMD (fun _ : CoefIdxD n d => 0) x a = 0 := by
  classical
  simp [mapMD, BstLean.Part36.coefD]

private lemma Pcal_zero (k : ℕ) (T : Tens n) (x : Fin n → ℝ) :
    Pcal k T (fun _ : CoefIdxD n d => 0) x = 0 := by
  classical
  unfold Pcal
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simp only [uJ, contr, mapMD_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, zero_pow hj0, mul_zero, Finset.sum_const_zero, zero_div]

private lemma variance_at_zero (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) :
    varU μ (Pcal k T (fun _ : CoefIdxD n d => 0)) = 0 := by
  simp only [varU, Pcal_zero, integral_zero, sub_self, zero_pow (by decide : 2 ≠ 0)]

private lemma tail_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun N : ℕ => (μ {z | a / ((N : ℝ) + 1) ≤ |f z|}).toReal)
      Filter.atTop (nhds (μ {z | f z ≠ 0}).toReal) := by
  let S (N : ℕ) := {z | a / ((N : ℝ) + 1) ≤ |f z|}
  have hmono : Monotone S := by
    intro i j hij z hz
    exact le_trans (div_le_div_of_nonneg_left ha.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)) hz
  have hunion : (⋃ N, S N) = {z | f z ≠ 0} := by
    ext z
    constructor
    · intro hz
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hz
      have hpos : 0 < a / ((N : ℝ) + 1) := div_pos ha (by positivity)
      exact abs_pos.mp (lt_of_lt_of_le hpos hN)
    · intro hz
      have hpos : 0 < |f z| := abs_pos.mpr hz
      obtain ⟨N, hN⟩ := exists_nat_gt (a / |f z|)
      apply Set.mem_iUnion.mpr
      refine ⟨N, (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mpr ?_⟩
      have he := (div_lt_iff₀ hpos).mp hN
      nlinarith
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ht

private lemma fradelizi_nonzero_dichotomy (hFr : FradeliziGauss) {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (h : ℕ) (hdeg : P.totalDegree ≤ h) :
    (stdGauss ι {z | MvPolynomial.eval z P ≠ 0}).toReal = 0 ∨
      (stdGauss ι {z | MvPolynomial.eval z P ≠ 0}).toReal = 1 := by
  have ha : 0 < (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval 3 :=
    lt_of_lt_of_le zero_lt_one (Polynomial.Chebyshev.one_le_eval_T_real _ (by norm_num))
  have hL := tail_tendsto_zero (stdGauss ι) (fun z => MvPolynomial.eval z P)
    ((Polynomial.Chebyshev.T ℝ (h : ℤ)).eval 3) ha
  have hR := tail_tendsto_zero (stdGauss ι) (fun z => MvPolynomial.eval z P) 1 zero_lt_one
  have hbound (N : ℕ) :
      (stdGauss ι {z | (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval 3 /
        ((N : ℝ) + 1) ≤ |MvPolynomial.eval z P|}).toReal ≤
      (stdGauss ι {z | 1 / ((N : ℝ) + 1) ≤ |MvPolynomial.eval z P|}).toReal ^ 2 := by
    have hf := hFr ι P h hdeg 3 (1 / ((N : ℝ) + 1)) (by norm_num) (by positivity)
    norm_num only [show (3 + 1 : ℝ) / 2 = 2 by norm_num, Real.rpow_two] at hf
    have he : (1 / ((N : ℝ) + 1)) * (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval 3 =
        (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval 3 / ((N : ℝ) + 1) := by ring
    rw [he] at hf
    exact hf
  have hq := le_of_tendsto_of_tendsto' hL (hR.pow 2) hbound
  have hq0 : 0 ≤ (stdGauss ι {z | MvPolynomial.eval z P ≠ 0}).toReal := ENNReal.toReal_nonneg
  have hq1 : (stdGauss ι {z | MvPolynomial.eval z P ≠ 0}).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr
      prob_le_one
  by_cases hz : (stdGauss ι {z | MvPolynomial.eval z P ≠ 0}).toReal = 0
  · exact Or.inl hz
  · right
    have hqpos : 0 < (stdGauss ι {z | MvPolynomial.eval z P ≠ 0}).toReal :=
      lt_of_le_of_ne hq0 (Ne.symm hz)
    rcases eq_or_lt_of_le hq1 with he | hlt
    · exact he
    · have hmul := mul_pos hqpos (sub_pos.mpr hlt)
      nlinarith

private lemma gaussian_open_pos {ι : Type*} [Fintype ι] :
    Measure.IsOpenPosMeasure (stdGauss ι) := by
  letI : Measure.IsOpenPosMeasure (ProbabilityTheory.gaussianReal 0 1) :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  unfold stdGauss
  infer_instance

private lemma fradelizi_null_fiber (hFr : FradeliziGauss) {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (h : ℕ) (hdeg : P.totalDegree ≤ h)
    (hnotconst : ∀ a : ℝ, ∃ z, MvPolynomial.eval z P ≠ a) (a : ℝ) :
    stdGauss ι {z | MvPolynomial.eval z P = a} = 0 := by
  classical
  letI := gaussian_open_pos (ι := ι)
  let R : MvPolynomial ι ℝ := P + MvPolynomial.C (-a)
  have hRdeg : R.totalDegree ≤ h := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    exact max_le hdeg (by simp)
  have hnonzero : ∃ z, MvPolynomial.eval z R ≠ 0 := by
    obtain ⟨z, hz⟩ := hnotconst a
    refine ⟨z, ?_⟩
    intro he
    apply hz
    simp only [R, MvPolynomial.eval_add, MvPolynomial.eval_C] at he
    linarith
  have hmeas : MeasurableSet {z | MvPolynomial.eval z R ≠ 0} :=
    (R.continuous_eval.measurable (measurableSet_singleton 0)).compl
  rcases fradelizi_nonzero_dichotomy hFr R h hRdeg with hzero | hone
  · have hzero' : stdGauss ι {z | MvPolynomial.eval z R ≠ 0} = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right (measure_ne_top _ _)
    have hae : (fun z => MvPolynomial.eval z R) =ᵐ[stdGauss ι] fun _ => 0 := by
      simpa only [Filter.EventuallyEq, ae_iff, not_not] using hzero'
    have he := MeasureTheory.Measure.eq_of_ae_eq hae R.continuous_eval continuous_const
    obtain ⟨z, hz⟩ := hnonzero
    exact False.elim (hz (congrFun he z))
  · have hcompl : (stdGauss ι {z | MvPolynomial.eval z R ≠ 0}ᶜ).toReal = 0 := by
      rw [← measureReal_def, probReal_compl_eq_one_sub hmeas]
      simp only [measureReal_def, hone, sub_self]
    have hcompl' : stdGauss ι {z | MvPolynomial.eval z R ≠ 0}ᶜ = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hcompl |>.resolve_right (measure_ne_top _ _)
    have hsets : {z | MvPolynomial.eval z P = a} = {z | MvPolynomial.eval z R ≠ 0}ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_not,
        R, MvPolynomial.eval_add, MvPolynomial.eval_C]
      constructor <;> intro he <;> linarith
    rw [hsets]
    exact hcompl'

private lemma continuous_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hnull : ∀ a, μ {z | f z = a} = 0) :
    Continuous (fun a : ℝ => (μ {z | a ≤ f z}).toReal) := by
  classical
  let F (a : ℝ) (z : Ω) : ℝ := if a ≤ f z then 1 else 0
  have hset (a : ℝ) : MeasurableSet {z | a ≤ f z} := measurableSet_le measurable_const hf
  have hFint (a : ℝ) : (∫ z, F a z ∂μ) = (μ {z | a ≤ f z}).toReal := by
    change (∫ z, {z | a ≤ f z}.indicator (fun _ => (1 : ℝ)) z ∂μ) = _
    exact integral_indicator_one (hset a)
  apply continuous_iff_continuousAt.mpr
  intro a
  have hmeas : ∀ᶠ t in nhds a, AEStronglyMeasurable (F t) μ :=
    Filter.Eventually.of_forall fun t =>
      (measurable_const.piecewise (hset t) measurable_const).aestronglyMeasurable
  have hbound : ∀ᶠ t in nhds a, ∀ᵐ z ∂μ, ‖F t z‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro t
    apply Filter.Eventually.of_forall
    intro z
    dsimp [F]
    split_ifs <;> norm_num
  have hlim : ∀ᵐ z ∂μ, Filter.Tendsto (fun t => F t z) (nhds a) (nhds (F a z)) := by
    have hae : ∀ᵐ z ∂μ, f z ≠ a := by
      simpa only [ae_iff, Set.mem_setOf_eq, not_not] using hnull a
    filter_upwards [hae] with z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_nhds hlt] with t ht
      simp only [F, not_le.mpr hlt, not_le.mpr ht, if_false]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_nhds hgt] with t ht
      simp only [F, hgt.le, ht.le, if_true]
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    hmeas hbound (integrable_const _) hlim
  simpa only [ContinuousAt, hFint] using ht

private lemma positive_quantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hnonneg : ∀ z, 0 ≤ f z) (hnull : ∀ a, μ {z | f z = a} = 0)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ M : ℝ, 0 < M ∧ (μ {z | M ≤ f z}).toReal = q := by
  let S (N : ℕ) := {z | (N : ℝ) + 1 ≤ f z}
  have hmono : Antitone S := by
    intro i j hij z hz
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    exact le_trans hij' hz
  have hmeas (N : ℕ) : MeasurableSet (S N) := measurableSet_le measurable_const hf
  have hinter : (⋂ N, S N) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨N, hN⟩ := exists_nat_gt (f z)
    have he := Set.mem_iInter.mp hz N
    change (N : ℝ) + 1 ≤ f z at he
    linarith
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hmeas N).nullMeasurableSet)
    hmono ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  have htR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  have hevent : ∀ᶠ N : ℕ in Filter.atTop, (μ (S N)).toReal < q :=
    htR.eventually (gt_mem_nhds hq0)
  obtain ⟨N, hN⟩ := hevent.exists
  have hzero : (μ {z | 0 ≤ f z}).toReal = 1 := by
    have he : {z | 0 ≤ f z} = Set.univ := Set.eq_univ_of_forall hnonneg
    rw [he, measure_univ, ENNReal.toReal_one]
  have hcont := continuous_tail μ f hf hnull
  obtain ⟨M, hM⟩ := intermediate_value_univ ((N : ℝ) + 1) 0 hcont
    ⟨hN.le, by rw [hzero]; exact hq1.le⟩
  change (μ {z | M ≤ f z}).toReal = q at hM
  refine ⟨M, ?_, hM⟩
  by_contra hm
  have hm0 : M ≤ 0 := le_of_not_gt hm
  have he : {z | M ≤ f z} = Set.univ := Set.eq_univ_of_forall fun z => hm0.trans (hnonneg z)
  rw [he, measure_univ, ENNReal.toReal_one] at hM
  linarith

private lemma lamP_gt_one (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 - Real.exp (-1)) : 1 < lamP p := by
  have hp : 0 < 1 - p := by linarith [Real.exp_pos (-1)]
  have hlog0 : Real.log (1 - p) < 0 := Real.log_neg hp (by linarith)
  have hlog1 : -1 < Real.log (1 - p) :=
    (Real.lt_log_iff_exp_lt hp).mpr (by linarith)
  rw [lamP, ← neg_div_neg_eq, neg_neg]
  exact (one_lt_div (neg_pos.mpr hlog0)).mpr (by linarith)

private lemma exp_neg_inv_lamP (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 - Real.exp (-1)) : Real.exp (-1 / lamP p) = 1 - p := by
  have hp : 0 < 1 - p := by linarith [Real.exp_pos (-1)]
  have hlog : Real.log (1 - p) ≠ 0 := ne_of_lt (Real.log_neg hp (by linarith))
  have he : -1 / lamP p = Real.log (1 - p) := by
    unfold lamP
    field_simp
  rw [he, Real.exp_log hp]

private lemma fradelizi_chebP (hFr : FradeliziGauss) {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (h : ℕ) (hdeg : P.totalDegree ≤ h)
    (ell c : ℝ) (hell : 1 < ell) (hc : 0 < c) :
    (stdGauss ι {z | c * (chebP h).eval ell ≤ |MvPolynomial.eval z P|}).toReal ≤
      ((stdGauss ι {z | c ≤ |MvPolynomial.eval z P|}).toReal) ^ ell := by
  have hf := hFr ι P h hdeg (2 * ell - 1) c (by linarith) hc
  have hexp : (2 * ell - 1 + 1) / 2 = ell := by ring
  simpa only [chebP, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one, hexp] using hf

private lemma quantile_tail_lower (hFr : FradeliziGauss) {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (h : ℕ) (hdeg : P.totalDegree ≤ h)
    (p c : ℝ) (hp0 : 0 < p) (hp1 : p < 1 - Real.exp (-1)) (hc : 0 < c)
    (hquant : Real.exp (-1) ≤
      (stdGauss ι {z | c * (chebP h).eval (lamP p) ≤ |MvPolynomial.eval z P|}).toReal) :
    1 - p ≤ (stdGauss ι {z | c ≤ |MvPolynomial.eval z P|}).toReal := by
  have hp : 0 < 1 - p := by linarith [Real.exp_pos (-1)]
  have hlog : Real.log (1 - p) ≠ 0 := ne_of_lt (Real.log_neg hp (by linarith))
  have hl := lamP_gt_one p hp0 hp1
  have hpow : (1 - p) ^ lamP p = Real.exp (-1) := by
    rw [Real.rpow_def_of_pos hp]
    congr 1
    unfold lamP
    field_simp
  apply (Real.rpow_le_rpow_iff hp.le ENNReal.toReal_nonneg (by linarith : 0 < lamP p)).mp
  rw [hpow]
  exact hquant.trans (fradelizi_chebP hFr P h hdeg (lamP p) c hl hc)

private lemma iterate_derivative_comp_linear (P : Polynomial ℝ) (m : ℕ) :
    Polynomial.derivative^[m] (P.comp (2 * Polynomial.X - 1)) =
      Polynomial.C ((2 : ℝ) ^ m) *
        (Polynomial.derivative^[m] P).comp (2 * Polynomial.X - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Polynomial.derivative_mul, Polynomial.derivative_C]
    simp only [zero_mul, zero_add, Polynomial.derivative_comp,
      Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_ofNat,
      Polynomial.derivative_X, Polynomial.derivative_one, zero_mul, zero_add, mul_one, sub_zero]
    rw [pow_succ, Polynomial.C_mul]
    simp only [Polynomial.C_ofNat]
    ring

private lemma T_iterate_derivative_nonneg (h m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ (Polynomial.derivative^[m] (Polynomial.Chebyshev.T ℝ (h : ℤ))).eval x := by
  have hs := Polynomial.Chebyshev.T_iterate_derivative_mem_span_T (R := ℝ) h m
  refine Submodule.span_induction (p := fun P _ => 0 ≤ P.eval x) ?_ ?_ ?_ ?_ hs
  · intro P hP
    obtain ⟨j, hj, rfl⟩ := hP
    exact zero_le_one.trans (Polynomial.Chebyshev.one_le_eval_T_real _ hx)
  · simp
  · intro P Q hP hQ ihP ihQ
    simpa only [Polynomial.eval_add] using add_nonneg ihP ihQ
  · intro a P hP ih
    simpa only [Polynomial.eval_smul, nsmul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_natCast] using mul_nonneg (Nat.cast_nonneg a) ih

private lemma chebP_derivative_nonneg (h m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ (Polynomial.derivative^[m] (chebP h)).eval x := by
  rw [chebP, iterate_derivative_comp_linear]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one]
  exact mul_nonneg (by positivity) (T_iterate_derivative_nonneg h m _ (by linarith))

private lemma chebP_degree (h : ℕ) : (chebP h).natDegree ≤ h := by
  unfold chebP
  apply Polynomial.natDegree_comp_le.trans
  rw [Polynomial.Chebyshev.natDegree_T]
  simp only [Int.natAbs_natCast]
  have hd : (2 * Polynomial.X - 1 : Polynomial ℝ).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simpa using (Polynomial.natDegree_mul_le (p := (2 : Polynomial ℝ)) (q := Polynomial.X))
    · simp
  simpa using Nat.mul_le_mul_left h hd

private lemma exponential_derivative_integral (P : Polynomial ℝ) (h : ℕ)
    (hdeg : P.natDegree ≤ h) (hnonneg : ∀ x : ℝ, 1 < x → 0 ≤ P.derivative.eval x) :
    (∫ x in Set.Ioi (1 : ℝ), Real.exp (-x) * P.derivative.eval x) =
      Real.exp (-1) * ∑ m ∈ Finset.Icc 1 h, (Polynomial.derivative^[m] P).eval 1 := by
  classical
  let Q : Polynomial ℝ := ∑ i ∈ Finset.range h, Polynomial.derivative^[i + 1] P
  have hlast : Polynomial.derivative^[h + 1] P = 0 :=
    Polynomial.iterate_derivative_eq_zero (by omega)
  have hQderiv : Q.derivative = Q - P.derivative := by
    have hd : Q.derivative = ∑ i ∈ Finset.range h, Polynomial.derivative^[i + 2] P := by
      simp only [Q, map_sum, ← Function.iterate_succ_apply', Nat.add_assoc]
    have he0 : (∑ i ∈ Finset.range (h + 1), Polynomial.derivative^[i + 1] P) = Q := by
      rw [Finset.sum_range_succ, hlast, add_zero]
    have he1 : (∑ i ∈ Finset.range (h + 1), Polynomial.derivative^[i + 1] P) =
        Q.derivative + P.derivative := by
      rw [Finset.sum_range_succ', hd]
      simp only [Nat.zero_add, Function.iterate_one, Nat.add_assoc]
    rw [he0] at he1
    exact (eq_sub_iff_add_eq).mpr he1.symm
  have hQone : Q.eval 1 = ∑ m ∈ Finset.Icc 1 h, (Polynomial.derivative^[m] P).eval 1 := by
    simp only [Q, Polynomial.eval_finsetSum]
    refine Finset.sum_bij (fun i hi => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Icc]
      have := Finset.mem_range.mp hi
      omega
    · intro i hi j hj he
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      rfl
  have hderiv (x : ℝ) : HasDerivAt (fun x => -(Real.exp (-x) * Q.eval x))
      (Real.exp (-x) * P.derivative.eval x) x := by
    have hd := (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).mul
      (Q.hasDerivAt x)).neg
    change HasDerivAt (fun t => -(Real.exp (-t) * Q.eval t))
      (-(Real.exp (-x) * -1 * Q.eval x + Real.exp (-x) * Q.derivative.eval x)) x at hd
    convert hd using 1
    rw [hQderiv, Polynomial.eval_sub]
    ring
  have hlim : Filter.Tendsto (fun x => -(Real.exp (-x) * Q.eval x))
      Filter.atTop (nhds 0) := by
    have ht := Q.tendsto_div_exp_atTop.neg
    simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm, neg_zero] using ht
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (1 : ℝ))
    (fun x hx => hderiv x)
    (fun x hx => mul_nonneg (Real.exp_pos _).le (hnonneg x hx)) hlim
  simpa only [zero_sub, neg_neg, hQone] using he

private lemma Ch_integral (h : ℕ) :
    Ch h = 1 + ∫ x in Set.Ioi (1 : ℝ), Real.exp (-x) * (chebP h).derivative.eval x := by
  rw [exponential_derivative_integral (chebP h) h (chebP_degree h)]
  · rfl
  · intro x hx
    simpa only [Function.iterate_one] using chebP_derivative_nonneg h 1 x hx.le

private lemma exponential_polynomial_integrable (P : Polynomial ℝ) :
    IntegrableOn (fun x => Real.exp (-x) * P.eval x) (Set.Ioi (0 : ℝ)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : (fun x => Real.exp (-x) * (P + Q).eval x) =
        (fun x => Real.exp (-x) * P.eval x) + (fun x => Real.exp (-x) * Q.eval x) := by
      funext x
      simp only [Polynomial.eval_add, Pi.add_apply, mul_add]
    rw [he]
    exact hP.add hQ
  | monomial n c =>
    have hi := (Real.GammaIntegral_convergent (by positivity : 0 < (n : ℝ) + 1)).const_mul c
    have he : (fun x => Real.exp (-x) * (Polynomial.monomial n c).eval x) =
        fun x => c * (Real.exp (-x) * x ^ ((n : ℝ) + 1 - 1)) := by
      funext x
      simp only [Polynomial.eval_monomial, add_sub_cancel_right, Real.rpow_natCast]
      ring
    rw [he]
    exact hi

private lemma chebP_growth (h : ℕ) (hh : 1 ≤ h) (x : ℝ) (hx : 1 ≤ x) :
    x ≤ (chebP h).eval x := by
  have hy : 1 ≤ 2 * x - 1 := by linarith
  have hu : 0 ≤ Real.arcosh (2 * x - 1) := Real.arcosh_nonneg hy
  have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  have hcosh : Real.cosh (Real.arcosh (2 * x - 1)) ≤
      Real.cosh ((h : ℝ) * Real.arcosh (2 * x - 1)) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hu, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)]
    nlinarith
  rw [Real.cosh_arcosh hy] at hcosh
  have he : (chebP h).eval x = Real.cosh ((h : ℝ) * Real.arcosh (2 * x - 1)) := by
    simp only [chebP, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
    calc
      _ = (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval (Real.cosh (Real.arcosh (2 * x - 1))) := by
        rw [Real.cosh_arcosh hy]
      _ = _ := by
        simpa only [Int.cast_natCast] using
          Polynomial.Chebyshev.T_real_cosh (Real.arcosh (2 * x - 1)) (h : ℤ)
  rw [he]
  linarith

private lemma Ch_pos (h : ℕ) : 0 < Ch h := by
  have hs : 0 ≤ ∑ m ∈ Finset.Icc 1 h, (Polynomial.derivative^[m] (chebP h)).eval 1 :=
    Finset.sum_nonneg fun m hm => chebP_derivative_nonneg h m 1 le_rfl
  unfold Ch
  positivity

private lemma chebP_pos (h : ℕ) (ell : ℝ) (hell : 1 ≤ ell) : 0 < (chebP h).eval ell := by
  have he : (chebP h).eval ell = (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval (2 * ell - 1) := by
    simp only [chebP, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  rw [he]
  exact lt_of_lt_of_le zero_lt_one
    (Polynomial.Chebyshev.one_le_eval_T_real _ (by linarith))

private lemma fradelizi_mean_bound (hFr : FradeliziGauss) {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (h : ℕ) (hh : 1 ≤ h) (hdeg : P.totalDegree ≤ h)
    (hnonneg : ∀ z, 0 ≤ MvPolynomial.eval z P)
    (hnull : ∀ a, stdGauss ι {z | MvPolynomial.eval z P = a} = 0)
    (hpos : 0 < ∫ z, MvPolynomial.eval z P ∂stdGauss ι)
    (M : ℝ) (hM : 0 < M)
    (hquant : (stdGauss ι {z | M ≤ MvPolynomial.eval z P}).toReal = Real.exp (-1)) :
    (∫ z, MvPolynomial.eval z P ∂stdGauss ι) ≤ Ch h * M := by
  let g (t : ℝ) := (stdGauss ι {z | t ≤ MvPolynomial.eval z P}).toReal
  let F (x : ℝ) := M * (chebP h).eval x
  let F' (x : ℝ) := M * (chebP h).derivative.eval x
  have hgcont : Continuous g := continuous_tail _ _ P.continuous_eval.measurable hnull
  have hg0 (t : ℝ) : 0 ≤ g t := ENNReal.toReal_nonneg
  have hg1 (t : ℝ) : g t ≤ 1 :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr prob_le_one
  have hi := gaussian_polynomial_integrable P
  have hlayer : (∫ z, MvPolynomial.eval z P ∂stdGauss ι) = ∫ t in Set.Ioi (0 : ℝ), g t :=
    hi.integral_eq_integral_meas_le (Filter.Eventually.of_forall hnonneg)
  have hgi : IntegrableOn g (Set.Ioi (0 : ℝ)) :=
    Integrable.of_integral_ne_zero (by rw [← hlayer]; exact hpos.ne')
  have hFcont : Continuous F := continuous_const.mul (chebP h).continuous
  have hFderiv (x : ℝ) : HasDerivAt F (F' x) x := (chebP h).hasDerivAt x |>.const_mul M
  have hF'0 (x : ℝ) (hx : 1 ≤ x) : 0 ≤ F' x := by
    apply mul_nonneg hM.le
    simpa only [Function.iterate_one] using chebP_derivative_nonneg h 1 x hx
  have hF0 (x : ℝ) (hx : 1 ≤ x) : 0 < F x := mul_pos hM (chebP_pos h x hx)
  have hFtop : Filter.Tendsto F Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ (Filter.Tendsto.const_mul_atTop hM Filter.tendsto_id)
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left (chebP_growth h hh x hx) hM.le
  have hFone : F 1 = M := by
    simp only [F, chebP, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
    norm_num only [show (2 * (1 : ℝ) - 1) = 1 by norm_num,
      Polynomial.Chebyshev.T_eval_one, mul_one]
  have htail (x : ℝ) (hx : 1 < x) : g (F x) ≤ Real.exp (-x) := by
    have ht := fradelizi_chebP hFr P h hdeg x M hx hM
    simp_rw [abs_of_nonneg (hnonneg _)] at ht
    rw [hquant, ← Real.exp_mul] at ht
    simpa only [neg_one_mul] using ht
  have hexi : IntegrableOn (fun x => Real.exp (-x) * (chebP h).derivative.eval x)
      (Set.Ioi (1 : ℝ)) :=
    (exponential_polynomial_integrable (chebP h).derivative).mono_set
      (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hupperi : IntegrableOn (fun x => Real.exp (-x) * F' x) (Set.Ioi (1 : ℝ)) := by
    have he : (fun x => Real.exp (-x) * F' x) =
        fun x => M * (Real.exp (-x) * (chebP h).derivative.eval x) := by
      funext x
      dsimp [F']
      ring
    rw [he]
    exact hexi.const_mul M
  have hti : IntegrableOn (fun x => g (F x) * F' x) (Set.Ioi (1 : ℝ)) := by
    apply hupperi.mono' ((hgcont.comp hFcont).mul
      (continuous_const.mul (chebP h).derivative.continuous)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change |g (F x) * F' x| ≤ Real.exp (-x) * F' x
    rw [abs_of_nonneg (mul_nonneg (hg0 _) (hF'0 x hx.le))]
    exact mul_le_mul_of_nonneg_right (htail x hx) (hF'0 x hx.le)
  have hchange := integral_comp_mul_deriv_Ioi (a := (1 : ℝ)) hFcont.continuousOn hFtop
    (fun x hx => (hFderiv x).hasDerivWithinAt) hgcont.continuousOn
    (hgi.mono_set (by
      rintro t ⟨x, hx, rfl⟩
      exact hF0 x hx))
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hti)
  change (∫ x in Set.Ioi (1 : ℝ), g (F x) * F' x) = ∫ t in Set.Ioi (F 1), g t at hchange
  rw [hFone] at hchange
  have htailint : (∫ t in Set.Ioi M, g t) ≤ M * (Ch h - 1) := by
    rw [← hchange]
    have hb := integral_mono_ae hti hupperi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_le_mul_of_nonneg_right (htail x hx) (hF'0 x hx.le))
    have he : (∫ x in Set.Ioi (1 : ℝ), Real.exp (-x) * F' x) = M * (Ch h - 1) := by
      have hf : (fun x => Real.exp (-x) * F' x) =
          fun x => M * (Real.exp (-x) * (chebP h).derivative.eval x) := by
        funext x
        dsimp [F']
        ring
      rw [hf, integral_const_mul, Ch_integral]
      ring
    exact he ▸ hb
  have hhead : (∫ t in Set.Ioc 0 M, g t) ≤ M := by
    have hb := integral_mono (hgi.mono_set Set.Ioc_subset_Ioi_self)
      (integrableOn_const (by simp : volume (Set.Ioc (0 : ℝ) M) ≠ ∞)) (hg1)
    simpa only [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal hM.le, sub_zero, smul_eq_mul, mul_one] using hb
  rw [hlayer, ← Set.Ioc_union_Ioi_eq_Ioi hM.le,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hgi.mono_set Set.Ioc_subset_Ioi_self)
      (hgi.mono_set (Set.Ioi_subset_Ioi hM.le))]
  nlinarith

private lemma smallball_of_mean_bound (hFr : FradeliziGauss) {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (k : ℕ) (hdeg : P.totalDegree ≤ 2 * k)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 - Real.exp (-1))
    (M : ℝ) (hM0 : 0 < M)
    (hquant : (stdGauss ι {z | M ≤ MvPolynomial.eval z P}).toReal = Real.exp (-1))
    (hnonneg : ∀ z, 0 ≤ MvPolynomial.eval z P) (hC : 0 < Ch (2 * k))
    (hmean : (∫ z, MvPolynomial.eval z P ∂stdGauss ι) ≤ Ch (2 * k) * M) :
    stdGauss ι {z | MvPolynomial.eval z P <
      tsb k p * ∫ z', MvPolynomial.eval z' P ∂stdGauss ι} ≤ ENNReal.ofReal p := by
  let A := (chebP (2 * k)).eval (lamP p)
  have hA : 0 < A := chebP_pos _ _ (lamP_gt_one p hp0 hp1).le
  have hc : 0 < M / A := div_pos hM0 hA
  have hscale : M / A * A = M := div_mul_cancel₀ M hA.ne'
  have hquant' : Real.exp (-1) ≤
      (stdGauss ι {z | M / A * (chebP (2 * k)).eval (lamP p) ≤
        |MvPolynomial.eval z P|}).toReal := by
    change Real.exp (-1) ≤ (stdGauss ι {z | M / A * A ≤ |MvPolynomial.eval z P|}).toReal
    simp_rw [hscale, abs_of_nonneg (hnonneg _)]
    exact hquant.ge
  have htail := quantile_tail_lower hFr P (2 * k) hdeg p (M / A) hp0 hp1 hc hquant'
  simp_rw [abs_of_nonneg (hnonneg _)] at htail
  have hthreshold : tsb k p * (∫ z, MvPolynomial.eval z P ∂stdGauss ι) ≤ M / A := by
    change 1 / (Ch (2 * k) * A) * (∫ z, MvPolynomial.eval z P ∂stdGauss ι) ≤ M / A
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (mul_pos hC hA)).mpr
    have he : M / A * (Ch (2 * k) * A) = Ch (2 * k) * M := by
      field_simp
      <;> ring
    rw [he]
    exact hmean
  apply (measure_mono (show {z | MvPolynomial.eval z P <
      tsb k p * ∫ z', MvPolynomial.eval z' P ∂stdGauss ι} ⊆
        {z | MvPolynomial.eval z P < M / A} from fun z hz => lt_of_lt_of_le hz hthreshold)).trans
  have he : {z | MvPolynomial.eval z P < M / A} = {z | M / A ≤ MvPolynomial.eval z P}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [he]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp0.le, ← measureReal_def,
    probReal_compl_eq_one_sub (measurableSet_le measurable_const P.continuous_eval.measurable)]
  change 1 - (stdGauss ι {z | M / A ≤ MvPolynomial.eval z P}).toReal ≤ p
  linarith

/-- **Lemma SB**: `Pr_Z{Var_μ 𝒫(Z) < t_sb E_Z Var_μ 𝒫} ≤ p_sb`, from Fradelizi's Corollary 4. -/
theorem smallball43 (hFr : FradeliziGauss) (hn : 1 ≤ n) (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)}
    (hμ : SphLaw n μ) (k : ℕ) (hk : 1 ≤ k) (T : Tens n) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 - Real.exp (-1)) :
    stdGauss (CoefIdxD n d) {Z | varU μ (Pcal k T Z) <
      tsb k p * ∫ Z', varU μ (Pcal k T Z') ∂stdGauss (CoefIdxD n d)} ≤ ENNReal.ofReal p := by
  by_cases hz : (∫ Z, varU μ (Pcal (d := d) k T Z) ∂stdGauss (CoefIdxD n d)) = 0
  · exact smallball_zero_mean μ k T p hz
  · have hmean : 0 < ∫ Z, varU μ (Pcal (d := d) k T Z) ∂stdGauss (CoefIdxD n d) :=
      lt_of_le_of_ne (variance_mean_nonneg μ k T) (Ne.symm hz)
    obtain ⟨P, hP, hdeg⟩ := variance_polynomial (d := d) hμ k T
    have hfun : (fun Z => varU μ (Pcal (d := d) k T Z)) =
        fun Z => MvPolynomial.eval Z P := funext hP
    have hi : Integrable (fun Z => varU μ (Pcal (d := d) k T Z))
        (stdGauss (CoefIdxD n d)) := by
      rw [hfun]
      exact gaussian_polynomial_integrable P
    have hP0 : MvPolynomial.eval (fun _ => 0) P = 0 := by
      rw [← hP, variance_at_zero]
    have hPpos : 0 < ∫ Z, MvPolynomial.eval Z P ∂stdGauss (CoefIdxD n d) := by
      simpa only [hfun] using hmean
    have hnotconst : ∀ a : ℝ, ∃ Z, MvPolynomial.eval Z P ≠ a := by
      intro a
      by_contra hcon
      push_neg at hcon
      have ha : a = 0 := by rw [← hcon (fun _ => 0), hP0]
      have he : (fun Z => MvPolynomial.eval Z P) = fun _ => (0 : ℝ) := by
        funext Z
        rw [hcon Z, ha]
      rw [he, integral_zero] at hPpos
      exact lt_irrefl 0 hPpos
    have hnull := fradelizi_null_fiber hFr P (2 * k) hdeg hnotconst
    have hnonneg (Z : CoefIdxD n d → ℝ) : 0 ≤ MvPolynomial.eval Z P := by
      rw [← hP]
      exact variance_nonneg μ _
    obtain ⟨M, hM, hquant⟩ := positive_quantile (stdGauss (CoefIdxD n d))
      (fun Z => MvPolynomial.eval Z P) P.continuous_eval.measurable hnonneg hnull
      (Real.exp (-1)) (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by norm_num))
    have hbound := fradelizi_mean_bound hFr P (2 * k) (by omega) hdeg hnonneg hnull
      hPpos M hM hquant
    simpa only [hP] using smallball_of_mean_bound hFr P k hdeg p hp0 hp1
      M hM hquant hnonneg (Ch_pos _) hbound

end BstLean.Part43
