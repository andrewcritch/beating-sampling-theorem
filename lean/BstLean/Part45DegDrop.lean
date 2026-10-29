import BstLean.Part45Defs

/-!
# Part 45, wave 1: polynomiality of `V`, and Lemma H(i) (degree drop in the constant column)

Specification: `delegations/answers/p45-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the
statements. Do not use `native_decide` or `axiom` anywhere. This file imports `Part45Defs` only (a
prover may also import finished Part 29–44 files, but no other Part 45 wave-1 file).

Suggested route.
* `var_poly45` is Part 43's private `variance_polynomial` (in `Part43SmallBall.lean`); copy it.
* `degdrop45` (omSHARP §3, Lemma H(i)): `𝒫(joinZ c Z)(x) = F(c + w(x))`, `w(x) = Zφ(x) − (constant
  column)`. In `T_j[(c + w)^{⊗j}]` the only monomials of degree `j` in `c` are `T_j[c^{⊗j}]`, constant in
  `x`; for `j < k` the degree is `< k` anyway. So `𝒫 − E_μ 𝒫` is a polynomial in `c` of degree `≤ k − 1`
  with coefficients polynomial in `x`, and `V = E_μ (𝒫 − E_μ 𝒫)²` is a polynomial of degree `≤ 2(k−1)`
  (coefficients are `μ`-integrals of polynomials, finite because `μ` lives on the sphere).
  No symmetry of `T` is needed.
-/

namespace BstLean.Part45

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι)
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiSq frob Tens TSymm varU Pcal Nn Kc thetaT etaR etaK GamP Lk Bfix Pn)
open BstLean.Part40 (SphLaw SignSym)
open BstLean.Part43 (Params43 bq tau43 xi43 nu43 FradeliziGauss)

open BstLean.Part41 (uJ contr)

variable {n d : ℕ}

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
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul]
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



variable {ι : Type*}

private abbrev GeneralJoint (n : ℕ) (ι : Type*) :=
  MvPolynomial (ι) C((Fin n → ℝ), ℝ)

private noncomputable def generalEval (P : GeneralJoint n ι)
    (Z : ι → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z P

private lemma general_integral {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (P : GeneralJoint n ι) :
    ∃ Q : MvPolynomial (ι) ℝ,
      (∀ Z, (∫ x, generalEval P Z x ∂μ) = MvPolynomial.eval Z Q) ∧
      Q.totalDegree ≤ P.totalDegree := by
  classical
  refine ⟨∑ e ∈ P.support, MvPolynomial.monomial e (∫ x, P.coeff e x ∂μ), ?_, ?_⟩
  · intro Z
    have hE (x) : generalEval P Z x =
        ∑ e ∈ P.support, P.coeff e x * e.prod (fun i a => Z i ^ a) := by
      conv_lhs => unfold generalEval; rw [P.as_sum]
      simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
        Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
    simp_rw [hE]
    rw [integral_finsetSum _ (fun e _ =>
      (sphere_cont_integrable hμ (P.coeff e).continuous).mul_const _)]
    simp only [integral_mul_const, map_sum, MvPolynomial.eval_monomial]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro e he
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)

private lemma general_continuous (P : GeneralJoint n ι) (Z : ι → ℝ) :
    Continuous (generalEval P Z) := by
  classical
  have he : generalEval P Z = fun x =>
      ∑ e ∈ P.support, P.coeff e x * e.prod (fun i a => Z i ^ a) := by
    funext x
    conv_lhs => unfold generalEval; rw [P.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  rw [he]
  exact continuous_finsetSum _ fun e he => (P.coeff e).continuous.mul continuous_const

private lemma general_variance {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (P : GeneralJoint n ι) (r : ℕ) (hd : P.totalDegree ≤ r) :
    ∃ Q : MvPolynomial ι ℝ, Q.totalDegree ≤ 2 * r ∧
      ∀ z, MvPolynomial.eval z Q = varU μ (generalEval P z) := by
  classical
  obtain ⟨Q, hQ, hQd⟩ := general_integral hμ P
  obtain ⟨R, hR, hRd⟩ := general_integral hμ (P ^ 2)
  refine ⟨R + MvPolynomial.C (-1) * Q ^ 2, ?_, ?_⟩
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact hRd.trans ((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hd))
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hQd.trans hd))
  · intro z
    rw [variance_expansion hμ _ (sphere_cont_integrable hμ (general_continuous P z))
      (sphere_cont_integrable hμ ((general_continuous P z).pow 2))]
    have hr := hR z
    simp only [generalEval, map_pow] at hr
    change (∫ x, generalEval P z x ^ 2 ∂μ) = _ at hr
    rw [hQ z, hr]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_pow]
    ring

private lemma prod_drop {κ : Type*} [DecidableEq κ] {R : Type*} [CommRing R]
    (s : Finset κ) (a : κ → MvPolynomial ι R) (b : κ → R)
    (ha : ∀ t ∈ s, (a t).totalDegree ≤ 1) :
    ((∏ t ∈ s, (a t + MvPolynomial.C (b t))) - ∏ t ∈ s, a t).totalDegree ≤
      s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    have hs : ∀ u ∈ s, (a u).totalDegree ≤ 1 := fun u hu => ha u (Finset.mem_insert_of_mem hu)
    have hat := ha t (Finset.mem_insert_self t s)
    by_cases he : s = ∅
    · subst s
      simp [MvPolynomial.totalDegree_C]
    · have hc : 1 ≤ s.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      rw [Finset.prod_insert ht, Finset.prod_insert ht, Finset.card_insert_of_notMem ht]
      have hident : (a t + MvPolynomial.C (b t)) * (∏ u ∈ s, (a u + MvPolynomial.C (b u))) -
          a t * (∏ u ∈ s, a u) =
          (a t + MvPolynomial.C (b t)) *
            ((∏ u ∈ s, (a u + MvPolynomial.C (b u))) - ∏ u ∈ s, a u) +
          MvPolynomial.C (b t) * (∏ u ∈ s, a u) := by ring
      rw [hident]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        have htdeg : (a t + MvPolynomial.C (b t)).totalDegree ≤ 1 :=
          (MvPolynomial.totalDegree_add _ _).trans (max_le hat (by simp))
        have hi := ih hs
        omega
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        simp only [MvPolynomial.totalDegree_C, zero_add]
        apply (MvPolynomial.totalDegree_finsetProd _ _).trans
        have hh : ∑ u ∈ s, (a u).totalDegree ≤ ∑ _u ∈ s, 1 :=
          Finset.sum_le_sum hs
        simpa using hh

/-- `V(Z) = Var_μ 𝒫(Z)` is a polynomial of degree `≤ 2k` in `Z` (Part 43's private
`variance_polynomial`). -/
theorem var_poly45 {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ) (T : Tens n) :
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ, P.totalDegree ≤ 2 * k ∧
      ∀ Z, MvPolynomial.eval Z P = varU μ (Pcal k T Z) := by
  obtain ⟨P, hP, hd⟩ := variance_polynomial (d := d) hμ k T
  exact ⟨P, hd, fun Z => (hP Z).symm⟩

private lemma map_join (c : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ)
    (a : Fin n) : mapMD (joinZ c Z) x a = c a + mapMD (joinZ (fun _ => 0) Z) x a := by
  classical
  unfold mapMD
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hzero (v : Fin n → ℝ) :
      (∑ β : Sym (Fin n) 0, BstLean.Part36.coefD (joinZ v Z) 0 β a *
        BstLean.Part36.monoVal x β.1) = v a := by
    have hb (β : Sym (Fin n) 0) : β.1 = 0 := Multiset.card_eq_zero.mp β.2
    simp only [Fintype.sum_unique]
    rw [hb]
    simp [BstLean.Part36.coefD, joinZ, BstLean.Part36.monoVal]
  rw [hzero, hzero, add_zero]
  rw [add_comm _ (c a)]
  congr 1

private noncomputable def residualJoint (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    GeneralJoint n (Fin n) :=
  ∑ j ∈ Finset.Icc 1 k, (∑ w : Fin j → Fin n,
    MvPolynomial.C (ContinuousMap.const _ (T j w)) *
      ((∏ t, (MvPolynomial.X (w t) + MvPolynomial.C
        ⟨fun x => mapMD (joinZ (fun _ => 0) Z) x (w t), by
          have hh := jointEval_continuous (mapJoint (d := d) (w t)) (joinZ (fun _ => 0) Z)
          rw [show jointEval (mapJoint (d := d) (w t)) (joinZ (fun _ => 0) Z) =
            (fun x => mapMD (joinZ (fun _ => 0) Z) x (w t)) from
            funext (mapJoint_eval (w t) (joinZ (fun _ => 0) Z))] at hh
          exact hh⟩)) - ∏ t, MvPolynomial.X (w t))) *
      MvPolynomial.C (ContinuousMap.const _ ((Real.sqrt (DD n d) ^ j)⁻¹))

private noncomputable def pureColumn (k : ℕ) (T : Tens n) (c : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, (∑ w : Fin j → Fin n, T j w * ∏ t, c (w t)) /
    Real.sqrt (DD n d) ^ j

private lemma residual_eval (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) :
    generalEval (residualJoint k T Z) c x = Pcal k T (joinZ c Z) x - pureColumn (d := d) k T c := by
  classical
  simp only [residualJoint, generalEval, map_sum, map_mul, map_sub, map_prod, map_add,
    MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
    Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  simp only [ContinuousMap.const_apply, ContinuousMap.coe_mk]
  unfold Pcal pureColumn uJ contr
  simp_rw [map_join c Z, div_eq_mul_inv]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

private lemma residual_degree (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    (residualJoint k T Z).totalDegree ≤ k - 1 := by
  classical
  unfold residualJoint
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, add_zero]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro w hw
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (prod_drop Finset.univ (fun t : Fin j => MvPolynomial.X (w t)) _
    (by intros; simp)).trans
  simp only [Finset.card_univ, Fintype.card_fin]
  have := (Finset.mem_Icc.mp hj).2
  omega

/-- **Lemma H(i)**: with the non-constant columns of `Z` fixed, `c ↦ V(joinZ c Z)` is a polynomial
of degree `≤ 2(k − 1)` in the constant column `c`. -/
theorem degdrop45 {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ) (T : Tens n)
    (Z : CoefIdxD n d → ℝ) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 2 * (k - 1) ∧
      ∀ c, MvPolynomial.eval c P = varU μ (Pcal k T (joinZ c Z)) := by
  classical
  let := hμ.prob
  obtain ⟨P, hd, hP⟩ := general_variance hμ (residualJoint k T Z) (k - 1)
    (residual_degree k T Z)
  refine ⟨P, hd, fun c => ?_⟩
  rw [hP c]
  have hf : Continuous (Pcal k T (joinZ c Z)) := by
    have hh := jointEval_continuous (pJoint (d := d) k T) (joinZ c Z)
    rw [show jointEval (pJoint (d := d) k T) (joinZ c Z) = Pcal k T (joinZ c Z) from
      funext (pJoint_eval k T (joinZ c Z))] at hh
    exact hh
  have hm : (∫ x, generalEval (residualJoint k T Z) c x ∂μ) =
      (∫ x, Pcal k T (joinZ c Z) x ∂μ) - pureColumn (d := d) k T c := by
    simp_rw [residual_eval]
    rw [integral_sub (sphere_cont_integrable hμ hf) (integrable_const _)]
    simp
  unfold varU
  rw [hm]
  simp_rw [residual_eval]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  ring

end BstLean.Part45
