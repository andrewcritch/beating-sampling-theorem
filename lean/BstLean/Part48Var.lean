import BstLean.Part43Defs

/-!
# Part 48, wave 1: the variance is a polynomial in the Gaussian coefficients (proved)

Specification: `delegations/answers/p48-spec-opus.md`. The private lemmas of `Part43SmallBall`
(`map_polynomial` to `variance_polynomial`, and `gaussian_polynomial_integrable`) are copied verbatim,
because they are private there. They do not use `FradeliziGauss`.

* `var_poly`: `V(Z) = Var_μ 𝒫(Z)` is `eval Z P` for a real polynomial `P` of total degree `≤ 2k`.
* `gauss_poly_integrable`: every real polynomial is integrable under `stdGauss ι`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)
open BstLean.Part43

variable {n d : ℕ}

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

/-- **The variance is a polynomial**: `Var_μ 𝒫(Z) = eval Z P` with `deg P ≤ 2k`, for a law `μ` on the
sphere. -/
theorem var_poly {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ) (T : Tens n) :
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, varU μ (Pcal k T Z) = MvPolynomial.eval Z P) ∧ P.totalDegree ≤ 2 * k :=
  variance_polynomial hμ k T

/-- Every real polynomial is integrable under the standard Gaussian. -/
theorem gauss_poly_integrable {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z P) (stdGauss ι) :=
  gaussian_polynomial_integrable P

end BstLean.Part48
