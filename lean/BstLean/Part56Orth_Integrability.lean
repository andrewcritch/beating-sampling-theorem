import BstLean.Part56Defs
import BstLean.Part53Floor_Energy
import BstLean.Part53Wick

namespace BstLean.Part56.Orth

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part41 (Mono Tens fval contr colM)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part40 (SphLaw)
open BstLean.Part53 (sg TF fvA heatA linZ)

variable {n d : ℕ}

private lemma sphere_cont_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
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

lemma gaussian_eval_integrable {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _

abbrev JointPoly (n d : ℕ) :=
  MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)

noncomputable def jointEval (p : JointPoly n d)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z p

private lemma joint_integral_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (p : JointPoly n d) :
    ∃ q : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z,
      (∫ x, jointEval p Z x ∂μ) = MvPolynomial.eval Z q := by
  classical
  refine ⟨∑ e ∈ p.support, MvPolynomial.monomial e
    (∫ x, p.coeff e x ∂μ), ?_⟩
  intro Z
  have hE (x) : jointEval p Z x =
      ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a) := by
    conv_lhs => unfold jointEval; rw [p.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  simp_rw [hE]
  rw [integral_finsetSum _ (fun e _ =>
    (sphere_cont_integrable hμ (p.coeff e).continuous).mul_const _)]
  simp only [integral_mul_const, map_sum, MvPolynomial.eval_monomial]

private lemma continuous_mono (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) := by
  exact continuous_multiset_prod s (fun i _ => continuous_apply i)

private noncomputable def mapJoint (a : Fin n) : JointPoly n d :=
  ∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then MvPolynomial.X ⟨⟨i, h⟩, (β, a)⟩ else 0) *
      MvPolynomial.C ⟨fun x => BstLean.Part36.monoVal x β.1, continuous_mono β.1⟩

private lemma mapJoint_eval (a : Fin n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (mapJoint a) Z x = BstLean.Part36.mapMD Z x a := by
  classical
  unfold mapJoint jointEval BstLean.Part36.mapMD BstLean.Part36.coefD
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i < d + 1 := Finset.mem_range.mp hi
  simp [h]

noncomputable def bJoint (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) : JointPoly n d :=
  MvPolynomial.C (ContinuousMap.const _ f0) +
    ∑ j ∈ Finset.Icc 1 k, ∑ w : Fin j → Fin n,
      MvPolynomial.C (ContinuousMap.const _ (T j w)) *
        ∏ t, MvPolynomial.C (ContinuousMap.const _ s) * mapJoint (w t)

lemma bJoint_eval (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (bJoint k f0 T s) Z x = fval k f0 T (mapMD (s • Z) x) := by
  classical
  have hscale : ∀ a, mapMD (s • Z) x a = s * mapMD Z x a := by
    intro a
    unfold mapMD BstLean.Part36.coefD
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring
  simp only [bJoint, jointEval, map_add, map_sum, map_mul, map_prod,
    MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Pi.evalRingHom_apply,
    ContinuousMap.coeFnRingHom_apply, ContinuousMap.const_apply]
  have hm (a : Fin n) :
      MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z
        (mapJoint a) = mapMD Z x a := mapJoint_eval a Z x
  simp [fval, contr, hscale, hm]

private lemma B_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ,
      ∀ Z, BofQ μ k f0 T (s • Z) = MvPolynomial.eval Z p := by
  obtain ⟨p, hp⟩ := joint_integral_polynomial hμ (bJoint (d := d) k f0 T s)
  refine ⟨p, ?_⟩
  intro Z
  rw [BofQ, ← hp]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (bJoint_eval k f0 T s Z x).symm)

private lemma gaussian_poly_memLp (p : MvPolynomial (CoefIdxD n d) ℝ) :
    MemLp (fun Z => MvPolynomial.eval Z p) 2 (stdGauss (CoefIdxD n d)) := by
  apply (memLp_two_iff_integrable_sq p.continuous_eval.aestronglyMeasurable).2
  convert gaussian_eval_integrable (p ^ 2) using 1
  funext Z
  exact (MvPolynomial.eval_pow (f := Z) (p := p) 2).symm

/-- The first integrability assertion in the orthogonality interface. -/
theorem B_memLp {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) :
    MemLp (fun Z : CoefIdxD n d → ℝ => BofQ μ k f0 T (s • Z)) 2
      (stdGauss (CoefIdxD n d)) := by
  obtain ⟨p, hp⟩ := B_polynomial (d := d) hμ k f0 T s
  simpa only [← hp] using gaussian_poly_memLp p

/-- The variance integrability assertion in the orthogonality interface. -/
theorem variance_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : BstLean.Part41.TSymm k T) (s : ℝ) :
    Integrable (fun Z : CoefIdxD n d → ℝ => varFQ μ k f0 T (s • Z))
      (stdGauss (CoefIdxD n d)) := by
  exact (BstLean.Part53.FloorEnergy.varFQ_energy53 k s f0 T hT
    (BstLean.Part53.lemmaW53 k) hμ).1

private lemma phiB_cont (d j : ℕ) (p : Mono n d) :
    Continuous (fun x : Fin n → ℝ => phiB d j x p) := by
  unfold phiB
  split_ifs
  · exact continuous_mono p.2.1
  · exact continuous_const

private lemma kJ_cont_left (d j : ℕ) (v : Fin n → ℝ) :
    Continuous (fun x => kJ d j x v) := by
  unfold kJ
  exact continuous_finsetSum _ (fun p _ => (phiB_cont d j p).mul continuous_const)

private lemma kJ_cont_diag (d j : ℕ) : Continuous (fun x : Fin n → ℝ => kJ d j x x) := by
  unfold kJ
  exact continuous_finsetSum _ (fun p _ => (phiB_cont d j p).mul (phiB_cont d j p))

private lemma betaJ_cont (d j : ℕ) (v : Fin n → ℝ) : Continuous (betaJ d j v) :=
  (kJ_cont_left d j v).div_const _

private lemma tauR_cont (d : ℕ) (v : Fin n → ℝ) : Continuous (tauR d v) := by
  unfold tauR KR
  exact continuous_finsetSum _ (fun j _ => (kJ_cont_diag d j).sub
    (((kJ_cont_left d j v).mul (kJ_cont_left d j v)).div_const _))

private lemma heat_cont (k c : ℕ) (A : Tens n) (s : ℝ) (v : Fin n → ℝ)
    (w : Fin c → Fin n) :
    Continuous (fun x => heatA k (s ^ 2 * tauR d v x) A c w) := by
  unfold heatA
  apply continuous_finsetSum
  intro i hi
  exact (((((continuous_const.mul (tauR_cont d v)).div_const 2).pow i).div_const _).mul
    continuous_const).mul continuous_const

private noncomputable def anchorJoint (v : Fin n → ℝ) (s : ℝ) (j : ℕ) (a : Fin n) :
    JointPoly n d :=
  ∑ p : Mono n d, MvPolynomial.C (ContinuousMap.const _ (s * phiB d j v p)) *
    MvPolynomial.X ⟨p.1, (p.2, a)⟩

private lemma anchorJoint_eval (v : Fin n → ℝ) (s : ℝ) (j : ℕ) (a : Fin n)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (anchorJoint v s j a) Z x = ancRK (s • Z) v j a := by
  classical
  simp only [anchorJoint, jointEval, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', RingHom.comp_apply, Pi.evalRingHom_apply,
    ContinuousMap.coeFnRingHom_apply, ContinuousMap.const_apply,
    ancRK, linZ, colM, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private noncomputable def meanJoint (v : Fin n → ℝ) (s : ℝ) (a : Fin n) : JointPoly n d :=
  ∑ j ∈ Finset.range (d + 1),
    MvPolynomial.C ⟨betaJ d j v, betaJ_cont d j v⟩ * anchorJoint v s j a

private lemma meanJoint_eval (v : Fin n → ℝ) (s : ℝ) (a : Fin n)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (meanJoint v s a) Z x = mux (s • Z) v x a := by
  classical
  simp only [meanJoint, jointEval, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply,
    mux, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom)
    Z (anchorJoint v s j a) = ancRK (s • Z) v j a from anchorJoint_eval v s j a Z x]
  rfl

private noncomputable def heatJoint (k : ℕ) (A : Tens n) (s : ℝ) (v : Fin n → ℝ) :
    JointPoly n d :=
  ∑ c ∈ Finset.range (k + 1), ∑ w : Fin c → Fin n,
    MvPolynomial.C ⟨fun x => heatA k (s ^ 2 * tauR d v x) A c w,
      heat_cont k c A s v w⟩ * ∏ t, meanJoint v s (w t)

private lemma heatJoint_eval (k : ℕ) (A : Tens n) (s : ℝ) (v : Fin n → ℝ)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (heatJoint k A s v) Z x =
      fvA k (heatA k (s ^ 2 * tauR d v x) A) (mux (s • Z) v x) := by
  classical
  simp only [heatJoint, jointEval, map_sum, map_mul, map_prod, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply, fvA, contr]
  simp only [show ∀ a : Fin n, MvPolynomial.eval₂Hom
    ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z (meanJoint v s a) =
      mux (s • Z) v x a from fun a => meanJoint_eval v s a Z x]
  rfl

/-- The heat predictor is a polynomial in the Gaussian coefficients. -/
theorem heat_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z,
      gLineH μ k f0 T v (sg n d • Z) = MvPolynomial.eval Z p := by
  obtain ⟨p, hp⟩ := joint_integral_polynomial hμ
    (heatJoint k (TF k f0 T) (sg n d) v)
  refine ⟨p, fun Z => ?_⟩
  rw [← hp]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => (heatJoint_eval k (TF k f0 T) (sg n d) v Z x).symm)

/-- The second integrability assertion in the orthogonality interface. -/
theorem heat_memLp {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) :
    MemLp (fun Z : CoefIdxD n d → ℝ => gLineH μ k f0 T v (sg n d • Z)) 2
      (stdGauss (CoefIdxD n d)) := by
  obtain ⟨p, hp⟩ := heat_polynomial (d := d) hμ k f0 T v
  simpa only [← hp] using gaussian_poly_memLp p

theorem joint_mean_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : JointPoly n d) : Integrable (fun Z => ∫ x, jointEval p Z x ∂μ)
      (stdGauss (CoefIdxD n d)) := by
  obtain ⟨q, hq⟩ := joint_integral_polynomial hμ p
  simpa only [hq] using gaussian_eval_integrable q

end BstLean.Part56.Orth
