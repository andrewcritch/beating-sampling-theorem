import BstLean.Part53Defs

/-! Polynomial representations and Gaussian integrability for the Part 53 error. -/

namespace BstLean.Part53

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part41 (Tens fval contr colM)
open BstLean.Part43 (BofQ)
open BstLean.Part40 (SphLaw)

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

private lemma gaussian_eval_integrable {ι : Type*} [Fintype ι]
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

private abbrev JointPoly (n d : ℕ) :=
  MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)

private noncomputable def jointEval (p : JointPoly n d)
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

private noncomputable def bJoint (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) : JointPoly n d :=
  MvPolynomial.C (ContinuousMap.const _ f0) +
    ∑ j ∈ Finset.Icc 1 k, ∑ w : Fin j → Fin n,
      MvPolynomial.C (ContinuousMap.const _ (T j w)) *
        ∏ t, MvPolynomial.C (ContinuousMap.const _ s) * mapJoint (w t)

private lemma bJoint_eval (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
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

private noncomputable def gPoly (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) :
    MvPolynomial (CoefIdxD n d) ℝ :=
  ∑ c ∈ Finset.range (k + 1), ∑ w : Fin c → Fin n,
    MvPolynomial.C (heatA k (aH n d) (TF k f0 T) c w) *
      ∏ t, MvPolynomial.C s * MvPolynomial.X
        ⟨(default : BstLean.Part41.Mono n d).1, ((default : BstLean.Part41.Mono n d).2, w t)⟩

private lemma gPoly_eval (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
    (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (gPoly k f0 T s) = g0 n d k f0 T (s • Z) := by
  classical
  simp [gPoly, g0, fvA, contr, colM, Pi.smul_apply, smul_eq_mul]

/-- The Gaussian squared error is integrable for every probability law on the sphere.
No symmetry, degree, density bound, or Gaussian chaos interface is needed. -/
theorem error53_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) :
    Integrable (fun Z => (BofQ μ k f0 T (s • Z) - g0 n d k f0 T (s • Z)) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
  obtain ⟨p, hp⟩ := B_polynomial (d := d) hμ k f0 T s
  convert gaussian_eval_integrable ((p - gPoly (d := d) k f0 T s) ^ 2) using 1
  funext Z
  simp only [MvPolynomial.eval_pow, map_sub, hp, gPoly_eval]

/-- Integrability under the frozen density-law hypothesis. -/
theorem error53_integrable_dens {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hμ : DensLaw n μ Λ) (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Integrable (fun Z => (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
  apply error53_integrable
  obtain ⟨hp, ρ, -, -, heq, -⟩ := hμ
  refine ⟨hp, ?_⟩
  rw [heq]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

/-- Polynomial integrands permit exchanging the Gaussian and sphere integrals. -/
theorem error53_gaussian_exchange {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)) :
    (∫ Z, ∫ x, MvPolynomial.eval₂Hom
      ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z p ∂μ
        ∂stdGauss (CoefIdxD n d)) =
    ∫ x, ∫ Z, MvPolynomial.eval₂Hom
      ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z p
        ∂stdGauss (CoefIdxD n d) ∂μ := by
  classical
  let mon (e : CoefIdxD n d →₀ ℕ) (Z : CoefIdxD n d → ℝ) : ℝ :=
    e.prod (fun i a => Z i ^ a)
  have hmon (e : CoefIdxD n d →₀ ℕ) : Integrable (mon e) (stdGauss (CoefIdxD n d)) := by
    simpa [mon, MvPolynomial.eval_monomial] using
      gaussian_eval_integrable (MvPolynomial.monomial e (1 : ℝ))
  have hexp (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
      jointEval p Z x = ∑ e ∈ p.support, p.coeff e x * mon e Z := by
    conv_lhs => unfold jointEval; rw [p.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply, mon]
  have hinnerμ (Z : CoefIdxD n d → ℝ) :
      (∫ x, jointEval p Z x ∂μ) =
        ∑ e ∈ p.support, (∫ x, p.coeff e x ∂μ) * mon e Z := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun e _ =>
      (sphere_cont_integrable hμ (p.coeff e).continuous).mul_const _)]
    simp only [integral_mul_const]
  have hinnerG (x : Fin n → ℝ) :
      (∫ Z, jointEval p Z x ∂stdGauss (CoefIdxD n d)) =
        ∑ e ∈ p.support, p.coeff e x * ∫ Z, mon e Z ∂stdGauss (CoefIdxD n d) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun e _ => (hmon e).const_mul _)]
    simp only [integral_const_mul]
  change (∫ Z, ∫ x, jointEval p Z x ∂μ ∂stdGauss (CoefIdxD n d)) =
    ∫ x, ∫ Z, jointEval p Z x ∂stdGauss (CoefIdxD n d) ∂μ
  simp_rw [hinnerμ, hinnerG]
  rw [integral_finsetSum _ (fun e _ => (hmon e).const_mul _),
    integral_finsetSum _ (fun e _ =>
      (sphere_cont_integrable hμ (p.coeff e).continuous).mul_const _)]
  simp only [integral_const_mul, integral_mul_const]

end BstLean.Part53
