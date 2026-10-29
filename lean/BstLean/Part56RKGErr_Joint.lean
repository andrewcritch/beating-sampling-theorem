import BstLean.Part56RKGErr_Polynomial
import BstLean.Part56RKGErr_Cauchy
import BstLean.Part53Floor_Covariance

/-! Finite polynomial expansions justify the conditional covariance integral exchanges. -/
namespace BstLean.Part56.RKGErr

set_option autoImplicit false

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)

abbrev JointPoly (n : ℕ) (κ : Type*) := MvPolynomial κ C((Fin n → ℝ), ℝ)

noncomputable def jointEval {n : ℕ} {κ : Type*} (P : JointPoly n κ)
    (W : κ → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) W P

noncomputable def mono {κ : Type*} (e : κ →₀ ℕ) (W : κ → ℝ) : ℝ :=
  MvPolynomial.eval W (MvPolynomial.monomial e (1 : ℝ))

theorem joint_separated {n : ℕ} {κ : Type*} (P : JointPoly n κ)
    (W : κ → ℝ) (x : Fin n → ℝ) :
    jointEval P W x = ∑ e ∈ P.support, P.coeff e x * mono e W := by
  classical
  conv_lhs => unfold jointEval; rw [P.as_sum]
  simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
    Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply, mono,
    MvPolynomial.eval_monomial, one_mul]

theorem jointEval_continuous {n : ℕ} {κ : Type*} (P : JointPoly n κ) (W : κ → ℝ) :
    Continuous (jointEval P W) := by
  change Continuous (fun x => jointEval P W x)
  simp_rw [joint_separated]
  exact continuous_finsetSum _ (fun e _ => (P.coeff e).continuous.mul_const _)

theorem jointEval_memLp {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) (x : Fin n → ℝ) :
    MemLp (fun W => jointEval P W x) 2 (stdGauss κ) := by
  let E := (Pi.evalRingHom (fun _ : Fin n → ℝ => ℝ) x).comp ContinuousMap.coeFnRingHom
  have he (W : κ → ℝ) : jointEval P W x = MvPolynomial.eval W (MvPolynomial.map E P) := by
    have hh : (MvPolynomial.eval W).comp (MvPolynomial.map E) = MvPolynomial.eval₂Hom E W := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro i
        simp
    exact (congrArg (fun f => f P) hh).symm
  simpa only [← he] using polynomial_memLp (MvPolynomial.map E P)

noncomputable def jointMean {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) :
    C((Fin n → ℝ), ℝ) :=
  ∑ e ∈ P.support, P.coeff e * ContinuousMap.const _ (∫ W, mono e W ∂stdGauss κ)

theorem jointMean_eq {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) (x : Fin n → ℝ) :
    jointMean P x = ∫ W, jointEval P W x ∂stdGauss κ := by
  simp_rw [joint_separated]
  have hi (e : κ →₀ ℕ) : Integrable (mono e) (stdGauss κ) :=
    gaussian_polynomial_integrable (MvPolynomial.monomial e (1 : ℝ))
  rw [integral_finsetSum _ (fun e _ => (hi e).const_mul _)]
  simp [jointMean, integral_const_mul]

noncomputable def centeredJoint {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) :
    JointPoly n κ := P - MvPolynomial.C (jointMean P)

theorem centeredJoint_eval {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ)
    (W : κ → ℝ) (x : Fin n → ℝ) :
    jointEval (centeredJoint P) W x = jointEval P W x - ∫ V, jointEval P V x ∂stdGauss κ := by
  simp only [centeredJoint, jointEval, map_sub, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  rw [jointMean_eq]
  rfl

noncomputable def jointCross {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ)
    (x y : Fin n → ℝ) : ℝ := ∫ W, jointEval P W x * jointEval P W y ∂stdGauss κ

theorem jointCross_sum {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) (x y : Fin n → ℝ) :
    jointCross P x y = ∑ e ∈ P.support, ∑ f ∈ P.support,
      (P.coeff e x * P.coeff f y) * (∫ W, mono e W * mono f W ∂stdGauss κ) := by
  classical
  unfold jointCross
  simp_rw [joint_separated, Finset.sum_mul, Finset.mul_sum]
  have hm (e f : κ →₀ ℕ) : Integrable (fun W => mono e W * mono f W) (stdGauss κ) :=
    (polynomial_memLp (MvPolynomial.monomial e 1)).integrable_mul
      (polynomial_memLp (MvPolynomial.monomial f 1))
  have he (W : κ → ℝ) (e f : κ →₀ ℕ) :
      (P.coeff e x * mono e W) * (P.coeff f y * mono f W) =
        (P.coeff e x * P.coeff f y) * (mono e W * mono f W) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _
    (fun f _ => (hm e f).const_mul _))]
  apply Finset.sum_congr rfl
  intro e he
  rw [integral_finsetSum _ (fun f _ => (hm e f).const_mul _)]
  simp only [integral_const_mul]

theorem jointCross_continuous {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => jointCross P p.1 p.2) := by
  simp_rw [jointCross_sum]
  exact continuous_finsetSum _ (fun e _ => continuous_finsetSum _ (fun f _ =>
    (((P.coeff e).continuous.comp continuous_fst).mul
      ((P.coeff f).continuous.comp continuous_snd)).mul_const _))

theorem jointCross_integrable {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => jointCross P p.1 p.2) (μ.prod μ) := by
  let := hμ.prob
  simp_rw [jointCross_sum]
  apply integrable_finsetSum
  intro e he
  apply integrable_finsetSum
  intro f hf
  exact ((BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ (P.coeff e).continuous).mul_prod
    (BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ (P.coeff f).continuous)).mul_const _

theorem jointDiagonal_continuous {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) :
    Continuous (fun x => jointCross P x x) :=
  (jointCross_continuous P).comp (continuous_id.prodMk continuous_id)

theorem jointDiagonal_nonneg {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ) (x : Fin n → ℝ) :
    0 ≤ jointCross P x x := integral_nonneg (fun _ => mul_self_nonneg _)

elab "rkg56SeparatedMeanSquare" : term => do
  let name := ("_private.BstLean.Part53Floor_Covariance.0.BstLean.Part53.FloorEnergy.separated_mean_square".splitOn ".").foldl
    (fun n s => if let some i := s.toNat? then Lean.Name.num n i else Lean.Name.str n s)
    Lean.Name.anonymous
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

theorem joint_integrated_square {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) :
    (∫ W, (∫ x, jointEval P W x ∂μ) ^ 2 ∂stdGauss κ) =
      ∫ p : (Fin n → ℝ) × (Fin n → ℝ), jointCross P p.1 p.2 ∂μ.prod μ := by
  let := hμ.prob
  have h := rkg56SeparatedMeanSquare hμ P.support (fun e x => P.coeff e x)
    (fun e => MvPolynomial.monomial e (1 : ℝ)) (fun e _ => (P.coeff e).continuous)
  change (∫ W, (∫ x, ∑ e ∈ P.support, P.coeff e x * mono e W ∂μ) ^ 2 ∂stdGauss κ) =
    ∫ x, ∫ y, ∫ W, (∑ e ∈ P.support, P.coeff e x * mono e W) *
      (∑ e ∈ P.support, P.coeff e y * mono e W) ∂stdGauss κ ∂μ ∂μ at h
  simp_rw [← joint_separated] at h
  rw [h]
  exact (integral_prod _ (jointCross_integrable P hμ)).symm

/-- The analytic covariance step for a finite polynomial field. -/
theorem joint_error_bound {n : ℕ} {κ : Type*} [Fintype κ] (P : JointPoly n κ)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hR : MemLp R 2 (μ.prod μ))
    (hbound : ∀ x y, jointCross P x y ≤ |R (x, y)| *
      Real.sqrt (jointCross P x x) * Real.sqrt (jointCross P y y)) :
    (∫ W, (∫ x, jointEval P W x ∂μ) ^ 2 ∂stdGauss κ) ≤
      Real.sqrt (∫ p, R p ^ 2 ∂μ.prod μ) * ∫ x, jointCross P x x ∂μ := by
  let := hμ.prob
  rw [joint_integrated_square P hμ]
  exact rkg56_covariance_cauchy μ R _ hR (jointCross_integrable P hμ)
    (fun x => jointCross P x x) (jointDiagonal_continuous P).measurable
    (BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ (jointDiagonal_continuous P))
    (jointDiagonal_nonneg P) (fun p => hbound p.1 p.2)

end BstLean.Part56.RKGErr
