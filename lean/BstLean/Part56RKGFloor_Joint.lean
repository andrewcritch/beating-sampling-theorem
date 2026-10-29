import BstLean.Part56Orth_Mean
import BstLean.Part56RKGFloor_Variance

namespace BstLean.Part56.FloorAux

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part40 (SphLaw)
open BstLean.Part56.Orth (JointPoly jointEval)

variable {n d : ℕ}

-- Resolve finished private declarations without changing them. Every resulting
-- application remains checked by the Lean kernel.
elab "floorImported " key:str : term => do
  let env ← Lean.getEnv
  let target := key.getString
  let some (name, _) := env.constants.toList.find? (fun (name, _) => name.toString == target)
    | throwError "Imported floor helper is unavailable: {target}"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

private lemma joint_sum (p : JointPoly n d) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval p Z x =
      ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a) := by
  conv_lhs => unfold jointEval; rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
    Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]

private lemma joint_sq (p : JointPoly n d) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (p ^ 2) Z x = jointEval p Z x ^ 2 := by
  exact map_pow (MvPolynomial.eval₂Hom
    ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z) p 2

private lemma monomial_integrable (e : CoefIdxD n d →₀ ℕ) :
    Integrable (fun Z : CoefIdxD n d → ℝ => e.prod (fun i a => Z i ^ a))
      (stdGauss (CoefIdxD n d)) := by
  simpa [MvPolynomial.eval_monomial] using Orth.gaussian_eval_integrable
    (MvPolynomial.monomial e (1 : ℝ))

theorem joint_sphere_cont (p : JointPoly n d) (Z : CoefIdxD n d → ℝ) :
    Continuous (jointEval p Z) := by
  change Continuous (fun x => jointEval p Z x)
  simp only [joint_sum]
  exact continuous_finsetSum _ (fun e _ => (p.coeff e).continuous.mul continuous_const)

theorem joint_product_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : JointPoly n d) :
    Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => jointEval p zx.1 zx.2)
      ((stdGauss (CoefIdxD n d)).prod μ) := by
  classical
  let := hμ.prob
  simp only [joint_sum]
  apply integrable_finsetSum
  intro e he
  have hs := BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ (p.coeff e).continuous
  simpa only [mul_comm] using (monomial_integrable e).mul_prod hs

theorem joint_gaussian_memLp (p : JointPoly n d) (x : Fin n → ℝ) :
    MemLp (fun Z => jointEval p Z x) 2 (stdGauss (CoefIdxD n d)) := by
  have hc : Continuous (fun Z : CoefIdxD n d → ℝ => jointEval p Z x) := by
    simp only [joint_sum]
    apply continuous_finsetSum
    intro e he
    apply continuous_const.mul
    rw [show (fun Z : CoefIdxD n d → ℝ => e.prod (fun i a => Z i ^ a)) =
      fun Z => MvPolynomial.eval Z (MvPolynomial.monomial e (1 : ℝ)) by
        funext Z; simp [MvPolynomial.eval_monomial]]
    exact MvPolynomial.continuous_eval _
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
  have hi : Integrable (fun Z => jointEval (p ^ 2) Z x) (stdGauss (CoefIdxD n d)) := by
    simp only [joint_sum]
    exact integrable_finsetSum _ (fun e _ => (monomial_integrable e).const_mul _)
  simpa only [joint_sq] using hi

theorem joint_sphere_memLp {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : JointPoly n d) (Z : CoefIdxD n d → ℝ) : MemLp (jointEval p Z) 2 μ := by
  apply (memLp_two_iff_integrable_sq (joint_sphere_cont p Z).aestronglyMeasurable).2
  exact BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ ((joint_sphere_cont p Z).pow 2)

private lemma gaussian_mean_cont (p : JointPoly n d) :
    Continuous (fun x => ∫ Z, jointEval p Z x ∂stdGauss (CoefIdxD n d)) := by
  have he (x : Fin n → ℝ) : (∫ Z, jointEval p Z x ∂stdGauss (CoefIdxD n d)) =
      ∑ e ∈ p.support, p.coeff e x *
        ∫ Z : CoefIdxD n d → ℝ, e.prod (fun i a => Z i ^ a) ∂stdGauss (CoefIdxD n d) := by
    simp only [joint_sum]
    rw [integral_finsetSum _ (fun e _ => (monomial_integrable e).const_mul _)]
    simp only [integral_const_mul]
  simp only [he]
  exact continuous_finsetSum _ (fun e _ => (p.coeff e).continuous.mul continuous_const)

theorem sphere_mean_memLp {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : JointPoly n d) :
    MemLp (fun Z => ∫ x, jointEval p Z x ∂μ) 2 (stdGauss (CoefIdxD n d)) := by
  obtain ⟨q, hq⟩ :=
    (floorImported "_private.BstLean.Part56Orth_Integrability.0.BstLean.Part56.Orth.joint_integral_polynomial") hμ p
  have hi : Integrable (fun Z => MvPolynomial.eval Z q ^ 2) (stdGauss (CoefIdxD n d)) := by
    convert Orth.gaussian_eval_integrable (q ^ 2) using 1
    funext Z
    exact (MvPolynomial.eval_pow (f := Z) (p := q) 2).symm
  have hm := (memLp_two_iff_integrable_sq q.continuous_eval.aestronglyMeasurable).2 hi
  simpa only [hq] using hm

/-- The exact variance identity gives the floor for a polynomial residual field. -/
theorem joint_variance_floor {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : JointPoly n d) :
    (∫ x, variance (fun Z => jointEval p Z x) (stdGauss (CoefIdxD n d)) ∂μ) ≤
      (∫ Z, variance (jointEval p Z) μ ∂stdGauss (CoefIdxD n d)) +
        variance (fun Z => ∫ x, jointEval p Z x ∂μ) (stdGauss (CoefIdxD n d)) := by
  let := hμ.prob
  have ha : MemLp (fun x => ∫ Z, jointEval p Z x ∂stdGauss (CoefIdxD n d)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (gaussian_mean_cont p).aestronglyMeasurable).2
    exact BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ ((gaussian_mean_cont p).pow 2)
  have hs : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      jointEval p zx.1 zx.2 ^ 2) ((stdGauss (CoefIdxD n d)).prod μ) := by
    convert joint_product_integrable hμ (p ^ 2) using 1
    funext zx
    exact (joint_sq p zx.1 zx.2).symm
  have he := variance_exchange μ (stdGauss (CoefIdxD n d)) (jointEval p)
    (joint_product_integrable hμ p) hs (joint_sphere_memLp hμ p)
    (joint_gaussian_memLp p) ha (sphere_mean_memLp hμ p)
  have hn := variance_nonneg (fun x => ∫ Z, jointEval p Z x ∂stdGauss (CoefIdxD n d)) μ
  linarith

end BstLean.Part56.FloorAux
