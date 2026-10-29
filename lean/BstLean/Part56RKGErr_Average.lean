import BstLean.Part56RKGErr_Conditional
import BstLean.Part56RKGErr_Integrability

namespace BstLean.Part56.RKGErr
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens TSymm fval)
open BstLean.Part43 (BofQ)
open BstLean.Part53 (sg)
variable {n d : ℕ}

theorem map_continuous :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => mapMD p.1 p.2) := by
  classical
  apply continuous_pi
  intro i
  unfold mapMD
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro b hb
  apply Continuous.mul
  · unfold BstLean.Part36.coefD
    split_ifs <;> fun_prop
  · have hc : Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x b.1) := by
      unfold BstLean.Part36.monoVal
      exact continuous_multiset_prod b.1 (fun i _ => continuous_apply i)
    exact hc.comp continuous_snd

theorem Sfl_measurable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) (hv : UnitV v) :
    StronglyMeasurable (fun Z : CoefIdxD n d → ℝ => Sfl μ d k f0 T v (sg n d • Z)) := by
  let := hμ.prob
  let F := fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) × (CoefIdxD n d → ℝ) =>
    fval k f0 T (mapMD (sg n d • FloorAux.splitField v p.1.1 p.2) p.1.2)
  have hF : Continuous F := by
    apply (fval_continuous k f0 T).comp
    apply (map_continuous (n := n) (d := d)).comp
      (f := fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) × (CoefIdxD n d → ℝ) =>
        (sg n d • FloorAux.splitField v p.1.1 p.2, p.1.2))
    apply Continuous.prodMk _ (continuous_snd.comp continuous_fst)
    unfold FloorAux.splitField
    have hfst : Continuous (fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) ×
        (CoefIdxD n d → ℝ) => p.1.1) := continuous_fst.comp continuous_fst
    have hsnd : Continuous (fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) ×
        (CoefIdxD n d → ℝ) => p.2) := continuous_snd
    exact (((Orth.projection_continuous (d := d) v).comp hfst).add
        (hsnd.sub ((Orth.projection_continuous (d := d) v).comp hsnd))).const_smul (sg n d)
  have h1 := hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (CoefIdxD n d))
  have h2 := (hF.pow 2).stronglyMeasurable.integral_prod_right' (ν := stdGauss (CoefIdxD n d))
  have hV : StronglyMeasurable (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      variance (fun W => fval k f0 T (mapMD (sg n d • FloorAux.splitField v p.1 W) p.2))
        (stdGauss (CoefIdxD n d))) := by
    have he (p : (CoefIdxD n d → ℝ) × (Fin n → ℝ)) :
        variance (fun W => F (p, W)) (stdGauss (CoefIdxD n d)) =
          (∫ W, F (p, W) ^ 2 ∂stdGauss (CoefIdxD n d)) -
            (∫ W, F (p, W) ∂stdGauss (CoefIdxD n d)) ^ 2 := by
      have hm := jointEval_memLp (residualJoint k f0 T v p.1) p.2
      simp only [residualJoint_map] at hm
      exact variance_eq_sub hm
    change StronglyMeasurable (fun p => variance (fun W => F (p, W)) (stdGauss (CoefIdxD n d)))
    have hh : StronglyMeasurable (fun p =>
        (∫ W, F (p, W) ^ 2 ∂stdGauss (CoefIdxD n d)) -
          (∫ W, F (p, W) ∂stdGauss (CoefIdxD n d)) ^ 2) := h2.sub (h1.pow 2)
    simpa only [← he] using hh
  simpa only [FloorAux.Sfl_as_variance k f0 T v hv] using hV.integral_prod_right' (ν := μ)

theorem Sfl_integrable (hS : PropSplit56 d)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) (hv : UnitV v) :
    Integrable (fun Z : CoefIdxD n d → ℝ => Sfl μ d k f0 T v (sg n d • Z))
      (stdGauss (CoefIdxD n d)) := by
  let := hμ.prob
  let ν := stdGauss (CoefIdxD n d)
  let A := fun Z : CoefIdxD n d → ℝ => ∫ x, fval k f0 T (mapMD (sg n d • Z) x) ^ 2 ∂μ
  have hA : Integrable A ν := by
    have hi := FloorAux.joint_product_integrable hμ (Orth.bJoint (d := d) k f0 T (sg n d) ^ 2)
    have he (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
        Orth.jointEval (Orth.bJoint k f0 T (sg n d) ^ 2) Z x =
          fval k f0 T (mapMD (sg n d • Z) x) ^ 2 := by
      rw [Orth.jointEval, map_pow]
      change Orth.jointEval (Orth.bJoint k f0 T (sg n d)) Z x ^ 2 = _
      rw [Orth.bJoint_eval]
    simp only [he] at hi
    exact hi.integral_prod_left
  have hmp := Orth.resampling_measurePreserving hS v hv
  have hr : Integrable (fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
      A (FloorAux.splitField v p.1 p.2)) (ν.prod ν) := hmp.integrable_comp_of_integrable hA
  apply hr.integral_prod_left.mono' (Sfl_measurable hμ k f0 T v hv).aestronglyMeasurable
  apply ae_of_all
  intro Z
  rw [Real.norm_eq_abs, abs_of_nonneg (FloorAux.Sfl_nonneg k f0 T v hv Z μ)]
  rw [FloorAux.Sfl_as_variance k f0 T v hv Z μ]
  have hi := FloorAux.joint_product_integrable hμ (residualJoint k f0 T v Z ^ 2)
  have he (W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
      Orth.jointEval (residualJoint k f0 T v Z ^ 2) W x =
        fval k f0 T (mapMD (sg n d • FloorAux.splitField v Z W) x) ^ 2 := by
    rw [Orth.jointEval, map_pow]
    change jointEval (residualJoint k f0 T v Z) W x ^ 2 = _
    rw [residualJoint_map]
  simp only [he] at hi
  change _ ≤ ∫ W, ∫ x, fval k f0 T (mapMD (sg n d • FloorAux.splitField v Z W) x) ^ 2 ∂μ ∂ν
  rw [integral_integral_swap hi]
  exact integral_mono_of_nonneg (ae_of_all _ (fun x => variance_nonneg _ _))
    hi.integral_prod_right (ae_of_all _ (fun x => variance_le_expectation_sq
      (by simpa only [residualJoint_map] using
        (jointEval_memLp (residualJoint k f0 T v Z) x).aestronglyMeasurable)))

end BstLean.Part56.RKGErr
