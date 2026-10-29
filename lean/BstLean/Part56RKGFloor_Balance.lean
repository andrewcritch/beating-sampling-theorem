import BstLean.Part56RKGFloor_Gaussian
import BstLean.Part56RKGFloor_Joint
import BstLean.Part56Orth_Conditional

namespace BstLean.Part56.FloorAux

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono Tens TSymm fval varU contr)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg linZ nsq)
open BstLean.Part56.Orth (JointPoly jointEval)

variable {n d : ℕ}

noncomputable def splitField (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) :
    CoefIdxD n d → ℝ := projA v Z + (W - projA v W)

private noncomputable def residualJoint (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) : JointPoly n d :=
  (floorImported "_private.BstLean.Part56Orth_Mean.0.BstLean.Part56.Orth.resampleJoint")
    v Z (Orth.bJoint k f0 T (sg n d))

private lemma residualJoint_eval (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (residualJoint k f0 T v Z) W x =
      fval k f0 T (mapMD (sg n d • splitField v Z W) x) := by
  dsimp only [residualJoint]
  rw [(floorImported "_private.BstLean.Part56Orth_Mean.0.BstLean.Part56.Orth.resampleJoint_eval"),
    Orth.bJoint_eval]
  rfl

private lemma residual_integral_test (v : Fin n → ℝ) (hv : UnitV v)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ)
    (H : (Fin n → ℝ) → ℝ) (hH : Continuous H) :
    (∫ W, H (mapMD (sg n d • splitField v Z W) x) ∂stdGauss (CoefIdxD n d)) =
      ∫ g, H (mux (sg n d • Z) v x +
        (sg n d * Real.sqrt (tauR d v x)) • g) ∂stdGauss (Fin n) := by
  have hsg : 0 ≤ sg n d := by unfold sg; positivity
  have hs : Real.sqrt (nsq (sg n d • Orth.residualFeature (d := d) v x)) =
      sg n d * Real.sqrt (tauR d v x) := by
    rw [Orth.residualFeature_scaled_norm (sg n d) v hv x,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hsg]
  simp only [splitField, Orth.resampled_map]
  have hi := linear_gaussian_integral (sg n d • Orth.residualFeature (d := d) v x)
    (fun y => H (mux (sg n d • Z) v x + y))
    (hH.comp (continuous_const.add continuous_id))
  rw [hs] at hi
  exact hi

private lemma fval_cont (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Continuous (fval k f0 T) := by
  unfold fval contr
  fun_prop

/-- The residual section variance equals the frozen `cvarG`, including `τ = 0`. -/
theorem residual_section_variance (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    variance (fun W => fval k f0 T (mapMD (sg n d • splitField v Z W) x))
        (stdGauss (CoefIdxD n d)) =
      cvarG k f0 T (sg n d * Real.sqrt (tauR d v x)) (mux (sg n d • Z) v x) := by
  have hm := joint_gaussian_memLp (residualJoint k f0 T v Z) x
  simp only [residualJoint_eval] at hm
  rw [variance_eq_sub hm]
  simp only [Pi.pow_apply]
  unfold cvarG
  rw [residual_integral_test v hv Z x (fun y => fval k f0 T y ^ 2)
      ((fval_cont k f0 T).pow 2),
    residual_integral_test v hv Z x (fval k f0 T) (fval_cont k f0 T)]

/-- The frozen `Sfl` is the average residual section variance. -/
theorem Sfl_as_variance (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ)
    (μ : Measure (Fin n → ℝ)) :
    Sfl μ d k f0 T v (sg n d • Z) =
      ∫ x, variance (fun W => fval k f0 T (mapMD (sg n d • splitField v Z W) x))
        (stdGauss (CoefIdxD n d)) ∂μ := by
  unfold Sfl
  apply integral_congr_ae
  exact ae_of_all _ (fun x => (residual_section_variance k f0 T v hv Z x).symm)

theorem Sfl_nonneg (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ)
    (μ : Measure (Fin n → ℝ)) : 0 ≤ Sfl μ d k f0 T v (sg n d • Z) := by
  rw [Sfl_as_variance k f0 T v hv Z μ]
  exact integral_nonneg (fun x => variance_nonneg _ _)

/-- At each fixed anchor value, the section variance is bounded by the spatial
variance plus the squared conditional prediction error. -/
theorem pointwise_balance {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) :
    Sfl μ d k f0 T v (sg n d • Z) ≤
      (∫ W, varFQ μ k f0 T (sg n d • splitField v Z W)
        ∂stdGauss (CoefIdxD n d)) +
      ∫ W, (BofQ μ k f0 T (sg n d • splitField v Z W) -
        gLineH μ k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) := by
  let P := residualJoint k f0 T v Z
  have hp := joint_variance_floor hμ P
  have hV (W : CoefIdxD n d → ℝ) :
      variance (jointEval P W) μ = varFQ μ k f0 T (sg n d • splitField v Z W) := by
    rw [variance_eq_integral (joint_sphere_memLp hμ P W).aemeasurable]
    simp only [P, residualJoint_eval]
    rfl
  have hm : MemLp (fun W => BofQ μ k f0 T (sg n d • splitField v Z W)) 2
      (stdGauss (CoefIdxD n d)) := by
    simpa only [P, residualJoint_eval, BofQ] using sphere_mean_memLp hμ P
  have hB : variance (fun W => ∫ x, jointEval P W x ∂μ) (stdGauss (CoefIdxD n d)) =
      ∫ W, (BofQ μ k f0 T (sg n d • splitField v Z W) -
        gLineH μ k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) := by
    simp only [P, residualJoint_eval]
    change variance (fun W => BofQ μ k f0 T (sg n d • splitField v Z W)) _ = _
    rw [variance_eq_integral hm.aemeasurable]
    have he := Orth.resampled_mean hμ k f0 T hT v hv Z
    change (∫ W, BofQ μ k f0 T (sg n d • splitField v Z W)
      ∂stdGauss (CoefIdxD n d)) = gLineH μ k f0 T v (sg n d • Z) at he
    rw [he]
  rw [hB] at hp
  simp only [hV] at hp
  simpa only [P, residualJoint_eval, ← Sfl_as_variance k f0 T v hv Z μ] using hp

/-- Integrating the pointwise floor gives the balance bound used in RK-G. -/
theorem integrated_balance (k : ℕ) (hE : PropRKGErr56 d k)
    (hO : PropOrth56 d k) (hS : PropSplit56 d)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)) ≤
      EV56 d μ k f0 T +
        ∫ Z, (BofQ μ k f0 T (sg n d • Z) -
          gLineH μ k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) := by
  obtain ⟨hB, hG, hV, ho⟩ := hO n μ hμ v hv f0 T hT
  obtain ⟨hErr, he⟩ := hE n μ hμ v hv f0 T hT
  let ν := stdGauss (CoefIdxD n d)
  let A := fun M : CoefIdxD n d → ℝ =>
    varFQ μ k f0 T (sg n d • M) +
      (BofQ μ k f0 T (sg n d • M) - gLineH μ k f0 T v (sg n d • M)) ^ 2
  let r := fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
    splitField v p.1 p.2
  have hA : Integrable A ν := hV.add hErr
  have hmp : MeasurePreserving r (ν.prod ν) ν :=
    Orth.resampling_measurePreserving hS v hv
  have hr : Integrable (fun p => A (r p)) (ν.prod ν) :=
    hmp.integrable_comp_of_integrable hA
  have hVr : Integrable (fun p => varFQ μ k f0 T (sg n d • r p)) (ν.prod ν) :=
    hmp.integrable_comp_of_integrable hV
  have hEr : Integrable (fun p =>
      (BofQ μ k f0 T (sg n d • r p) - gLineH μ k f0 T v (sg n d • r p)) ^ 2)
      (ν.prod ν) := hmp.integrable_comp_of_integrable hErr
  have hheat (Z W : CoefIdxD n d → ℝ) :
      gLineH μ k f0 T v (sg n d • splitField v Z W) =
        gLineH μ k f0 T v (sg n d • Z) :=
    Orth.heat_resampling μ k f0 T v hv (sg n d) Z W
  have hpoint : (fun Z => Sfl μ d k f0 T v (sg n d • Z)) ≤ᵐ[ν]
      fun Z => ∫ W, A (r (Z, W)) ∂ν := by
    filter_upwards [hVr.prod_right_ae, hEr.prod_right_ae] with Z hZv hZe
    dsimp only [r] at hZv hZe
    change Sfl μ d k f0 T v (sg n d • Z) ≤
      ∫ W, varFQ μ k f0 T (sg n d • splitField v Z W) +
        (BofQ μ k f0 T (sg n d • splitField v Z W) -
          gLineH μ k f0 T v (sg n d • splitField v Z W)) ^ 2 ∂ν
    rw [integral_add hZv hZe]
    simp only [hheat]
    exact pointwise_balance hμ k f0 T hT v hv Z
  have hle := integral_mono_of_nonneg
    (ae_of_all ν (fun Z => Sfl_nonneg k f0 T v hv Z μ)) hr.integral_prod_left hpoint
  have hEq : (∫ Z, ∫ W, A (r (Z, W)) ∂ν ∂ν) = ∫ M, A M ∂ν := by
    rw [← integral_prod (fun p => A (r p)) hr]
    conv_rhs => rw [← hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable
      (hmp.map_eq.symm ▸ hA.aestronglyMeasurable)).symm
  rw [hEq] at hle
  change (∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂ν) ≤
    ∫ M, varFQ μ k f0 T (sg n d • M) +
      (BofQ μ k f0 T (sg n d • M) - gLineH μ k f0 T v (sg n d • M)) ^ 2 ∂ν at hle
  rw [integral_add hV hErr] at hle
  exact hle

end BstLean.Part56.FloorAux
