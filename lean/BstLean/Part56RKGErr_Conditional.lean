import BstLean.Part56RKGErr_Covariance
import BstLean.Part56RKGErr_Joint
import BstLean.Part56RKGFloor_Balance

namespace BstLean.Part56.RKGErr

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono Tens TSymm fval)
open BstLean.Part43 (BofQ)
open BstLean.Part53 (sg nsq linZ)
variable {n d : ℕ}

elab "rkg56Imported " key:str : term => do
  let name := (key.getString.splitOn ".").foldl
    (fun n s => if let some i := s.toNat? then Lean.Name.num n i else Lean.Name.str n s)
    Lean.Name.anonymous
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

noncomputable def residualJoint (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) : JointPoly n (CoefIdxD n d) :=
  (rkg56Imported "_private.BstLean.Part56Orth_Mean.0.BstLean.Part56.Orth.resampleJoint")
    v Z (Orth.bJoint k f0 T (sg n d))

theorem residualJoint_eval (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (residualJoint k f0 T v Z) W x =
      fval k f0 T (mux (sg n d • Z) v x + linZ W (sg n d • Orth.residualFeature v x)) := by
  dsimp only [residualJoint]
  change Orth.jointEval _ W x = _
  rw [(rkg56Imported "_private.BstLean.Part56Orth_Mean.0.BstLean.Part56.Orth.resampleJoint_eval"),
    Orth.bJoint_eval, Orth.resampled_map]

theorem residualJoint_map (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (residualJoint k f0 T v Z) W x =
      fval k f0 T (mapMD (sg n d • FloorAux.splitField v Z W) x) := by
  rw [residualJoint_eval]
  simp only [FloorAux.splitField, Orth.resampled_map]

theorem residual_diagonal (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointCross (centeredJoint (residualJoint k f0 T v Z)) x x =
      cvarG k f0 T (sg n d * Real.sqrt (tauR d v x)) (mux (sg n d • Z) v x) := by
  unfold jointCross
  simp only [centeredJoint_eval, residualJoint_eval, ← pow_two]
  apply linear_variance_eq_cvar
  rw [Orth.residualFeature_scaled_norm (sg n d) v hv x, mul_pow,
    Real.sq_sqrt (rkg56_tau_nonneg v x)]

theorem residual_cross_bound (hMC : LemmaMC56) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) (x y : Fin n → ℝ) :
    jointCross (centeredJoint (residualJoint k f0 T v Z)) x y ≤
      |rhoR d v x y| *
        Real.sqrt (jointCross (centeredJoint (residualJoint k f0 T v Z)) x x) *
        Real.sqrt (jointCross (centeredJoint (residualJoint k f0 T v Z)) y y) := by
  have hx : nsq (sg n d • Orth.residualFeature (d := d) v x) =
      (sg n d * Real.sqrt (tauR d v x)) ^ 2 := by
    rw [Orth.residualFeature_scaled_norm (sg n d) v hv x, mul_pow,
      Real.sq_sqrt (rkg56_tau_nonneg v x)]
  have hy : nsq (sg n d • Orth.residualFeature (d := d) v y) =
      (sg n d * Real.sqrt (tauR d v y)) ^ 2 := by
    rw [Orth.residualFeature_scaled_norm (sg n d) v hv y, mul_pow,
      Real.sq_sqrt (rkg56_tau_nonneg v y)]
  have hc : (∑ p : Mono n d, (sg n d • Orth.residualFeature v x) p *
      (sg n d • Orth.residualFeature v y) p) =
      (sg n d * Real.sqrt (tauR d v x)) *
        (sg n d * Real.sqrt (tauR d v y)) * rhoR d v x y := by
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ p : Mono n d, (sg n d * Orth.residualFeature v x p) *
      (sg n d * Orth.residualFeature v y p) = sg n d ^ 2 *
        (Orth.residualFeature v x p * Orth.residualFeature v y p) by intro p; ring]
    rw [← Finset.mul_sum, rkg56_residual_cross v hv x y, rkg56_KR_normalization v x y]
    ring
  have hb := linear_covariance_bound hMC k f0 T _ _ _ _ _
    (rkg56_abs_rho_le_one v x y) hx hy hc (mux (sg n d • Z) v x) (mux (sg n d • Z) v y)
  have he := covariance_eq_sub
    (fval_linear_memLp k f0 T (sg n d • Orth.residualFeature (d := d) v x) (mux (sg n d • Z) v x))
    (fval_linear_memLp k f0 T (sg n d • Orth.residualFeature (d := d) v y) (mux (sg n d • Z) v y))
  simp only [Pi.mul_apply] at he
  rw [← he] at hb
  rw [residual_diagonal k f0 T v hv Z x, residual_diagonal k f0 T v hv Z y]
  simp only [jointCross, centeredJoint_eval, residualJoint_eval, covariance]
  exact le_trans (le_abs_self _) hb

theorem rho_memLp {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (v : Fin n → ℝ) :
    MemLp (fun p : (Fin n → ℝ) × (Fin n → ℝ) => rhoR d v p.1 p.2) 2 (μ.prod μ) := by
  classical
  let := hμ.prob
  apply MemLp.of_bound (C := 1)
  · apply Measurable.aestronglyMeasurable
    have hp (j : ℕ) (q : Mono n d) : Continuous (fun x => phiB d j x q) :=
      (rkg56Imported "_private.BstLean.Part56Orth_Integrability.0.BstLean.Part56.Orth.phiB_cont") d j q
    unfold rhoR tauR KR kJ
    fun_prop (disch := exact (hp _ _).measurable)
  · exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using rkg56_abs_rho_le_one v p.1 p.2)

theorem centered_spatial_integral {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (v : Fin n → ℝ) (hv : UnitV v) (Z W : CoefIdxD n d → ℝ) :
    (∫ x, jointEval (centeredJoint (residualJoint k f0 T v Z)) W x ∂μ) =
      BofQ μ k f0 T (sg n d • FloorAux.splitField v Z W) -
        gLineH μ k f0 T v (sg n d • Z) := by
  let := hμ.prob
  let P := residualJoint k f0 T v Z
  have hm : Integrable (fun x => ∫ V, jointEval P V x ∂stdGauss (CoefIdxD n d)) μ := by
    simp only [← jointMean_eq]
    exact BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ (jointMean P).continuous
  simp only [centeredJoint_eval]
  rw [integral_sub (BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ
    (jointEval_continuous P W)) hm]
  have hi := FloorAux.joint_product_integrable hμ P
  rw [← integral_integral_swap hi]
  simp only [P, residualJoint_map]
  exact congrArg (fun a => BofQ μ k f0 T (sg n d • FloorAux.splitField v Z W) - a)
    (Orth.resampled_mean hμ k f0 T hT v hv Z)

theorem conditional_error_bound (hMC : LemmaMC56)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) :
    (∫ W, (BofQ μ k f0 T (sg n d • FloorAux.splitField v Z W) -
      gLineH μ k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
      Real.sqrt (deltaSq μ d v) * Sfl μ d k f0 T v (sg n d • Z) := by
  let P := centeredJoint (residualJoint k f0 T v Z)
  have hb := joint_error_bound P hμ (fun p => rhoR d v p.1 p.2) (rho_memLp hμ v)
    (residual_cross_bound hMC k f0 T v hv Z)
  simp only [P, centered_spatial_integral hμ k f0 T hT v hv, residual_diagonal k f0 T v hv Z] at hb
  have hd : (∫ p : (Fin n → ℝ) × (Fin n → ℝ), rhoR d v p.1 p.2 ^ 2 ∂μ.prod μ) =
      deltaSq μ d v := by
    let := hμ.prob
    exact integral_prod _ (rho_memLp hμ v).integrable_sq
  rw [hd] at hb
  exact hb

end BstLean.Part56.RKGErr
