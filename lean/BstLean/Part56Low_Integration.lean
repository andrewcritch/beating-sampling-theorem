import BstLean.Part56Low_Pointwise
import BstLean.Part56RKGErr_Average

namespace BstLean.Part56.LowIntegration

open MeasureTheory ProbabilityTheory BstLean.Part29 BstLean.Part36 BstLean.Part41
open BstLean.Part40 (SphLaw)
open BstLean.Part53 (sg TF)
open LowPointwise LowCoefficients LowScale
open BstLean.Part53.FloorHeat

variable {n d : ℕ}

lemma cvar_section_continuous (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) :
    Continuous (fun x => cvarG k f0 T (sg n d * Real.sqrt (tauR d v x))
      (mux (sg n d • Z) v x)) := by
  let P := RKGErr.residualJoint k f0 T v Z
  have h1 := (rkg56Imported "_private.BstLean.Part56RKGFloor_Joint.0.BstLean.Part56.FloorAux.gaussian_mean_cont") P
  have h2 := (rkg56Imported "_private.BstLean.Part56RKGFloor_Joint.0.BstLean.Part56.FloorAux.gaussian_mean_cont") (P ^ 2)
  have he (x : Fin n → ℝ) :
      cvarG k f0 T (sg n d * Real.sqrt (tauR d v x)) (mux (sg n d • Z) v x) =
      (∫ W, Orth.jointEval (P ^ 2) W x ∂stdGauss (CoefIdxD n d)) -
      (∫ W, Orth.jointEval P W x ∂stdGauss (CoefIdxD n d)) ^ 2 := by
    rw [← FloorAux.residual_section_variance k f0 T v hv Z x]
    have hm := RKGErr.jointEval_memLp P x
    rw [variance_eq_sub (by simpa only [P, RKGErr.residualJoint_map] using hm)]
    have hs (W : CoefIdxD n d → ℝ) : Orth.jointEval (P ^ 2) W x =
        fval k f0 T (mapMD (sg n d • FloorAux.splitField v Z W) x) ^ 2 := by
      rw [Orth.jointEval, map_pow]
      change RKGErr.jointEval P W x ^ 2 = _
      dsimp only [P]
      rw [RKGErr.residualJoint_map]
    have hm' (W : CoefIdxD n d → ℝ) : Orth.jointEval P W x =
        fval k f0 T (mapMD (sg n d • FloorAux.splitField v Z W) x) :=
      RKGErr.residualJoint_map k f0 T v Z W x
    simp only [hs, hm', Pi.pow_apply]
  have hh : Continuous (fun x =>
      (∫ W, Orth.jointEval (P ^ 2) W x ∂stdGauss (CoefIdxD n d)) -
      (∫ W, Orth.jointEval P W x ∂stdGauss (CoefIdxD n d)) ^ 2) := h2.sub (h1.pow 2)
  simpa only [← he] using hh

lemma cvar_joint_measurable (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) :
    StronglyMeasurable (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      cvarG k f0 T (sg n d * Real.sqrt (tauR d v p.2)) (mux (sg n d • p.1) v p.2)) := by
  let F := fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) × (CoefIdxD n d → ℝ) =>
    fval k f0 T (mapMD (sg n d • FloorAux.splitField v p.1.1 p.2) p.1.2)
  have hF : Continuous F := by
    apply (RKGErr.fval_continuous k f0 T).comp
    apply (RKGErr.map_continuous (n := n) (d := d)).comp
      (f := fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) × (CoefIdxD n d → ℝ) =>
        (sg n d • FloorAux.splitField v p.1.1 p.2, p.1.2))
    apply Continuous.prodMk _ (continuous_snd.comp continuous_fst)
    unfold FloorAux.splitField
    have hf : Continuous (fun p : ((CoefIdxD n d → ℝ) × (Fin n → ℝ)) ×
        (CoefIdxD n d → ℝ) => p.1.1) := continuous_fst.comp continuous_fst
    exact (((Orth.projection_continuous (d := d) v).comp hf).add
      (continuous_snd.sub ((Orth.projection_continuous (d := d) v).comp continuous_snd))).const_smul (sg n d)
  have h1 := hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (CoefIdxD n d))
  have h2 := (hF.pow 2).stronglyMeasurable.integral_prod_right' (ν := stdGauss (CoefIdxD n d))
  have he (p : (CoefIdxD n d → ℝ) × (Fin n → ℝ)) :
      cvarG k f0 T (sg n d * Real.sqrt (tauR d v p.2)) (mux (sg n d • p.1) v p.2) =
      (∫ W, F (p, W) ^ 2 ∂stdGauss (CoefIdxD n d)) -
      (∫ W, F (p, W) ∂stdGauss (CoefIdxD n d)) ^ 2 := by
    rw [← FloorAux.residual_section_variance k f0 T v hv p.1 p.2]
    apply variance_eq_sub
    simpa only [F, RKGErr.residualJoint_map] using
      RKGErr.jointEval_memLp (RKGErr.residualJoint k f0 T v p.1) p.2
  have hh : StronglyMeasurable (fun p =>
      (∫ W, F (p, W) ^ 2 ∂stdGauss (CoefIdxD n d)) -
      (∫ W, F (p, W) ∂stdGauss (CoefIdxD n d)) ^ 2) := h2.sub (h1.pow 2)
  simpa only [← he] using hh

lemma cvar_product_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) (hv : UnitV v) :
    Integrable (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      cvarG k f0 T (sg n d * Real.sqrt (tauR d v p.2)) (mux (sg n d • p.1) v p.2))
      ((stdGauss (CoefIdxD n d)).prod μ) := by
  letI := hμ.prob
  apply (integrable_prod_iff (cvar_joint_measurable k f0 T v hv).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun Z => BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ
    (cvar_section_continuous k f0 T v hv Z)), ?_⟩
  have hi := RKGErr.Sfl_integrable (LowSplit.propSplit56 d) hμ k f0 T v hv
  convert hi using 1
  funext Z
  unfold Sfl
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change ‖cvarG k f0 T (sg n d * Real.sqrt (tauR d v x)) (mux (sg n d • Z) v x)‖ = _
    rw [Real.norm_eq_abs, abs_of_nonneg (RKGErr.cvar_nonneg k f0 T _ _)]

lemma Sfl_integral_swap {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)) =
      ∫ x, ∫ Z, cvarG k f0 T (sg n d * Real.sqrt (tauR d v x)) (mux (sg n d • Z) v x)
        ∂stdGauss (CoefIdxD n d) ∂μ := by
  letI := hμ.prob
  unfold Sfl
  exact integral_integral_swap (cvar_product_integrable hμ k f0 T v hv)

lemma integrated_coefficient_lower {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (f0 : ℝ) (T : Tens n)
    (hT : TSymm k T) (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ x, (1 - (∑ a, x a * v a) ^ 2) ^ k ∂μ) *
      normSum k (scaleT (sg n d) (TF k f0 T)) ≤
    ((k + 1 : ℝ) ^ 3 * weightBound d k) * (n : ℝ) ^ ((k - 1) / 2) *
      ∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d) := by
  letI := hμ.prob
  have hc : Continuous (fun x : Fin n → ℝ => (1 - (∑ a, x a * v a) ^ 2) ^ k) :=
    (continuous_const.sub ((continuous_finsetSum _ (fun a _ =>
      (continuous_apply a).mul continuous_const)).pow 2)).pow k
  have hi := BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ hc
  have hj := (cvar_product_integrable (d := d) hμ k f0 T v hv).integral_prod_right
  have hs : 0 ≤ sg n d := by unfold sg; positivity
  have h := integral_mono_ae
    (hi.mul_const (normSum k (scaleT (sg n d) (TF k f0 T))))
    (hj.const_mul (((k + 1 : ℝ) ^ 3 * weightBound d k) * (n : ℝ) ^ ((k - 1) / 2)))
    (hμ.sphere.mono (fun x hx => pointwise_coefficient_lower k hn hd f0 T hT
      (sg n d) hs v x hv hx))
  simpa only [integral_mul_const, integral_const_mul, ← Sfl_integral_swap hμ k f0 T v hv] using h


end BstLean.Part56.LowIntegration
