import BstLean.Part53T2_Radial
import BstLean.Part53T2_Integrability

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens uJ varU)

variable {n d : ℕ}

lemma measurable_unit : Measurable (unitOfD (n := n) (d := d)) := by
  unfold unitOfD
  exact (measurable_const.div (Real.continuous_sqrt.measurable.comp (by fun_prop))).smul measurable_id

lemma scale_unit (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
    radialScale n d Z • unitOfD Z = sg n d • Z := by
  have hS : 0 < ∑ α, Z α ^ 2 := by
    obtain ⟨α, hα⟩ : ∃ α, Z α ≠ 0 := by
      by_contra h
      push Not at h
      exact hZ (funext h)
    exact lt_of_lt_of_le (by positivity)
      (Finset.single_le_sum (fun β _ => sq_nonneg (Z β)) (Finset.mem_univ α))
  have hs := (Real.sqrt_pos.mpr hS).ne'
  unfold radialScale unitOfD sg
  rw [smul_smul]
  congr 1
  field_simp

lemma gauss_ae_nonzero (hn : 1 ≤ n) :
    ∀ᵐ Z : CoefIdxD n d → ℝ ∂stdGauss (CoefIdxD n d), Z ≠ 0 := by
  let i0 : CoefIdxD n d := ⟨0, (Sym.nil, ⟨0, by omega⟩)⟩
  have h0 : stdGauss (CoefIdxD n d) {0} = 0 := by
    apply measure_mono_null (t := (fun Z : CoefIdxD n d → ℝ => Z i0) ⁻¹' {0})
    · intro Z hZ
      simp only [Set.mem_singleton_iff] at hZ
      simp [hZ]
    · unfold stdGauss
      rw [(measurePreserving_eval (fun _ : CoefIdxD n d => ProbabilityTheory.gaussianReal 0 1) i0).measure_preimage
        (measurableSet_singleton _).nullMeasurableSet]
      have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measure_singleton 0
  exact measure_eq_zero_iff_ae_notMem.mp h0

lemma polar_product (hP : GaussPolar53) (a : ℝ → ℝ≥0∞)
    (b : (CoefIdxD n d → ℝ) → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ Z, a (Real.sqrt (∑ α, Z α ^ 2)) * b (unitOfD Z) ∂stdGauss (CoefIdxD n d)) =
      (∫⁻ Z, a (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d)) *
        ∫⁻ Z, b (unitOfD Z) ∂stdGauss (CoefIdxD n d) := by
  have har : Measurable (fun Z : CoefIdxD n d → ℝ => a (Real.sqrt (∑ α, Z α ^ 2))) :=
    ha.comp (by fun_prop)
  have hbu := hb.comp measurable_unit
  have h := hP n d (fun W r => a r * b W) ((ha.comp measurable_snd).mul (hb.comp measurable_fst))
  rw [h]
  simp_rw [lintegral_mul_const _ har]
  exact lintegral_const_mul _ hbu

lemma var_u_scale (μ : Measure (Fin n → ℝ)) (T : Tens n) (j : ℕ)
    (l : ℝ) (W : CoefIdxD n d → ℝ) :
    varU μ (uJ T j (l • W)) = l ^ (2 * j) * varU μ (uJ T j W) := by
  unfold varU
  simp_rw [uJ_smul, integral_const_mul, ← mul_sub, mul_pow]
  rw [integral_const_mul, ← pow_mul, Nat.mul_comm j 2]

/-- The angular homogeneous variance is at most its normalized Gaussian expectation. -/
lemma angular_variance_le_gaussian (hP : GaussPolar53) (μ : Measure (Fin n → ℝ))
    (hμ : SphLaw n μ) (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    (∫⁻ Z, ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d)) ≤
      ENNReal.ofReal ((sg n d) ^ (2 * j) *
        ∫ Z, varU μ (uJ T j Z) ∂stdGauss (CoefIdxD n d)) := by
  let a := fun r : ℝ => ENNReal.ofReal ((r / Real.sqrt (DD n d)) ^ (2 * j))
  let b := fun W : CoefIdxD n d → ℝ => ENNReal.ofReal (varU μ (uJ T j W))
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hb : Measurable b := (varU_uJ_measurable μ hμ hn T j).ennreal_ofReal
  have hp := polar_product hP a b ha hb
  have hrad : 1 ≤ ∫⁻ Z, a (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d) := by
    change 1 ≤ ∫⁻ Z, ENNReal.ofReal (radialScale n d Z ^ (2 * j)) ∂stdGauss (CoefIdxD n d)
    rw [← ofReal_integral_eq_lintegral_ofReal (radialScale_even_integrable n d j hn)
      (Filter.Eventually.of_forall fun Z => pow_nonneg (radialScale_nonneg n d Z) _)]
    exact_mod_cast ENNReal.ofReal_le_ofReal (radialScale_even_moment_ge_one n d j hn)
  have hV0 (Z : CoefIdxD n d → ℝ) : 0 ≤ varU μ (uJ T j Z) :=
    integral_nonneg fun _ => sq_nonneg _
  have hsg : 0 ≤ sg n d := by unfold sg; positivity
  have he : (∫⁻ Z, a (Real.sqrt (∑ α, Z α ^ 2)) * b (unitOfD Z)
      ∂stdGauss (CoefIdxD n d)) =
      ENNReal.ofReal ((sg n d) ^ (2 * j) *
        ∫ Z, varU μ (uJ T j Z) ∂stdGauss (CoefIdxD n d)) := by
    have hpoint : ∀ᵐ Z ∂stdGauss (CoefIdxD n d),
        a (Real.sqrt (∑ α, Z α ^ 2)) * b (unitOfD Z) =
          ENNReal.ofReal ((sg n d) ^ (2 * j) * varU μ (uJ T j Z)) := by
      filter_upwards [gauss_ae_nonzero (d := d) hn] with Z hZ
      change ENNReal.ofReal (radialScale n d Z ^ (2 * j)) *
        ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) = _
      rw [← ENNReal.ofReal_mul (pow_nonneg (radialScale_nonneg n d Z) _),
        ← var_u_scale, scale_unit Z hZ, var_u_scale]
    rw [lintegral_congr_ae hpoint,
      ← ofReal_integral_eq_lintegral_ofReal ((varU_uJ_integrable μ hμ hn T j).const_mul _)
        (Filter.Eventually.of_forall fun Z => mul_nonneg (pow_nonneg hsg _) (hV0 Z)),
      integral_const_mul]
  calc
    _ = 1 * ∫⁻ Z, b (unitOfD Z) ∂stdGauss (CoefIdxD n d) := by rw [one_mul]
    _ ≤ (∫⁻ Z, a (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d)) *
        ∫⁻ Z, b (unitOfD Z) ∂stdGauss (CoefIdxD n d) :=
      by gcongr
    _ = _ := hp.symm.trans he

end BstLean.Part53.T2Aux
