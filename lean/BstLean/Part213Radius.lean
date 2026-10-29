import BstLean.Part213Polynomial
import BstLean.Part130Row

/-! Exact plane-radius moments for the collected location polynomial. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part186.RA

noncomputable def planeRadius (p : ℝ × ℝ) : ℝ := √(RR p)

lemma planeRadius_sq (p : ℝ × ℝ) : planeRadius p ^ 2 = RR p :=
  sq_sqrt (RR_nonneg p)

lemma planeRadius_integrable (j : ℕ) : Integrable (fun p => planeRadius p ^ j) ρ2 := by
  refine ((integrable_const (1 : ℝ)).add (int_RR_pow j).1).mono'
    ((measurable_RR.sqrt.pow_const j).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pow_nonneg (show 0 ≤ planeRadius p from sqrt_nonneg _) j)]
  change planeRadius p ^ j ≤ 1 + RR p ^ j
  by_cases h : planeRadius p ≤ 1
  · have h1 := pow_le_one₀ (show 0 ≤ planeRadius p from sqrt_nonneg _) h (n := j)
    linarith [pow_nonneg (RR_nonneg p) j]
  · have h1 : planeRadius p ≤ RR p := by
      have h2 := planeRadius_sq p
      have h3 : 1 < planeRadius p := lt_of_not_ge h
      nlinarith
    have h2 := pow_le_pow_left₀ (show 0 ≤ planeRadius p from sqrt_nonneg _) h1 j
    linarith

/-- Polar coordinates cancel the angular factor exactly. -/
theorem planeRadius_integral (j : ℕ) :
    ∫ p, planeRadius p ^ j ∂ρ2 =
      ∫ r in Ioi (0 : ℝ), r ^ (j + 1) * exp (-r ^ 2 / 2) := by
  let F : ℝ × ℝ → ℝ := fun p => planeRadius p ^ j
  have hγ : g1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  have hd : ∫ p, F p ∂ρ2 =
      ∫ p : ℝ × ℝ, (gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2).toReal * F p := by
    change (∫ p, F p ∂g1.prod g1) = _
    rw [hγ, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
    rw [← Measure.volume_eq_prod]
    exact integral_withDensity_eq_integral_toReal_smul
      (((measurable_gaussianPDF 0 1).comp measurable_fst).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd))
      (Filter.Eventually.of_forall fun p =>
        ENNReal.mul_lt_top (by simp [gaussianPDF]) (by simp [gaussianPDF])) F
  change (∫ p, F p ∂ρ2) = _
  rw [hd, ← integral_comp_polarCoord_symm]
  have he : ∀ p ∈ polarCoord.target,
      p.1 • ((gaussianPDF 0 1 (polarCoord.symm p).1 *
        gaussianPDF 0 1 (polarCoord.symm p).2).toReal * F (polarCoord.symm p)) =
      ((2 * π)⁻¹ * (p.1 ^ (j + 1) * exp (-p.1 ^ 2 / 2))) * (1 : ℝ) := by
    intro p hp
    rw [polarCoord_target] at hp
    have hr : 0 ≤ p.1 := hp.1.le
    simp only [polarCoord_symm_apply, smul_eq_mul, F, planeRadius, RR]
    rw [BstLean.Part130.gauss_density_polar]
    have hs : (p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2 = p.1 ^ 2 := by
      nlinarith [sin_sq_add_cos_sq p.2]
    rw [hs, sqrt_sq hr, pow_succ]
    ring
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet he,
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume.restrict (Ioo (-π) π))
      (fun r => (2 * π)⁻¹ * (r ^ (j + 1) * exp (-r ^ 2 / 2))) (fun _ => (1 : ℝ)),
    integral_const_mul]
  have ha : ∫ θ in Ioo (-π) π, (1 : ℝ) = 2 * π := by
    simp [Real.volume_Ioo, sub_neg_eq_add, pi_pos.le, ENNReal.toReal_ofReal]
    ring
  rw [ha]
  field_simp

/-- Every integer radius order has an exact Gamma expression. -/
theorem planeRadius_gamma (j : ℕ) :
    ∫ p, planeRadius p ^ j ∂ρ2 =
      (1 / 2 : ℝ) ^ (-((j : ℝ) + 2) / 2) * (1 / 2) * Gamma (((j : ℝ) + 2) / 2) := by
  rw [planeRadius_integral]
  have he : (fun r : ℝ => r ^ (j + 1) * exp (-r ^ 2 / 2)) =
      fun r => r ^ ((j : ℝ) + 1) * exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    funext r
    rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by push_cast; rfl,
      rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl, rpow_natCast]
    congr 2
    ring
  rw [he]
  simpa only [add_assoc, one_add_one_eq_two] using
    integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (j : ℝ) + 1) (b := 1 / 2)
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by norm_num)

/-- The first radius moment is the sharp Rayleigh mean. -/
theorem planeRadius_mean : ∫ p, planeRadius p ∂ρ2 = √(π / 2) := by
  have h := planeRadius_gamma 1
  simp only [pow_one, Nat.cast_one] at h
  rw [show -(1 + 2 : ℝ) / 2 = -(1 + 1 / 2) by norm_num,
    show (1 + 2 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
    Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Gamma_one_half_eq,
    rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    rpow_add (by norm_num : (0 : ℝ) < 1 / 2), rpow_one,
    ← sqrt_eq_rpow, sqrt_div (by norm_num : (0 : ℝ) ≤ 1), sqrt_one] at h
  rw [h, sqrt_div pi_pos.le]
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : √(2 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The third radius moment is three times the first moment. -/
theorem planeRadius_third : ∫ p, planeRadius p ^ 3 ∂ρ2 = 3 * √(π / 2) := by
  have h := planeRadius_gamma 3
  have h1 := planeRadius_gamma 1
  have he : (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) =
      2 * (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [show -(5 / 2 : ℝ) = -1 + (-(3 / 2 : ℝ)) by norm_num,
      rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num [rpow_neg_one]
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at h h1
  rw [he, show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
    Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)] at h
  rw [← planeRadius_mean]
  simp only [pow_one] at h1
  rw [h, h1]
  ring

#print axioms planeRadius_gamma
#print axioms planeRadius_mean
#print axioms planeRadius_third
end BstLean.Part213
