import BstLean.Part221ActiveTail

/-! The larger slope and the Gaussian integral give actual active radial moments. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part217

/-- Every moment alternative uses this same gate and radius distribution. -/
def ActiveRadialMoment160 (n : ℕ) (R2 : ℝ) : Prop :=
  ∀ hm : 0 < BstLean.Part130.mA n,
    (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius (d := n - 1 - 1) hm Z G ^ 160)
      ∂Measure.pi (fun _ : Fin (BstLean.Part130.mA n) => stdGauss (Fin (n - 1 - 1)))
      ∂Measure.pi (fun _ : Fin (BstLean.Part130.mA n) => gaussianReal 0 1)) ≤
      ENNReal.ofReal (R2 ^ 80)

theorem activeRadialMoment160_factorial {n : ℕ} (hn : 4 ≤ n) {a R2 : ℝ}
    (ha : 0 < a) (ha2 : ((n - 1 - 1 : ℕ) : ℝ) < a ^ 2)
    (hcal : (BstLean.Part130.mA n : ℝ) / 2 * exp (-densityRate (n - 1 - 1) a) ≤ 1)
    (hR : factorialMoment 160 a (a - ((n - 1 - 1 : ℕ) : ℝ) / a) ≤ R2 ^ 80) :
    ActiveRadialMoment160 n R2 := by
  intro hm
  exact (activeRadius_factorial_moment hm (by omega) ha ha2 hcal 160).trans
    (ENNReal.ofReal_le_ofReal hR)

theorem activeRadius_large_factorial_moment {m d : ℕ} (hm : 0 < m) (hd : 3 ≤ d)
    {a : ℝ} (ha : 0 < a) (ha2 : (d : ℝ) < a ^ 2)
    (hy : ((d : ℝ) - 1) * ((d : ℝ) + 1 + sqrt (4 * (d : ℝ) + 1)) /
      ((d : ℝ) - 2) ≤ a ^ 2)
    (hcal : (m : ℝ) / 2 * exp (-densityRate d a) ≤ 1) (ell : ℕ) :
    (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius hm Z G ^ ell)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
      ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) ≤
      ENNReal.ofReal (factorialMoment ell a (radialSlope (d : ℝ) a)) := by
  have ht : 0 < radialSlope (d : ℝ) a := by
    have hs := radial_slope_pos ha ha2
    have hden : 0 < a ^ 2 - (d : ℝ) + 1 := by linarith
    unfold radialSlope
    exact add_pos hs (div_pos (by positivity) hden)
  have h := shifted_tail_factorial (measurable_activeRadius hm)
    (fun p => activeMaximum_nonneg hm _ (fun i => sqrt_nonneg _)) ha ht
    (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_mul] using activeRadius_large_tail hm hd ha (by linarith) hy hcal) ell
  have hmeas : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) =>
      ENNReal.ofReal (activeRadius hm p.1 p.2 ^ ell)) :=
    ENNReal.measurable_ofReal.comp ((measurable_activeRadius hm).pow_const ell)
  rw [activeData, lintegral_prod _ hmeas.aemeasurable] at h
  exact h

/-- The calibration and the rate increment are the only radial tail premises. -/
theorem activeRadius_integral_moment {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d)
    {a t c J : ℝ} (ha : 0 < a) (hden : 0 < a ^ 2 - (d : ℝ) + 1)
    (hcal : (m : ℝ) / 2 * exp (-densityRate d a) ≤ 1)
    (hshift : ∀ v : ℝ, 0 < v → t * v + c * v ^ 2 / 2 ≤
      densityRate d (a + v) - densityRate d a)
    {ell : ℕ} (hell : 1 ≤ ell) (hJ0 : 0 ≤ J)
    (hJ : shiftedIntegral c (((ell - 1 : ℕ) : ℝ) / a - t) ≤ ENNReal.ofReal J) :
    (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius hm Z G ^ ell)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
      ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) ≤
      ENNReal.ofReal (a ^ ell + (ell : ℝ) * a ^ (ell - 1) * J) := by
  obtain ⟨hi, hb⟩ := shifted_tail_moment_bound (measurable_activeRadius hm)
    (fun p => activeMaximum_nonneg hm _ (fun i => sqrt_nonneg _)) ha hell
    (activeRadius_shifted_tail hm hd ha hden hcal hshift) hJ0 hJ
  have hnonneg : ∀ p : (Fin m → ℝ) × (Fin m → Fin d → ℝ),
      0 ≤ activeRadius hm p.1 p.2 ^ ell := fun p =>
    pow_nonneg (activeMaximum_nonneg hm _ (fun i => sqrt_nonneg _)) ell
  have h := ENNReal.ofReal_le_ofReal hb
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnonneg)] at h
  have hmeas : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) =>
      ENNReal.ofReal (activeRadius hm p.1 p.2 ^ ell)) :=
    ENNReal.measurable_ofReal.comp ((measurable_activeRadius hm).pow_const ell)
  rw [activeData, lintegral_prod _ hmeas.aemeasurable] at h
  exact h

theorem activeRadialMoment160_large_factorial {n : ℕ} (hn : 5 ≤ n) {a R2 : ℝ}
    (ha : 0 < a) (ha2 : ((n - 1 - 1 : ℕ) : ℝ) < a ^ 2)
    (hy : (((n - 1 - 1 : ℕ) : ℝ) - 1) *
      (((n - 1 - 1 : ℕ) : ℝ) + 1 + sqrt (4 * ((n - 1 - 1 : ℕ) : ℝ) + 1)) /
        (((n - 1 - 1 : ℕ) : ℝ) - 2) ≤ a ^ 2)
    (hcal : (BstLean.Part130.mA n : ℝ) / 2 * exp (-densityRate (n - 1 - 1) a) ≤ 1)
    (hR : factorialMoment 160 a (radialSlope ((n - 1 - 1 : ℕ) : ℝ) a) ≤ R2 ^ 80) :
    ActiveRadialMoment160 n R2 := by
  intro hm
  exact (activeRadius_large_factorial_moment hm (by omega) ha ha2 hy hcal 160).trans
    (ENNReal.ofReal_le_ofReal hR)

theorem activeRadialMoment160_integral {n : ℕ} (hn : 4 ≤ n) {a t c J R2 : ℝ}
    (ha : 0 < a) (hden : 0 < a ^ 2 - ((n - 1 - 1 : ℕ) : ℝ) + 1)
    (hcal : (BstLean.Part130.mA n : ℝ) / 2 * exp (-densityRate (n - 1 - 1) a) ≤ 1)
    (hshift : ∀ v : ℝ, 0 < v → t * v + c * v ^ 2 / 2 ≤
      densityRate (n - 1 - 1) (a + v) - densityRate (n - 1 - 1) a)
    (hJ0 : 0 ≤ J) (hJ : shiftedIntegral c (159 / a - t) ≤ ENNReal.ofReal J)
    (hR : a ^ 160 + 160 * a ^ 159 * J ≤ R2 ^ 80) :
    ActiveRadialMoment160 n R2 := by
  intro hm
  have h := activeRadius_integral_moment hm (by omega) ha hden hcal hshift
    (by norm_num : 1 ≤ 160) hJ0 (by simpa using hJ)
  exact h.trans (ENNReal.ofReal_le_ofReal (by simpa using hR))

end BstLean.Part221
