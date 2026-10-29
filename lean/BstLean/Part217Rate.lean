import BstLean.Part217Integral

/-! The radial rate has the basic shifted-tail slope. -/
namespace BstLean.Part217
open Real

noncomputable def radialRate (d r : ℝ) : ℝ := r ^ 2 / 2 - d * log r

theorem radialRate_shift {d a v : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (hv : 0 ≤ v) :
    radialRate d (a + v) - radialRate d a ≥ (a - d / a) * v + v ^ 2 / 2 := by
  have hav : 0 < a + v := by linarith
  have hlog := log_le_sub_one_of_pos (div_pos hav ha)
  rw [log_div hav.ne' ha.ne'] at hlog
  have he : (a + v) / a - 1 = v / a := by field_simp; ring
  rw [he] at hlog
  have h := mul_le_mul_of_nonneg_left hlog hd
  unfold radialRate
  have he' : d * (v / a) = d / a * v := by ring
  rw [he'] at h
  nlinarith

noncomputable def correctedRadialRate (d r : ℝ) : ℝ :=
  radialRate d r + log (r ^ 2 - d + 1)

theorem correctedRadialRate_shift {d a v : ℝ} (hd : 0 ≤ d) (ha : 0 < a)
    (hden : 0 < a ^ 2 - d + 1) (hv : 0 ≤ v) :
    correctedRadialRate d (a + v) - correctedRadialRate d a ≥
      (a - d / a) * v + v ^ 2 / 2 := by
  have hr : a ^ 2 - d + 1 ≤ (a + v) ^ 2 - d + 1 := by nlinarith
  have hl := log_le_log hden hr
  have hi := radialRate_shift hd ha hv
  unfold correctedRadialRate
  linarith

theorem radial_slope_pos {d a : ℝ} (ha : 0 < a) (hd : d < a ^ 2) :
    0 < a - d / a := by
  rw [sub_pos, div_lt_iff₀ ha]
  nlinarith

noncomputable def paperRadialRate (d r C : ℝ) : ℝ :=
  (r ^ 2 - d - d * log (r ^ 2 / d)) / 2 + log (r ^ 2 - d + 1) - log C

theorem paperRadialRate_identity {d r : ℝ} (hd : 0 < d) (hr : 0 < r) (C : ℝ) :
    paperRadialRate d r C = correctedRadialRate d r + (d * log d - d) / 2 - log C := by
  unfold paperRadialRate correctedRadialRate radialRate
  rw [log_div (pow_ne_zero 2 hr.ne') hd.ne', log_pow]
  ring

theorem paperRadialRate_shift {d a v C : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hden : 0 < a ^ 2 - d + 1) (hv : 0 ≤ v) :
    paperRadialRate d (a + v) C - paperRadialRate d a C ≥
      (a - d / a) * v + v ^ 2 / 2 := by
  rw [paperRadialRate_identity hd (by linarith : 0 < a + v), paperRadialRate_identity hd ha]
  have h := correctedRadialRate_shift hd.le ha hden hv
  linarith

end BstLean.Part217
