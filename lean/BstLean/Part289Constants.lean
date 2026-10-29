import BstLean.Part289Mix

/-! Coarse constants valid on both branches of the adopted floor. -/
namespace BstLean.Part289
open Real

theorem inverse_floor_le_six (n : ℕ) : 1 / scaleFloor n ≤ 6 := by
  have hs := scaleFloor_pos n
  have h := (scaleFloor_bounds n).1
  rw [div_le_iff₀ hs]
  linarith

theorem low_floor_inverse {n : ℕ} (hn : n < 11883) :
    1 / scaleFloor n = (100 / 17 : ℝ) := by rw [scaleFloor_low hn]; norm_num

theorem adopted_low_cutoff {n : ℕ} (hn : n < 11883) :
    scaleFloor n ≤ (1 - 45 / 10000) * (18 / 100) := by
  rw [scaleFloor_low hn]
  exact low_bias_cutoff_admissible

/-- With the paper's table error caps, 1650 replaces the old 1400 scale-error cap.
The small parameter is `t = sqrt(epsilon)`; no per-row data enter this estimate. -/
theorem table_scale_cap (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 64) :
    (130 * t * (n : ℝ) ^ 2 + (8 * t * n) * (2 * (9 * n) + 8 * t * n)) /
      scaleFloor n ≤ 1650 * t * (n : ℝ) ^ 2 := by
  have hnum : (0 : ℝ) ≤ 130 * t * (n : ℝ) ^ 2 + (8 * t * n) * (2 * (9 * n) + 8 * t * n) :=
    by positivity
  have he : 274 * t + 64 * t ^ 2 ≤ 275 * t := by
    nlinarith [mul_nonneg ht0 (by linarith : 0 ≤ 1 - 64 * t)]
  calc _ = (1 / scaleFloor n) *
        (130 * t * (n : ℝ) ^ 2 + (8 * t * n) * (2 * (9 * n) + 8 * t * n)) := by ring
    _ ≤ 6 * (130 * t * (n : ℝ) ^ 2 + (8 * t * n) * (2 * (9 * n) + 8 * t * n)) :=
      mul_le_mul_of_nonneg_right (inverse_floor_le_six n) hnum
    _ = 6 * (274 * t + 64 * t ^ 2) * (n : ℝ) ^ 2 := by ring
    _ ≤ 6 * (275 * t) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (sq_nonneg _)
    _ = _ := by ring

end BstLean.Part289

/-- info: 'BstLean.Part289.table_scale_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.table_scale_cap
