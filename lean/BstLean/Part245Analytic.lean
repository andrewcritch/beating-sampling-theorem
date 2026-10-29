import BstLean.Part197Kernel
import BstLean.Part182SNum

/-! Part 245: rational bounds for the actual kernel slope. -/
namespace BstLean.Part245
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197

theorem kdot_mono {a b : ℝ} (h : a ≤ b) : kdot a ≤ kdot b := by
  unfold kdot
  linarith [div_le_div_of_nonneg_right (Real.arccos_le_arccos h) Real.pi_pos.le]

/-- An upper half-angle endpoint and an arctangent remainder give a lower slope endpoint. -/
theorem kdot_lower {c q a d : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hq : 0 ≤ q) (hqs : (1 - c) / (1 + c) ≤ q ^ 2)
    (ha : atanSum 8 q + q ^ 17 / 17 ≤ a)
    (hd : d ≤ 1 - 2 * a / (3141592 / 1000000)) (ha0 : 0 ≤ a) :
    d ≤ kdot c := by
  have hr : angleRatio c ≤ q := (Real.sqrt_le_left hq).2 hqs
  have ht := (abs_le.mp (atan_remainder hq 8)).2
  have hat : Real.arctan q ≤ a := by norm_num at ht; linarith
  have hac : Real.arccos c ≤ 2 * a := by
    rw [arccos_half_angle hc hc1]
    linarith [Real.arctan_mono hr]
  have hdiv : Real.arccos c / π ≤ 2 * a / (3141592 / 1000000) :=
    (div_le_div_of_nonneg_right hac Real.pi_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by norm_num) sn_pi_lo.le)
  unfold kdot
  linarith

theorem kdot_073_lower : (7604 / 10000 : ℝ) ≤ kdot (73 / 100) := by
  apply kdot_lower (q := 39506 / 100000) (a := 37626 / 100000)
    <;> norm_num [atanSum, Finset.sum_range_succ]

theorem kdot_0778_lower : (7837 / 10000 : ℝ) ≤ kdot (778 / 1000) := by
  apply kdot_lower (q := 35336 / 100000) (a := 33967 / 100000)
    <;> norm_num [atanSum, Finset.sum_range_succ]

end BstLean.Part245
