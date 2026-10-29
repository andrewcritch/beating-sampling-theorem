import BstLean.Part169Scale

/-! Floor-parametric contraction and the pointwise Part 08 scale estimate. -/
namespace BstLean.Part289
open Real MeasureTheory

theorem floor_contraction {s₀ x Y : ℝ} (hY : s₀ ≤ Y) :
    |max s₀ x - Y| ≤ |x - Y| := by
  rcases le_total s₀ x with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, abs_of_nonpos (sub_nonpos.mpr hY),
      abs_of_nonpos (sub_nonpos.mpr (h.trans hY))]
    linarith

theorem floor_lipschitz (s₀ x y : ℝ) : |max s₀ x - max s₀ y| ≤ |x - y| := by
  rcases le_total s₀ x with hx | hx <;> rcases le_total s₀ y with hy | hy
  · rw [max_eq_right hx, max_eq_right hy]
  · rw [max_eq_right hx, max_eq_left hy, abs_of_nonneg (sub_nonneg.mpr hx),
      abs_of_nonneg (sub_nonneg.mpr (hy.trans hx))]; linarith
  · rw [max_eq_left hx, max_eq_right hy, abs_of_nonpos (sub_nonpos.mpr hy),
      abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]; linarith
  · rw [max_eq_left hx, max_eq_left hy, sub_self, abs_zero]; exact abs_nonneg _

theorem scale_pt_floor {s₀ γ d fb ft wb wt V : ℝ} (hs₀ : 0 < s₀)
    (hγ : 0 < γ) (hd : s₀ ≤ d) (hSbd : γ * d ≤ γ * (wb - fb ^ 2 - V)) :
    |γ * max s₀ (wt - ft ^ 2) / (γ * (wb - fb ^ 2 - V)) - 1| ≤
      (|wb - wt| + 2 * |fb| * |fb - ft| + (fb - ft) ^ 2 + |V|) / d := by
  have hd0 : 0 < d := hs₀.trans_le hd
  have hdY : d ≤ wb - fb ^ 2 - V := (mul_le_mul_iff_right₀ hγ).mp hSbd
  have hY0 : 0 < wb - fb ^ 2 - V := hd0.trans_le hdY
  have hraw : |(wt - ft ^ 2) - (wb - fb ^ 2 - V)| ≤
      |wb - wt| + 2 * |fb| * |fb - ft| + (fb - ft) ^ 2 + |V| := by
    have e : (wt - ft ^ 2) - (wb - fb ^ 2 - V) =
        -(wb - wt) + 2 * fb * (fb - ft) - (fb - ft) ^ 2 + V := by ring
    rw [e]
    calc _ ≤ |-(wb - wt)| + |2 * fb * (fb - ft)| + |(fb - ft) ^ 2| + |V| := by
          have h1 := abs_add_le (-(wb - wt) + 2 * fb * (fb - ft) - (fb - ft) ^ 2) V
          have h2 := abs_sub (-(wb - wt) + 2 * fb * (fb - ft)) ((fb - ft) ^ 2)
          have h3 := abs_add_le (-(wb - wt)) (2 * fb * (fb - ft))
          linarith
      _ = _ := by simp only [abs_neg, abs_mul, abs_two, abs_pow, sq_abs]
  have hf := (floor_contraction (x := wt - ft ^ 2) (hd.trans hdY)).trans hraw
  have e : γ * max s₀ (wt - ft ^ 2) / (γ * (wb - fb ^ 2 - V)) - 1 =
      (max s₀ (wt - ft ^ 2) - (wb - fb ^ 2 - V)) / (wb - fb ^ 2 - V) := by
    field_simp
  rw [e, abs_div, abs_of_pos hY0]
  exact (div_le_div_of_nonneg_right hf hY0.le).trans
    (div_le_div_of_nonneg_left (by positivity) hd0 hdY)

/-- The bias cutoff proposed for the lower branch satisfies the contraction condition. -/
theorem low_bias_cutoff_admissible : (17 / 100 : ℝ) ≤ (1 - 45 / 10000) * (18 / 100) := by
  norm_num

end BstLean.Part289

/-- info: 'BstLean.Part289.floor_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.floor_contraction
/-- info: 'BstLean.Part289.scale_pt_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.scale_pt_floor
