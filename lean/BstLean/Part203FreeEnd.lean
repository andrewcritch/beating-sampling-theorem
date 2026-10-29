import BstLean.Part203EndScalar

/-! Part 203: END for free root tangents with fixed b, K and C. -/
namespace BstLean.Part203
open Real

lemma plus_geometry {H b h x t : ℝ} (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 0 < x) (ht : 1 ≤ t) :
    (t * x + h) ^ 2 ≤ t ^ 2 * (x + h) ^ 2 ∧
    1 + H / (b * (t * x + h)) ≤ 1 + H / (b * (x + h)) ∧
    H * (b * (t * x + h)) + H ^ 2 ≤
      t ^ 2 * (H * (b * (x + h)) + H ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < x + h := by linarith
  have hr : x + h ≤ t * x + h := by nlinarith
  have hs : t * x + h ≤ t * (x + h) := by nlinarith
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have ht22 : 1 ≤ t ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · calc (t * x + h) ^ 2 ≤ (t * (x + h)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs 2
    _ = _ := by ring
  · have := div_le_div_of_nonneg_left hH (mul_pos hb hr0)
      (mul_le_mul_of_nonneg_left hr hb.le)
    linarith
  · have hrad : t * x + h ≤ t ^ 2 * (x + h) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hrad (mul_nonneg hH hb.le)
    have hh2 := mul_le_mul_of_nonneg_right ht22 (sq_nonneg H)
    nlinarith

lemma minus_geometry {H b h x t : ℝ} (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 2 * h + 2 * H / b < x) (ht : 1 ≤ t) :
    H < b * (x - h) ∧
    t ^ 2 * (x - h) ^ 2 ≤ (t * x - h) ^ 2 ∧
    0 ≤ 1 - H / (b * (x - h)) ∧
    1 - H / (b * (x - h)) ≤ 1 - H / (b * (t * x - h)) ∧
    t ^ 2 * (-H * (b * (x - h)) + H ^ 2) ≤
      -H * (b * (t * x - h)) + H ^ 2 := by
  have hd : 0 ≤ H / b := div_nonneg hH hb.le
  have hx' := hx
  rw [mul_div_assoc] at hx'
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < x - h := by linarith
  have hr : x - h ≤ t * x - h := by nlinarith
  have hW : H < b * (x - h) := by
    have hdiv : H / b < x - h := by linarith
    simpa [mul_comm] using (div_lt_iff₀ hb).mp hdiv
  refine ⟨hW, ?_, ?_, ?_, negative_beta_scale hH hb hh hx.le ht⟩
  · have hs : t * (x - h) ≤ t * x - h := by nlinarith
    calc t ^ 2 * (x - h) ^ 2 = (t * (x - h)) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hs 2
  · have := (div_lt_one (mul_pos hb hr0)).mpr hW
    linarith
  · have := div_le_div_of_nonneg_left hH (mul_pos hb hr0)
      (mul_le_mul_of_nonneg_left hr hb.le)
    linarith

lemma plus_product_scale {K L H b h x t : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hH : 0 ≤ H) (hb : 0 < b) (hh : 0 ≤ h) (hx : 0 < x) (ht : 1 ≤ t) :
    (t * x + h) ^ 2 * (exp (L * K * (1 + H / (b * (t * x + h)))) - 1) ≤
      t ^ 2 * ((x + h) ^ 2 * (exp (L * K * (1 + H / (b * (x + h)))) - 1)) := by
  obtain ⟨hw, ha, _⟩ := plus_geometry hH hb hh hx ht
  have hα : 0 ≤ 1 + H / (b * (t * x + h)) := by positivity
  have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha (mul_nonneg hL.le hK))
  have he0 : 0 ≤ exp (L * K * (1 + H / (b * (t * x + h)))) - 1 := by
    have := Real.one_le_exp (mul_nonneg (mul_nonneg hL.le hK) hα)
    linarith
  calc
    _ ≤ (t ^ 2 * (x + h) ^ 2) *
        (exp (L * K * (1 + H / (b * (t * x + h)))) - 1) :=
      mul_le_mul_of_nonneg_right hw he0
    _ ≤ (t ^ 2 * (x + h) ^ 2) *
        (exp (L * K * (1 + H / (b * (x + h)))) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

lemma minus_product_scale {K L H b h x t : ℝ} (hK : K ≤ 0) (hL : 0 < L)
    (hH : 0 ≤ H) (hb : 0 < b) (hh : 0 ≤ h)
    (hx : 2 * h + 2 * H / b < x) (ht : 1 ≤ t) :
    (t * x - h) ^ 2 * (exp (L * K * (1 - H / (b * (t * x - h)))) - 1) ≤
      t ^ 2 * ((x - h) ^ 2 * (exp (L * K * (1 - H / (b * (x - h)))) - 1)) := by
  obtain ⟨_, hw, ha0, ha, _⟩ := minus_geometry hH hb hh hx ht
  have he := exp_le_exp.mpr (mul_le_mul_of_nonpos_left ha
    (mul_nonpos_of_nonneg_of_nonpos hL.le hK))
  have he0 : exp (L * K * (1 - H / (b * (t * x - h)))) - 1 ≤ 0 := by
    have hα : 0 ≤ 1 - H / (b * (t * x - h)) := ha0.trans ha
    have := exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hL.le hK) hα)
    rw [exp_zero] at this
    linarith
  calc
    _ ≤ (t ^ 2 * (x - h) ^ 2) *
        (exp (L * K * (1 - H / (b * (t * x - h)))) - 1) :=
      mul_le_mul_of_nonpos_right hw he0
    _ ≤ (t ^ 2 * (x - h) ^ 2) *
        (exp (L * K * (1 - H / (b * (x - h)))) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- Exact positive END: no upper bound on the threshold is needed. -/
theorem exact_plus_END {C K L H b h x t : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 0 < L) (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 0 < x) (ht : 1 ≤ t) :
    exactRhs C K (1 + H / (b * (t * x + h)))
      (H * (b * (t * x + h)) + H ^ 2) ((t * x + h) ^ 2) L ≤
      t ^ 2 * exactRhs C K (1 + H / (b * (x + h)))
        (H * (b * (x + h)) + H ^ 2) ((x + h) ^ 2) L := by
  have hg := plus_geometry hH hb hh hx ht
  apply exact_scale hC hL (by nlinarith : 1 ≤ t ^ 2)
  · have := mul_le_mul_of_nonneg_left hg.2.2 hK
    nlinarith
  · have hα : 0 ≤ 1 + H / (b * (t * x + h)) := by positivity
    have := Real.one_le_exp (mul_nonneg (mul_nonneg hL.le hK) hα)
    have := mul_nonneg (sq_nonneg (t * x + h)) (by linarith :
      0 ≤ exp (L * K * (1 + H / (b * (t * x + h)))) - 1)
    linarith
  · exact plus_product_scale hK hL hH hb hh hx ht

/-- Exact negative END is restricted to the admissible probability interval. -/
theorem exact_minus_END {C K L H b h x t : ℝ} (hC : 0 ≤ C)
    (hK : K ≤ 0) (hL : 0 < L) (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 2 * h + 2 * H / b < x) (ht : 1 ≤ t)
    (hw : (t * x - h) ^ 2 ≤ 1) :
    exactRhs C K (1 - H / (b * (t * x - h)))
      (-H * (b * (t * x - h)) + H ^ 2) ((t * x - h) ^ 2) L ≤
      t ^ 2 * exactRhs C K (1 - H / (b * (x - h)))
        (-H * (b * (x - h)) + H ^ 2) ((x - h) ^ 2) L := by
  have hg := minus_geometry hH hb hh hx ht
  apply exact_scale hC hL (by nlinarith : 1 ≤ t ^ 2)
  · have := mul_le_mul_of_nonpos_left hg.2.2.2.2 hK
    nlinarith
  · exact bernoulli_pos (sq_nonneg _) hw
  · exact minus_product_scale hK hL hH hb hh hx ht

theorem tg_plus_END {C K L H b h x t u₀ : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 0 < L) (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 0 < x) (ht : 1 ≤ t) (hu : -1 < u₀) :
    tgRhs C K (1 + H / (b * (t * x + h)))
      (H * (b * (t * x + h)) + H ^ 2) ((t * x + h) ^ 2) L u₀ ≤
      t ^ 2 * tgRhs C K (1 + H / (b * (x + h)))
        (H * (b * (x + h)) + H ^ 2) ((x + h) ^ 2) L u₀ := by
  have hg := plus_geometry hH hb hh hx ht
  apply tg_scale hC hL hu (by nlinarith : 1 ≤ t ^ 2)
  · have := mul_le_mul_of_nonneg_left hg.2.2 hK
    nlinarith
  · exact plus_product_scale hK hL hH hb hh hx ht

theorem tg_minus_END {C K L H b h x t u₀ : ℝ} (hC : 0 ≤ C)
    (hK : K ≤ 0) (hL : 0 < L) (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 2 * h + 2 * H / b < x) (ht : 1 ≤ t)
    (hu : -1 < u₀) :
    tgRhs C K (1 - H / (b * (t * x - h)))
      (-H * (b * (t * x - h)) + H ^ 2) ((t * x - h) ^ 2) L u₀ ≤
      t ^ 2 * tgRhs C K (1 - H / (b * (x - h)))
        (-H * (b * (x - h)) + H ^ 2) ((x - h) ^ 2) L u₀ := by
  have hg := minus_geometry hH hb hh hx ht
  apply tg_scale hC hL hu (by nlinarith : 1 ≤ t ^ 2)
  · have := mul_le_mul_of_nonpos_left hg.2.2.2.2 hK
    nlinarith
  · exact minus_product_scale hK hL hH hb hh hx ht

end BstLean.Part203
