import BstLean.Part248Network

/-! Algebraic adapters from dimension denominators to the single variable x = 1/n. -/
namespace BstLean.Part293
open Real BstLean.Part195 BstLean.Part248

theorem variance_normalization {N k C : ℝ} (hN : 0 < N) (hk : k < N) :
    C / (N * (N - k)) = C * (1 / N) ^ 2 / (1 - k * (1 / N)) := by
  have hd : 0 < 1 - k * (1 / N) := by
    rw [mul_one_div, sub_pos, div_lt_one hN]
    exact hk
  field_simp <;> ring

theorem latitude_normalization {N k C : ℝ} (hN : 0 < N) (hk : k < N)
    (hC : 0 ≤ C) :
    √(C / (N * (N - k))) = √C * (1 / N) / √(1 - k * (1 / N)) := by
  have hd : 0 < 1 - k * (1 / N) := by
    rw [mul_one_div, sub_pos, div_lt_one hN]
    exact hk
  have hden : 0 < N * (N - k) := mul_pos hN (sub_pos.mpr hk)
  apply (sq_eq_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt (div_nonneg hC hden.le), div_pow, mul_pow,
    sq_sqrt hC, sq_sqrt hd.le]
  exact variance_normalization hN hk

theorem rotation_latitude_le {N k C R : ℝ} {q : ℕ}
    (hN : 0 < N) (hk : k < N) (hC : 0 ≤ C) (hR : rotationConstant q ≤ R) :
    rotationConstant q * √(C / (N * (N - k))) ≤
      R * √C * (1 / N) / √(1 - k * (1 / N)) := by
  calc
    _ ≤ R * √(C / (N * (N - k))) :=
      mul_le_mul_of_nonneg_right hR (sqrt_nonneg _)
    _ = _ := by rw [latitude_normalization hN hk hC]; ring

theorem reciprocal_bound_mono {d Y X4 X8 X12 Z4 Z8 Z12 : ℝ}
    (hd : 0 < d) (hY : 0 < Y) (h8 : 0 ≤ X8) (h12 : 0 ≤ X12)
    (h4Z : X4 ≤ Z4) (h8Z : X8 ≤ Z8) (h12Z : X12 ≤ Z12) :
    bound3 d Y X4 X8 X12 ≤ bound3 d Y Z4 Z8 Z12 := by
  unfold bound3
  apply add_le_add
  · apply add_le_add
    · exact add_le_add le_rfl (div_le_div_of_nonneg_right h4Z (by positivity))
    · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h8 h8Z 2) (by positivity)
  · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h12 h12Z 3) (by positivity)

theorem deficit_rotation_le (q : ℕ) {H μ s Rhalf R : ℝ}
    (hμ : 0 ≤ μ) (hs : 0 ≤ s)
    (hh : rotationConstant (q / 2) ≤ Rhalf) (hR : rotationConstant q ≤ R) :
    deficitConstant q H μ s ≤ 2 * H + 2 * μ * (Rhalf * s) + (R * s) ^ 2 := by
  unfold deficitConstant
  apply add_le_add
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hh hs) (by positivity))
  · exact pow_le_pow_left₀ (mul_nonneg (rotationConstant_nonneg q) hs)
      (mul_le_mul_of_nonneg_right hR hs) 2

end BstLean.Part293

/-- info: 'BstLean.Part293.latitude_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.latitude_normalization
