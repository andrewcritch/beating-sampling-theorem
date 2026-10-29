import BstLean.Part293Normalize
import BstLean.Part162Int

/-! Algebraic normalization of the dimension factors in the mixture price. -/
namespace BstLean.Part293
open Real BstLean.Part162

theorem dimension_sqrt_ratio {N L : ℝ} (hN : 0 < N) :
    N * √(L / N) = √L * √N := by
  have hs0 : √N ≠ 0 := (sqrt_pos.mpr hN).ne'
  rw [sqrt_div' L hN.le]
  calc
    _ = (√N) ^ 2 * (√L / √N) := by rw [sq_sqrt hN.le]
    _ = _ := by field_simp <;> ring

theorem normalized_tK {N L K e d tau : ℝ} (hN : 0 < N) :
    tK K N (√L) (e * tau) (√N * d * tau) =
      K * (N * tau ^ 2) * (e ^ 2 / 2 + d ^ 2 + √(L / N) * e * d) := by
  have hs : (√N * d * tau) ^ 2 = N * d ^ 2 * tau ^ 2 := by
    rw [mul_pow, mul_pow, sq_sqrt hN.le]
  have hc := dimension_sqrt_ratio (L := L) hN
  unfold tK
  rw [hs, mul_pow]
  calc
    _ = K * (N * tau ^ 2 * (e ^ 2 / 2 + d ^ 2) +
      (√L * √N) * tau ^ 2 * e * d) := by ring
    _ = _ := by rw [← hc]; ring

theorem normalized_latitude_square {N k C R : ℝ} (hN : 0 < N)
    (hk : k < N) (hC : 0 ≤ C) :
    N * (R * √(C / (N * (N - k)))) ^ 2 =
      R ^ 2 * C * (1 / N) / (1 - k * (1 / N)) := by
  rw [mul_pow, sq_sqrt (div_nonneg hC (mul_nonneg hN.le (sub_nonneg.mpr hk.le))),
    variance_normalization hN hk]
  field_simp <;> ring

theorem epsilon_square_scaled {N d w : ℝ} (hd : 0 ≤ d) :
    N * ((1 + 2 * w / √d) ^ 2 - 1) ^ 2 =
      16 * (N * w ^ 2) / d * (1 + w / √d) ^ 2 := by
  have he : (1 + 2 * w / √d) ^ 2 - 1 = 4 * (w / √d) * (1 + w / √d) := by ring
  rw [he]
  calc
    _ = 16 * N * (w / √d) ^ 2 * (1 + w / √d) ^ 2 := by ring
    _ = _ := by rw [div_pow, sq_sqrt hd]; ring

end BstLean.Part293

/-- info: 'BstLean.Part293.normalized_tK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.normalized_tK
