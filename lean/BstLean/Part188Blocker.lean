import BstLean.Part188MT169
import BstLean.Part184Def2

namespace BstLean.Part188
open Real
open BstLean.Part130 BstLean.Part169 BstLean.Part170

theorem sqrt_16200_old_bound_false : ¬ (1274 / 10 : ℝ) ≤ √(16200 : ℝ) := by
  intro h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16200)
  nlinarith [Real.sqrt_nonneg (16200 : ℝ)]

theorem location_fluctuation_old_cap_false :
    ¬ BstLean.Part184.FflB 16200 (O1n 16200) (5957 / 10000) ≤ 1114 / 100000 := by
  have hn0 : (0 : ℝ) < 16200 := by norm_num
  have hs : 0 < √(16200 : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : √(16200 : ℝ) ^ 2 = 16200 := Real.sq_sqrt hn0.le
  have hu : √(16200 : ℝ) ≤ 12728 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hlr : (12727 / 100 : ℝ) ≤ √(16200 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; norm_num
  have hO : O1n 16200 ^ 2 = 2 * (√(16200 : ℝ) + 2) ^ 2 := by
    unfold O1n
    norm_num
    rw [mul_pow]
    nlinarith [hsq]
  set R := √(16200 : ℝ) * √(tA 16200 * (5957 / 10000 * O1n 16200 ^ 2 / ((16200 : ℝ) - 2))) with hR
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hi : 0 ≤ tA 16200 * (5957 / 10000 * O1n 16200 ^ 2 / ((16200 : ℝ) - 2)) := by
    have hd : (0 : ℝ) < 16200 - 2 := by norm_num
    exact mul_nonneg (by unfold tA mA; positivity)
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hd.le)
  have hR2 : R ^ 2 = (5957 / 10000) * 4 * (√(16200 : ℝ) + 2) ^ 2 / (16200 * 16198) := by
    rw [hR, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hi, hO]
    unfold tA mA
    norm_num
    ring
  have hsmall : ((1114 / 100000 : ℝ) * (200 / 181)) ^ 2 < R ^ 2 := by
    rw [hR2]
    nlinarith [sq_nonneg (√(16200 : ℝ) - 12727 / 100)]
  intro h
  unfold BstLean.Part184.FflB at h
  norm_num only [Nat.cast_ofNat] at h
  have he : 181 / 100 * √(16200 : ℝ) *
      √(tA 16200 * (5957 / 10000 * O1n 16200 ^ 2 / ((16200 : ℝ) - 2))) / 2 = 181 / 200 * R := by rw [hR]; ring
  norm_num at he
  rw [he] at h
  nlinarith

end BstLean.Part188
