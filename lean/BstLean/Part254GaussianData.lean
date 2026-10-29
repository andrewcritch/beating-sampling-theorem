import BstLean.Part254Gaussian

namespace BstLean.Part254
open Real BstLean.Part146 BstLean.Part156

theorem gaussianTail_28 :
    (510425 / 10 ^ 8 : ℝ) ≤ gaussianTail (28 / 10) ∧
    gaussianTail (28 / 10) ≤ (5110297 / 10 ^ 9 : ℝ) := by
  have hl : (375311098851 / 10 ^ 12 : ℝ) ≤ exp (-(98 / 100)) := by
    apply le_exp_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hu : exp (-(98 / 100 : ℝ)) ≤ 375311098852 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 375311098851 / 10 ^ 12) hl 4
  have hpU := pow_le_pow_left₀ (exp_nonneg _) hu 4
  rw [← Real.exp_nat_mul] at hpL hpU
  norm_num at hpL hpU
  apply gaussianTail_enclosure (lo := (375311098851 / 10 ^ 12) ^ 4)
    (hi := (375311098852 / 10 ^ 12) ^ 4) (by norm_num) (by positivity)
  · convert hpL using 1 <;> norm_num
  · convert hpU using 1 <;> norm_num
  · norm_num
  · norm_num [nP, eP]

theorem gaussianTail_32 :
    (1373524 / 10 ^ 9 : ℝ) ≤ gaussianTail (32 / 10) ∧
    gaussianTail (32 / 10) ≤ (1374279 / 10 ^ 9 : ℝ) := by
  have hl : (527292424043 / 10 ^ 12 : ℝ) ≤ exp (-(64 / 100)) := by
    apply le_exp_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hu : exp (-(64 / 100 : ℝ)) ≤ 527292424044 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 527292424043 / 10 ^ 12) hl 8
  have hpU := pow_le_pow_left₀ (exp_nonneg _) hu 8
  rw [← Real.exp_nat_mul] at hpL hpU
  norm_num at hpL hpU
  apply gaussianTail_enclosure (lo := (527292424043 / 10 ^ 12) ^ 8)
    (hi := (527292424044 / 10 ^ 12) ^ 8) (by norm_num) (by positivity)
  · convert hpL using 1 <;> norm_num
  · convert hpU using 1 <;> norm_num
  · norm_num
  · norm_num [nP, eP]

theorem gaussianTail_6 :
    (1973157 / 10 ^ 15 : ℝ) ≤ gaussianTail (6) ∧
    gaussianTail (6) ≤ (1973176 / 10 ^ 15 : ℝ) := by
  have hl : (569782824730 / 10 ^ 12 : ℝ) ≤ exp (-(5625 / 10000)) := by
    apply le_exp_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hu : exp (-(5625 / 10000 : ℝ)) ≤ 569782824731 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 569782824730 / 10 ^ 12) hl 32
  have hpU := pow_le_pow_left₀ (exp_nonneg _) hu 32
  rw [← Real.exp_nat_mul] at hpL hpU
  norm_num at hpL hpU
  apply gaussianTail_enclosure (lo := (569782824730 / 10 ^ 12) ^ 32)
    (hi := (569782824731 / 10 ^ 12) ^ 32) (by norm_num) (by positivity)
  · convert hpL using 1 <;> norm_num
  · convert hpU using 1 <;> norm_num
  · norm_num
  · norm_num [nP, eP]

theorem gaussianTail_8 :
    (1244190 / 10 ^ 21 : ℝ) ≤ gaussianTail (8) ∧
    gaussianTail (8) ≤ (1244193 / 10 ^ 21 : ℝ) := by
  have hl : (367879441171 / 10 ^ 12 : ℝ) ≤ exp (-(1)) := by
    apply le_exp_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hu : exp (-(1 : ℝ)) ≤ 367879441172 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 367879441171 / 10 ^ 12) hl 32
  have hpU := pow_le_pow_left₀ (exp_nonneg _) hu 32
  rw [← Real.exp_nat_mul] at hpL hpU
  norm_num at hpL hpU
  apply gaussianTail_enclosure (lo := (367879441171 / 10 ^ 12) ^ 32)
    (hi := (367879441172 / 10 ^ 12) ^ 32) (by norm_num) (by positivity)
  · convert hpL using 1 <;> norm_num
  · convert hpU using 1 <;> norm_num
  · norm_num
  · norm_num [nP, eP]

end BstLean.Part254

