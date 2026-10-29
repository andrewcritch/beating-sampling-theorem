import BstLean.Part253FiniteCentre
import BstLean.Part253Exp
import BstLean.Part219Direction

/-! The installed Part153 Jacobian constant fits the centre operator allowance. -/
namespace BstLean.Part253
open Real BstLean.Part152 BstLean.Part153

theorem gauss160_upper : gaussMomConst 160 ≤ 12 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (320 : ℕ) ≠ 0) (by norm_num)
  rw [gaussMomConst_pow (by norm_num : 1 ≤ 160)]
  rw [show 320 = 160 * 2 by rfl, pow_mul]
  norm_num [Nat.factorial]

theorem epsS_upper : epsS 12225 160 0.006 ≤ 0.00000000000002 := by
  unfold epsS
  have h := exp_negative_bound 32 (by norm_num :
    ((2.71828 : ℝ) ^ 32)⁻¹ ≤ 0.00000000000002)
  apply le_trans ?_ h
  apply exp_le_exp.mpr
  norm_num

theorem jS_upper : jS 12225 160 0.006 ≤ 1.055 := by
  have hm := gauss160_upper
  have hm0 := gaussMomConst_nonneg 160
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 1.414213563 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(1 + 2 * (0.006 : ℝ)) ≤ 1.005982108 := sqrt_le_iff.mpr (by norm_num)
  have h1 : n1S 12225 160 0.006 ≤ 1.020160883 := by
    unfold n1S
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ (1.005982108 : ℝ) + 1.414213563 / 110.566721 +
          1.414213563 * 12 / 12225 := by gcongr
      _ ≤ (1.020160883 : ℝ) := by norm_num
  have hb : b2S 12225 160 ≤ 1.42839234 := by
    unfold b2S
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ (1.414213563 : ℝ) * (1 + 1 / 110.566721 + 12 / 12225) := by gcongr
      _ ≤ (1.42839234 : ℝ) := by norm_num
  have he := epsS_upper
  have he0 : 0 ≤ epsS 12225 160 0.006 := (exp_pos _).le
  have hb0 : 0 ≤ b2S 12225 160 := by unfold b2S; positivity
  have h22 : n2S 12225 160 0.006 ≤ 1.020160884 := by
    unfold n2S
    have hprod := mul_le_mul he hb hb0 (by norm_num : (0 : ℝ) ≤ 0.00000000000002)
    linarith
  have hr : rcS 12225 160 ≤ 1.001388186 := by
    unfold rcS
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ 1 + (1.414213563 : ℝ) * 12 / 12225 := by gcongr
      _ ≤ (1.001388186 : ℝ) := by norm_num
  have hc : rchiS 12225 160 ≤ 1.56770064 := by
    unfold rchiS
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ (1.414213563 : ℝ) * (1 + 12 / 110.566721) := by gcongr
      _ ≤ (1.56770064 : ℝ) := by norm_num
  have h220 := n2S_nonneg 12225 160 (by norm_num : (0 : ℝ) ≤ 0.006)
  have hr0 : 0 ≤ rcS 12225 160 := by unfold rcS; positivity
  have hc0 : 0 ≤ rchiS 12225 160 := by unfold rchiS; positivity
  unfold jS
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.020160884 : ℝ) ^ 2 + 1.001388186 * 1.56770064 / 110.566721 := by gcongr
    _ ≤ (1.055 : ℝ) := by norm_num

end BstLean.Part253
