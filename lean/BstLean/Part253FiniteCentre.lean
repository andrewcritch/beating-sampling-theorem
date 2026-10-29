import BstLean.Part253Mass
import BstLean.Part211Source
import BstLean.Part150Num

/-! A checked finite-binomial centre allowance at the actual program length. -/
namespace BstLean.Part253
open Real

theorem wn_upper : BstLean.Part153.wn 12225 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 12225 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12225 12225 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12225)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12225)
  simp only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12225
  have hb0 := BstLean.Part150.betaJ_nonneg 12225
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12225 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12225 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12225 * BstLean.Part150.betaJ 12225) * 12225) ≤
      157.2237 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12225)) * 12225 := by gcongr
      _ ≤ (157.2237 : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12225 * 12225 *
      (1 + BstLean.Part154.deltaChi 12225 12 + 2 / π) / BstLean.Part154.csC) ≤
      179.9616 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12225 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr
      _ ≤ (179.9616 : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12225 : ℝ) / BstLean.Part154.csC) ≤ 97.15259 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12225 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ (97.15259 : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12225 : ℝ) * 157.2237 +
        2 * (1792 / 10000 / 12225) * 179.9616 +
        4 * (1 / 2.506628) * 1.036505 * 97.15259 *
          (81 / 1000 / 12225 + (1792 / 10000 / 12225) ^ 2) := by gcongr
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part253
