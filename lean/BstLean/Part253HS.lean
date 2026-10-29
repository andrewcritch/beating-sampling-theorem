import BstLean.Part253FiniteCentre
import BstLean.Part253Exp
import BstLean.Part211Profile

/-! Interval bounds for the centre Hilbert--Schmidt profile. -/
namespace BstLean.Part253
open Real Set BstLean.Part194 BstLean.Part211

theorem S0_lower : (11458 : ℝ) ≤ S0 12225 := by
  have hs : √(12 * (12225 - 1 : ℝ)) ≤ 383 := sqrt_le_iff.mpr (by norm_num)
  unfold S0
  simp only [Nat.cast_ofNat]
  linarith

theorem a0_upper : a0 12225 ≤ 0.00595916 := by
  have hs24 : √(24 : ℝ) ≤ 4.89897949 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have hn2 : (10.51507 : ℝ) ≤ √(√12225) := le_sqrt_of_sq_le (by linarith)
  unfold a0
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (4.89897949 : ℝ) / (1.414213562 * 110.566721 * 10.51507) := by gcongr
    _ ≤ (0.00595916 : ℝ) := by norm_num

theorem hs_interval {θ a b C D Q K A T S : ℝ}
    (hw : θ ∈ Icc a b) (ha : 0 < a) (hb : b ≤ 1)
    (hC : 2 * (1 - a) / (3.141592 * a) ≤ C) (hC0 : 0 ≤ C)
    (hD : 1 + 2 * C * 12225 / 11458 ≤ D ^ 2) (hD0 : 0 < D)
    (hQ : 1 - ((1 - 0.00000615) * (1 - 1 / 11458)) / D / 2 ≤ Q)
    (hCH : (1 + 0.006) * (Q ^ 2 + 1 / 12225) +
      (1 + 1 / 0.006) * (3 / (16 * 12225)) + 4 * (1 + 2 / 12225) / 12225 ≤ K ^ 4)
    (hK : 0 ≤ K) (hA : 0 < A) (hAsq : A ^ 2 ≤ a)
    (hT : 0 ≤ T) (hTsq : b ≤ T ^ 2)
    (hS : (K + 0.00595916 / A) ^ 4 * (b * T) ≤ S) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ S := by
  have hθ := ha.trans_le hw.1
  have hθ1 := hw.2.trans hb
  have hlo := hw.1
  have hhi := hw.2
  have hb0 : 0 ≤ b := hθ.le.trans hhi
  have hj := J0_bounds (by norm_num : 64 ≤ 12225) hθ hθ1
  have hc : axialC θ ≤ C := by
    unfold axialC
    apply le_trans ?_ hC
    apply div_le_div₀ (by have := hw.1; have := hw.2; nlinarith : 0 ≤ 2 * (1 - a))
      (by have := hw.1; linarith) (mul_pos (by norm_num) ha)
    have hp := pi_gt_d6.le
    gcongr
  have hs0 := S0_lower
  have hd : √(1 + 2 * axialC θ * 12225 / S0 12225) ≤ D := by
    apply sqrt_le_iff.mpr
    refine ⟨hD0.le, ?_⟩
    apply le_trans ?_ hD
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    gcongr
  have hden : 0 < √(1 + 2 * axialC θ * 12225 / S0 12225) := by
    have hc0 : 0 ≤ axialC θ := by
      unfold axialC
      apply div_nonneg (by linarith) (by positivity)
    have hspos : 0 < S0 12225 := by linarith
    positivity
  have hn : (1 - 0.00000615 : ℝ) * (1 - 1 / 11458) ≤
      (1 - exp (-12)) * (1 - 1 / S0 12225) := by
    have he := exp_minus_twelve_upper
    have he0 : 0 ≤ 1 - exp (-12 : ℝ) := by linarith
    have hs : (1 : ℝ) / S0 12225 ≤ 1 / 11458 := by
      gcongr
    gcongr
  have hJ : ((1 - 0.00000615 : ℝ) * (1 - 1 / 11458)) / D ≤ J0 12225 θ := by
    unfold J0
    simp only [Nat.cast_ofNat]
    exact div_le_div₀ (le_trans (by norm_num) hn) hn hden hd
  have hq : qHS 12225 θ ≤ Q := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS 12225 θ := by linarith [hj.2.2.1]
  have hqQ : 0 ≤ Q := hq0.trans hq
  have hch : CH 12225 θ 0.006 ≤ K ^ 4 := by
    unfold CH
    simp only [Nat.cast_ofNat]
    apply le_trans ?_ hCH
    gcongr
  have hroot : √(√(CH 12225 θ 0.006)) ≤ K := by
    apply sqrt_le_iff.mpr
    refine ⟨hK, sqrt_le_iff.mpr ⟨sq_nonneg K, ?_⟩⟩
    simpa only [← pow_mul] using hch
  have hθroot : A ≤ √θ := le_sqrt_of_sq_le (hAsq.trans hw.1)
  have hθroot1 : √θ ≤ T := sqrt_le_iff.mpr ⟨hT, hw.2.trans hTsq⟩
  rw [hsProfile_eq_paper (by norm_num) hθ]
  have ha0 : 0 ≤ a0 12225 := by unfold a0; positivity
  have ha0u := a0_upper
  apply le_trans ?_ hS
  gcongr

end BstLean.Part253
