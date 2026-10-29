import BstLean.Part253HS
import BstLean.Part277Mono
import BstLean.Part291Band

namespace BstLean.BlueprintLow
open Real Set BstLean.Part194 BstLean.Part211 BstLean.Part253

theorem hsS0_8000 : (7379 : ℝ) ≤ S0 8000 := by
  have hs : √(12 * (8000 - 1 : ℝ)) ≤ 310 := sqrt_le_iff.mpr (by norm_num)
  unfold S0
  simp only [Nat.cast_ofNat]
  linarith

theorem hsA0_8000 : a0 8000 ≤ 0.008191 := by
  have hs24 : √(24 : ℝ) ≤ 4.89897949 := sqrt_le_iff.mpr (by norm_num)
  have hs2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hn : (89.442719 : ℝ) ≤ √8000 := le_sqrt_of_sq_le (by norm_num)
  have hn2 : (9.457416 : ℝ) ≤ √(√8000) := le_sqrt_of_sq_le (by linarith)
  unfold a0
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (4.89897949 : ℝ) / (1.414213562 * 89.442719 * 9.457416) := by gcongr
    _ ≤ (0.008191 : ℝ) := by norm_num

theorem hsInterval8000 {θ a b C D Q K A T S : ℝ}
    (hw : θ ∈ Icc a b) (ha : 0 < a) (hb : b ≤ 1)
    (hC : 2 * (1 - a) / (3.141592 * a) ≤ C) (hC0 : 0 ≤ C)
    (hD : 1 + 2 * C * 8000 / 7379 ≤ D ^ 2) (hD0 : 0 < D)
    (hQ : 1 - ((1 - 0.00000615) * (1 - 1 / 7379)) / D / 2 ≤ Q)
    (hCH : (1 + 0.006) * (Q ^ 2 + 1 / 8000) +
      (1 + 1 / 0.006) * (3 / (16 * 8000)) + 4 * (1 + 2 / 8000) / 8000 ≤ K ^ 4)
    (hK : 0 ≤ K) (hA : 0 < A) (hAsq : A ^ 2 ≤ a)
    (hT : 0 ≤ T) (hTsq : b ≤ T ^ 2)
    (hS : (K + 0.008191 / A) ^ 4 * (b * T) ≤ S) :
    hsProfile 8000 θ 0.006 * (θ * √θ) ≤ S := by
  have hθ := ha.trans_le hw.1
  have hθ1 := hw.2.trans hb
  have hlo := hw.1
  have hhi := hw.2
  have hb0 : 0 ≤ b := hθ.le.trans hhi
  have hj := J0_bounds (by norm_num : 64 ≤ 8000) hθ hθ1
  have hc : axialC θ ≤ C := by
    unfold axialC
    apply le_trans ?_ hC
    apply div_le_div₀ (by nlinarith : 0 ≤ 2 * (1 - a))
      (by linarith) (mul_pos (by norm_num) ha)
    have hp := pi_gt_d6.le
    gcongr
  have hs0 := hsS0_8000
  have hc0 : 0 ≤ axialC θ := by unfold axialC; exact div_nonneg (by linarith) (by positivity)
  have hd : √(1 + 2 * axialC θ * 8000 / S0 8000) ≤ D := by
    apply sqrt_le_iff.mpr
    refine ⟨hD0.le, le_trans ?_ hD⟩
    gcongr
  have hden : 0 < √(1 + 2 * axialC θ * 8000 / S0 8000) := by
    have hspos : 0 < S0 8000 := by linarith
    positivity
  have hn : (1 - 0.00000615 : ℝ) * (1 - 1 / 7379) ≤
      (1 - exp (-12)) * (1 - 1 / S0 8000) := by
    have he := exp_minus_twelve_upper
    have he0 : 0 ≤ 1 - exp (-12 : ℝ) := by linarith
    have hs : (1 : ℝ) / S0 8000 ≤ 1 / 7379 := by gcongr
    gcongr
  have hJ : ((1 - 0.00000615 : ℝ) * (1 - 1 / 7379)) / D ≤ J0 8000 θ := by
    unfold J0
    simp only [Nat.cast_ofNat]
    exact div_le_div₀ (le_trans (by norm_num) hn) hn hden hd
  have hq : qHS 8000 θ ≤ Q := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS 8000 θ := by linarith [hj.2.2.1]
  have hqQ : 0 ≤ Q := hq0.trans hq
  have hch : CH 8000 θ 0.006 ≤ K ^ 4 := by
    unfold CH
    simp only [Nat.cast_ofNat]
    apply le_trans ?_ hCH
    gcongr
  have hroot : √(√(CH 8000 θ 0.006)) ≤ K := by
    apply sqrt_le_iff.mpr
    refine ⟨hK, sqrt_le_iff.mpr ⟨sq_nonneg K, ?_⟩⟩
    simpa only [← pow_mul] using hch
  have hθroot : A ≤ √θ := le_sqrt_of_sq_le (hAsq.trans hw.1)
  have hθroot1 : √θ ≤ T := sqrt_le_iff.mpr ⟨hT, hw.2.trans hTsq⟩
  rw [hsProfile_eq_paper (by norm_num) hθ]
  have ha0 : 0 ≤ a0 8000 := by unfold a0; positivity
  have ha0u := hsA0_8000
  apply le_trans ?_ hS
  gcongr

end BstLean.BlueprintLow
