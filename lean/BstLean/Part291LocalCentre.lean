import BstLean.Part291CentreTransfer
import BstLean.Part291HSAffine

/-! Local centre envelopes. The constants may depend on a dimension band and
a noise interval; the conclusions hold for every dimension in that band. -/
namespace BstLean.BlueprintLow
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem centreGamma54 {n : ℕ} (hn : 8000 ≤ n) {Θ : ℝ}
    (hΘ0 : 0 < Θ) (hΘ1 : Θ ≤ 0.54) :
    0 < gammaRatio n 0.011 Θ ∧ gammaRatio n 0.011 Θ ≤ 0.000143 := by
  have hw := centreWnBand hn
  have hwu := hw.2
  have hw0 : 0 < wn n := by linarith [hw.1]
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold gammaRatio
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.045222 : ℝ) * 0.54 / ((1 - 0.011) * 8000) := by gcongr
      _ ≤ _ := by norm_num

theorem centreSecondGap54 {γ : ℝ} (hγ : γ ≤ 0.000143) :
    (0.06334 : ℝ) ≤ gap 1 γ 1.14 := by
  have hs : (0.99992849 : ℝ) ≤ √(1 - γ) := le_sqrt_of_sq_le (by linarith)
  have hk : (1.067707825 : ℝ) ≤ √1.14 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.14 ≤ 0.936585813 := by
    calc
      _ ≤ (1 : ℝ) / 1.067707825 := by gcongr
      _ ≤ _ := by norm_num
  unfold gap
  rw [one_mul]
  linarith

theorem localCentreMoment {n : ℕ} (hn : LowBand n)
    {Θ W R G Nu Nhi T1 T2 E1 E2 S : ℝ}
    (hΘ : Θ ∈ Icc (0.46 : ℝ) 0.54)
    (hW : wn n ≤ W) (hR : rhoBar n csC ≤ R)
    (hG : gammaRatio n 0.011 Θ ≤ G) (hNu : 4 * R + R ^ 2 ≤ Nu)
    (hNhi : (n : ℝ) ≤ Nhi) (hS : 0 ≤ S)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hGap1 : 2 * R * E1 ≤ 0.105169208 ^ 2)
    (hGap2 : 2 * G * E2 ≤ 0.06334 ^ 2)
    (hT1 : exp (-E1) ≤ T1) (hT2 : exp (-E2) ≤ T2) :
    momentAllowance n csC 0.011 1.25 1.14 Θ S ≤
      4 * 0.090846 * 1.193734 * S / 1.600601 +
      W * Nhi * (T1 / 1.118033988 + T2 / 1.067707825) +
      4 * W * ((2 * Θ * R + 0.6863 * (4 * W / 1.29521) * Nu) / 3.141592 + Θ / 10 ^ 40) +
      4 * Θ * W * 2.519668 * R := by
  have hθ0 : 0 < Θ := lt_of_lt_of_le (by norm_num) hΘ.1
  have hwlo := (centreWnBand hn.1).1
  have hw0 : 0 ≤ wn n := by linarith
  have hW0 : 0 ≤ W := hw0.trans hW
  have hr := centreRhoBand hn
  have hr0 : 0 < rhoBar n csC := by linarith [hr.1]
  have hR0 : 0 ≤ R := hr0.le.trans hR
  have hg := centreGamma54 hn.1 hθ0 hΘ.2
  have hgap1 := centreFirstGap hr.2
  have hgap2 := centreSecondGap54 hg.2
  have ht1 : tail 2 (rhoBar n csC) 1.25 ≤ T1 := by
    have hE : E1 ≤ gap 2 (rhoBar n csC) 1.25 ^ 2 / (2 * rhoBar n csC) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * rhoBar n csC)]
      nlinarith [mul_le_mul_of_nonneg_right hR hE1]
    unfold tail
    apply le_trans ?_ hT1
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio n 0.011 Θ) 1.14 ≤ T2 := by
    have hE : E2 ≤ gap 1 (gammaRatio n 0.011 Θ) 1.14 ^ 2 / (2 * gammaRatio n 0.011 Θ) := by
      rw [le_div_iff₀ (by linarith [hg.1] : 0 < 2 * gammaRatio n 0.011 Θ)]
      nlinarith [mul_le_mul_of_nonneg_right hG hE2]
    unfold tail
    apply le_trans ?_ hT2
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hk : (1.118033988 : ℝ) ≤ √1.25 := le_sqrt_of_sq_le (by norm_num)
  have hk3 : (1.067707825 : ℝ) ≤ √1.14 := le_sqrt_of_sq_le (by norm_num)
  have ht10 : 0 ≤ tail 2 (rhoBar n csC) 1.25 := by unfold tail; positivity
  have ht20 : 0 ≤ tail 1 (gammaRatio n 0.011 Θ) 1.14 := by unfold tail; positivity
  have hT10 : 0 ≤ T1 := ht10.trans ht1
  have hT20 : 0 ≤ T2 := ht20.trans ht2
  have hNhi0 : 0 ≤ Nhi := (Nat.cast_nonneg n).trans hNhi
  have hbad : badAllowance n csC 0.011 1.25 1.14 Θ ≤
      W * Nhi * (T1 / 1.118033988 + T2 / 1.067707825) := by
    unfold badAllowance
    gcongr
  have hv : nuR (rhoBar n csC) ≤ Nu := by unfold nuR; nlinarith
  have hv0 : 0 ≤ nuR (rhoBar n csC) := by unfold nuR; positivity
  have hNu0 : 0 ≤ Nu := hv0.trans hv
  have hp := centrePiSmall hr0 hr.2
  have hp0 := piBar_nonneg (rhoBar n csC)
  have hc := BstLean.Part253.cs_lower
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hn.1; omega)
  have hrn : rhoBar n csC * n ≤ 4 * W / 1.29521 := by
    have he : rhoBar n csC * n = 4 * wn n / csC := by unfold rhoBar; field_simp
    rw [he]
    gcongr
  have hpi := pi_gt_d6.le
  have hlin : linearAllowance n csC Θ ≤
      4 * W * ((2 * Θ * R + 0.6863 * (4 * W / 1.29521) * Nu) / 3.141592 + Θ / 10 ^ 40) := by
    unfold linearAllowance
    rw [show (6863 / 10000 : ℝ) * rhoBar n csC * n * nuR (rhoBar n csC) =
      (6863 / 10000 : ℝ) * (rhoBar n csC * n) * nuR (rhoBar n csC) by ring]
    convert (show 4 * wn n * ((2 * Θ * rhoBar n csC +
      (6863 / 10000) * (rhoBar n csC * n) * nuR (rhoBar n csC)) / π +
      Θ * piBar (rhoBar n csC)) ≤
      4 * W * ((2 * Θ * R + (6863 / 10000) * (4 * W / 1.29521) * Nu) / 3.141592 +
        Θ * (1 / 10 ^ 40)) by gcongr) using 1 <;> ring
  have hbn : bN n csC Θ ≤ 4 * Θ * W * 2.519668 * R := by
    have hq := normalizedQB hr.1 hr.2
    unfold bN
    calc
      _ ≤ 4 * Θ * wn n * (2.519668 * rhoBar n csC ^ 2) / rhoBar n csC := by gcongr
      _ = 4 * Θ * wn n * 2.519668 * rhoBar n csC := by field_simp
      _ ≤ _ := by gcongr
  have hrest : restAllowance csC 0.011 1.25 1.14 S ≤
      4 * 0.090846 * 1.193734 * S / 1.600601 := by
    have hk : K0 ≤ 0.090846 := by
      unfold K0
      apply (div_le_iff₀ (by positivity : 0 < 4 * π)).mpr
      linarith [pi_lt_d6]
    have hk0 : 0 ≤ K0 := by unfold K0; exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
    have hs : √((1.25 : ℝ) * 1.14) ≤ 1.193734 := sqrt_le_iff.mpr (by norm_num)
    have ht : (1.600601 : ℝ) ≤ √(2 * csC * (1 - 0.011)) := le_sqrt_of_sq_le (by linarith)
    unfold restAllowance
    gcongr
  unfold momentAllowance
  linarith

end BstLean.BlueprintLow
