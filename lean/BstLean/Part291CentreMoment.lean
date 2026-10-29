import BstLean.Part291CentreBasic
import BstLean.Part291HS
import BstLean.Part269TailBounds

namespace BstLean.BlueprintLow
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem centreGammaBand {n : ℕ} (hn : 8000 ≤ n) :
    0 < gammaRatio n 0.011 0.528 ∧ gammaRatio n 0.011 0.528 ≤ 0.000139504 := by
  have hw := centreWnBand hn
  have hwl := hw.1
  have hwu := hw.2
  have hw0 : 0 < wn n := by linarith
  have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold gammaRatio
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.045222 : ℝ) * 0.528 / ((1 - 0.011) * 8000) := by gcongr
      _ ≤ _ := by norm_num

theorem centreFirstGap {ρ : ℝ} (hρ : ρ ≤ 0.000403496) :
    (0.105169208 : ℝ) ≤ gap 2 ρ 1.25 := by
  have hs : (0.9995964 : ℝ) ≤ √(1 - 2 * ρ) := le_sqrt_of_sq_le (by linarith)
  have hk : (1.118033988 : ℝ) ≤ √1.25 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.25 ≤ 0.894427192 := by
    calc
      _ ≤ (1 : ℝ) / 1.118033988 := by gcongr
      _ ≤ _ := by norm_num
  unfold gap
  linarith

theorem centreSecondGap {γ : ℝ} (hγ : γ ≤ 0.000139504) :
    (0.063344432 : ℝ) ≤ gap 1 γ 1.14 := by
  have hs : (0.999930245 : ℝ) ≤ √(1 - γ) := le_sqrt_of_sq_le (by linarith)
  have hk : (1.067707825 : ℝ) ≤ √1.14 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.14 ≤ 0.936585813 := by
    calc
      _ ≤ (1 : ℝ) / 1.067707825 := by gcongr
      _ ≤ _ := by norm_num
  unfold gap
  rw [one_mul]
  linarith

theorem centreExp137 : exp (-13.7 : ℝ) ≤ 0.000001122447 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.354315435980 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem centreExp1438 : exp (-14.38 : ℝ) ≤ 0.000000568651 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.456530527409 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem centreBadBand {n : ℕ} (hn : LowBand n) :
    badAllowance n csC 0.011 1.25 1.14 0.528 ≤ 0.019084 := by
  have hw := centreWnBand hn.1
  have hwu := hw.2
  have hw0 : 0 ≤ wn n := by linarith [hw.1]
  have hr := centreRhoBand hn
  have hg := centreGammaBand hn.1
  have hgap := centreFirstGap hr.2
  have hgapG := centreSecondGap hg.2
  have hnr : (n : ℝ) ≤ 11882 := by exact_mod_cast hn.2
  have ht1 : tail 2 (rhoBar n csC) 1.25 ≤ 0.000001122447 := by
    have he : (13.7 : ℝ) ≤ gap 2 (rhoBar n csC) 1.25 ^ 2 / (2 * rhoBar n csC) := by
      apply (le_div_iff₀ (by linarith [hr.1] : 0 < 2 * rhoBar n csC)).mpr
      nlinarith [hr.2]
    unfold tail
    apply le_trans ?_ centreExp137
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio n 0.011 0.528) 1.14 ≤ 0.000000568651 := by
    have he : (14.38 : ℝ) ≤ gap 1 (gammaRatio n 0.011 0.528) 1.14 ^ 2 /
        (2 * gammaRatio n 0.011 0.528) := by
      apply (le_div_iff₀ (by linarith [hg.1] : 0 < 2 * gammaRatio n 0.011 0.528)).mpr
      nlinarith [hg.2]
    unfold tail
    apply le_trans ?_ centreExp1438
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hk : (1.118033988 : ℝ) ≤ √1.25 := le_sqrt_of_sq_le (by norm_num)
  have hk3 : (1.067707825 : ℝ) ≤ √1.14 := le_sqrt_of_sq_le (by norm_num)
  have ht10 : 0 ≤ tail 2 (rhoBar n csC) 1.25 := by unfold tail; positivity
  have ht20 : 0 ≤ tail 1 (gammaRatio n 0.011 0.528) 1.14 := by unfold tail; positivity
  unfold badAllowance
  calc
    _ ≤ 1.045222 * (11882 : ℝ) *
        (0.000001122447 / 1.118033988 + 0.000000568651 / 1.067707825) := by gcongr
    _ ≤ (0.019084 : ℝ) := by norm_num

theorem centreLinearBand {n : ℕ} (hn : LowBand n) :
    linearAllowance n csC 0.528 ≤ 0.005326 := by
  have hw := centreWnBand hn.1
  have hwu := hw.2
  have hw0 : 0 ≤ wn n := by linarith [hw.1]
  have hr := centreRhoBand hn
  have hru := hr.2
  have hr0 : 0 ≤ rhoBar n csC := by linarith [hr.1]
  have hp := centrePiSmall (by linarith [hr.1]) hr.2
  have hp0 := piBar_nonneg (rhoBar n csC)
  have hv : nuR (rhoBar n csC) ≤ 0.001614147 := by unfold nuR; nlinarith [hr.1, hr.2]
  have hv0 : 0 ≤ nuR (rhoBar n csC) := by unfold nuR; positivity
  have hc := BstLean.Part253.cs_lower
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hn.1; omega)
  have he : rhoBar n csC * n = 4 * wn n / csC := by
    unfold rhoBar
    field_simp
  have hrn : rhoBar n csC * n ≤ 4 * (1.045222 : ℝ) / 1.29521 := by rw [he]; gcongr
  have hpi := pi_gt_d6.le
  unfold linearAllowance
  rw [show (6863 / 10000 : ℝ) * rhoBar n csC * n * nuR (rhoBar n csC) =
    (6863 / 10000 : ℝ) * (rhoBar n csC * n) * nuR (rhoBar n csC) by ring]
  calc
    _ ≤ 4 * (1.045222 : ℝ) * ((2 * 0.528 * 0.000403496 +
        (6863 / 10000) * (4 * 1.045222 / 1.29521) * 0.001614147) / 3.141592 +
        0.528 * (1 / 10 ^ 40)) := by gcongr
    _ ≤ (0.005326 : ℝ) := by norm_num

theorem centreRestBound : restAllowance csC 0.011 1.25 1.14 0.1826 ≤ 0.049488 := by
  have hc := BstLean.Part253.cs_lower
  have hk : K0 ≤ 0.090846 := by
    unfold K0
    apply (div_le_iff₀ (by positivity : 0 < 4 * π)).mpr
    linarith [pi_lt_d6]
  have hk0 : 0 ≤ K0 := by unfold K0; exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hs : √((1.25 : ℝ) * 1.14) ≤ 1.193734 := sqrt_le_iff.mpr (by norm_num)
  have ht : (1.600601 : ℝ) ≤ √(2 * csC * (1 - 0.011)) := le_sqrt_of_sq_le (by linarith)
  unfold restAllowance
  calc
    _ ≤ 4 * (0.090846 : ℝ) * 1.193734 * 0.1826 / 1.600601 := by gcongr
    _ ≤ (0.049488 : ℝ) := by norm_num

theorem centreMomentBand {n : ℕ} (hn : LowBand n) :
    momentAllowance n csC 0.011 1.25 1.14 0.528 0.1826 ≤ 0.0762 := by
  have h1 := centreRestBound
  have h2 := centreLinearBand hn
  have h3 := centreBnBand hn
  have h4 := centreBadBand hn
  unfold momentAllowance
  linarith

theorem centreMomentCertificate {n : ℕ} (hn : LowBand n) :
    MomentCertificate n 0.011 1.25 1.14 0.46 0.528 0.1826 (fun _ => 0.006) where
  delta_nonneg := by norm_num
  delta_lt := by norm_num
  k_gt := by norm_num
  k3_gt := by norm_num
  theta_lower := by norm_num
  v_pos := fun _ _ => by norm_num
  supremum := fun _ hw => hsProfileBand hn.1 hw
  ratio := by have h := centreRhoBand hn; linarith [h.2]
  ratio_gamma := (centreGammaBand hn.1).2.trans (by norm_num)
  gap := by have h := centreFirstGap (centreRhoBand hn).2; linarith
  gap_gamma := by have h := centreSecondGap (centreGammaBand hn.1).2; linarith

end BstLean.BlueprintLow
