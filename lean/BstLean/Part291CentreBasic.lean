import BstLean.Part291Band
import BstLean.Part277Instances
import BstLean.Part253CentreConstants

/-! Uniform centre coefficients. Normalizing QB by rho squared avoids a
spurious factor from the ratio of the two dimension endpoints. -/
namespace BstLean.BlueprintLow
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem centreWnBand {n : ℕ} (hn : 8000 ≤ n) : 1 ≤ wn n ∧ wn n ≤ 1.045222 := by
  constructor
  · unfold wn
    have h : 0 ≤ 2 / √(n : ℝ) := by positivity
    nlinarith
  · exact BstLean.Part277.wn_upperP (n0 := 8000) (by norm_num) hn
      (r := 89.442719) (by norm_num) (by norm_num) (by norm_num)

theorem centreRhoBand {n : ℕ} (hn : LowBand n) :
    (0.00025 : ℝ) ≤ rhoBar n csC ∧ rhoBar n csC ≤ 0.000403496 := by
  have hw := centreWnBand hn.1
  have hwlo := hw.1
  have hwhi := hw.2
  have hw0 : 0 ≤ wn n := by linarith
  have hc := BstLean.Part253.cs_lower
  have hu := BstLean.Part253.cs_upper
  have hnl : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hnu : (n : ℝ) ≤ 11882 := by exact_mod_cast hn.2
  have hcp : 0 < csC := by linarith
  unfold rhoBar
  constructor
  · calc
      _ ≤ 4 / ((1.295212 : ℝ) * 11882) := by norm_num
      _ ≤ _ := by gcongr; linarith
  · calc
      _ ≤ 4 * (1.045222 : ℝ) / (1.29521 * 8000) := by gcongr
      _ ≤ _ := by norm_num

theorem centrePiSmall {ρ : ℝ} (hl : 0 < ρ) (hu : ρ ≤ 0.000403496) :
    piBar ρ ≤ (1 / 10 ^ 40 : ℝ) := by
  have hs : (0.999595 : ℝ) ≤ √(1 - 2 * ρ) := le_sqrt_of_sq_le (by linarith)
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √2 ≤ 0.707106782 := by
    calc
      _ ≤ (1 : ℝ) / 1.414213562 := by gcongr
      _ ≤ _ := by norm_num
  have he : (100 : ℝ) ≤ (√(1 - 2 * ρ) - 1 / √2) ^ 2 / (2 * ρ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * ρ)).mpr
    nlinarith
  have h := BstLean.Part253.exp_negative_bound 100
    (by norm_num : ((2.71828 : ℝ) ^ 100)⁻¹ ≤ 1 / 10 ^ 40)
  unfold piBar
  apply le_trans ?_ h
  apply exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  linarith

theorem normalizedCentreCoefficients {ρ : ℝ}
    (hl : (0.00025 : ℝ) ≤ ρ) (hu : ρ ≤ 0.000403496) :
    cc0 ρ (piBar ρ) ≤ 0.763829 * ρ ∧
    cc1 ρ (piBar ρ) ≤ 0.486025 * ρ ∧ cc2 ρ ≤ 0.282136 * ρ := by
  have hρ : 0 ≤ ρ := by linarith
  have hp := centrePiSmall (by linarith) hu
  have hp0 := piBar_nonneg ρ
  have hv0 : 0 ≤ nuR ρ := by unfold nuR; positivity
  have hv : nuR ρ ≤ 4.000404 * ρ := by unfold nuR; nlinarith
  have hv1 : nuR ρ ≤ 1 := by nlinarith
  have hs : √(ρ * nuR ρ) ≤ 2.000101 * ρ := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h := mul_le_mul_of_nonneg_left hv hρ
    nlinarith [sq_nonneg ρ]
  have hsp : √(piBar ρ * nuR ρ) ≤ (1 / 10 ^ 16 : ℝ) * ρ := by
    have h : √(piBar ρ * nuR ρ) ≤ (1 / 10 ^ 20 : ℝ) := by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      exact (mul_le_mul hp hv1 hv0 (by positivity)).trans (by norm_num)
    linarith
  have hsr : √(piBar ρ * ρ) ≤ (1 / 10 ^ 16 : ℝ) * ρ := by
    have h : √(piBar ρ * ρ) ≤ (1 / 10 ^ 20 : ℝ) := by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      exact (mul_le_mul hp (by linarith : ρ ≤ 1) hρ (by positivity)).trans (by norm_num)
    linarith
  have hz := BstLean.Part253.phi_zero_upper
  have ho := BstLean.Part253.phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  constructor
  · unfold cc0
    calc
      _ ≤ 0.399 * ρ / 2 + 0.399 * (4.000404 * ρ) / (2 * 1.414213562) +
          (3 / 2 : ℝ) * 0.399 * ((1 / 10 ^ 16) * ρ) := by gcongr
      _ ≤ 0.763829 * ρ := by norm_num; nlinarith only [hρ]
  constructor
  · unfold cc1
    calc
      _ ≤ 0.243 * (2.000101 * ρ) + 2 * ((1 / 10 ^ 16 : ℝ) * ρ) := by gcongr
      _ ≤ 0.486025 * ρ := by nlinarith
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * ρ / 1.414213562 := by gcongr
      _ ≤ 0.282136 * ρ := by norm_num; nlinarith only [hρ]

theorem normalizedQB {ρ : ℝ} (hl : (0.00025 : ℝ) ≤ ρ) (hu : ρ ≤ 0.000403496) :
    QB ρ (piBar ρ) ≤ 2.519668 * ρ ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := normalizedCentreCoefficients hl hu
  have hr : 0 ≤ ρ := by linarith
  have hp := piBar_nonneg ρ
  have hv : 0 ≤ nuR ρ := by unfold nuR; positivity
  have hz := (phiG_pos 0).le
  have ho := (phiG_pos 1).le
  have hc0 : 0 ≤ cc0 ρ (piBar ρ) := by unfold cc0; positivity
  have hc1 : 0 ≤ cc1 ρ (piBar ρ) := by unfold cc1; positivity
  have hc2 : 0 ≤ cc2 ρ := by unfold cc2; positivity
  have hpi : √(2 / π) ≤ (0.798 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ pi_pos).mpr
    linarith [pi_gt_d6]
  unfold QB
  calc
    _ ≤ (0.763829 * ρ) ^ 2 + (0.486025 * ρ) ^ 2 + 3 * (0.282136 * ρ) ^ 2 +
      2 * 0.798 * (0.763829 * ρ) * (0.486025 * ρ) +
      2 * (0.763829 * ρ) * (0.282136 * ρ) +
      4 * 0.798 * (0.486025 * ρ) * (0.282136 * ρ) := by gcongr
    _ ≤ 2.519668 * ρ ^ 2 := by nlinarith [sq_nonneg ρ]

theorem centreBnBand {n : ℕ} (hn : LowBand n) : bN n csC 0.528 ≤ 0.002245 := by
  have hw := centreWnBand hn.1
  have hr := centreRhoBand hn
  have hw0 : 0 ≤ wn n := by linarith [hw.1]
  have hwhi := hw.2
  have hrhi := hr.2
  have hp : 0 < rhoBar n csC := by linarith [hr.1]
  have hq := normalizedQB hr.1 hr.2
  unfold bN
  calc
    _ ≤ 4 * 0.528 * wn n * (2.519668 * rhoBar n csC ^ 2) / rhoBar n csC := by gcongr
    _ = 4 * 0.528 * wn n * 2.519668 * rhoBar n csC := by field_simp
    _ ≤ 4 * 0.528 * 1.045222 * 2.519668 * 0.000403496 := by gcongr
    _ ≤ (0.002245 : ℝ) := by norm_num

end BstLean.BlueprintLow
