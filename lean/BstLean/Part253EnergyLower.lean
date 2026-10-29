import BstLean.Part253FiniteCentre
import BstLean.Part182SNum

/-! A lower energy certificate for the computed centre throughout the source window. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206

theorem kappa_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  have ha0 : 0 ≤ arcsin q := arcsin_nonneg.mpr hq
  apply div_le_div₀ (by positivity : 0 ≤ √(1 - q ^ 2) + q * (π / 2 + arcsin q))
    ?_ pi_pos hp'
  exact add_le_add hroot (mul_le_mul_of_nonneg_left (by linarith) hq)

theorem gMinus_lower : (0.99886685 : ℝ) ≤ gMinus 12225 := by
  have hs : (0.9999999933 : ℝ) ≤ √(1 - 2 / (12225 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold gMinus
  simp only [Nat.cast_ofNat]
  have h : (0.9999999933 : ℝ) - 2 * 3.464102 / 12225 ≤
      √(1 - 2 / (12225 : ℝ) ^ 2) - 2 * √12 / 12225 := by linarith
  nlinarith

theorem gPlus_upper : BstLean.Part211.gPlus 12225 ≤ 1.00113378 := by
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part211.gPlus
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 * (3.464102 : ℝ) / 12225) ^ 2 := by gcongr
    _ ≤ (1.00113378 : ℝ) := by norm_num

theorem gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12225 := by
  unfold BstLean.Part211.gPlus
  have h := sqrt_nonneg (12 : ℝ)
  simp only [Nat.cast_ofNat]
  nlinarith

theorem mean_lower_window {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.532) :
    (0.76589 : ℝ) ≤ meanLowerRoot 12225 θ ∧ meanLowerRoot 12225 θ ≤ 1 := by
  have hk : (0.58781269 : ℝ) ≤ kappa (0.468 : ℝ) := by
    apply kappa_lower_rational (s := 0.883728465)
      <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (0.468 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by have := hw.2; linarith,
      by have := hw.1; linarith⟩) (by have := hw.2; linarith)
  have hk1 := (kappa_mem (by have := hw.2; linarith : -1 ≤ 1 - θ)
    (by have := hw.1; linarith : 1 - θ ≤ 1)).2
  have hs : (0.766457 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12225 -
      2 / (12225 : ℝ) ^ 2) := le_sqrt_of_sq_le (by have := hw.2; linarith)
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12225 - 2 / (12225 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by have := hw.1; linarith⟩
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_data {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.532) :
    0 ≤ kappa (meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225) - 2 / (12225 : ℝ) ^ 2 ∧
    (0.81583 : ℝ) ≤ √(gMinus 12225 *
      (kappa (meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225) - 2 / (12225 : ℝ) ^ 2)) -
      2 * √(12 * BstLean.Part211.gPlus 12225) / 12225 -
      finiteEnergy 12225 12225 (11 / 1000) / √12225 ∧
    (0.665 : ℝ) ≤ energyLower 12225 (gMinus 12225) (BstLean.Part211.gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) θ := by
  have hm := mean_lower_window hw
  have hg := gPlus_upper
  have hg1 := gPlus_lower
  have hgm := gMinus_lower
  have hr : (0.58592 : ℝ) ≤ meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225 := by
    apply (le_div_iff₀ (by linarith : 0 < BstLean.Part211.gPlus 12225)).mpr
    nlinarith
  have hr1 : meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225 ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < BstLean.Part211.gPlus 12225)).mpr
    nlinarith
  have hk : (0.6674 : ℝ) ≤ kappa (0.58592 : ℝ) := by
    apply kappa_lower_rational (s := 0.810368899)
      <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (0.58592 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225 ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith, hr1⟩) hr
  have hbr : (0.6674 : ℝ) - 2 / 12225 ^ 2 ≤
      kappa (meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225) - 2 / (12225 : ℝ) ^ 2 := by
    linarith
  have hs : (0.81648 : ℝ) ≤ √(gMinus 12225 *
      (kappa (meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225) - 2 / (12225 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hgm hbr (by norm_num : (0 : ℝ) ≤ 0.6674 - 2 / 12225 ^ 2)
      (by linarith : 0 ≤ gMinus 12225)
    linarith
  have ht : √(12 * BstLean.Part211.gPlus 12225) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12225 12225 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12225 12225 (11 / 1000) / √12225 ≤ 0.008646 / 110.566721 := by
    gcongr
  unfold energyLower
  simp only [Nat.cast_ofNat]
  have hb : (0.81583 : ℝ) ≤ √(gMinus 12225 *
      (kappa (meanLowerRoot 12225 θ ^ 2 / BstLean.Part211.gPlus 12225) - 2 / (12225 : ℝ) ^ 2)) -
      2 * √(12 * BstLean.Part211.gPlus 12225) / 12225 - finiteEnergy 12225 12225 (11 / 1000) / √12225 := by
    linarith
  refine ⟨le_trans (by norm_num) hbr, hb, ?_⟩
  nlinarith

theorem energy_lower_window {θ : ℝ} (hw : θ ∈ Icc (0.46 : ℝ) 0.532) :
    (0.665 : ℝ) ≤ energyLower 12225 (gMinus 12225) (BstLean.Part211.gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) θ := (energy_lower_data hw).2.2

end BstLean.Part253
