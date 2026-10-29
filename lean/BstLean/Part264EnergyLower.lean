import BstLean.Part264FiniteCentre
import BstLean.Part253EnergyLower

/-! Uniform lower energy and centre-certificate guards on the local noise window. -/
namespace BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206

theorem gMinus_lower {n : ℕ} (hn : 12225 ≤ n) : (0.99886685 : ℝ) ≤ gMinus n := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hns : (12225 : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (by norm_num) hnR 2
  have hi : 2 / (n : ℝ)^2 ≤ 2 / (12225 : ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hns
  have hs : (0.9999999933 : ℝ) ≤ √(1 - 2 / (n : ℝ)^2) :=
    le_sqrt_of_sq_le (by linarith)
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hd : 2 * √(12 : ℝ) / n ≤ 2 * (3.464102 : ℝ) / 12225 := by gcongr
  unfold gMinus
  nlinarith

theorem gPlus_upper {n : ℕ} (hn : 12225 ≤ n) : BstLean.Part211.gPlus n ≤ 1.00113378 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part211.gPlus
  calc
    _ ≤ (1 + 2 * (3.464102 : ℝ) / 12225)^2 := by gcongr
    _ ≤ (1.00113378 : ℝ) := by norm_num

theorem gPlus_lower (n : ℕ) : (1 : ℝ) ≤ BstLean.Part211.gPlus n := by
  unfold BstLean.Part211.gPlus
  have h : 0 ≤ 2 * √(12 : ℝ) / n := by positivity
  nlinarith

theorem energy_root_guard {n : ℕ} (hn : 12225 ≤ n) :
    2 * √(12 : ℝ) / n < √(1 - 2 / (n : ℝ)^2) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hns : (12225 : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (by norm_num) hnR 2
  have hi : 2 / (n : ℝ)^2 ≤ 2 / (12225 : ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hns
  have hs : (0.9999999933 : ℝ) ≤ √(1 - 2 / (n : ℝ)^2) := le_sqrt_of_sq_le (by linarith)
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hd : 2 * √(12 : ℝ) / n ≤ 2 * (3.464102 : ℝ) / 12225 := by gcongr
  linarith

theorem mean_lower_window {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (0.46 : ℝ) 0.532) :
    (0.76589 : ℝ) ≤ meanLowerRoot n θ ∧ meanLowerRoot n θ ≤ 1 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi : 2 / (n : ℝ)^2 ≤ 2 / (12225 : ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hnR 2)
  have hd : 8 * θ / n ≤ 8 * (0.532 : ℝ) / 12225 := by gcongr <;> exact hw.2
  have hk : (0.58781269 : ℝ) ≤ kappa (0.468 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := 0.883728465) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (0.468 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by have := hw.2; linarith,
      by have := hw.1; linarith⟩) (by have := hw.2; linarith)
  have hk1 := (kappa_mem (by have := hw.2; linarith : -1 ≤ 1 - θ)
    (by have := hw.1; linarith : 1 - θ ≤ 1)).2
  have hs : (0.766457 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / n - 2 / (n : ℝ)^2) :=
    le_sqrt_of_sq_le (by linarith)
  have hs1 : √(kappa (1 - θ) - 8 * θ / n - 2 / (n : ℝ)^2) ≤ 1 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h0 : 0 ≤ 8 * θ / n := by have := hw.1; positivity
    have h1 : 0 ≤ 2 / (n : ℝ)^2 := by positivity
    linarith
  have ht : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have htail : 2 * √(12 : ℝ) / n ≤ 2 * (3.464102 : ℝ) / 12225 := by gcongr
  have ht0 : 0 ≤ 2 * √(12 : ℝ) / n := by positivity
  unfold meanLowerRoot
  constructor <;> linarith

theorem energy_lower_data {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (0.46 : ℝ) 0.532) :
    0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ)^2 ∧
    (0.81583 : ℝ) ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ)^2)) -
      2 * √(12 * BstLean.Part211.gPlus n) / n - finiteEnergy n n (11 / 1000) / √(n : ℝ) ∧
    (0.665 : ℝ) ≤ energyLower n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) θ := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hi : 2 / (n : ℝ)^2 ≤ 2 / (12225 : ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hnR 2)
  have hm := mean_lower_window hn hw
  have hg := gPlus_upper hn
  have hg1 := gPlus_lower n
  have hgm := gMinus_lower hn
  have hr : (0.58592 : ℝ) ≤ meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n := by
    apply (le_div_iff₀ (by linarith : 0 < BstLean.Part211.gPlus n)).mpr
    nlinarith
  have hr1 : meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < BstLean.Part211.gPlus n)).mpr
    nlinarith
  have hk : (0.6674 : ℝ) ≤ kappa (0.58592 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := 0.810368899) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (0.58592 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith, hr1⟩) hr
  have hbr : (0.6674 : ℝ) - 2 / 12225 ^ 2 ≤
      kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ)^2 := by linarith
  have hs : (0.81648 : ℝ) ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ)^2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hgm hbr (by norm_num : (0 : ℝ) ≤ 0.6674 - 2 / 12225 ^ 2)
      (by linarith : 0 ≤ gMinus n)
    linarith
  have ht : √(12 * BstLean.Part211.gPlus n) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have htail : 2 * √(12 * BstLean.Part211.gPlus n) / n ≤ 2 * (3.466066 : ℝ) / 12225 := by gcongr
  have hnr : (110.566721 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hf := finite_centre_upper hn
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy n n (11 / 1000) / √(n : ℝ) ≤ 0.008646 / 110.566721 := by gcongr
  have hb : (0.81583 : ℝ) ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ)^2)) -
      2 * √(12 * BstLean.Part211.gPlus n) / n - finiteEnergy n n (11 / 1000) / √(n : ℝ) := by linarith
  refine ⟨le_trans (by norm_num) hbr, hb, ?_⟩
  unfold energyLower
  nlinarith

theorem plow_lower {n : ℕ} (hn : 12225 ≤ n) :
    (0.56048 : ℝ) ≤ BstLean.Part154.plow n 0.011 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold BstLean.Part154.plow
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12225) := by norm_num
    _ ≤ _ := by gcongr

theorem finite_guard {n : ℕ} (hn : 12225 ≤ n) :
    finiteEnergy n n 0.011 / √(n : ℝ) < BstLean.Part154.plow n (11 / 1000) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : (110.566721 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hf : finiteEnergy n n 0.011 ≤ 0.008646 := by
    convert finite_centre_upper hn using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  have hd : finiteEnergy n n 0.011 / √(n : ℝ) ≤ 0.008646 / 110.566721 := by gcongr
  have hp : (0.56048 : ℝ) ≤ BstLean.Part154.plow n (11 / 1000) := by
    convert plow_lower hn using 1 <;> norm_num
  exact hd.trans_lt (lt_of_lt_of_le (by norm_num) hp)

end BstLean.Part264
