import BstLean.Part253Mass

namespace BstLean.Part263
open Real

noncomputable def layerBound (n : ℕ) : ℝ :=
  (54477338763354130 / 10 ^ 16 : ℝ) * (14142135623730951 / 10 ^ 16) / n +
    5 / (2 * (n : ℝ) ^ 2)

noncomputable def energyBound (n : ℕ) : ℝ :=
  (13627217491968550 / 10 ^ 16 : ℝ) * (2 * layerBound n + layerBound n ^ 2)

theorem energy_allowance_bound {n : ℕ} (hn : 1 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ energyBound n := by
  have hl : BstLean.Part222.paperLayerAllowance n ≤ layerBound n := by
    unfold BstLean.Part222.paperLayerAllowance layerBound
    gcongr
    · convert BstLean.Part253.rotation_sixteen_le using 1 <;> norm_num
    · exact sqrt_le_iff.mpr (by norm_num)
  have h0 : 0 ≤ BstLean.Part222.paperLayerAllowance n := by
    unfold BstLean.Part222.paperLayerAllowance
    exact add_nonneg (div_nonneg
      (mul_nonneg (BstLean.Part195.rotationConstant_nonneg _) (sqrt_nonneg _))
      (by positivity)) (by positivity)
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ (13627217491968550 / 10 ^ 16 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num)
    have he := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 20000)
      (by norm_num : (32 : ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at he
    rw [he]
    norm_num
  rw [BstLean.Part222.energyAllowance_formula hn]
  unfold energyBound
  gcongr

theorem paperLayerAllowance_mono {n : ℕ} (hn : 12225 ≤ n) :
    BstLean.Part222.paperLayerAllowance n ≤ BstLean.Part222.paperLayerAllowance 12225 := by
  have hnr : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  unfold BstLean.Part222.paperLayerAllowance
  gcongr
  exact mul_nonneg (BstLean.Part195.rotationConstant_nonneg _) (sqrt_nonneg _)

theorem energy_allowance_le {n : ℕ} (hn : 12225 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ (1718175627 / 10 ^ 12 : ℝ) := by
  have hmono : BstLean.Part222.energyAllowance n ≤ BstLean.Part222.energyAllowance 12225 := by
    rw [BstLean.Part222.energyAllowance_formula (by omega : 1 ≤ n),
      BstLean.Part222.energyAllowance_formula (by norm_num : 1 ≤ 12225)]
    have hl := paperLayerAllowance_mono hn
    have h0 : 0 ≤ BstLean.Part222.paperLayerAllowance n := by
      unfold BstLean.Part222.paperLayerAllowance
      exact add_nonneg (div_nonneg
        (mul_nonneg (BstLean.Part195.rotationConstant_nonneg _) (sqrt_nonneg _))
        (by positivity)) (by positivity)
    gcongr
  convert hmono.trans BstLean.Part253.energy_allowance_le using 1 <;> norm_num

end BstLean.Part263
