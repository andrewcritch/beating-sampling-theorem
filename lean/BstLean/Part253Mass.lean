import BstLean.Part222AllowanceOrders
import Mathlib.Analysis.Real.Pi.Bounds

/-! Rational certificates for the order-twenty-four mass formula. -/
namespace BstLean.Part253
open Real

noncomputable def rotationPowerCap : ℝ :=
  (3.14159265358979323847 / 2) ^ 24 * 316234143225

theorem rotation_power_le : BstLean.Part195.rotationConstant 12 ^ 24 ≤ rotationPowerCap := by
  have h := BstLean.Part195.rotationConstant_pow (by norm_num : 1 ≤ 12) (by norm_num)
  have hg : BstLean.Part162.gmom (2 * 12) = 316234143225 := by
    rw [BstLean.Part162.gmom_even]
    norm_num [Finset.prod_range_succ]
  rw [hg] at h
  rw [h]
  unfold rotationPowerCap
  gcongr
  exact pi_lt_d20.le

theorem rotation_sixteen_le : BstLean.Part195.rotationConstant 16 ≤ 5.4477338763354130 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num)
  have h := BstLean.Part195.rotationConstant_pow (by norm_num : 1 ≤ 16) (by norm_num)
  have hg : BstLean.Part162.gmom (2 * 16) = 191898783962510625 := by
    rw [BstLean.Part162.gmom_even]
    norm_num [Finset.prod_range_succ]
  rw [hg] at h
  rw [h]
  calc
    _ ≤ ((3.14159265358979323847 : ℝ) / 2) ^ 32 * 191898783962510625 := by
      gcongr
      exact pi_lt_d20.le
    _ ≤ (5.4477338763354130 : ℝ) ^ 32 := by norm_num

theorem energy_allowance_le : BstLean.Part222.energyAllowance 12225 ≤ 0.001718175627 := by
  rw [BstLean.Part222.energyAllowance_formula (by norm_num)]
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 1.3627217491968550 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num)
    have he := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 20000)
      (by norm_num : (32 : ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at he
    rw [he]
    norm_num
  have hs : √(2 : ℝ) ≤ 1.4142135623730951 := sqrt_le_iff.mpr (by norm_num)
  have hl : BstLean.Part222.paperLayerAllowance 12225 ≤ 0.000630221973914 := by
    unfold BstLean.Part222.paperLayerAllowance
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ 5.4477338763354130 * 1.4142135623730951 / 12225 +
          5 / (2 * (12225 : ℝ) ^ 2) := by
        gcongr
        exact rotation_sixteen_le
      _ ≤ _ := by norm_num
  have h0 : 0 ≤ BstLean.Part222.paperLayerAllowance 12225 := by
    unfold BstLean.Part222.paperLayerAllowance
    exact add_nonneg (div_nonneg
      (mul_nonneg (BstLean.Part195.rotationConstant_nonneg _) (sqrt_nonneg _)) (by norm_num))
      (by norm_num)
  calc
    _ ≤ (1.3627217491968550 : ℝ) *
        (2 * 0.000630221973914 + 0.000630221973914 ^ 2) := by gcongr
    _ ≤ (0.001718175627 : ℝ) := by norm_num

/-- Squared rational endpoints certify the actual square-root gap. -/
theorem gap_lower {E xi u d a b q : ℝ}
    (ha : 0 ≤ a) (hE : E ≤ a ^ 2) (hb : 0 ≤ b) (hxi : xi / 12225 ≤ b ^ 2)
    (_hq : 0 ≤ q) (hs : (q + a + b) ^ 2 ≤ (1 - u) ^ 2 - d) :
    q ≤ √((1 - u) ^ 2 - d) - (√E + √(xi / 12225)) := by
  have h1 : √E ≤ a := sqrt_le_iff.mpr ⟨ha, hE⟩
  have h2 : √(xi / 12225) ≤ b := sqrt_le_iff.mpr ⟨hb, hxi⟩
  have h3 : q + a + b ≤ √((1 - u) ^ 2 - d) :=
    le_sqrt_of_sq_le hs
  linarith

/-- All high powers in the final premise are powers of rational numbers. -/
theorem mass_bound_rational {M H xi E u d a b q beta : ℝ}
    (_hM : 0 ≤ M) (ha : 0 ≤ a) (hE : E ≤ a ^ 2)
    (hb : 0 ≤ b) (hxi : xi / 12225 ≤ b ^ 2) (hq : 0 < q)
    (hs : (q + a + b) ^ 2 ≤ (1 - u) ^ 2 - d)
    (hscalar : (12225 : ℝ) * ((H / u) ^ 32 +
      rotationPowerCap * (M / 12225) ^ 12 / q ^ 24) ≤ beta) :
    BstLean.Part222.massBoundOrder 12225 12 M H xi E u d ≤ beta := by
  have hg := gap_lower ha hE hb hxi hq.le hs
  have hgp : 0 < √((1 - u) ^ 2 - d) - (√E + √(xi / 12225)) := hq.trans_le hg
  apply le_trans ?_ hscalar
  unfold BstLean.Part222.massBoundOrder
  norm_num only [Nat.cast_ofNat, Nat.reduceMul]
  gcongr
  · unfold rotationPowerCap
    positivity
  · exact rotation_power_le

end BstLean.Part253
