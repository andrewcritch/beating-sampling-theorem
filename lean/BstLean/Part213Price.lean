import Mathlib.Analysis.SpecialFunctions.Pow.Real
import BstLean.Part130Defs

/-! The scalar RA16 factors satisfy their moment-price guards exactly. -/
namespace BstLean.Part213
open Real

/-- This is the square of the paper's location correction factor at order sixteen. -/
noncomputable def locationR16 (n : ℝ) : ℝ := 2 * (715 : ℝ) ^ (1 / 8 : ℝ) / n

/-- This is the paper's energy correction factor at order sixteen. -/
noncomputable def energyR16 (n : ℝ) : ℝ := 2 * (1216070380 : ℝ) ^ (1 / 16 : ℝ) / n

lemma root_nat_power {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : k ≠ 0) :
    (a ^ ((k : ℝ)⁻¹)) ^ k = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha,
    inv_mul_cancel₀ (by exact_mod_cast hk : (k : ℝ) ≠ 0), Real.rpow_one]

theorem location_price16 {n : ℝ} (hn : 0 < n) :
    715 * (n ^ 2) ^ 4 * 2 ^ 8 = (n ^ 2 * locationR16 n) ^ 8 := by
  have hroot : ((715 : ℝ) ^ (1 / 8 : ℝ)) ^ 8 = 715 := by
    simpa [one_div] using root_nat_power (by norm_num : (0 : ℝ) ≤ 715)
      (by decide : (8 : ℕ) ≠ 0)
  have he : n ^ 2 * locationR16 n = 2 * n * (715 : ℝ) ^ (1 / 8 : ℝ) := by
    unfold locationR16
    field_simp [hn.ne'] <;> ring
  rw [he, mul_pow, hroot]
  ring

theorem energy_price16 {n : ℝ} (hn : 0 < n) :
    1216070380 * (n ^ 2) ^ 8 * 2 ^ 16 = (n ^ 2 * energyR16 n) ^ 16 := by
  have hroot : ((1216070380 : ℝ) ^ (1 / 16 : ℝ)) ^ 16 = 1216070380 := by
    simpa [one_div] using root_nat_power (by norm_num : (0 : ℝ) ≤ 1216070380)
      (by decide : (16 : ℕ) ≠ 0)
  have he : n ^ 2 * energyR16 n = 2 * n * (1216070380 : ℝ) ^ (1 / 16 : ℝ) := by
    unfold energyR16
    field_simp [hn.ne'] <;> ring
  rw [he, mul_pow, hroot]
  ring

/-- The width is the actual Agent width, including every frontier dimension. -/
theorem location_price_network {n : ℕ} (hn : 1 ≤ n) :
    715 * (BstLean.Part130.mA n : ℝ) ^ 4 * 2 ^ 8 =
      ((BstLean.Part130.mA n : ℝ) * locationR16 n) ^ 8 := by
  simpa [BstLean.Part130.mA] using
    location_price16 (show (0 : ℝ) < n by exact_mod_cast (by omega : 0 < n))

theorem energy_price_network {n : ℕ} (hn : 1 ≤ n) :
    1216070380 * (BstLean.Part130.mA n : ℝ) ^ 8 * 2 ^ 16 =
      ((BstLean.Part130.mA n : ℝ) * energyR16 n) ^ 16 := by
  simpa [BstLean.Part130.mA] using
    energy_price16 (show (0 : ℝ) < n by exact_mod_cast (by omega : 0 < n))

#print axioms location_price_network
#print axioms energy_price_network
end BstLean.Part213
