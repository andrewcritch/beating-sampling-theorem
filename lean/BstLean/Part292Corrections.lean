import BstLean.Part292ExactCaps
import BstLean.Part130Defs

/-! Exact-centering row corrections on the whole low band. -/
namespace BstLean.Part292
open Real BstLean.Part239 BstLean.Part130

theorem correction52_band {n : ℕ} (hn : 8000 ≤ n) :
    exactCorrection 52 (mA n) ≤ (9/2 : ℝ) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 64000000 ≤ mA n := by unfold mA; nlinarith
  have h := exact_partition_cap_52 (mA n) hm
  apply le_of_pow_le_pow_left₀ (by norm_num : (52 : ℕ) ≠ 0) (by positivity)
  rw [exactCorrection_pow (by norm_num), div_pow]
  calc
    _ ≤ ((9/2 : ℝ)^52 * (mA n : ℝ)^26) / (mA n : ℝ)^52 :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by
      simp only [mA, Nat.cast_pow, ← pow_mul]
      field_simp <;> ring

theorem correction104_band {n : ℕ} (hn : 8000 ≤ n) :
    exactCorrection 104 (mA n) ≤ (63/10 : ℝ) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 64000000 ≤ mA n := by unfold mA; nlinarith
  have h := exact_partition_cap_104 (mA n) hm
  apply le_of_pow_le_pow_left₀ (by norm_num : (104 : ℕ) ≠ 0) (by positivity)
  rw [exactCorrection_pow (by norm_num), div_pow]
  calc
    _ ≤ ((63/10 : ℝ)^104 * (mA n : ℝ)^52) / (mA n : ℝ)^104 :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by
      simp only [mA, Nat.cast_pow, ← pow_mul]
      field_simp <;> ring

end BstLean.Part292

/-- info: 'BstLean.Part292.correction104_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.correction104_band
