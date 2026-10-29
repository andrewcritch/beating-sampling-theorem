import BstLean.Part169Num
import BstLean.Part285IntervalTools

/-! Coarser existing finite-rule constants suffice at the lower dimension endpoint. -/
namespace BstLean.Part293
open Real BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem finite_rule_constants {J : ℕ} (hJ : 640000 ≤ J) :
    c1F (exp (1 / 2) / 12) J ≤ 19 / 100 ∧
      c2F (exp (1 / 2) / 12) J ≤ 9 / 100 := by
  have hJR : (640000 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hpi : (3.14 : ℝ) ≤ π ∧ π ≤ 3.1416 :=
    ⟨by linarith [pi_gt_d2], by linarith [pi_lt_d4]⟩
  have hs1 : 0 ≤ √(π / 2) ∧ √(π / 2) ≤ 1.254 :=
    ⟨sqrt_nonneg _, sqrt_le_iff.mpr ⟨by norm_num, by linarith [hpi.2]⟩⟩
  have hs2 : 0 ≤ √(2 * π) ∧ √(2 * π) ≤ 2.507 :=
    ⟨sqrt_nonneg _, sqrt_le_iff.mpr ⟨by norm_num, by linarith [hpi.2]⟩⟩
  have hsJ : 800 ≤ √(J : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hji : 0 ≤ (J : ℝ)⁻¹ ∧ (J : ℝ)⁻¹ ≤ 1 / 640000 := by
    refine ⟨inv_nonneg.mpr hJ0.le, ?_⟩
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 640000) hJR
  have hsi : 0 ≤ (√(J : ℝ))⁻¹ ∧ (√(J : ℝ))⁻¹ ≤ 1 / 800 := by
    refine ⟨inv_nonneg.mpr (sqrt_nonneg _), ?_⟩
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 800) hsJ
  have he : 0 ≤ exp (1 / 2 : ℝ) ∧ exp (1 / 2 : ℝ) ≤ 1.6488 :=
    ⟨(exp_pos _).le, BstLean.Part169.exp_half_le.trans (by norm_num)⟩
  have hex : 0 ≤ exp (-((J : ℝ) / 2)) ∧ exp (-((J : ℝ) / 2)) ≤ 1 :=
    ⟨(exp_pos _).le, exp_le_one_iff.mpr (by linarith)⟩
  unfold c1F c2F
  generalize √(π / 2) = p1 at *
  generalize √(2 * π) = p2 at *
  generalize exp (1 / 2 : ℝ) = eh at *
  generalize exp (-((J : ℝ) / 2)) = er at *
  generalize π = pi at *
  simp only [div_eq_mul_inv]
  generalize (J : ℝ)⁻¹ = ji at *
  generalize (√(J : ℝ))⁻¹ = si at *
  constructor <;> interval_num

theorem finite_rule_size {n : ℕ} (hn : 8000 ≤ n) : 640000 ≤ Jz n := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (81 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hceil : (n : ℝ) * √(n : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    rw [← rpow_three_halves]
    exact Nat.le_ceil _
  have hc : (640001 : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    nlinarith
  have hcN : 640001 ≤ ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by exact_mod_cast hc
  unfold Jz
  omega

theorem finite_rule_constants_band {n : ℕ} (hn : 8000 ≤ n) :
    c1F (exp (1 / 2) / 12) (Jz n) ≤ 19 / 100 ∧
      c2F (exp (1 / 2) / 12) (Jz n) ≤ 9 / 100 :=
  finite_rule_constants (finite_rule_size hn)

theorem finite_rule_denominator {n : ℕ} (hn : 8000 ≤ n) :
    (n : ℝ) * √(n : ℝ) - 1 ≤ (Jz n : ℝ) := by
  have hc : 1 ≤ ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hJ := finite_rule_size hn
    unfold Jz at hJ
    omega
  have h : (n : ℝ) * √(n : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    rw [← rpow_three_halves]
    exact Nat.le_ceil _
  unfold Jz
  rw [Nat.cast_sub hc]
  push_cast
  linarith

theorem finite_rule_ratio {n : ℕ} (hn : 8000 ≤ n) :
    ((n : ℝ) * √(n : ℝ)) / Jz n ≤
      1 / (1 - (1 / (n : ℝ)) * √(1 / (n : ℝ))) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (81 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hN : (0 : ℝ) < n := by linarith
  have hM : (1 : ℝ) < (n : ℝ) * √(n : ℝ) := by nlinarith
  have hJ := finite_rule_denominator hn
  calc
    _ ≤ ((n : ℝ) * √(n : ℝ)) / ((n : ℝ) * √(n : ℝ) - 1) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hJ
    _ = _ := by
      simp only [one_div, sqrt_inv]
      have hs0 : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hN).ne'
      field_simp [hN.ne', hs0, (sub_pos.mpr hM).ne'] <;> ring

end BstLean.Part293

/-- info: 'BstLean.Part293.finite_rule_constants_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.finite_rule_constants_band
