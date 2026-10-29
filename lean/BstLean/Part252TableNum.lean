import BstLean.Part252Table
import BstLean.Part252PassEvent
import BstLean.Part169Num

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12225 ∧ √12225 ≤ 111 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12225 ∧ 1000000 ≤ Jz 12225 := by
  have hr : (1105 / 10 : ℝ) ≤ √12225 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12225 : ℝ) * √12225 ≤ (⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12225
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12225 : ℝ) = (⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12225 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12225 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12225) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12225 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12225 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12225 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12225 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12225 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12225 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12225) :
    (12225 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12225 * √(qB 12225))) ≤
      52 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12225 * √(qB 12225) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12225 : ℝ) * √(qB 12225) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12225) :
    (12225 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12225 * √(qB 12225))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12225 : ℝ) * √(qB 12225) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12225 : ℝ) * (√12225 *
      (c1F (exp (1 / 2) / 12) (Jz 12225) * (186 / 10000) / Jz 12225)) ≤
      358 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12225)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 111)
  have he : (12225 : ℝ) * (√12225 *
      (c1F (exp (1 / 2) / 12) (Jz 12225) * (186 / 10000) / Jz 12225)) =
      (12225 * (√12225 * c1F (exp (1 / 2) / 12) (Jz 12225)) * (186 / 10000)) /
        Jz 12225 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12225)]
  nlinarith

theorem row_energy_rule :
    (12225 : ℝ) * (12225 *
      (c2F (exp (1 / 2) / 12) (Jz 12225) * (186 / 10000) ^ 2 / Jz 12225)) ≤
      346 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12225)]
  nlinarith

end BstLean.Part252
