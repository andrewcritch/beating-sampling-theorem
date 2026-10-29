import BstLean.Part292Events
import BstLean.Part253Exp

/-! A rational cap for the four low-band suppliers. This numerical theorem
does not replace the proofs that the actual moments satisfy these caps. -/
namespace BstLean.Part292
open Real

noncomputable def momentCap (i : Fin 4) : ℝ :=
  ![277 / 10000, 635 / 100000, 1074 / 10000, 575 / 100000] i

theorem momentCap_nonneg (i : Fin 4) : 0 ≤ momentCap i := by
  fin_cases i <;> norm_num [momentCap]

theorem firstLayerCharge_bound : firstLayerCharge ≤ 112346 / 10^9 := by
  have he12 := BstLean.Part253.exp_minus_twelve_upper
  have he18 : exp (-18 : ℝ) ≤ 153 / 10^10 := by
    simpa only [Nat.cast_ofNat] using BstLean.Part253.exp_negative_bound 18
      (by norm_num : ((2.71828 : ℝ) ^ 18)⁻¹ ≤ 153 / 10^10)
  unfold firstLayerCharge
  linarith

theorem tableCharge_cap : tableCharge momentCap < 699108 / 10^9 := by
  have hnum : (112346 / 10^9 : ℝ) +
      (momentCap 0 / tableAllowance 0) ^ 24 +
      (momentCap 1 / tableAllowance 1) ^ 104 +
      (momentCap 2 / tableAllowance 2) ^ 18 +
      (momentCap 3 / tableAllowance 3) ^ 104 < 699108 / 10^9 := by
    norm_num [momentCap, tableAllowance]
  have he : tableCharge momentCap = firstLayerCharge +
      (momentCap 0 / tableAllowance 0) ^ 24 +
      (momentCap 1 / tableAllowance 1) ^ 104 +
      (momentCap 2 / tableAllowance 2) ^ 18 +
      (momentCap 3 / tableAllowance 3) ^ 104 := by
    simp [tableCharge, Fin.sum_univ_succ, tableOrder, add_assoc]
  rw [he]
  linarith [firstLayerCharge_bound]

theorem tableCharge_mono {B C : Fin 4 → ℝ} (hB : ∀ i, 0 ≤ B i)
    (hBC : ∀ i, B i ≤ C i) : tableCharge B ≤ tableCharge C := by
  unfold tableCharge
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (div_nonneg (hB i) (tableAllowance_pos i).le)
    (div_le_div_of_nonneg_right (hBC i) (tableAllowance_pos i).le) _

theorem tableCharge_lt_of_caps {B : Fin 4 → ℝ} (hB : ∀ i, 0 ≤ B i)
    (hcap : ∀ i, B i ≤ momentCap i) : tableCharge B < 699108 / 10^9 :=
  (tableCharge_mono hB hcap).trans_lt tableCharge_cap

theorem tableCharge_le_budget {B : Fin 4 → ℝ} (hB : ∀ i, 0 ≤ B i)
    (hcap : ∀ i, B i ≤ momentCap i) : tableCharge B ≤ 706 / 10^6 :=
  (tableCharge_lt_of_caps hB hcap).le.trans (by norm_num)

end BstLean.Part292

/-- info: 'BstLean.Part292.tableCharge_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.tableCharge_cap
