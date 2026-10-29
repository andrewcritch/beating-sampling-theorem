import BstLean.Part247Numeric
import BstLean.Part245Charge
import BstLean.Part182TImono

/-! Part 247: actual fixed-pair TI hypotheses with the repaired caps and charge. -/
namespace BstLean.Part247
open MeasureTheory Real BstLean.Part130 BstLean.Part182 BstLean.Part244
open BstLean.Part238 (TI3_hyp)

theorem eta_exponent {n : ℕ} (hn : 11883 ≤ n) :
    (46 : ℝ) ≤ 2 * eta ^ 2 * (mA n : ℝ) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11883) hnR 2
  rw [en_M]
  norm_num [eta] at *
  nlinarith

theorem charge_bound {n : ℕ} (hn : 11883 ≤ n) :
    53 * exp (-46) + 12 * exp (-2 * eta ^ 2 * (mA n : ℝ)) ≤
      65 * exp (-46) := by
  have h := Real.exp_le_exp.mpr (show -2 * eta ^ 2 * (mA n : ℝ) ≤ -46 by
    linarith [eta_exponent hn])
  linarith

theorem badmass_bound :
    (65 * exp (-46)) / (1 / 3400) ≤ (24 / 10 ^ 16 : ℝ) := by
  have h := BstLean.Part245.sharp_badmass_3400 (n := 11883) (by norm_num)
  rwa [BstLean.Part245.sharp_charge_eq (by norm_num : 0 < (11883 : ℕ))] at h

theorem wide_TI3 {n : ℕ} (hn : 11883 ≤ n) :
    TI3_hyp n (34 / 100) (73 / 100) (663 / 1000) (35 / 1000) (40 / 100)
      (65 * exp (-46)) := by
  have h := ta_TI3_sharp (by omega : 2 ≤ n) (by norm_num : (0 : ℝ) ≤ 34 / 100)
    (by norm_num : (73 / 100 : ℝ) < 1) (by norm_num [eta] : 0 ≤ eta)
    (by norm_num : (0 : ℝ) ≤ 46) (wide_num hn)
  intro x x' hx hx' hlo hhi
  exact (h x x' hx hx' hlo hhi).trans (charge_bound hn)

theorem core_TI3 {n : ℕ} (hn : 11883 ≤ n) :
    TI3_hyp n (40 / 100) (63 / 100) (595 / 1000) (35 / 1000) (25 / 100)
      (65 * exp (-46)) := by
  have h := ta_TI3_sharp (by omega : 2 ≤ n) (by norm_num : (0 : ℝ) ≤ 40 / 100)
    (by norm_num : (63 / 100 : ℝ) < 1) (by norm_num [eta] : 0 ≤ eta)
    (by norm_num : (0 : ℝ) ≤ 46) (core_num hn)
  intro x x' hx hx' hlo hhi
  exact (h x x' hx hx' hlo hhi).trans (charge_bound hn)

theorem wide_TI {n : ℕ} (hn : 11883 ≤ n) :
    TI_hyp n (34 / 100) (73 / 100) (67 / 100) (65 * exp (-46)) :=
  TI_hyp_mono wide_lam le_rfl
    (TI_hyp_of_TI3 (by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (wide_TI3 hn))

theorem core_TI {n : ℕ} (hn : 11883 ≤ n) :
    TI_hyp n (40 / 100) (63 / 100) (60 / 100) (65 * exp (-46)) :=
  TI_hyp_mono core_lam le_rfl
    (TI_hyp_of_TI3 (by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (core_TI3 hn))

end BstLean.Part247
