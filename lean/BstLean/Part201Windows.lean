import BstLean.Part159Kap

/-! Part 201: sphere and kernel windows for every dimension from 4096. -/

namespace BstLean.Part201
open Real
open BstLean.Part130 BstLean.Part159
open BstLean.Part137 (cN)

theorem cN_even_window {n : ℕ} (hn : 4096 ≤ n) :
    1 / (13 * (n : ℝ)) ≤ cN (2 * n) ^ 2 ∧ cN (2 * n) ^ 2 ≤ 8 / (100 * (n : ℝ)) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨h1, h2⟩ := cN_sq_window (N := 2 * n) (by omega)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hNcast] at h1 h2
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  constructor
  · refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · refine h2.trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith


theorem rN_even_window {n : ℕ} (hn : 4096 ≤ n) :
    317 / 1000 ≤ 4 * (n : ℝ) * cN (2 * n) ^ 2 ∧
    4 * (n : ℝ) * cN (2 * n) ^ 2 < 31835 / 100000 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := rN_window (N := 2 * n) (by omega)
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hcast] at h1 h2
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d2
  have hd : 0 < π * (2 * (n : ℝ) - 1) := mul_pos Real.pi_pos (by linarith)
  constructor
  · have h : (317 / 1000 : ℝ) ≤ 1 / π := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith
    nlinarith
  · have h : 2 * (n : ℝ) / (π * (2 * (n : ℝ) - 1)) < 31835 / 100000 := by
      rw [div_lt_iff₀ hd]
      have hprod := mul_pos (sub_pos.mpr hp1) (by linarith : 0 < 2 * (n : ℝ) - 1)
      nlinarith
    nlinarith

theorem kap1_window {n : ℕ} (hn : 4096 ≤ n) :
    49372 / 100000 ≤ BstLean.Part140.kap1 (2 * n) ∧
    BstLean.Part140.kap1 (2 * n) ≤ 4938 / 10000 :=
  BstLean.Part140.kap1_window hn

end BstLean.Part201

#print axioms BstLean.Part201.cN_even_window
#print axioms BstLean.Part201.rN_even_window
#print axioms BstLean.Part201.kap1_window
