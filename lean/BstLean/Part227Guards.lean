import BstLean.Part227Window

/-! Part 227: uniform positive-denominator guards from dimension 4096. -/
namespace BstLean.Part227
open Real
open BstLean.Part130 BstLean.Part136 BstLean.Part140

theorem perturbation_small {n : ℕ} (hn : 4096 ≤ n) :
    0 ≤ perturbation n ∧ perturbation n ≤ 1 / 10 ^ 12 := by
  have hm := BstLean.Part137.mW_ge_pow42 hn
  have hm' : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast hm
  have hmp : (0 : ℝ) < mW n := by linarith
  constructor
  · unfold perturbation; positivity
  · unfold perturbation
    rw [div_le_iff₀ hmp]
    linarith only [hm']

theorem kernelError_small {n : ℕ} (hn : 4096 ≤ n) :
    0 ≤ kernelError n ∧ kernelError n ≤ 1 / 10 ^ 7 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  constructor
  · unfold kernelError; positivity
  · unfold kernelError
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hn', sq_nonneg ((n : ℝ) - 4096)]

/-- All three sign guards hold on the full frontier interval and beyond. -/
theorem window_guards {n : ℕ} (hn : 4096 ≤ n) {eB : ℝ} (heB : eB ≤ 1 / 100) :
    0 ≤ kap1 (2 * n) - eB ∧
      √(perturbation n) < √(kap1 (2 * n) - eB) ∧ kernelError n < kap1 (2 * n) := by
  obtain ⟨hk, _⟩ := BstLean.Part140.kap1_window hn
  obtain ⟨hp0, hp1⟩ := perturbation_small hn
  obtain ⟨_, hd1⟩ := kernelError_small hn
  have hL : 0 ≤ kap1 (2 * n) - eB := by linarith only [hk, heB]
  have hgap : perturbation n < kap1 (2 * n) - eB := by linarith only [hp1, hk, heB]
  exact ⟨hL, Real.sqrt_lt_sqrt hp0 hgap, by linarith only [hd1, hk]⟩

/-- A fixed enclosing product window is available without a finite dimension table. -/
theorem product_enclosure {n : ℕ} (hn : 4096 ≤ n) {eB : ℝ}
    (heB0 : 0 ≤ eB) (heB1 : eB ≤ 1 / 1000) :
    2 ≤ productLower n eB ∧ productUpper n eB ≤ 2060 / 1000 := by
  obtain ⟨hk1, hk2⟩ := BstLean.Part140.kap1_window hn
  obtain ⟨hp0, hp1⟩ := perturbation_small hn
  obtain ⟨hd0, hd1⟩ := kernelError_small hn
  have hkpos : 0 < kap1 (2 * n) := by linarith only [hk1]
  have hmpos : 0 < kap1 (2 * n) - kernelError n := by linarith only [hk1, hd1]
  have hp : √(perturbation n) ≤ 1 / 10 ^ 6 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num at hp1 ⊢; exact hp1⟩
  have hl : (7019 / 10000 : ℝ) ≤ √(kap1 (2 * n) - eB) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hk1, heB1]
  have hu : √(kap1 (2 * n) + eB) ≤ 704 / 1000 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith only [hk2, heB1]⟩
  have hnl : (7019 / 10000 - 1 / 10 ^ 6 : ℝ) ^ 2 ≤
      (√(kap1 (2 * n) - eB) - √(perturbation n)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith only [hl, hp]) 2
  have hnu : (√(kap1 (2 * n) + eB) + √(perturbation n)) ^ 2 ≤
      (704 / 1000 + 1 / 10 ^ 6 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hu, hp]) 2
  have hdu : (1001 / 1000) * (kap1 (2 * n) + kernelError n) ^ 2 ≤
      (1001 / 1000) * (493801 / 1000000 : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hk2, hd1]) 2
  have hdl : (999 / 1000) * (493719 / 1000000 : ℝ) ^ 2 ≤
      (999 / 1000) * (kap1 (2 * n) - kernelError n) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) (by linarith only [hk1, hd1]) 2
  constructor
  · unfold productLower
    rw [le_div_iff₀ (by positivity)]
    have hnum : (2 : ℝ) * ((1001 / 1000) * (493801 / 1000000) ^ 2) ≤
        (7019 / 10000 - 1 / 10 ^ 6) ^ 2 := by norm_num
    linarith only [hnl, hdu, hnum]
  · unfold productUpper
    rw [div_le_iff₀ (by positivity)]
    have hnum : (704 / 1000 + 1 / 10 ^ 6 : ℝ) ^ 2 ≤
        (2060 / 1000) * ((999 / 1000) * (493719 / 1000000) ^ 2) := by norm_num
    linarith only [hnu, hdl, hnum]

end BstLean.Part227
#print axioms BstLean.Part227.perturbation_small
#print axioms BstLean.Part227.kernelError_small
#print axioms BstLean.Part227.window_guards
#print axioms BstLean.Part227.product_enclosure
