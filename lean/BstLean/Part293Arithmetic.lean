import BstLean.Part289SmallTable

/-! The actual finite table needs an arithmetic comparison only in odd dimension. -/
namespace BstLean.Part293
open Real BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part272 BstLean.Part289

structure ArithmeticInputs {n : ℕ} (c : Ret n) : Prop where
  energy_pos : 0 < eR c
  output_norm : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * 1.081
  location : ∀ g, g ≤ Js n - 1 →
    |passFSt c g - passF c g| ≤ 8 * ((1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5) * n
  energy : ∀ g, g ≤ Js n - 1 →
    |passWSt c g - passW c g| ≤ 130 * ((1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5) * (n : ℝ) ^ 2
  exact_location : ∀ g, g ≤ Js n - 1 → |passF c g| ≤ 9 * n

theorem arithmetic_comparison {n : ℕ} (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (P : Odd n → ArithmeticInputs c) :
    |√(qTilde (statedDesign2 n) t c) -
      √(qTilde (idealDesignFloor n (scaleFloor n)) t c)| ≤ 1 / 10 ^ 20 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [statedDesign2_even (by omega) he]
    norm_num
  · have S := P ho
    have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
    have hu := paper_small_parameter (show 1 ≤ n by omega)
    exact odd_root_of_small_tables (by omega) t c hu.1 hu.2 (by norm_num)
      (by linarith : (1.081 : ℝ) ≤ n) S.energy_pos S.output_norm
      S.location S.energy S.exact_location

end BstLean.Part293

/-- info: 'BstLean.Part293.arithmetic_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.arithmetic_comparison
