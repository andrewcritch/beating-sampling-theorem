import BstLean.Part201Kernel

/-! Part 201: the P10f constant package for every dimension from 4096. -/

namespace BstLean.Part201

open BstLean.Part130
open BstLean.Part137 (cN)
open BstLean.Part140 (kap1)
open BstLean.Part157 (cNt kapT)
open BstLean.Part159 (ConstC ConstK)

/-- All conclusions of P10f constants use the existing program constants. -/
theorem constants_4096 {n : ℕ} (hn : 4096 ≤ n) :
    (1 / (13 * (n : ℝ)) ≤ cN (2 * n) ^ 2 ∧
      cN (2 * n) ^ 2 ≤ 8 / (100 * (n : ℝ))) ∧
    (317 / 1000 ≤ 4 * (n : ℝ) * cN (2 * n) ^ 2 ∧
      4 * (n : ℝ) * cN (2 * n) ^ 2 < 31835 / 100000) ∧
    |cNt n - cN (2 * n)| ≤ cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ∧
    |kapT n - kap1 (2 * n)| ≤ 2 / (10 ^ 5 * (n : ℝ) ^ 2) ∧
    ConstC n ∧ ConstK n :=
  ⟨cN_even_window hn, rN_even_window hn,
    BstLean.Part159.cNt_close (by omega), kapT_close_strong hn, constC hn, constK hn⟩

end BstLean.Part201

#print BstLean.Part201.constants_4096
#print axioms BstLean.Part201.constants_4096
