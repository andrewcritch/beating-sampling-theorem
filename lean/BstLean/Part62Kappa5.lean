import BstLean.Part62HyperK

/-!
# Part 62: the criterion at `κ = 5` for degrees `4` and `6`

`KCrit 4 5 γ5` and `KCrit 6 5 γ5` with `γ5 = (1.74, 3.88, 9.65, 25.3, 68.3, 187.6)`: rational
upper bounds of `√(E He_c⁴)/c!`, `c = 1..6`, from the exact moments `E4 c` (`Part62HermK.He4_eq`).
So `E P⁴ ≤ 5⁸ (E P²)²` at degree `≤ 4` and `E P⁴ ≤ 5¹² (E P²)²` at degree `≤ 6`
(`fourth_moment_5_4`, `fourth_moment_5_6`).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part62

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom)

/-- Rational upper bounds of `√(E He_c⁴)/c!` for `c = 1..6`. -/
noncomputable def γ5 : ℕ → ℝ
  | 1 => 174 / 100
  | 2 => 388 / 100
  | 3 => 965 / 100
  | 4 => 253 / 10
  | 5 => 683 / 10
  | 6 => 1876 / 10
  | _ => 0

lemma γ5_nonneg (c : ℕ) : 0 ≤ γ5 c := by
  unfold γ5; split <;> norm_num

lemma hco_tab1 : hco 1 0 = 0 ∧ hco 1 1 = 1 := by
  refine ⟨?_, ?_⟩ <;> norm_num [hco, Nat.factorial]

set_option maxHeartbeats 8000000 in
lemma E4_1 : E4 1 ≤ (1 : ℝ) ^ 2 * (174 / 100) ^ 2 := by
  obtain ⟨h0, h1⟩ := hco_tab1
  simp only [E4, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1]
  norm_num [gaussMom, Nat.doubleFactorial]

lemma hco_tab2 : hco 2 0 = -1 ∧ hco 2 1 = 0 ∧ hco 2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [hco, Nat.factorial]

set_option maxHeartbeats 8000000 in
lemma E4_2 : E4 2 ≤ (2 : ℝ) ^ 2 * (388 / 100) ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := hco_tab2
  simp only [E4, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]
  norm_num [gaussMom, Nat.doubleFactorial]

lemma hco_tab3 : hco 3 0 = 0 ∧ hco 3 1 = -3 ∧ hco 3 2 = 0 ∧ hco 3 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hco, Nat.factorial]

set_option maxHeartbeats 8000000 in
lemma E4_3 : E4 3 ≤ (6 : ℝ) ^ 2 * (965 / 100) ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := hco_tab3
  simp only [E4, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3]
  norm_num [gaussMom, Nat.doubleFactorial]

lemma hco_tab4 : hco 4 0 = 3 ∧ hco 4 1 = 0 ∧ hco 4 2 = -6 ∧ hco 4 3 = 0 ∧ hco 4 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hco, Nat.factorial]

set_option maxHeartbeats 8000000 in
lemma E4_4 : E4 4 ≤ (24 : ℝ) ^ 2 * (253 / 10) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hco_tab4
  simp only [E4, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4]
  norm_num [gaussMom, Nat.doubleFactorial]

lemma hco_tab5 : hco 5 0 = 0 ∧ hco 5 1 = 15 ∧ hco 5 2 = 0 ∧ hco 5 3 = -10 ∧ hco 5 4 = 0 ∧ hco 5 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hco, Nat.factorial]

set_option maxHeartbeats 8000000 in
lemma E4_5 : E4 5 ≤ (120 : ℝ) ^ 2 * (683 / 10) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hco_tab5
  simp only [E4, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5]
  norm_num [gaussMom, Nat.doubleFactorial]

lemma hco_tab6 : hco 6 0 = -15 ∧ hco 6 1 = 0 ∧ hco 6 2 = 45 ∧ hco 6 3 = 0 ∧ hco 6 4 = -15 ∧ hco 6 5 = 0 ∧ hco 6 6 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hco, Nat.factorial]

set_option maxHeartbeats 8000000 in
lemma E4_6 : E4 6 ≤ (720 : ℝ) ^ 2 * (1876 / 10) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hco_tab6
  simp only [E4, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6]
  norm_num [gaussMom, Nat.doubleFactorial]

lemma E4_le_γ5 (c : ℕ) (hc : c ∈ Finset.Icc 1 6) :
    ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤ (c.factorial : ℝ) ^ 2 * γ5 c ^ 2 := by
  rw [He4_eq]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hc
  interval_cases c
  · simpa [γ5] using E4_1
  · simpa [γ5, Nat.factorial] using E4_2
  · simpa [γ5, Nat.factorial] using E4_3
  · simpa [γ5, Nat.factorial] using E4_4
  · simpa [γ5, Nat.factorial] using E4_5
  · simpa [γ5, Nat.factorial] using E4_6

lemma kcrit5_4 : KCrit 4 5 γ5 := by
  refine ⟨by norm_num, γ5_nonneg, fun c hc => E4_le_γ5 c ?_, ?_⟩
  · have := Finset.mem_Icc.mp hc; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  · norm_num [Finset.sum_Icc_succ_top, γ5]

lemma kcrit5_6 : KCrit 6 5 γ5 := by
  refine ⟨by norm_num, γ5_nonneg, fun c hc => E4_le_γ5 c hc, ?_⟩
  norm_num [Finset.sum_Icc_succ_top, γ5]

/-- `E P⁴ ≤ 5⁸ (E P²)²` for polynomials of degree `≤ 4`. -/
theorem fourth_moment_5_4 : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    P.totalDegree ≤ 4 →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        5 ^ 8 * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 :=
  fourth_moment_kappa 4 5 γ5 kcrit5_4

/-- `E P⁴ ≤ 5¹² (E P²)²` for polynomials of degree `≤ 6`. -/
theorem fourth_moment_5_6 : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    P.totalDegree ≤ 6 →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        5 ^ 12 * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 :=
  fourth_moment_kappa 6 5 γ5 kcrit5_6

end BstLean.Part62
