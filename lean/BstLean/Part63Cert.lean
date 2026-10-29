import BstLean.Part63Final

/-!
# Part 63: numeric certificates for Theorem 4 (deliverable 3 of `p63-spec`)

At `K = 2`, `ε = 1/2`, failure `1/100`:

* `N59_22 : N59 2 2 2 (1/2) ≤ 10^105` (`(d_M, d_f) = (2, 2)`);
* `N59_33 : N59 3 3 2 (1/2) ≤ 10^198` (`(3, 3)`);
* `N59_13 : N59 1 3 2 (1/2) ≤ 10^195` (`(1, 3)`).

`part63_22`, `part63_33`, `part63_13` restate `part63_general` at these thresholds.
Each constant of the chain is first evaluated exactly (`CE63_22`, `CV63_22`, `C2_63_22`, …) with
`norm_num`. Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part63

open MeasureTheory BstLean.Cost
open BstLean.Part59
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono heavyCount)

lemma exp_Lam63 (K : ℝ) : Real.exp (Lam63 K) = 2 * (|K| + 1) := by
  unfold Lam63; rw [Real.exp_log (by positivity)]

/-- Evaluate a finite constant: filters, `erase 0`, `range`, `Icc`, factorials. -/
macro "eval63" : tactic => `(tactic| (
  simp (config := {decide := true}) only [← Finset.filter_ne', Finset.filter_filter, Finset.sum_filter,
    Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton] <;>
  norm_num [Nat.factorial, Nat.doubleFactorial]))

/-! ## Exact constants -/

lemma CE63_22 : CE63 2 2 2 = 259200 := by
  unfold CE63 BstLean.Part53.error53_correction_constant ErrorAux59x.mainConstant59x
    BstLean.Part53.FloorCorrection.correctionConstant BstLean.Part53.FloorCorrection.heatFactor
  simp only [exp_Lam63, Finset.sum_range_succ, Finset.sum_range_zero]
  eval63

lemma CE63_33 : CE63 3 3 2 = 28833120 := by
  unfold CE63 BstLean.Part53.error53_correction_constant ErrorAux59x.mainConstant59x
    BstLean.Part53.FloorCorrection.correctionConstant BstLean.Part53.FloorCorrection.heatFactor
  simp only [exp_Lam63, Finset.sum_range_succ, Finset.sum_range_zero]
  eval63

lemma CE63_13 : CE63 1 3 2 = 1727520 := by
  unfold CE63 BstLean.Part53.error53_correction_constant ErrorAux59x.mainConstant59x
    BstLean.Part53.FloorCorrection.correctionConstant BstLean.Part53.FloorCorrection.heatFactor
  simp only [exp_Lam63, Finset.sum_range_succ, Finset.sum_range_zero]
  eval63

lemma CV63_22 : CV63 2 2 2 = 14452140306548 := by
  unfold CV63 LV63 BstLean.Part53.FloorCorrection.correctionConstant
    BstLean.Part53.FloorCorrection.heatFactor
  eval63

lemma CF63_22 : FloorCorrection59x.totalCorrectionConstant 2 2 2 = 0 := by
  unfold FloorCorrection59x.totalCorrectionConstant FloorCorrection59x.correctionConstant
    FloorCorrection59x.heatFactor
  eval63

lemma nF63_22 : nF63 2 2 2 ≤ 26 := by
  unfold nF63
  rw [CF63_22]
  have h : ⌊max (2 * (max (2 : ℝ) 1 * BstLean.Part53.cG 2)) (8 * 0) + 1⌋₊ ≤ 25 :=
    Nat.floor_le_of_le (by norm_num [BstLean.Part53.cG, Nat.doubleFactorial])
  omega

lemma C2_63_22 : C2_63 2 2 2 = 6243844889479771728000 := by
  unfold C2_63 C2rad63
  rw [CV63_22]
  simp (config := {decide := true}) only [Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton, CR63, mR63]
  norm_num

lemma CV63_33 : CV63 3 3 2 = 2269669458930506180142858 := by
  unfold CV63 LV63 BstLean.Part53.FloorCorrection.correctionConstant
    BstLean.Part53.FloorCorrection.heatFactor
  eval63

lemma CF63_33 : FloorCorrection59x.totalCorrectionConstant 3 3 2 = 272160 := by
  unfold FloorCorrection59x.totalCorrectionConstant FloorCorrection59x.correctionConstant
    FloorCorrection59x.heatFactor
  eval63

lemma nF63_33 : nF63 3 3 2 ≤ 2177282 := by
  unfold nF63
  rw [CF63_33]
  have h : ⌊max (2 * (max (2 : ℝ) 1 * BstLean.Part53.cG 2)) (8 * 272160) + 1⌋₊ ≤ 2177281 :=
    Nat.floor_le_of_le (by norm_num [BstLean.Part53.cG, Nat.doubleFactorial])
  omega

lemma C2_63_33 : C2_63 3 3 2 = 13660229995367491353300670907991299988000 := by
  unfold C2_63 C2rad63
  rw [CV63_33]
  simp (config := {decide := true}) only [Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton, CR63, mR63]
  norm_num

lemma CV63_13 : CV63 1 3 2 = 392829991720997002422 := by
  unfold CV63 LV63 BstLean.Part53.FloorCorrection.correctionConstant
    BstLean.Part53.FloorCorrection.heatFactor
  eval63

lemma CF63_13 : FloorCorrection59x.totalCorrectionConstant 1 3 2 = 15120 := by
  unfold FloorCorrection59x.totalCorrectionConstant FloorCorrection59x.correctionConstant
    FloorCorrection59x.heatFactor
  eval63

lemma nF63_13 : nF63 1 3 2 ≤ 120962 := by
  unfold nF63
  rw [CF63_13]
  have h : ⌊max (2 * (max (2 : ℝ) 1 * BstLean.Part53.cG 2)) (8 * 15120) + 1⌋₊ ≤ 120961 :=
    Nat.floor_le_of_le (by norm_num [BstLean.Part53.cG, Nat.doubleFactorial])
  omega

lemma C2_63_13 : C2_63 1 3 2 = 2364286136412002459746402456666092000 := by
  unfold C2_63 C2rad63
  rw [CV63_13]
  simp (config := {decide := true}) only [Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton, CR63, mR63]
  norm_num

/-! ## The thresholds -/

/-- A sufficient condition for `N59 d k K ε ≤ B`. -/
lemma N59_le_of (d k : ℕ) (K ε : ℝ) (B : ℕ) (h100 : 100 ≤ B) (hc : 3 * k + 6 * d + 20 ≤ B)
    (hF : nF63 d k K ≤ B)
    (hA : Afail63 ε (tsb63 k (1 / 100 / 2) / 32) (C1_63 d k K) (C2_63 d k K) / (1 / 100 - 1 / 100 / 2)
      ≤ (B : ℝ) - 1) :
    N59 d k K ε ≤ B := by
  unfold N59 Nfail63 nfail63 n2_63
  have hceil : ⌈Afail63 ε (tsb63 k (1 / 100 / 2) / 32) (C1_63 d k K) (C2_63 d k K) /
      (1 / 100 - 1 / 100 / 2)⌉₊ ≤ B - 1 := by
    apply Nat.ceil_le.mpr
    have : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]; exact hA
  refine max_le (max_le (max_le (max_le (by omega) (max_le (max_le hF (by omega)) (by omega))) (by omega))
    hc) h100

/-- **Certificate**: `N59 2 2 2 (1/2) ≤ 10^105` (`(d_M, d_f) = (2, 2)`, `K = 2`, `ε = 1/2`). -/
theorem N59_22 : N59 2 2 2 (1 / 2) ≤ 10 ^ 105 := by
  apply N59_le_of
  · norm_num
  · norm_num
  · exact (nF63_22).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_22, C2_63_22]
    unfold tsb63 BstLean.Part62.tK
    norm_num

/-- **Certificate**: `N59 3 3 2 (1/2) ≤ 10^198` (`(d_M, d_f) = (3, 3)`, `K = 2`, `ε = 1/2`). -/
theorem N59_33 : N59 3 3 2 (1 / 2) ≤ 10 ^ 198 := by
  apply N59_le_of
  · norm_num
  · norm_num
  · exact (nF63_33).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_33, C2_63_33]
    unfold tsb63 BstLean.Part62.tK
    norm_num

/-- **Certificate**: `N59 1 3 2 (1/2) ≤ 10^195` (`(d_M, d_f) = (1, 3)`, `K = 2`, `ε = 1/2`). -/
theorem N59_13 : N59 1 3 2 (1 / 2) ≤ 10 ^ 195 := by
  apply N59_le_of
  · norm_num
  · norm_num
  · exact (nF63_13).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_13, C2_63_13]
    unfold tsb63 BstLean.Part62.tK
    norm_num

/-- **Theorem 4 at `(d_M, d_f) = (2, 2)`, `K = 2`, `ε = 1/2`, failure `1/100`, every `n ≥ 10^105`.** -/
theorem part63_22 :
    ∀ n : ℕ, 10 ^ 105 ≤ n → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 (1 / 2) ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ 2 →
        ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
          stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
            (1 / 2 : ℝ) ^ 2 * varP μ 2 c (unitOfD Z) <
              (BP μ 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := fun n hn =>
  (part63_general 2 2 (by norm_num) (by norm_num) 2 (1 / 2) (by norm_num)).2 n (N59_22.trans hn)

/-- **Theorem 4 at `(d_M, d_f) = (3, 3)`, `K = 2`, `ε = 1/2`, failure `1/100`, every `n ≥ 10^198`.** -/
theorem part63_33 :
    ∀ n : ℕ, 10 ^ 198 ≤ n → ∃ pg : Prog (In59 n 3 3) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 3 3 → ℝ, pg.eval v () = g0Q n 3 3 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 3 3 (1 / 2) ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ 2 →
        ∀ c : Mono n 3 → ℝ, TopNZ 3 c →
          stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
            (1 / 2 : ℝ) ^ 2 * varP μ 3 c (unitOfD Z) <
              (BP μ 3 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := fun n hn =>
  (part63_general 3 3 (by norm_num) (by norm_num) 2 (1 / 2) (by norm_num)).2 n (N59_33.trans hn)

/-- **Theorem 4 at `(d_M, d_f) = (1, 3)`, `K = 2`, `ε = 1/2`, failure `1/100`, every `n ≥ 10^195`.** -/
theorem part63_13 :
    ∀ n : ℕ, 10 ^ 195 ≤ n → ∃ pg : Prog (In59 n 1 3) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 1 3 → ℝ, pg.eval v () = g0Q n 1 3 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 1 3 (1 / 2) ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ 2 →
        ∀ c : Mono n 3 → ℝ, TopNZ 3 c →
          stdGauss (CoefIdxD n 1) {Z | Z ≠ 0 ∧
            (1 / 2 : ℝ) ^ 2 * varP μ 3 c (unitOfD Z) <
              (BP μ 3 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := fun n hn =>
  (part63_general 3 1 (by norm_num) (by norm_num) 2 (1 / 2) (by norm_num)).2 n (N59_13.trans hn)

end BstLean.Part63
