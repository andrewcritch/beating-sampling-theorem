import BstLean.Part66T4
import BstLean.Part66LevelOrd

/-!
# Part 66: Theorem 4 at the ordered-node level `tO`

`N59O d k K ε = N59t d k K ε (tO (2k) (1/200))`. Certificates at `K = 2`, `ε = 1/2`:
`10^59` (2,2), `10^96` (3,3), `10^92` (1,3). `part66T4O_general` instantiates
`Part66T4.part66T4_general_of` with `Part66LevelOrd.sb_level_ordered`.
Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part66

open MeasureTheory BstLean.Cost
open BstLean.Part59
open BstLean.Part63
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono heavyCount)

/-- The threshold of Theorem 4 at the ordered-node level `tO (2k) (1/200)`. -/
noncomputable def N59O (d k : ℕ) (K ε : ℝ) : ℕ := N59t d k K ε (tO (2 * k) (1 / 200))

/-- **Certificate**: `N59O 2 2 2 (1/2) ≤ 10^59`. -/
theorem N59O_22 : N59O 2 2 2 (1 / 2) ≤ 10 ^ 59 := by
  apply N59t_le_of
  · norm_num
  · norm_num
  · exact (nF63_22).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_22, C2_63_22]
    unfold tO
    norm_num [Nat.factorial]

/-- **Certificate**: `N59O 3 3 2 (1/2) ≤ 10^96`. -/
theorem N59O_33 : N59O 3 3 2 (1 / 2) ≤ 10 ^ 96 := by
  apply N59t_le_of
  · norm_num
  · norm_num
  · exact (nF63_33).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_33, C2_63_33]
    unfold tO
    norm_num [Nat.factorial]

/-- **Certificate**: `N59O 1 3 2 (1/2) ≤ 10^92`. -/
theorem N59O_13 : N59O 1 3 2 (1 / 2) ≤ 10 ^ 92 := by
  apply N59t_le_of
  · norm_num
  · norm_num
  · exact (nF63_13).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_13, C2_63_13]
    unfold tO
    norm_num [Nat.factorial]

/-- **Theorem 4 with the ordered-node threshold** `N59O d k K ε`. -/
theorem part66T4O_general (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε : ℝ) (hε : 0 < ε) :
    100 ≤ N59O d k K ε ∧ ∀ n : ℕ, N59O d k K ε ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) :=
  part66T4_general_of k d hd hk K ε hε _ (tO_pos _ _ (by norm_num))
    (sb_level_ordered (2 * k) (by omega) (1 / 200) (by norm_num))

/-- **Theorem 4 at `(2,2)`, `K = 2`, `ε = 1/2`, failure `1/100`, every `n ≥ 10^59`.** -/
theorem part66T4O_22 :
    ∀ n : ℕ, 10 ^ 59 ≤ n → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 (1 / 2) ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ 2 →
        ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
          stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
            (1 / 2 : ℝ) ^ 2 * varP μ 2 c (unitOfD Z) <
              (BP μ 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := fun n hn =>
  (part66T4O_general 2 2 (by norm_num) (by norm_num) 2 (1 / 2) (by norm_num)).2 n (N59O_22.trans hn)

/-- **Theorem 4 at `(3,3)`, `K = 2`, `ε = 1/2`, failure `1/100`, every `n ≥ 10^96`.** -/
theorem part66T4O_33 :
    ∀ n : ℕ, 10 ^ 96 ≤ n → ∃ pg : Prog (In59 n 3 3) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 3 3 → ℝ, pg.eval v () = g0Q n 3 3 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 3 3 (1 / 2) ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ 2 →
        ∀ c : Mono n 3 → ℝ, TopNZ 3 c →
          stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
            (1 / 2 : ℝ) ^ 2 * varP μ 3 c (unitOfD Z) <
              (BP μ 3 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := fun n hn =>
  (part66T4O_general 3 3 (by norm_num) (by norm_num) 2 (1 / 2) (by norm_num)).2 n (N59O_33.trans hn)

/-- **Theorem 4 at `(1,3)`, `K = 2`, `ε = 1/2`, failure `1/100`, every `n ≥ 10^92`.** -/
theorem part66T4O_13 :
    ∀ n : ℕ, 10 ^ 92 ≤ n → ∃ pg : Prog (In59 n 1 3) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 1 3 → ℝ, pg.eval v () = g0Q n 1 3 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 1 3 (1 / 2) ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ 2 →
        ∀ c : Mono n 3 → ℝ, TopNZ 3 c →
          stdGauss (CoefIdxD n 1) {Z | Z ≠ 0 ∧
            (1 / 2 : ℝ) ^ 2 * varP μ 3 c (unitOfD Z) <
              (BP μ 3 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := fun n hn =>
  (part66T4O_general 3 1 (by norm_num) (by norm_num) 2 (1 / 2) (by norm_num)).2 n (N59O_13.trans hn)

end BstLean.Part66
