import BstLean.Part81Final1b
import BstLean.Part81Final2
import BstLean.Part81Final3b
import BstLean.Part81FinalU

/-!
# Part 81: Theorem 4 at `d_f = 2`, every map degree `d_M ≥ 1`, uniform `D`, with a threshold that
does not grow with `d_M`

Role: `delegations/statements/p81-spec.md`.
* `N81 d`: `8200` at `d = 1`, `5400` at `d = 2`, `6700` at `d = 3`, `8200` at `d ≥ 4`.
* `part81_gen`: the theorem for every `d ≥ 1` and every `n ≥ N81 d`.
* `N81_le`: `N81 d ≤ 8200`. `part81_unif`: every `d ≥ 1`, every `n ≥ 8200`.
The four cases are `part81_12` (`Part81Final1b`), `part81_22` (`Part81Final2`), `part81_32`
(`Part81Final3b`), `part81_ge4` (`Part81FinalU`).
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59

/-- The dimension threshold at map degree `d` (and `d_f = 2`, `ε = 1/2`, failure `1/100`). -/
def N81 (d : ℕ) : ℕ := if d = 2 then 5400 else if d = 3 then 6700 else 8200

theorem N81_le (d : ℕ) : N81 d ≤ 8200 := by
  unfold N81; split_ifs <;> norm_num

/-- **Theorem 4 at `d_f = 2`, every map degree `d ≥ 1`, uniform `D`, `ε = 1/2`, failure
`≤ 1/100`, every `n ≥ N81 d`.** -/
theorem part81_gen :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, N81 d ≤ n → ∃ pg : Prog (In59 n d 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d 2 → ℝ, pg.eval v () = g0Q n d 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro d hd n hn
  by_cases h1 : d = 1
  · subst h1; exact part81_12 n (by simpa [N81] using hn)
  by_cases h2 : d = 2
  · subst h2; exact part81_22 n (by simpa [N81] using hn)
  by_cases h3 : d = 3
  · subst h3; exact part81_32 n (by simpa [N81] using hn)
  · exact part81_ge4 d (by omega) n (by simpa [N81, h2, h3] using hn)

/-- **One threshold for every map degree**: `d ≥ 1`, `n ≥ 8200`. The threshold at `d_f = 2` does
not grow with the map degree. -/
theorem part81_unif :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 8200 ≤ n → ∃ pg : Prog (In59 n d 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d 2 → ℝ, pg.eval v () = g0Q n d 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) :=
  fun d hd n hn => part81_gen d hd n ((N81_le d).trans hn)

end BstLean.Part81

#print axioms BstLean.Part81.part81_12
#print axioms BstLean.Part81.part81_22
#print axioms BstLean.Part81.part81_32
#print axioms BstLean.Part81.part81_ge4
#print axioms BstLean.Part81.part81_gen
#print axioms BstLean.Part81.part81_unif
