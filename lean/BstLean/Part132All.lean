import BstLean.Part132Final

/-!
# Part 132: the finite-width mean of Theorem C

Role: `delegations/statements/p132-spec.md`. This module imports every file of Part 132 and states
the consequence for Part 131.

Files: `Part132Persp` (compositions of `κ`, supporting lines, the perspective function),
`Part132Layer` (the one-layer step), `Part132Net` (a whole network), `Part132Rows` (independent
rows), `Part132Num`, `Part132Quad` (bounds of `κ`), `Part132Defs`, `Part132Mean` (item 1),
`Part132Agent`, `Part132Cos`, `Part132World`, `Part132B2` (the lower bound of `b₂`),
`Part132Upper`, `Part132Cross`, `Part132Cross2` (the upper bound of `b₁₁`), `Part132Final`
(`meanJ132`).

* `thmC_of_var132`: `thmC_conditional_focus` of Part 131 at `r = 2`, `n ≥ 4 096`, with the first
  number supplied by `meanJ132`: Theorem C now follows from one number, an upper bound `V` of
  `Var J` with `1/16 ≤ (3/25)·j²/(j² + V)`, `j = (314/1000)·(4/n)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory
open BstLean.Part130 BstLean.Part131

universe w

/-- **Theorem C from the variance alone** (`r = 2`, the widths of the Focus, `n ≥ 4 096`). If
`Var J ≤ V` and `1/16 ≤ (3/25)·j²/(j² + V)` with `j = (314/1000)·(4/n)`, then the conclusion of
`thmC_conditional_focus` holds. -/
theorem thmC_of_var132 {n : ℕ} (hn : 4096 ≤ n) {V : ℝ}
    (hvar : Var[Jall; lawAll (2 * n) (mW n) n (mA n) (mF n)] ≤ V)
    (hjV : 1 / 16 ≤ 3 / 25 * ((314 / 1000 * (4 / (n : ℝ))) ^ 2 /
      ((314 / 1000 * (4 / (n : ℝ))) ^ 2 + V))) :
    MeasurableSet {x : MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1 |
      1 / 40 ≤ sepProbN (mA n) x.1 x.2} ∧
    1 / 26 ≤ (lawWF (2 * n) (mW n) n (mF n)).real {x | 1 / 40 ≤ sepProbN (mA n) x.1 x.2} ∧
    ∀ (W : MlpParam (2 * n) (mW n) n) (F : MlpParam n (mF n) 1), 1 / 40 ≤ sepProbN (mA n) W F →
      ∀ (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
        (c : Ω' → ℝ), Measurable c →
        1 / 80 ≤ ((mlpGauss n (mA n) n).prod ν).real
          {q : MlpParam n (mA n) n × Ω' | sdn W q.1 F / 2 < |c q.2 - Bn W q.1 F|} :=
  thmC_conditional_focus.{w} (r := 2) (by norm_num) (by omega) (meanJ132_pos hn) (meanJ132 hn)
    hvar hjV

end BstLean.Part132

open BstLean.Part132 in
#print axioms meanJ_eq
open BstLean.Part132 in
#print axioms relu_layer_lower
open BstLean.Part132 in
#print axioms lin_layer_lower
open BstLean.Part132 in
#print axioms b2_lower
open BstLean.Part132 in
#print axioms b11_upper
open BstLean.Part132 in
#print axioms b11_upper2
open BstLean.Part132 in
#print axioms kk_quad
open BstLean.Part132 in
#print axioms meanJ_lower2
open BstLean.Part132 in
#print axioms meanJ132
open BstLean.Part132 in
#print axioms thmC_of_var132
