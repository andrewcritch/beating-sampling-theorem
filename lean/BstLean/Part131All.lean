import BstLean.Part131ThmC

/-!
# Part 131: the probability step and the estimator consequence of Theorem C

Role: `delegations/statements/p131-spec.md`. This file imports every module of Part 131 and states
`thmC_conditional` at the widths of the Focus (`N = r·n`, `m_W = ⌈n^{7/2}⌉`, `m_A = n²`,
`m_F = ⌈n^{3/2}⌉`).

Modules: `Part131Tail` (the one-dimensional Gaussian tail), `Part131Block` (item 1),
`Part131Cantelli` (item 2), `Part131Estimator` (item 5, abstract), `Part131Fubini`,
`Part131Net` (item 3), `Part131Space` (the probability space, measurability),
`Part131Integrable` (`J` is in `L²`), `Part131ThmC` (items 4, 5, 6).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory
open BstLean.Part130

universe w

/-- **`thmC_conditional` at the widths of the Focus.** `r ≥ 1`, `n ≥ 1`; `W : ℝ^{rn} → ℝⁿ` with
hidden width `⌈n^{7/2}⌉`, `A` with hidden width `n²`, `F` with hidden width `⌈n^{3/2}⌉`. From two
numbers `j`, `V` with `E J ≥ j > 0`, `Var J ≤ V` and `(3/25)·j²/(j² + V) ≥ 1/16`: the set
`{(W, F) | Δ(W, F) ≥ 1/40}` has probability at least `1/26`, and for every `(W, F)` in it every
estimator that reads nothing of `A` fails at accuracy `1/2` with probability at least `1/80` over
`(A, ω)`. -/
theorem thmC_conditional_focus {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) {j V : ℝ} (hj : 0 < j)
    (hmean : j ≤ ∫ t, Jall t ∂lawAll (r * n) (mW n) n (mA n) (mF n))
    (hvar : Var[Jall; lawAll (r * n) (mW n) n (mA n) (mF n)] ≤ V)
    (hjV : 1 / 16 ≤ 3 / 25 * (j ^ 2 / (j ^ 2 + V))) :
    MeasurableSet {x : MlpParam (r * n) (mW n) n × MlpParam n (mF n) 1 |
      1 / 40 ≤ sepProbN (mA n) x.1 x.2} ∧
    1 / 26 ≤ (lawWF (r * n) (mW n) n (mF n)).real {x | 1 / 40 ≤ sepProbN (mA n) x.1 x.2} ∧
    ∀ (W : MlpParam (r * n) (mW n) n) (F : MlpParam n (mF n) 1), 1 / 40 ≤ sepProbN (mA n) W F →
      ∀ (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
        (c : Ω' → ℝ), Measurable c →
        1 / 80 ≤ ((mlpGauss n (mA n) n).prod ν).real
          {q : MlpParam n (mA n) n × Ω' | sdn W q.1 F / 2 < |c q.2 - Bn W q.1 F|} :=
  thmC_conditional.{w} hn (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
    hj hmean hvar hjV

end BstLean.Part131

open BstLean.Part131 in
#print axioms thmC_conditional_focus
