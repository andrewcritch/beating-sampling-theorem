import BstLean.Part154Meas

/-!
# Part 154: joint measurability of the event `GoodC` in `(c, τ)` and `(A₁, A₂)`
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150

/-- The family of the events `GoodC n n c τ`, as a set of `((c, τ), (A₁, A₂))`. -/
def SC8 (n : ℕ) :
    Set (((Fin n → ℝ) × ℝ) ×
      (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) :=
  {x | x.2 ∈ GoodC n n x.1.1 x.1.2}

theorem measurableSet_SC8 {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (SC8 n) :=
  measurableSet_SCgen hn

end BstLean.Part154
