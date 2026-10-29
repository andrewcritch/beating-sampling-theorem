import BstLean.Part291SourceEvents
import BstLean.Part252Operator
import BstLean.Part277Instances

namespace BstLean.BlueprintLow
open Real MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part215 BstLean.Part222

/-- The existing order-160 operator event also controls the actual fourth moment. -/
theorem Xi4_on_operator_event {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) {a : AgentPair n}
    (ha : a ∈ operatorEvent c τ η δ) :
    Xi4 a.1 a.2 c τ ≤ operatorXiAllowance c τ η δ :=
  BstLean.Part252.fourth_on_operator_event c τ η hδ ha

theorem agentXi4Band {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {a : AgentPair n} (ha : a ∈ agentCentreEvent c τ) :
    Xi4 a.1 a.2 c τ ≤ 1.269 * (2 / (n : ℝ)) / n := by
  have hop : BstLean.Part219.operatorAllowance c τ 0.006
      (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ 1.269 := by
    convert BstLean.Part277.operator_allowance_8000 hn c hτ using 1 <;> norm_num
  rcases ha with ⟨⟨_, ⟨_, hOp⟩⟩, _⟩
  have hOp' : a ∈ operatorEvent c τ 0.006 (ENNReal.ofReal (1 / 20000)) := by
    simpa only [show (6 / 1000 : ℝ) = 0.006 by norm_num] using hOp
  have hXi : Xi4 a.1 a.2 c τ ≤ BstLean.Part222.operatorXiAllowance c τ 0.006
      (ENNReal.ofReal (1 / 20000)) :=
    Xi4_on_operator_event c τ 0.006 (by norm_num) hOp'
  have hcap : BstLean.Part222.operatorXiAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ≤
      1.269 * (2 / (n : ℝ)) / n :=
    BstLean.Part222.operatorXiAllowance_le (n := n) c τ 0.006 1.269 _ hop
  exact hXi.trans hcap

end BstLean.BlueprintLow
