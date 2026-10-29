import BstLean.Part189Baseline
import BstLean.Part150Prog4

/-!
Part 189: connections to existing executable cost definitions.
The Agent connection concerns the Part 150 reference pass. It does not
identify that pass with all the stored data of the Theorem 7 program.
-/

namespace BstLean.Part189
open BstLean.Part130
noncomputable section

theorem agentReference_cost {n : ℕ} (hn : 1 ≤ n) :
    (BstLean.Part150.passProg n (n ^ 2) n).cost + (2 * n + 9) = agentAllowance n := by
  rw [BstLean.Part150.passProg_cost_paper hn, BstLean.Part150.CA45, agentAllowance]
  ring

theorem classifierReference_cost {n : ℕ} (hn : 1 ≤ n) :
    (mlpProg n (mF n) 1).cost + 2 = classifierAllowance n := by
  rw [mlpProg_cost_eq]
  have h := mlpCost_formula (k := n) (q := 1) hn (one_le_mF hn)
  unfold classifierAllowance
  ring_nf at h ⊢
  omega

/-- The comparison consumes one operation; the allowance has one extra operation. -/
theorem classifierReference_le {n : ℕ} (hn : 1 ≤ n) :
    (mlpProg n (mF n) 1).cost + 1 ≤ classifierAllowance n := by
  have h := classifierReference_cost hn
  omega

end
end BstLean.Part189
