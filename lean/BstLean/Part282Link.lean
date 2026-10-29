import BstLean.Part282All

/-!
# Part 282 (C2), the programs against the corrected schedule

Each verified program costs at most its entry of `orderedWork''` (`Part282Count`):

* `draw_cost_le`: latitude + node selection (comparisons) + hit ≤ `drawWork''`;
* `node_cost_eq` (even `n ≥ 4`): `nodeProg` = `nodeWork''`;
* `out_cost_eq`: `outProg draws` = `outWork'' draws`;
* `agent_cost_le`: `agentProg` ≤ `agentWork''`;

and `paperCount''_lt` bounds the whole schedule.
-/

namespace BstLean.Part282

open BstLean.Part130 BstLean.Part189 BstLean.Part279 BstLean.Part157

theorem draw_cost_le {n : ℕ} (hn : 1 ≤ n) (L H s : ℝ) :
    (latProg (n - 1)).cost + (selectNode (Js n) L H s).2 + (hitProg n (mF n)).cost ≤
      (drawWork'' n).cost := by
  have h := selectNode_count (Js n) L H s
  rw [latProg_cost, hitProg_cost, drawWork''_cost hn]
  simp only [Js, gridNodes] at h ⊢
  omega

theorem node_cost_eq {n : ℕ} (hn : 4 ≤ n) (he : n % 2 = 0) :
    (nodeProg n).cost = (nodeWork'' n).cost := by
  have hJ : BstLean.Part169.Jz n = conditionalSigns n := rfl
  have e : n ^ 2 + (n ^ 2 - 1) = 2 * n ^ 2 - 1 := by
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  rw [nodeProg_cost (by omega)]
  simp only [nodeWork'', chain, Work.cost, sphereRowWork'', if_pos he, evenRow''_cost,
    matVecWork_cost, twoMomentAtom_cost, hJ, e]
  ring

theorem out_cost_eq : (outProg draws).cost = (outWork'' draws).cost := by
  rw [outProg_cost]
  simp [outWork'', Work.cost]

theorem agent_cost_le {n : ℕ} (hn : 1 ≤ n) : (agentProg n).cost ≤ (agentWork'' n).cost := by
  have h1 := agentWork_cost hn
  have h2 := agentReference_cost hn
  rw [agentProg_cost hn]
  simp only [agentWork'', Work.cost, mul_one]
  omega

/-- info: 'BstLean.Part282.draw_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms draw_cost_le
/-- info: 'BstLean.Part282.node_cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms node_cost_eq
/-- info: 'BstLean.Part282.agent_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agent_cost_le

end BstLean.Part282
