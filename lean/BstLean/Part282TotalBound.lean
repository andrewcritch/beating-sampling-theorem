import BstLean.Part282Total

/-!
# Part 282 (C2): the sum of the block costs is below the bound (even `n ≥ 8000`)
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part189 BstLean.Part279

theorem totalCost_le_orderedWork {n : ℕ} (hn : 8000 ≤ n) (he : n % 2 = 0) :
    totalCost n draws ≤ (orderedWork n).cost := by
  have hW := world_cost_le (n := n) (by omega)
  have hA := agentProg_cost (n := n) (by omega)
  have hA1 := agentWork_cost (n := n) (by omega)
  have hA2 := agentReference_cost (n := n) (by omega)
  have hO := outProg_cost draws
  have hcost := orderedWork_cost n
  rw [worldWork_eq] at hcost
  simp only [Work.cost] at hcost
  -- draws
  have hD := draw_cost_le (n := n) (by omega) 0 1 0
  have hD2 := drawWork''_lt (n := n) (by omega)
  have hlat := latProg_cost (n - 1)
  have hhit := hitProg_cost n (mF n)
  have hdc := drawWork''_cost (n := n) (by omega)
  have hJs : Js n = gridNodes n := rfl
  have h1 : (latProg (n - 1)).cost + (Nat.log 2 (Js n) + 2) + (hitProg n (mF n)).cost <
      drawAllowance n := by
    rw [← drawWork_cost, hJs]; omega
  have hDr : draws * ((latProg (n - 1)).cost + (Nat.log 2 (Js n) + 2) + (hitProg n (mF n)).cost) +
      draws ≤ draws * drawAllowance n := by
    have := Nat.mul_le_mul_left draws (Nat.succ_le_of_lt h1)
    rw [Nat.mul_succ] at this
    exact this
  -- nodes
  have hN := node_cost_eq (n := n) (by omega) he
  have hN2 := nodeWork''_le (n := n) (by omega)
  have hGr : Js n * (nodeProg n).cost + n ^ 2 ≤ (gridWork n).cost := by
    have hg : (gridWork n).cost = gridNodes n * (nodeWork n).cost := rfl
    have h := Nat.mul_le_mul_left (gridNodes n) hN2
    have hx : n ^ 2 ≤ gridNodes n * (4 * n ^ 2) := by
      have : 1 ≤ gridNodes n := by unfold gridNodes; omega
      calc n ^ 2 = 1 * n ^ 2 := by ring
        _ ≤ gridNodes n * n ^ 2 := Nat.mul_le_mul_right _ this
        _ ≤ gridNodes n * (4 * n ^ 2) := Nat.mul_le_mul_left _ (by omega)
    rw [hN, hg, hJs, Nat.mul_add] at *
    omega
  -- setup
  have hR := rdProg_cost (n := n) (by omega)
  have hG := gridProg_cost n
  have hE := ebProg_cost n (by omega)
  have hS : (rdProg n).cost + (gridProg n).cost + (ebProg n).cost + 1 + n ^ 2 + 4 ≤
      setupAllowance n := by
    have h3 : n ^ 2 * (4 * n + 2) + 5 * n ^ 2 ≤ 100 * n ^ 3 := by
      have : n ^ 3 = n ^ 2 * n := by ring
      rw [this]; nlinarith
    have h5 : 12 * n + 15 + 5 * (512 * n) + 10 ≤ 100 * (512 * n) := by omega
    rw [hR, hG, hE]
    unfold setupAllowance
    rw [hJs]
    unfold gridNodes
    omega
  have hd : 8 ≤ draws := by unfold draws; norm_num
  unfold totalCost
  rw [hA, hO]
  omega

theorem totalCost_lt {n : ℕ} (hn : 8000 ≤ n) (he : n % 2 = 0) :
    (totalCost n draws : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have h : (totalCost n draws : ℝ) ≤ ((orderedWork n).cost : ℝ) := by
    exact_mod_cast totalCost_le_orderedWork hn he
  have h2 := orderedWork_lt_8000 hn
  have h3 : (1.0003 : ℝ) = 10003 / 10000 := by norm_num
  rw [h3]
  exact lt_of_le_of_lt h h2

end BstLean.Part282

/-- info: 'BstLean.Part282.totalCost_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.totalCost_lt
