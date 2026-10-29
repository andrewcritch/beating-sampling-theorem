import BstLean.Part279All

/-!
# Part 282 (C2), the corrected count

The programs of Part 282 cost more than some entries of `Part279.orderedWork'`:

* even sphere row: `6P + 58` operations, `P = (n − 4)/2` (`Part282Row.rowProg_cost`), against
  `3n + 29` (`sphereRowWork'`): the branches without branching cost more;
* node pass after the rows: `6M + 6` more operations than `nodeWork'` (`Part282Node.nodeTail_cost`):
  the sums `Σe`, `Σa²`, `Σβb`, `Σβ₂` and the scalars are not in `nodeWork'`;
* one draw: the latitude (`2n + 4`), at most `Nat.log 2 J_s + 2` comparisons
  (`Part282Draw.selectNode_count`), the hit program (`3n + 11 + mlpCost n m_F 1`), against
  `drawWork'` (the hit test is three operations, not one comparison);
* the output: `(k − 1) + 8` operations (`Part282Out.outProg_cost`) against `k + 4`.

* the global Agent pass: `n²` divisions more than `agentWork` (`Part282Agent.agentProg_cost`).

`orderedWork''` is `orderedWork'` with these entries replaced (the odd sphere row, the World
pass, the Agent pass and the setup are those of Part 279). `orderedWork''_le`: its cost is at most
that of the Part 189 schedule, so `paperCount''_lt`: it is below `1.0003·2n⁷` for `n ≥ 8000`.
-/

namespace BstLean.Part282

open BstLean.Part130 BstLean.Part189 BstLean.Part279

noncomputable section

/-- The even row of `Part282Row.rowProg`: three Horner loops (`2P` each) and 58 operations. -/
def evenRow'' (n : ℕ) : Work :=
  .thenDo (.repeat (3 * ((n - 4) / 2)) (ops [.mul, .add])) (.repeat 58 (.op .mul))

theorem evenRow''_cost (n : ℕ) : (evenRow'' n).cost = 6 * ((n - 4) / 2) + 58 := by
  simp [evenRow'', Work.cost, ops_cost]; ring

def sphereRowWork'' (n : ℕ) : Work := if n % 2 = 0 then evenRow'' n else sphereRowWork' n

theorem sphereRowWork''_le (n : ℕ) : (sphereRowWork'' n).cost + 11 ≤ (sphereRowWork n).cost := by
  unfold sphereRowWork''
  by_cases he : n % 2 = 0
  · rw [if_pos he, evenRow''_cost, sphereRowWork_even he]; omega
  · rw [if_neg he, sphereRowWork'_odd he, sphereRowWork_odd he]; omega

/-- One node: the rows, then the node pass after the rows (`Part282Node.nodeTail`). -/
def nodeWork'' (n : ℕ) : Work := chain [
  .repeat (n ^ 2) (sphereRowWork'' n),
  matVecWork (n ^ 2) (n ^ 2),
  .repeat (n ^ 2) (.repeat (conditionalSigns n + 1) twoMomentAtom),
  .repeat (6 * n ^ 2 + 6) (.op .add)]

def gridWork'' (n : ℕ) : Work := .repeat (gridNodes n) (nodeWork'' n)

theorem nodeWork''_le {n : ℕ} (hn : 3 ≤ n) :
    (nodeWork'' n).cost + 4 * n ^ 2 ≤ (nodeWork n).cost := by
  have h := sphereRowWork''_le n
  have h4 : 6 ≤ n ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left (n ^ 2) h
  simp only [nodeWork'', nodeWork, chain, Work.cost, twoMomentAtom_cost]
  nlinarith [hm, h4]

theorem gridWork''_le {n : ℕ} (hn : 3 ≤ n) :
    (gridWork'' n).cost + n ^ 2 ≤ (gridWork n).cost := by
  have h := Nat.mul_le_mul_left (gridNodes n) (nodeWork''_le hn)
  have hg : 1 ≤ gridNodes n := by unfold gridNodes; omega
  simp only [gridWork'', gridWork, Work.cost]
  nlinarith [h, hg]

/-- The Agent pass of `Part282Agent.agentProg`: `passProg` and `n²` divisions `b_j = b̃′_j/ρ`. -/
def agentWork'' (n : ℕ) : Work := .thenDo (agentWork n) (.repeat (n ^ 2) (.op .div))

/-- One draw: latitude, node selection, hit. -/
def drawWork'' (n : ℕ) : Work := chain [
  .repeat (2 * (n - 1) - 1 + 7) (.op .add),
  .repeat (Nat.log 2 (gridNodes n) + 2) (.op .compare),
  .repeat (3 * n + 11) (.op .mul),
  matVecWork (mF n) n, .repeat (mF n) (.op .relu),
  matVecWork (mF n) (mF n), .repeat (mF n) (.op .relu),
  matVecWork 1 (mF n)]

theorem drawWork''_cost {n : ℕ} (hn : 1 ≤ n) :
    (drawWork'' n).cost = 2 * (n - 1) - 1 + 7 + (Nat.log 2 (gridNodes n) + 2) + (3 * n + 11) +
      mlpCost n (mF n) 1 := by
  simp only [drawWork'', chain_cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Work.cost, matVecWork_cost, mlpCost]
  have hm := one_le_mF hn
  have e1 : n + (n - 1) = 2 * n - 1 := by omega
  have e2 : mF n + (mF n - 1) = 2 * mF n - 1 := by omega
  rw [e1, e2]
  ring

theorem drawWork''_lt {n : ℕ} (hn : 2 ≤ n) : (drawWork'' n).cost < (drawWork n).cost := by
  rw [drawWork''_cost (by omega), drawWork_cost]
  have hl := log_gridNodes_lt n
  have hc := BstLean.Part189.classifierReference_cost (n := n) (by omega)
  rw [mlpProg_cost_eq] at hc
  unfold drawAllowance
  omega

/-- The output: `k − 1` additions and 8 operations. -/
def outWork'' (k : ℕ) : Work := .thenDo (.repeat (k - 1) (.op .add)) (.repeat 8 (.op .sub))

def orderedWork'' (n : ℕ) : Work :=
  .thenDo (worldWork' n)
    (.thenDo (agentWork'' n)
      (.thenDo (setupWork' n)
        (.thenDo (gridWork'' n)
          (.thenDo (.repeat draws (drawWork'' n)) (outWork'' draws)))))

theorem orderedWork''_le {n : ℕ} (hn : 8000 ≤ n) :
    (orderedWork'' n).cost ≤ (orderedWork n).cost := by
  have h1 := worldWork'_le hn
  have h2 := setupWork'_le hn
  have h3 := gridWork''_le (by omega : 3 ≤ n)
  have h4 := drawWork''_lt (by omega : 2 ≤ n)
  have h5 : draws * (drawWork'' n).cost + draws ≤ draws * (drawWork n).cost := by
    have := Nat.mul_le_mul_left draws (Nat.succ_le_of_lt h4)
    rw [Nat.mul_succ] at this
    exact this
  have hd : 8 ≤ draws := by unfold draws; norm_num
  simp only [orderedWork'', orderedWork, outWork'', outputWork, agentWork'', Work.cost, ops_cost,
    List.length_cons, List.length_nil, mul_one]
  generalize n ^ 2 = q at h3 ⊢
  omega

theorem paperCount''_lt {n : ℕ} (hn : 8000 ≤ n) :
    ((orderedWork'' n).cost : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have h : ((orderedWork'' n).cost : ℝ) ≤ ((orderedWork n).cost : ℝ) := by
    exact_mod_cast orderedWork''_le hn
  have h2 := orderedWork_lt_8000 hn
  have h3 : (1.0003 : ℝ) = 10003 / 10000 := by norm_num
  rw [h3]
  exact lt_of_le_of_lt h h2

end

end BstLean.Part282

/-- info: 'BstLean.Part282.paperCount''_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.paperCount''_lt
