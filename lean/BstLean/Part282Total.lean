import BstLean.Part282Top

/-!
# Part 282 (C2), the total count of the verified blocks, and the composed value (even `n`)

`totalCost n k`: the sum of the costs of the verified blocks of one run with `k` draws:
the World pass (`worldProg`), the Agent pass (`agentProg`), the row data (`rdProg`), the grid
(`gridProg`), `√e_b` (`ebProg`), `τ₀²` (one operation), `J_s` node passes (`nodeProg`), `k` draws
(latitude, at most `Nat.log 2 J_s + 2` comparisons, hit) and the output (`outProg`).
The bound of `totalCost` against the Part 189 schedule is NOT proved here (an attempt timed out;
see the report).

`progOut_composed` (even `n`): the output of the program, `progOut (statedDesign n)`, is the
output block applied to the hit blocks, each at the node selected by the latitude, with the stored
tables given by the node block. Together with `bWp_eq_worldProg`, `tau0p_eq_worldProg`,
`bAp_eq_agentProg`, `rdProg_alpha`, `rdProg_kappa`, `gridProg_s`, `gridProg_w`, `latProg_eval`,
`selectNode_eq`, every input of these blocks is a block output. What is NOT proved: one theorem
that substitutes all block outputs at once, in a model with a table read at a computed index.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part189 BstLean.Part279 BstLean.Part272
open BstLean.Part169 (A2 bR nodeS nodeL nodeH Jz)

noncomputable section

/-! ## `√e_b = √(|b|²/n)` -/

def ebProg (n : ℕ) : RProg (Fin (mA n)) Unit :=
  (RProg.ofProg (Prog.sumProd ((List.finRange (mA n)).map fun j => (Arg.inp j, Arg.inp j)))).bind
    (RExpr.sqrt (RExpr.div (.inp (Sum.inr ())) (.cst (n : ℚ)))).prog

theorem ebProg_eval {n : ℕ} (b : Fin (mA n) → ℝ) : (ebProg n).eval b () = √(normSq b / n) := by
  rw [ebProg, RProg.eval_bind, RExpr.eval_prog]
  simp only [RExpr.eval_sqrt, RExpr.eval_div, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr,
    RProg.eval_ofProg, eval_sumProd, List.map_map]
  rw [normSq, Fin.sum_univ_def]
  congr 2
  · congr 1
    apply List.map_congr_left
    intro j _
    simp [Arg.eval, pow_two]
  all_goals simp

theorem ebProg_cost (n : ℕ) (hn : 1 ≤ n) : (ebProg n).cost = 2 * n ^ 2 + 1 := by
  have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  simp [ebProg, cost_sumProd, mA]
  omega

/-- `worldProg` costs at most `worldTail` (the World pass of `worldWork'` without step 1;
`worldTail` also charges `ĉ = W₃b_W`, which `worldProg` does not compute). -/
theorem world_cost_le {n : ℕ} (hn : 1 ≤ n) :
    (worldProg (mW n) (2 * n) (JW n) (cQ n) (dQ n) (kapA n) (kapB n) (piQ n) n).cost ≤
      (worldTail n).cost := by
  have hm := one_le_mW hn
  have hJ : JW n = worldSigns n := rfl
  rw [worldProg_cost _ _ _ _ _ _ _ _ _ hm (by omega), hJ]
  simp only [worldTail, Work.cost, dotWork_cost, matVecWork_cost, binomialSetup_cost,
    sharedMean_cost, ops_cost, List.length_cons, List.length_nil]
  have e1 : 2 * n + (2 * n - 1) = 4 * n - 1 := by omega
  have e2 : mW n + (mW n - 1) = 2 * mW n - 1 := by omega
  have e3 : 2 * (2 * n) + 1 = 4 * n - 1 + 2 := by omega
  rw [e1, e2, e3]
  have h7 := worldSigns_ge hn
  have h8 : 2 * mW n - 1 ≤ n * (2 * mW n - 1) := Nat.le_mul_of_pos_left _ (by omega)
  simp only [Nat.zero_add, Nat.reduceAdd, mul_one] at *
  omega


/-! ## The total count -/

/-- The sum of the costs of the verified blocks for `k` draws (the node selection is counted by
its bound `Nat.log 2 J_s + 2`). -/
def totalCost (n k : ℕ) : ℕ :=
  (worldProg (mW n) (2 * n) (JW n) (cQ n) (dQ n) (kapA n) (kapB n) (piQ n) n).cost +
    (agentProg n).cost + (rdProg n).cost + (gridProg n).cost + (ebProg n).cost + 1 +
    Js n * (nodeProg n).cost +
    k * ((latProg (n - 1)).cost + (Nat.log 2 (Js n) + 2) + (hitProg n (mF n)).cost) +
    (outProg k).cost

/-! ## The composed value (even `n`) -/

/-- The inputs of the node block at node `g`. -/
def nodeIn {n : ℕ} (c : Ret n) (g : ℕ) : NFIn (mA n) → ℝ :=
  nfVal (nodeS c g) (√(1 - nodeS c g ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c) (normSq (bR c))

/-- The selected node of a draw. -/
def drawNode {n : ℕ} (c : Ret n) (d : DrawSp n) : ℕ :=
  nodeIdx (Js n) (√(normSq c.1.2) / rhoC' c - 6 * tau0p c.1.1 / rhoC' c)
    (√(normSq c.1.2) / rhoC' c + 6 * tau0p c.1.1 / rhoC' c)
    (latitude (√(normSq c.1.2)) (tau0p c.1.1) d.1)

/-- **The output of the stated program as a composition of the verified blocks (even `n`).** -/
theorem progOut_composed {n : ℕ} (he : Even n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) :
    progOut (statedDesign n) t a k θ σ =
      (outProg k).eval (oVal a (fun i =>
        (hitProg n (mF n)).eval
          (hitVal
            ((nodeProg n).eval (nodeIn (ret (statedDesign n).toCentres θ)
              (drawNode (ret (statedDesign n).toCentres θ) (σ i))) 0)
            ((nodeProg n).eval (nodeIn (ret (statedDesign n).toCentres θ)
              (drawNode (ret (statedDesign n).toCentres θ) (σ i))) 1)
            (√(normSq (bAp (ret (statedDesign n).toCentres θ).1
              (ret (statedDesign n).toCentres θ).2.1.1) / (n : ℝ)))
            t (ret (statedDesign n).toCentres θ).2.1.2 (σ i).2 (ret (statedDesign n).toCentres θ).2.2)
          ())) () := by
  rw [progOut_eq_outProg]
  refine congrArg (fun x => (outProg k).eval (oVal a x) ()) (funext fun i => ?_)
  rw [statedDesign, hitFn_eq_hitProg, passFSt_eq_nodeProg he, passWSt_eq_nodeProg he]
  rfl

end

end BstLean.Part282

/-- info: 'BstLean.Part282.world_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.world_cost_le
/-- info: 'BstLean.Part282.progOut_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.progOut_composed
