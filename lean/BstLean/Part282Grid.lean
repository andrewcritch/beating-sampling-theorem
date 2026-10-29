import BstLean.Part282Node

/-!
# Part 282 (C2), the grid scalars and the nodes

Paper: `theorem7-01-statement-program.tex`, step 4. Lean: `Part169Pass.nodeL`, `nodeH`,
`nodeS`.

`gridProg n`: from the inputs `|ĉ|²` and `τ₀`: `|ĉ|`, `ρ = √(|ĉ|² + nτ₀²)`, `L`, `H`,
`Δ = (H − L)/J_s` (output `Sum.inl (Sum.inl i)`, `i = 0, 1, 2` for `L`, `H`, `Δ`), and for each
node `g < J_s`: `s_g = L + (g + 1/2)Δ` and `√(1 − s_g²)` (output `Sum.inr (g, 0)`,
`Sum.inr (g, 1)`). `gridProg_L`, `gridProg_H`, `gridProg_s`, `gridProg_w`: the values are
`nodeL c`, `nodeH c`, `nodeS c g`, `√(1 − (nodeS c g)²)`. `gridProg_cost`: `15 + 5 J_s`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157
open BstLean.Part169 (nodeL nodeH nodeD nodeS tauR rhoR)

noncomputable section

/-- The inputs: `![|ĉ|², τ₀]`. -/
abbrev GIn : Type := Fin 2

/-- `ρ`, then `|ĉ|/ρ` and `6τ₀/ρ`. -/
def gStage1 (n : ℕ) : Fin 2 → RExpr GIn :=
  ![RExpr.sqrt (RExpr.add (.inp 0) (RExpr.mul (.cst (n : ℚ)) (RExpr.mul (.inp 1) (.inp 1)))),
    RExpr.sqrt (.inp 0)]

/-- `L = |ĉ|/ρ − 6τ₀/ρ`, `H = |ĉ|/ρ + 6τ₀/ρ`. -/
def gStage2 : Fin 2 → RExpr (GIn ⊕ Fin 2) :=
  ![RExpr.sub (RExpr.div (.inp (Sum.inr 1)) (.inp (Sum.inr 0)))
      (RExpr.div (RExpr.mul (.cst 6) (.inp (Sum.inl 1))) (.inp (Sum.inr 0))),
    RExpr.add (RExpr.div (.inp (Sum.inr 1)) (.inp (Sum.inr 0)))
      (RExpr.div (RExpr.mul (.cst 6) (.inp (Sum.inl 1))) (.inp (Sum.inr 0)))]

/-- `L`, `H`, `Δ`. -/
def gStage3 (n : ℕ) : Fin 3 → RExpr (GIn ⊕ Fin 2) :=
  ![.inp (Sum.inr 0), .inp (Sum.inr 1),
    RExpr.div (RExpr.sub (.inp (Sum.inr 1)) (.inp (Sum.inr 0))) (.cst (Js n : ℚ))]

def pLHD (n : ℕ) : RProg GIn (Fin 3) :=
  ((RProg.parV (gStage1 n)).bind (RProg.parV gStage2)).bind (RProg.parV (gStage3 n))

/-- `s_g = L + (g + 1/2)Δ`, then `√(1 − s_g·s_g)`. -/
def nodeSE (g : ℕ) : RExpr (GIn ⊕ Fin 3) :=
  RExpr.add (.inp (Sum.inr 0)) (RExpr.mul (.cst ((g : ℚ) + 1 / 2)) (.inp (Sum.inr 2)))

def nodeProgG (g : ℕ) : RProg (GIn ⊕ Fin 3) (Unit ⊕ Unit) :=
  RProg.ext (nodeSE g).prog
    (RExpr.sqrt (RExpr.sub (.cst 1) (RExpr.mul (.inp (Sum.inr ())) (.inp (Sum.inr ()))))).prog

/-- **The grid program.** -/
def gridProg (n : ℕ) : RProg GIn (Fin 3 ⊕ (Fin (Js n) × (Unit ⊕ Unit))) :=
  RProg.ext (pLHD n) (RProg.parL2 (fun g : Fin (Js n) => nodeProgG g) (List.finRange (Js n)))

def gVal {n : ℕ} (c : Ret n) : GIn → ℝ := ![normSq c.1.2, tauR c]

theorem pLHD_eval {n : ℕ} (c : Ret n) :
    (pLHD n).eval (gVal c) = ![nodeL c, nodeH c, nodeD c] := by
  have h1 : (RProg.parV (gStage1 n)).eval (gVal c) = ![rhoR c, √(normSq c.1.2)] := by
    funext i
    fin_cases i
    · simp [gStage1, gVal, rhoR, BstLean.Part150.rhoC, pow_two]
    · simp [gStage1, gVal]
  have h2 : (RProg.parV gStage2).eval (Sum.elim (gVal c) ((RProg.parV (gStage1 n)).eval (gVal c))) =
      ![nodeL c, nodeH c] := by
    rw [h1]
    funext i
    fin_cases i
    · simp [gStage2, gVal, nodeL] <;> ring
    · simp [gStage2, gVal, nodeH] <;> ring
  have h12 : ((RProg.parV (gStage1 n)).bind (RProg.parV gStage2)).eval (gVal c) =
      ![nodeL c, nodeH c] := by
    funext i; rw [RProg.eval_bind]; exact congrFun h2 i
  funext i
  rw [pLHD, RProg.eval_bind, h12]
  fin_cases i
  · simp [gStage3]
  · simp [gStage3]
  · simp [gStage3, nodeD]

theorem gridProg_LHD {n : ℕ} (c : Ret n) (i : Fin 3) :
    (gridProg n).eval (gVal c) (Sum.inl i) = ![nodeL c, nodeH c, nodeD c] i := by
  rw [gridProg, RProg.eval_ext_inl, pLHD_eval]

theorem gridProg_s {n : ℕ} (c : Ret n) (g : Fin (Js n)) :
    (gridProg n).eval (gVal c) (Sum.inr (g, Sum.inl ())) = nodeS c g := by
  rw [gridProg, RProg.eval_ext_inr, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange g),
    nodeProgG, RProg.eval_ext_inl, RExpr.eval_prog, pLHD_eval]
  simp [nodeSE, nodeS]

theorem gridProg_w {n : ℕ} (c : Ret n) (g : Fin (Js n)) :
    (gridProg n).eval (gVal c) (Sum.inr (g, Sum.inr ())) = √(1 - nodeS c g ^ 2) := by
  rw [gridProg, RProg.eval_ext_inr, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange g),
    nodeProgG, RProg.eval_ext_inr, RExpr.eval_prog]
  simp only [RExpr.eval_sqrt, RExpr.eval_sub, RExpr.eval_mul, RExpr.eval_inp, RExpr.eval_cst,
    Sum.elim_inr]
  have h := gridProg_s c g
  rw [gridProg, RProg.eval_ext_inr, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange g),
    nodeProgG, RProg.eval_ext_inl, RExpr.eval_prog] at h
  rw [RExpr.eval_prog, h]
  simp [pow_two]

theorem gridProg_cost (n : ℕ) : (gridProg n).cost = 15 + 5 * Js n := by
  rw [gridProg, RProg.cost_ext, RProg.cost_parL2,
    BstLean.Part282.list_sum_const _ _ 5 (fun g => by simp [nodeProgG, nodeSE])]
  simp [pLHD, RProg.cost_parV, Fin.sum_univ_succ, gStage1, gStage2, gStage3] <;> omega

end

end BstLean.Part282

/-- info: 'BstLean.Part282.gridProg_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.gridProg_w
