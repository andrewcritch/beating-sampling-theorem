import BstLean.Part282Kit
import BstLean.Part157Paper
import BstLean.Part150Prog4

/-!
# Part 282 (C2), the global Agent pass

Paper: `theorem7-01-statement-program.tex`, step 3. Lean: `Part157Paper.bAp`.

`agentProg n`: the arithmetic pass `Part150.passAll n (n²) n` (all its stored values, among them
`b̃′_j`, `ρ`, `c̃_A`), followed by the `n²` divisions `b_j = b̃′_j/ρ`.
`bAp_eq_agentProg`: for `τ₀ > 0`, output `Sum.inr j` is `bAp wc θ j`. (The Part 150 value
theorems need `τ > 0`; for `τ₀ = 0` nothing is proved here.)
`agentProg_cost`: the cost of `passProg n (n²) n` plus `n²`. Part 189 `agentWork` forms `b`
directly (it divides the common second-layer weights by `ρ` first) and charges `2n` fewer than
`passProg`; this program is therefore `n² − 2n` operations above `agentWork`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150 BstLean.Part157

noncomputable section

/-- `b_j = b̃′_j/ρ`. -/
def bDivE {n m J : ℕ} (j : Fin m) : RExpr (PIn n m ⊕ PV n m J) :=
  RExpr.div (.inp (Sum.inr (.b j))) (.inp (Sum.inr .rho))

def agentProg (n : ℕ) : RProg (PIn n (n ^ 2)) (PV n (n ^ 2) n ⊕ Fin (n ^ 2)) :=
  RProg.ext (passAll n (n ^ 2) n) (RProg.parF fun j => (bDivE (J := n) j).prog)

theorem passAll_b {n m J : ℕ} (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (hτ : 0 < τ) (j : Fin m) :
    (passAll n m J).eval (passVal c τ A₁ A₂ A₃) (.b j) = bT J J A₁ A₂ c τ j := by
  simp only [passAll, RProg.eval_stage, Option.elim]
  exact pA3_b c τ A₁ A₂ A₃ hτ j

theorem passAll_rho {n m J : ℕ} (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) :
    (passAll n m J).eval (passVal c τ A₁ A₂ A₃) .rho = rhoC c τ := by
  simp only [passAll, RProg.eval_stage, Option.elim]
  exact pA3_rho c τ A₁ A₂ A₃

theorem agentProg_eval {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (n ^ 2)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ) (A₃ : Matrix (Fin n) (Fin (n ^ 2)) ℝ) (hτ : 0 < τ)
    (j : Fin (n ^ 2)) :
    (agentProg n).eval (passVal c τ A₁ A₂ A₃) (Sum.inr j) = bT n n A₁ A₂ c τ j / rhoC c τ := by
  rw [agentProg, RProg.eval_ext_inr, RProg.eval_parF, RExpr.eval_prog]
  simp only [bDivE, RExpr.eval_div, RExpr.eval_inp, Sum.elim_inr]
  rw [passAll_b c τ A₁ A₂ A₃ hτ, passAll_rho]

/-- **The global Agent centre of the stated program is the Agent program** (for `τ₀ > 0`). -/
theorem bAp_eq_agentProg {n : ℕ} (wc : WRet n) (θ : AHid n) (A₃ : Matrix (Fin n) (Fin (n ^ 2)) ℝ)
    (hτ : 0 < tau0p wc.1) (j : Fin (mA n)) :
    bAp wc θ j = (agentProg n).eval (passVal wc.2 (tau0p wc.1) θ.1 θ.2 A₃) (Sum.inr j) := by
  exact (agentProg_eval (n := n) wc.2 (tau0p wc.1) θ.1 θ.2 A₃ hτ j).symm

theorem agentProg_cost {n : ℕ} (_hn : 1 ≤ n) :
    (agentProg n).cost = (passProg n (n ^ 2) n).cost + n ^ 2 := by
  rw [agentProg, RProg.cost_ext, RProg.cost_parF_eq _ 1 (fun j => by simp [bDivE]), passProg,
    RProg.cost_mapOut]
  ring

end

end BstLean.Part282

/-- info: 'BstLean.Part282.bAp_eq_agentProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.bAp_eq_agentProg
