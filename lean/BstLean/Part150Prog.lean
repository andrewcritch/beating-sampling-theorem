import BstLean.Part150CDefs
import BstLean.Part149Prog

/-!
# Part 150, item 4, tools: straight-line programs over a flat type of named variables

Role: `delegations/statements/p150-spec.md`, item 4.

The model is `RProg` of `Part130Cost`: operations `+ − × ÷ √ relu`, each costs one; reading an
input, a register or a RATIONAL constant is free; total division `x/0 = 0`.

A program with many intermediate values is written as a list of STAGES over one type `V` of
named variables. The current program `P : RProg ι V` gives a value to every variable (a variable
that is not yet computed reads `0`). A stage `q : RProg V κ` reads the variables and computes
the new values with index `κ`; `d : V → Option κ` says which variable gets which new value.

* `RProg.stage P q d`, `RProg.eval_stage`, `RProg.cost_stage`.
* `op1Stage op a b`: one operation for each index: `card κ` operations.
* `dotStage c a b`: `Σ_j x_{a k j}·x_{b k j}` for each index `k`: `card κ·(2c − 1)` operations.
* `sumStage c a`: `Σ_j x_{a k j}` for each index `k`: `card κ·(c − 1)` operations.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open BstLean.Cost
open BstLean.Part130 BstLean.Part140

noncomputable section

variable {ι V κ : Type}

/-- Add one stage to a program over the variables `V`. -/
def _root_.BstLean.Part130.RProg.stage (P : RProg ι V) (q : RProg V κ) (d : V → Option κ) :
    RProg ι V :=
  P.bind ⟨(q.mapIn Sum.inr).body,
    fun x => (d x).elim (.inp (Sum.inr x)) (fun k => (q.mapIn Sum.inr).out k)⟩

theorem _root_.BstLean.Part130.RProg.eval_stage (P : RProg ι V) (q : RProg V κ)
    (d : V → Option κ) (v : ι → ℝ) (x : V) :
    (P.stage q d).eval v x = (d x).elim (P.eval v x) (fun k => q.eval (P.eval v) k) := by
  simp only [RProg.stage, RProg.eval_bind]
  cases h : d x with
  | none => simp [RProg.eval, Arg.eval, h]
  | some k =>
    have := RProg.eval_mapIn Sum.inr q (Sum.elim v (P.eval v)) k
    simp only [RProg.eval, h, Option.elim] at this ⊢
    rw [this]
    rfl

@[simp] theorem _root_.BstLean.Part130.RProg.cost_stage (P : RProg ι V) (q : RProg V κ)
    (d : V → Option κ) : (P.stage q d).cost = P.cost + q.cost := by
  simp [RProg.stage, RProg.cost, RProg.bind, RProg.mapIn]

section stages

variable [Fintype κ] [DecidableEq κ]

/-- One operation for each index `k`: `op (a k) (b k)`. -/
def op1Stage (op : ROp) (a b : κ → Arg V) : RProg V κ :=
  RProg.par (fun k => ⟨[⟨op, a k, b k⟩], fun _ => .reg 0⟩) (Finset.univ : Finset κ).toList

theorem op1Stage_eval (op : ROp) (a b : κ → Arg V) (v : V → ℝ) (k : κ) :
    (op1Stage op a b).eval v k = op.eval ((a k).eval v []) ((b k).eval v []) := by
  rw [op1Stage, RProg.eval_par_mem _ _ _ _ (Finset.mem_toList.mpr (Finset.mem_univ k))]
  simp [RProg.eval, rrun, RInstr.eval, Arg.eval]

theorem op1Stage_cost (op : ROp) (a b : κ → Arg V) :
    (op1Stage op a b).cost = Fintype.card κ := by
  rw [op1Stage, RProg.cost_par]
  simp [RProg.cost]

/-- `Σ_j x_{a k j}·x_{b k j}` for each index `k`. -/
def dotStage (c : ℕ) (a b : κ → Fin c → V) : RProg V κ :=
  RProg.ofProg (Prog.par (fun k =>
    Prog.sumProd ((List.finRange c).map fun j => (Arg.inp (a k j), Arg.inp (b k j))))
    (Finset.univ : Finset κ).toList)

theorem dotStage_eval (c : ℕ) (a b : κ → Fin c → V) (v : V → ℝ) (k : κ) :
    (dotStage c a b).eval v k = ∑ j, v (a k j) * v (b k j) := by
  rw [dotStage, RProg.eval_ofProg,
    eval_par_mem _ _ _ _ (Finset.mem_toList.mpr (Finset.mem_univ k)), eval_sumProd, List.map_map,
    Fin.sum_univ_def]
  rfl

theorem dotStage_cost (c : ℕ) (a b : κ → Fin c → V) :
    (dotStage c a b).cost = Fintype.card κ * (2 * c - 1) := by
  simp [dotStage, cost_par, cost_sumProd]

/-- `Σ_j x_{a k j}` for each index `k`. -/
def sumStage (c : ℕ) (a : κ → Fin c → V) : RProg V κ :=
  RProg.ofProg (Prog.par (fun k => sumProg c (a k)) (Finset.univ : Finset κ).toList)

theorem sumStage_eval (c : ℕ) (a : κ → Fin c → V) (v : V → ℝ) (k : κ) :
    (sumStage c a).eval v k = ∑ j, v (a k j) := by
  rw [sumStage, RProg.eval_ofProg,
    eval_par_mem _ _ _ _ (Finset.mem_toList.mpr (Finset.mem_univ k)), sumProg_eval]

theorem sumStage_cost (c : ℕ) (a : κ → Fin c → V) :
    (sumStage c a).cost = Fintype.card κ * (c - 1) := by
  simp [sumStage, cost_par, sumProg_cost]

end stages

end

end BstLean.Part150
