import BstLean.Part130Cost

/-!
# Part 282 (C2), kit: combinators for straight-line programs `RProg`

This file adds combinators to the model `BstLean.Part130.RProg` (operations
`+ − × ÷ √ relu`, each of cost one; rational constants and inputs are free; total division).

* `RExpr`: an expression tree. `RExpr.prog e` is a program that computes `e`; its cost is
  `e.size`, the number of operation nodes (`RExpr.eval_prog`, `RExpr.cost_prog`).
* `RProg.ext p q`: run `p`, then `q` on the inputs and `p`'s outputs; keep both sets of outputs.
* `RProg.parL p l`: one program `p k` for each `k` in the list `l`.
* `RProg.iter init step k`: `k` steps of a loop with a state of type `σ`.
* `horner`: the Horner loop for `Σ_{r ≤ P} c_r z^r`, `2P` operations.
* `ind_pos`, `ind_ne`: with total division, `relu x / relu x` is the indicator of `0 < x`,
  and `x / x` is the indicator of `x ≠ 0`. The programs use these to write the branches of
  the stated program without branching.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130

noncomputable section

variable {ι κ κ₂ ν σ : Type}

/-! ## Single instructions and constant programs -/

/-- One instruction. -/
def RProg.op1 (o : ROp) (a b : Arg ι) : RProg ι Unit := ⟨[⟨o, a, b⟩], fun _ => .reg 0⟩

@[simp] theorem RProg.eval_op1 (o : ROp) (a b : Arg ι) (v : ι → ℝ) (u : Unit) :
    (RProg.op1 o a b).eval v u = o.eval (a.eval v []) (b.eval v []) := by
  cases a <;> cases b <;> rfl

@[simp] theorem RProg.cost_op1 (o : ROp) (a b : Arg ι) : (RProg.op1 o a b).cost = 1 := rfl

/-- No instruction: each output is an argument. -/
def RProg.ofArgs (o : κ → Arg ι) : RProg ι κ := ⟨[], o⟩

@[simp] theorem RProg.eval_ofArgs (o : κ → Arg ι) (v : ι → ℝ) (k : κ) :
    (RProg.ofArgs o).eval v k = (o k).eval v [] := rfl

@[simp] theorem RProg.cost_ofArgs (o : κ → Arg ι) : (RProg.ofArgs o).cost = 0 := rfl

/-! ## Expressions -/

/-- An expression tree over the inputs `ι`. -/
inductive RExpr (ι : Type)
  | inp (i : ι)
  | cst (q : ℚ)
  | op (o : ROp) (a b : RExpr ι)

/-- The value of an expression. -/
def RExpr.eval (v : ι → ℝ) : RExpr ι → ℝ
  | .inp i => v i
  | .cst q => (q : ℝ)
  | .op o a b => o.eval (a.eval v) (b.eval v)

/-- The number of operation nodes. -/
def RExpr.size : RExpr ι → ℕ
  | .inp _ => 0
  | .cst _ => 0
  | .op _ a b => a.size + b.size + 1

/-- The program of an expression (no sharing of subexpressions). -/
def RExpr.prog : RExpr ι → RProg ι Unit
  | .inp i => RProg.ofArgs fun _ => .inp i
  | .cst q => RProg.ofArgs fun _ => .cst q
  | .op o a b => (a.prog).bind (((b.prog).mapIn Sum.inl).bind
      (RProg.op1 o (.inp (Sum.inl (Sum.inr ()))) (.inp (Sum.inr ()))))

@[simp] theorem RExpr.eval_prog (e : RExpr ι) (v : ι → ℝ) (u : Unit) :
    e.prog.eval v u = e.eval v := by
  induction e generalizing v with
  | inp i => rfl
  | cst q => rfl
  | op o a b iha ihb =>
    simp only [RExpr.prog, RProg.eval_bind, RProg.eval_op1, RExpr.eval]
    have h1 : (Sum.elim v (a.prog.eval v) ∘ Sum.inl) = v := rfl
    simp only [Arg.eval, Sum.elim_inl, Sum.elim_inr]
    rw [RProg.eval_mapIn, h1, iha, ihb]

@[simp] theorem RExpr.cost_prog (e : RExpr ι) : e.prog.cost = e.size := by
  induction e with
  | inp i => rfl
  | cst q => rfl
  | op o a b iha ihb =>
    simp only [RExpr.prog, RProg.cost_bind, RProg.cost_mapIn, RProg.cost_op1, iha, ihb,
      RExpr.size]
    omega

/-- Short names for expressions. -/
def RExpr.add (a b : RExpr ι) : RExpr ι := .op .add a b
def RExpr.sub (a b : RExpr ι) : RExpr ι := .op .sub a b
def RExpr.mul (a b : RExpr ι) : RExpr ι := .op .mul a b
def RExpr.div (a b : RExpr ι) : RExpr ι := .op .div a b
def RExpr.sqrt (a : RExpr ι) : RExpr ι := .op .sqrt a (.cst 0)
def RExpr.relu (a : RExpr ι) : RExpr ι := .op .relu a (.cst 0)

@[simp] theorem RExpr.eval_inp (v : ι → ℝ) (i : ι) : (RExpr.inp i).eval v = v i := rfl
@[simp] theorem RExpr.eval_cst (v : ι → ℝ) (q : ℚ) : (RExpr.cst q : RExpr ι).eval v = q := rfl
@[simp] theorem RExpr.eval_add (v : ι → ℝ) (a b : RExpr ι) :
    (a.add b).eval v = a.eval v + b.eval v := rfl
@[simp] theorem RExpr.eval_sub (v : ι → ℝ) (a b : RExpr ι) :
    (a.sub b).eval v = a.eval v - b.eval v := rfl
@[simp] theorem RExpr.eval_mul (v : ι → ℝ) (a b : RExpr ι) :
    (a.mul b).eval v = a.eval v * b.eval v := rfl
@[simp] theorem RExpr.eval_div (v : ι → ℝ) (a b : RExpr ι) :
    (a.div b).eval v = a.eval v / b.eval v := rfl
@[simp] theorem RExpr.eval_sqrt (v : ι → ℝ) (a : RExpr ι) :
    (a.sqrt).eval v = Real.sqrt (a.eval v) := rfl
@[simp] theorem RExpr.eval_relu (v : ι → ℝ) (a : RExpr ι) :
    (a.relu).eval v = BstLean.Part130.relu (a.eval v) := rfl

@[simp] theorem RExpr.size_inp (i : ι) : (RExpr.inp i).size = 0 := rfl
@[simp] theorem RExpr.size_cst (q : ℚ) : (RExpr.cst q : RExpr ι).size = 0 := rfl
@[simp] theorem RExpr.size_add (a b : RExpr ι) : (a.add b).size = a.size + b.size + 1 := rfl
@[simp] theorem RExpr.size_sub (a b : RExpr ι) : (a.sub b).size = a.size + b.size + 1 := rfl
@[simp] theorem RExpr.size_mul (a b : RExpr ι) : (a.mul b).size = a.size + b.size + 1 := rfl
@[simp] theorem RExpr.size_div (a b : RExpr ι) : (a.div b).size = a.size + b.size + 1 := rfl
@[simp] theorem RExpr.size_sqrt (a : RExpr ι) : (a.sqrt).size = a.size + 1 := rfl
@[simp] theorem RExpr.size_relu (a : RExpr ι) : (a.relu).size = a.size + 1 := rfl

/-! ## Sequencing that keeps the earlier outputs -/

/-- Run `p`, then `q` on the inputs and `p`'s outputs; the outputs are those of `p` and of `q`. -/
def RProg.ext (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) : RProg ι (κ ⊕ ν) :=
  p.bind ⟨q.body, Sum.elim (fun k => .inp (Sum.inr k)) q.out⟩

@[simp] theorem RProg.eval_ext_inl (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) (v : ι → ℝ) (k : κ) :
    (RProg.ext p q).eval v (Sum.inl k) = p.eval v k := by
  rw [RProg.ext, RProg.eval_bind]
  rfl

@[simp] theorem RProg.eval_ext_inr (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) (v : ι → ℝ) (l : ν) :
    (RProg.ext p q).eval v (Sum.inr l) = q.eval (Sum.elim v (p.eval v)) l := by
  rw [RProg.ext, RProg.eval_bind]
  rfl

@[simp] theorem RProg.cost_ext (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) :
    (RProg.ext p q).cost = p.cost + q.cost := by
  rw [RProg.ext, RProg.cost_bind]
  rfl

/-! ## One program per element of a list -/

/-- One program `p k` for each `k ∈ l`; output `k` is `p k` for `k ∈ l` and `0` otherwise. -/
def RProg.parL [DecidableEq κ] (p : κ → RProg ι Unit) : List κ → RProg ι κ
  | [] => RProg.ofArgs fun _ => .cst 0
  | k :: l =>
      (p k).bind
        ⟨((RProg.parL p l).mapIn Sum.inl).body,
          fun j => if j = k then .inp (Sum.inr ()) else ((RProg.parL p l).mapIn Sum.inl).out j⟩

theorem RProg.eval_parL [DecidableEq κ] (p : κ → RProg ι Unit) (l : List κ) (v : ι → ℝ) (k : κ)
    (hk : k ∈ l) : (RProg.parL p l).eval v k = (p k).eval v () := by
  induction l with
  | nil => simp at hk
  | cons j l ih =>
    simp only [RProg.parL, RProg.eval_bind]
    by_cases h : k = j
    · subst h; simp [RProg.eval, Arg.eval]
    · have hk' : k ∈ l := by simpa [h] using hk
      have := RProg.eval_mapIn Sum.inl (RProg.parL p l) (Sum.elim v ((p j).eval v)) k
      simp only [RProg.eval, h, ite_false] at this ⊢
      rw [this]
      exact ih hk'

theorem RProg.cost_parL [DecidableEq κ] (p : κ → RProg ι Unit) (l : List κ) :
    (RProg.parL p l).cost = (l.map fun k => (p k).cost).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [RProg.parL, RProg.cost_bind, List.map_cons, List.sum_cons]
    rw [← ih]
    simp [RProg.cost, RProg.mapIn]

/-- One program for each index of `Fin m`. -/
def RProg.parF {m : ℕ} (p : Fin m → RProg ι Unit) : RProg ι (Fin m) :=
  RProg.parL p (List.finRange m)

@[simp] theorem RProg.eval_parF {m : ℕ} (p : Fin m → RProg ι Unit) (v : ι → ℝ) (k : Fin m) :
    (RProg.parF p).eval v k = (p k).eval v () :=
  RProg.eval_parL p _ v k (List.mem_finRange k)

theorem RProg.cost_parF_le {m : ℕ} (p : Fin m → RProg ι Unit) (c : ℕ) (hc : ∀ k, (p k).cost ≤ c) :
    (RProg.parF p).cost ≤ m * c := by
  rw [RProg.parF, RProg.cost_parL]
  have h : ∀ l : List (Fin m), (l.map fun k => (p k).cost).sum ≤ l.length * c := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hc a
      nlinarith
  simpa using h (List.finRange m)

theorem RProg.cost_parF_eq {m : ℕ} (p : Fin m → RProg ι Unit) (c : ℕ) (hc : ∀ k, (p k).cost = c) :
    (RProg.parF p).cost = m * c := by
  rw [RProg.parF, RProg.cost_parL]
  have h : ∀ l : List (Fin m), (l.map fun k => (p k).cost).sum = l.length * c := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, hc a]
      ring
  simpa using h (List.finRange m)

/-! ## Loops -/

/-- `k` steps of a loop: the state after step `j + 1` is `step j` applied to the inputs and the
state after step `j`. -/
def RProg.iter (init : RProg ι σ) (step : ℕ → RProg (ι ⊕ σ) σ) : ℕ → RProg ι σ
  | 0 => init
  | k + 1 => (RProg.iter init step k).bind (step k)

@[simp] theorem RProg.eval_iter_zero (init : RProg ι σ) (step : ℕ → RProg (ι ⊕ σ) σ)
    (v : ι → ℝ) : (RProg.iter init step 0).eval v = init.eval v := rfl

theorem RProg.eval_iter_succ (init : RProg ι σ) (step : ℕ → RProg (ι ⊕ σ) σ) (k : ℕ)
    (v : ι → ℝ) :
    (RProg.iter init step (k + 1)).eval v =
      (step k).eval (Sum.elim v ((RProg.iter init step k).eval v)) := by
  funext s
  rw [RProg.iter, RProg.eval_bind]

theorem RProg.cost_iter (init : RProg ι σ) (step : ℕ → RProg (ι ⊕ σ) σ) (k : ℕ) :
    (RProg.iter init step k).cost = init.cost + ∑ j ∈ Finset.range k, (step j).cost := by
  induction k with
  | zero => simp [RProg.iter]
  | succ k ih => rw [RProg.iter, RProg.cost_bind, ih, Finset.sum_range_succ]; ring

theorem RProg.cost_iter_const (init : RProg ι σ) (step : ℕ → RProg (ι ⊕ σ) σ) (k c : ℕ)
    (hc : ∀ j, (step j).cost = c) :
    (RProg.iter init step k).cost = init.cost + k * c := by
  rw [RProg.cost_iter]
  simp [hc]

/-! ## The Horner loop -/

/-- The Horner loop for `Σ_{r ≤ P} c r · z^r`. The input `z` is the argument `z` (an input of
`ι`); the coefficients are rational constants. The state after `j` steps is
`Σ_{r ≤ j} c (P − j + r) z^r`. -/
def hornerStep (c : ℕ → ℚ) (P : ℕ) (z : ι) (j : ℕ) : RProg (ι ⊕ Unit) Unit :=
  (RExpr.add (RExpr.mul (.inp (Sum.inr ())) (.inp (Sum.inl z))) (.cst (c (P - (j + 1))))).prog

def horner (c : ℕ → ℚ) (P : ℕ) (z : ι) : RProg ι Unit :=
  RProg.iter (RProg.ofArgs fun _ => .cst (c P)) (hornerStep c P z) P

theorem horner_eval_aux (c : ℕ → ℚ) (P : ℕ) (z : ι) (v : ι → ℝ) (j : ℕ) (hj : j ≤ P) :
    (RProg.iter (RProg.ofArgs fun _ => .cst (c P)) (hornerStep c P z) j).eval v () =
      ∑ r ∈ Finset.range (j + 1), (c (P - j + r) : ℝ) * v z ^ r := by
  induction j with
  | zero => simp [Arg.eval]
  | succ j ih =>
    rw [RProg.eval_iter_succ]
    simp only [hornerStep, RExpr.eval_prog, RExpr.eval_add, RExpr.eval_mul, RExpr.eval_inp,
      RExpr.eval_cst, Sum.elim_inr, Sum.elim_inl]
    rw [ih (by omega), Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    have hP : P - (j + 1) + 0 = P - (j + 1) := by omega
    rw [hP, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : P - j + r = P - (j + 1) + (r + 1) := by
      simp at hr; omega
    rw [hr', pow_succ]
    ring

theorem horner_eval (c : ℕ → ℚ) (P : ℕ) (z : ι) (v : ι → ℝ) :
    (horner c P z).eval v () = ∑ r ∈ Finset.range (P + 1), (c r : ℝ) * v z ^ r := by
  rw [horner, horner_eval_aux c P z v P le_rfl]
  simp

theorem horner_cost (c : ℕ → ℚ) (P : ℕ) (z : ι) : (horner c P z).cost = 2 * P := by
  rw [horner, RProg.cost_iter_const _ _ P 2 (fun j => by simp [hornerStep])]
  simp; ring

/-! ## Indicators by total division -/

/-- `relu x / relu x` is `1` for `0 < x` and `0` otherwise. -/
theorem ind_pos (x : ℝ) : relu x / relu x = if 0 < x then 1 else 0 := by
  unfold relu
  split_ifs with h
  · rw [max_eq_right h.le]; exact div_self h.ne'
  · rw [max_eq_left (not_lt.mp h)]; simp

/-- `x / x` is `1` for `x ≠ 0` and `0` otherwise. -/
theorem ind_ne (x : ℝ) : x / x = if x ≠ 0 then 1 else 0 := by
  split_ifs with h
  · exact div_self h
  · push_neg at h; simp [h]

/-- The selection `i·a + (1 − i)·b` for an indicator `i`. -/
theorem select_ite (p : Prop) [Decidable p] (a b : ℝ) :
    (if p then (1 : ℝ) else 0) * a + (1 - if p then (1 : ℝ) else 0) * b = if p then a else b := by
  split_ifs <;> ring

end

end BstLean.Part282

/-- info: 'BstLean.Part282.horner_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.horner_eval
