import Mathlib

/-!
# A real-RAM straight-line program model, with operation counts

A program over an input type `ι` with an output type `κ` is a finite list of instructions and an output
map. Each instruction is one of `+ − × ÷` on two arguments; an argument is an input `inp i`, an earlier
register `reg r` (the value of instruction number `r`, counted from `0`), or a rational constant `cst q`.
The cost of a program is its number of instructions: every instruction is one arithmetic operation, and
reading an input, a register or a constant is free.

Conventions (frozen):
* Evaluation is total. A register that is not yet computed reads `0` (`List.getD`); `x / 0 = 0` as in
  Lean's `ℝ`. Neither convention gives a program extra power: a register that reads `0` is a constant.
* Branching is not part of the model. Part 29's program may depend on `ε` (part 29, Setting), so its
  branch selection `ε² < h²` happens when the program is built, not when it runs.
* Programs need not be computable; the combinators below build them from smaller ones, and the
  `eval_*`/`cost_*` lemmas give their values and costs.

Do not use `native_decide` in this file or in any file that proves its lemmas.
-/

namespace BstLean.Cost

noncomputable section

/-- The four real-RAM operations. -/
inductive Op
  | add | sub | mul | div

/-- The value of an operation. -/
def Op.eval : Op → ℝ → ℝ → ℝ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- An argument: an input, a register, or a rational constant. -/
inductive Arg (ι : Type)
  | inp (i : ι)
  | reg (r : ℕ)
  | cst (q : ℚ)

/-- One instruction: an operation on two arguments. -/
structure Instr (ι : Type) where
  op : Op
  a : Arg ι
  b : Arg ι

/-- A straight-line program with inputs `ι` and outputs `κ`. -/
structure Prog (ι κ : Type) where
  body : List (Instr ι)
  out : κ → Arg ι

variable {ι ι₂ κ κ₂ ν : Type}

/-- The value of an argument, given the inputs `v` and the registers `R` computed so far. -/
def Arg.eval (v : ι → ℝ) (R : List ℝ) : Arg ι → ℝ
  | .inp i => v i
  | .reg r => R.getD r 0
  | .cst q => (q : ℝ)

/-- The value of an instruction. -/
def Instr.eval (v : ι → ℝ) (R : List ℝ) (I : Instr ι) : ℝ :=
  I.op.eval (I.a.eval v R) (I.b.eval v R)

/-- Run a list of instructions, appending each value to the registers. -/
def run (v : ι → ℝ) : List (Instr ι) → List ℝ → List ℝ
  | [], R => R
  | I :: is, R => run v is (R ++ [I.eval v R])

/-- The value of a program at output `k`. -/
def Prog.eval (p : Prog ι κ) (v : ι → ℝ) (k : κ) : ℝ :=
  (p.out k).eval v (run v p.body [])

/-- The cost of a program: its number of arithmetic instructions. -/
def Prog.cost (p : Prog ι κ) : ℕ := p.body.length

/-! ## Renaming and substitution of arguments -/

/-- Rename inputs. -/
def Arg.rename (σ : ι → ι₂) : Arg ι → Arg ι₂
  | .inp i => .inp (σ i)
  | .reg r => .reg r
  | .cst q => .cst q

def Instr.rename (σ : ι → ι₂) (I : Instr ι) : Instr ι₂ := ⟨I.op, I.a.rename σ, I.b.rename σ⟩

/-- Replace a register reference at or beyond `len` by the constant `0` (its value anyway). -/
def Arg.clamp (len : ℕ) : Arg ι → Arg ι
  | .reg r => if r < len then .reg r else .cst 0
  | a => a

/-- Substitute arguments `σ` for inputs and shift registers below `len` by `shift`. -/
def Arg.subst (σ : ι → Arg ι₂) (shift len : ℕ) : Arg ι → Arg ι₂
  | .inp i => σ i
  | .reg r => if r < len then .reg (r + shift) else .cst 0
  | .cst q => .cst q

def Instr.subst (σ : ι → Arg ι₂) (shift len : ℕ) (I : Instr ι) : Instr ι₂ :=
  ⟨I.op, I.a.subst σ shift len, I.b.subst σ shift len⟩

/-! ## Combinators -/

/-- A program with no instructions: each output is an input or a constant. -/
def Prog.ofArgs (o : κ → Arg ι) : Prog ι κ := ⟨[], o⟩

/-- A single instruction. -/
def Prog.op1 (op : Op) (a b : Arg ι) : Prog ι Unit := ⟨[⟨op, a, b⟩], fun _ => .reg 0⟩

/-- Rename the inputs of a program. -/
def Prog.mapIn (σ : ι → ι₂) (p : Prog ι κ) : Prog ι₂ κ :=
  ⟨p.body.map (Instr.rename σ), fun k => (p.out k).rename σ⟩

/-- Reindex the outputs of a program. -/
def Prog.mapOut (τ : κ₂ → κ) (p : Prog ι κ) : Prog ι κ₂ := ⟨p.body, fun k => p.out (τ k)⟩

/-- Sequencing with sharing: run `p`, then run `q` on the inputs together with `p`'s outputs. -/
def Prog.bind (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν) : Prog ι ν :=
  let s := p.body.length
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun k => (p.out k).clamp s)
  ⟨p.body ++ q.body.map (Instr.subst σ s q.body.length), fun l => (q.out l).subst σ s q.body.length⟩

/-- Run `p` and `q` side by side (no sharing between them). -/
def Prog.pair (p : Prog ι κ) (q : Prog ι κ₂) : Prog ι (κ ⊕ κ₂) :=
  p.bind ⟨(q.mapIn Sum.inl).body, Sum.elim (fun k => .inp (Sum.inr k)) (q.mapIn Sum.inl).out⟩

/-- Run one program per index in the list `l`; output `k` is program `p k` if `k ∈ l`, else `0`. -/
def Prog.par [DecidableEq κ] (p : κ → Prog ι Unit) : List κ → Prog ι κ
  | [] => .ofArgs fun _ => .cst 0
  | k :: l =>
      (p k).bind
        ⟨((Prog.par p l).mapIn Sum.inl).body,
          fun j => if j = k then .inp (Sum.inr ()) else ((Prog.par p l).mapIn Sum.inl).out j⟩

/-- The sum of a list of arguments, by `length − 1` additions (the empty sum is the constant `0`). -/
def Prog.sumArgs : List (Arg ι) → Prog ι Unit
  | [] => .ofArgs fun _ => .cst 0
  | [a] => .ofArgs fun _ => a
  | a :: b :: l =>
      (Prog.sumArgs (b :: l)).bind (Prog.op1 .add (a.rename Sum.inl) (.inp (Sum.inr ())))

/-- The sum of products `Σ aᵢ bᵢ` of a list of argument pairs, by `2·length − 1` operations. -/
def Prog.sumProd (l : List (Arg ι × Arg ι)) : Prog ι Unit :=
  (Prog.par (fun j : Fin l.length => Prog.op1 .mul (l.get j).1 (l.get j).2)
      (List.finRange l.length)).bind
    (Prog.sumArgs ((List.finRange l.length).map fun j => .inp (Sum.inr j)))

/-- A register file with named slots `κ`: run `p`, then recompute the slots in `l` by the programs `q`,
which read the inputs and `p`'s slots; every other slot keeps `p`'s value. -/
def Prog.update [DecidableEq κ] (p : Prog ι κ) (q : κ → Prog (ι ⊕ κ) Unit) (l : List κ) : Prog ι κ :=
  p.bind ⟨(Prog.par q l).body, fun k => if k ∈ l then (Prog.par q l).out k else .inp (.inr k)⟩

/-- `b + a·q` by two operations. -/
def Prog.axpy (q : ℚ) (a b : Arg ι) : Prog ι Unit :=
  (Prog.op1 .mul a (.cst q)).bind (Prog.op1 .add (b.rename Sum.inl) (.inp (Sum.inr ())))

/-! ## Value and cost lemmas -/

section lemmas

theorem run_append (v : ι → ℝ) (as bs : List (Instr ι)) (R : List ℝ) :
    run v (as ++ bs) R = run v bs (run v as R) := by
  induction as generalizing R with
  | nil => rfl
  | cons I is ih => simp only [List.cons_append, run]; exact ih _

theorem length_run (v : ι → ℝ) (is : List (Instr ι)) (R : List ℝ) :
    (run v is R).length = R.length + is.length := by
  induction is generalizing R with
  | nil => simp [run]
  | cons I is ih => simp [run, ih]; omega

@[simp] theorem eval_ofArgs (o : κ → Arg ι) (v : ι → ℝ) (k : κ) :
    (Prog.ofArgs o).eval v k = (o k).eval v [] := rfl

@[simp] theorem cost_ofArgs (o : κ → Arg ι) : (Prog.ofArgs o).cost = 0 := rfl

@[simp] theorem eval_op1 (op : Op) (a b : Arg ι) (v : ι → ℝ) (u : Unit) :
    (Prog.op1 op a b).eval v u = op.eval (a.eval v []) (b.eval v []) := by
  simp [Prog.op1, Prog.eval, run, Arg.eval, Instr.eval]

@[simp] theorem cost_op1 (op : Op) (a b : Arg ι) : (Prog.op1 op a b).cost = 1 := rfl

theorem Arg.eval_rename (σ : ι → ι₂) (v : ι₂ → ℝ) (R : List ℝ) (a : Arg ι) :
    (a.rename σ).eval v R = a.eval (v ∘ σ) R := by
  cases a <;> rfl

theorem run_rename (σ : ι → ι₂) (v : ι₂ → ℝ) (is : List (Instr ι)) (R : List ℝ) :
    run v (is.map (Instr.rename σ)) R = run (v ∘ σ) is R := by
  induction is generalizing R with
  | nil => rfl
  | cons I is ih =>
    simp only [List.map_cons, run]
    rw [ih]
    congr 2
    simp [Instr.eval, Instr.rename, Arg.eval_rename]

@[simp] theorem eval_mapIn (σ : ι → ι₂) (p : Prog ι κ) (v : ι₂ → ℝ) (k : κ) :
    (p.mapIn σ).eval v k = p.eval (v ∘ σ) k := by
  simp [Prog.mapIn, Prog.eval, run_rename, Arg.eval_rename]

@[simp] theorem cost_mapIn (σ : ι → ι₂) (p : Prog ι κ) : (p.mapIn σ).cost = p.cost := by
  simp [Prog.mapIn, Prog.cost]

@[simp] theorem eval_mapOut (τ : κ₂ → κ) (p : Prog ι κ) (v : ι → ℝ) (k : κ₂) :
    (p.mapOut τ).eval v k = p.eval v (τ k) := rfl

@[simp] theorem cost_mapOut (τ : κ₂ → κ) (p : Prog ι κ) : (p.mapOut τ).cost = p.cost := rfl

private theorem getD_append_left' (R S : List ℝ) (r : ℕ) (h : r < R.length) :
    (R ++ S).getD r 0 = R.getD r 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_right' (R S : List ℝ) (r : ℕ) :
    (R ++ S).getD (r + R.length) 0 = S.getD r 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : R.length ≤ r + R.length)]

theorem Arg.eval_subst (σ : ι → Arg ι₂) (v : ι₂ → ℝ) (R S : List ℝ) (len : ℕ)
    (hS : S.length ≤ len) (hσ : ∀ i T, (σ i).eval v (R ++ T) = (σ i).eval v R) (a : Arg ι) :
    (a.subst σ R.length len).eval v (R ++ S) = a.eval (fun i => (σ i).eval v R) S := by
  cases a with
  | inp i => simp only [Arg.subst]; rw [hσ]; rfl
  | reg r =>
    simp only [Arg.subst]
    split_ifs with h
    · simp only [Arg.eval]; exact getD_append_right' R S r
    · simp only [Arg.eval]
      rw [List.getD_eq_default _ _ (by omega)]
      simp
  | cst q => rfl

theorem run_subst (σ : ι → Arg ι₂) (v : ι₂ → ℝ) (R : List ℝ) (len : ℕ)
    (hσ : ∀ i T, (σ i).eval v (R ++ T) = (σ i).eval v R)
    (is : List (Instr ι)) (S : List ℝ) (hS : S.length + is.length ≤ len) :
    run v (is.map (Instr.subst σ R.length len)) (R ++ S) =
      R ++ run (fun i => (σ i).eval v R) is S := by
  induction is generalizing S with
  | nil => simp [run]
  | cons I is ih =>
    simp only [List.map_cons, run]
    have hS' : S.length ≤ len := by simp at hS; omega
    have : Instr.eval v (R ++ S) (Instr.subst σ R.length len I) =
        Instr.eval (fun i => (σ i).eval v R) S I := by
      simp only [Instr.eval, Instr.subst]
      rw [Arg.eval_subst σ v R S len hS' hσ, Arg.eval_subst σ v R S len hS' hσ]
    rw [this, List.append_assoc]
    exact ih _ (by simp at hS ⊢; omega)

private theorem clamp_eval (v : ι → ℝ) (R T : List ℝ) (a : Arg ι) :
    (a.clamp R.length).eval v (R ++ T) = a.eval v R := by
  cases a with
  | inp i => rfl
  | cst q => rfl
  | reg r =>
    simp only [Arg.clamp]
    split_ifs with h
    · simp only [Arg.eval]; exact getD_append_left' R T r h
    · simp only [Arg.eval]
      rw [List.getD_eq_default _ _ (by omega)]
      simp

theorem eval_bind (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν) (v : ι → ℝ) (l : ν) :
    (p.bind q).eval v l = q.eval (Sum.elim v (p.eval v)) l := by
  set R := run v p.body [] with hR
  have hlen : R.length = p.body.length := by simp [hR, length_run]
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun k => (p.out k).clamp p.body.length)
  have hσ : ∀ i T, (σ i).eval v (R ++ T) = (σ i).eval v R := by
    intro i T
    cases i with
    | inl i => rfl
    | inr k =>
      simp only [σ, Sum.elim_inr]
      rw [← hlen, clamp_eval]
      have := clamp_eval v R [] (p.out k)
      simpa using this.symm
  have hv : (fun i => (σ i).eval v R) = Sum.elim v (p.eval v) := by
    funext i
    cases i with
    | inl i => rfl
    | inr k =>
      simp only [σ, Sum.elim_inr, Prog.eval]
      rw [← hlen]
      have := clamp_eval v R [] (p.out k)
      simpa using this
  have hrun : run v (p.bind q).body [] = R ++ run (Sum.elim v (p.eval v)) q.body [] := by
    simp only [Prog.bind]
    rw [← hv]
    have h1 : run v (p.body ++ List.map (Instr.subst σ p.body.length q.body.length) q.body) [] =
        run v (List.map (Instr.subst σ p.body.length q.body.length) q.body) (R ++ []) := by
      rw [List.append_nil, hR, run_append]
    rw [h1, ← hlen]
    exact run_subst σ v R q.body.length hσ q.body [] (by simp)
  have key := Arg.eval_subst σ v R (run (fun i => (σ i).eval v R) q.body []) q.body.length
    (by simp [length_run]) hσ (q.out l)
  rw [hlen] at key
  simp only [Prog.eval]
  rw [hrun, ← hv]
  exact key

@[simp] theorem cost_bind (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν) :
    (p.bind q).cost = p.cost + q.cost := by
  simp [Prog.bind, Prog.cost]

@[simp] theorem eval_pair_inl (p : Prog ι κ) (q : Prog ι κ₂) (v : ι → ℝ) (k : κ) :
    (p.pair q).eval v (Sum.inl k) = p.eval v k := by
  simp only [Prog.pair, eval_bind]
  rfl

@[simp] theorem eval_pair_inr (p : Prog ι κ) (q : Prog ι κ₂) (v : ι → ℝ) (k : κ₂) :
    (p.pair q).eval v (Sum.inr k) = q.eval v k := by
  simp only [Prog.pair, eval_bind]
  have := eval_mapIn Sum.inl q (Sum.elim v (p.eval v)) k
  simpa [Prog.eval] using this

@[simp] theorem cost_pair (p : Prog ι κ) (q : Prog ι κ₂) :
    (p.pair q).cost = p.cost + q.cost := by
  simp only [Prog.pair, cost_bind]
  simp [Prog.cost, Prog.mapIn]

theorem eval_par_mem [DecidableEq κ] (p : κ → Prog ι Unit) (l : List κ) (v : ι → ℝ) (k : κ)
    (hk : k ∈ l) : (Prog.par p l).eval v k = (p k).eval v () := by
  induction l with
  | nil => simp at hk
  | cons j l ih =>
    simp only [Prog.par, eval_bind]
    by_cases h : k = j
    · subst h; simp [Prog.eval, Arg.eval]
    · have hk' : k ∈ l := by simpa [h] using hk
      have := eval_mapIn Sum.inl (Prog.par p l) (Sum.elim v ((p j).eval v)) k
      simp only [Prog.eval, h, ite_false] at this ⊢
      rw [this]
      exact ih hk'

theorem eval_par_not_mem [DecidableEq κ] (p : κ → Prog ι Unit) (l : List κ) (v : ι → ℝ) (k : κ)
    (hk : k ∉ l) : (Prog.par p l).eval v k = 0 := by
  induction l with
  | nil => simp [Prog.par, Arg.eval]
  | cons j l ih =>
    simp only [Prog.par, eval_bind]
    have h : k ≠ j := fun h => hk (h ▸ List.mem_cons_self)
    have hk' : k ∉ l := fun h' => hk (List.mem_cons_of_mem _ h')
    have := eval_mapIn Sum.inl (Prog.par p l) (Sum.elim v ((p j).eval v)) k
    simp only [Prog.eval, h, ite_false] at this ⊢
    rw [this]
    exact ih hk'

theorem cost_par [DecidableEq κ] (p : κ → Prog ι Unit) (l : List κ) :
    (Prog.par p l).cost = (l.map fun k => (p k).cost).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [Prog.par, cost_bind, List.map_cons, List.sum_cons]
    rw [← ih]
    simp [Prog.cost, Prog.mapIn]

theorem eval_sumArgs (l : List (Arg ι)) (v : ι → ℝ) (u : Unit) :
    (Prog.sumArgs l).eval v u = (l.map fun a => a.eval v []).sum := by
  induction l with
  | nil => simp [Prog.sumArgs, Arg.eval]
  | cons a l ih =>
    cases l with
    | nil => simp [Prog.sumArgs]
    | cons b l =>
      simp only [Prog.sumArgs, eval_bind, eval_op1, Op.eval, Arg.eval_rename]
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [← ih]
      cases a <;> rfl

theorem cost_sumArgs (l : List (Arg ι)) : (Prog.sumArgs l).cost = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [Prog.sumArgs, cost_bind, cost_op1] at ih ⊢
      rw [ih]
      simp

theorem eval_sumProd (l : List (Arg ι × Arg ι)) (v : ι → ℝ) (u : Unit) :
    (Prog.sumProd l).eval v u = (l.map fun ab => ab.1.eval v [] * ab.2.eval v []).sum := by
  simp only [Prog.sumProd, eval_bind, eval_sumArgs, List.map_map]
  have : ∀ j : Fin l.length, (Function.comp (fun a => Arg.eval (Sum.elim v
      ((Prog.par (fun j : Fin l.length => Prog.op1 .mul (l.get j).1 (l.get j).2)
        (List.finRange l.length)).eval v)) [] a) (fun j => Arg.inp (Sum.inr j))) j =
      (l.get j).1.eval v [] * (l.get j).2.eval v [] := by
    intro j
    simp only [Function.comp, Arg.eval, Sum.elim_inr]
    rw [eval_par_mem _ _ _ _ (List.mem_finRange j), eval_op1]
    rfl
  rw [List.map_congr_left (fun j _ => this j)]
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

theorem cost_sumProd (l : List (Arg ι × Arg ι)) : (Prog.sumProd l).cost = 2 * l.length - 1 := by
  simp only [Prog.sumProd, cost_bind, cost_par, cost_op1, cost_sumArgs, List.length_map,
    List.length_finRange, List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
  omega

theorem eval_update [DecidableEq κ] (p : Prog ι κ) (q : κ → Prog (ι ⊕ κ) Unit) (l : List κ)
    (v : ι → ℝ) (k : κ) :
    (p.update q l).eval v k =
      if k ∈ l then (q k).eval (Sum.elim v (p.eval v)) () else p.eval v k := by
  simp only [Prog.update, eval_bind]
  by_cases h : k ∈ l
  · have := eval_par_mem q l (Sum.elim v (p.eval v)) k h
    simp only [Prog.eval, h, ite_true] at this ⊢
    exact this
  · simp [Prog.eval, h, Arg.eval]

theorem cost_update [DecidableEq κ] (p : Prog ι κ) (q : κ → Prog (ι ⊕ κ) Unit) (l : List κ) :
    (p.update q l).cost = p.cost + (l.map fun k => (q k).cost).sum := by
  simp only [Prog.update, cost_bind]
  rw [← cost_par]
  rfl

@[simp] theorem eval_axpy (q : ℚ) (a b : Arg ι) (v : ι → ℝ) (u : Unit) :
    (Prog.axpy q a b).eval v u = b.eval v [] + a.eval v [] * q := by
  simp only [Prog.axpy, eval_bind, eval_op1, Op.eval, Arg.eval_rename]
  cases b <;> rfl

@[simp] theorem cost_axpy (q : ℚ) (a b : Arg ι) : (Prog.axpy q a b).cost = 2 := rfl

end lemmas

end

end BstLean.Cost
