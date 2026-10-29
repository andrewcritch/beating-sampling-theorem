import BstLean.Part130Defs
import BstLean.Part105Cost

/-!
# Part 130, costs: a cost model with `relu`, and one sample of `s_B` for ReLU MLPs

Role: `delegations/statements/p130-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

* `RProg`: the model `BstLean.Part105.SProg` (operations `+ − × ÷ √`) with one more operation,
  `relu t = max 0 t`, which costs one.
* `relu_eq_sqrt`, `reluSProg`: `relu` by four operations of the model `SProg`.
  `RProg.exists_sProg`: every `RProg` has an `SProg` with the same values and at most four times
  the cost.
* `mulVecProg r c`: a matrix–vector product by `r(2c − 1)` operations.
* `mlpProg k m q`: one evaluation of a ReLU MLP with two hidden layers, with cost at most
  `mlpCost k m q`.
* `sampleRProg r n mW mA mF`: one sample `F(A(W(u)/|W(u)|))`, with cost at most
  `sampleRCost r n mW mA mF`.
-/

namespace BstLean.Part130

open BstLean.Cost
open BstLean.Part105

noncomputable section

/-! ## §A The model with `relu` -/

section reluModel

variable {ι ι₂ κ κ₂ ν : Type}

/-- The operations of the model: the four real-RAM operations, the square root, and `relu`. -/
inductive ROp
  | add | sub | mul | div | sqrt | relu

/-- The value of an operation. `sqrt` and `relu` use their first argument only. -/
def ROp.eval : ROp → ℝ → ℝ → ℝ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .sqrt, a, _ => Real.sqrt a
  | .relu, a, _ => BstLean.Part130.relu a

/-- One instruction of the model. The arguments are those of the library model
(`BstLean.Cost.Arg`: an input, an earlier register, or a rational constant). -/
structure RInstr (ι : Type) where
  op : ROp
  a : Arg ι
  b : Arg ι

/-- **A straight-line program with square roots and `relu`.** This is the model
`BstLean.Part105.SProg` with one more operation.

Conventions:
* A program is a finite list of instructions and an output map. Each instruction is one of
  `+ − × ÷ √ relu` on arguments that are inputs, earlier registers or rational constants.
* The cost is the number of instructions: every arithmetic operation costs one, every square
  root costs one, and every `relu` (`max 0 t`) costs one. Reading an input, a register or a
  constant is free.
* Evaluation is total, as in the library model: a register that is not yet computed reads `0`,
  `x / 0 = 0`, and `√x = 0` for `x < 0` (`Real.sqrt`).
* There is no branching. `relu` is the only operation that is not a rational operation or a
  square root. -/
structure RProg (ι κ : Type) where
  body : List (RInstr ι)
  out : κ → Arg ι

/-- The value of an instruction. -/
def RInstr.eval (v : ι → ℝ) (R : List ℝ) (I : RInstr ι) : ℝ :=
  I.op.eval (I.a.eval v R) (I.b.eval v R)

/-- Run a list of instructions, appending each value to the registers. -/
def rrun (v : ι → ℝ) : List (RInstr ι) → List ℝ → List ℝ
  | [], R => R
  | I :: is, R => rrun v is (R ++ [I.eval v R])

/-- The value of a program at output `k`. -/
def RProg.eval (p : RProg ι κ) (v : ι → ℝ) (k : κ) : ℝ :=
  (p.out k).eval v (rrun v p.body [])

/-- The cost of a program: its number of instructions. -/
def RProg.cost (p : RProg ι κ) : ℕ := p.body.length

def RInstr.rename (σ : ι → ι₂) (I : RInstr ι) : RInstr ι₂ := ⟨I.op, I.a.rename σ, I.b.rename σ⟩

def RInstr.subst (σ : ι → Arg ι₂) (shift len : ℕ) (I : RInstr ι) : RInstr ι₂ :=
  ⟨I.op, I.a.subst σ shift len, I.b.subst σ shift len⟩

/-- The embedding of the five operations of `SProg`. -/
def sopToR : SOp → ROp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .sqrt => .sqrt

def sinstrToR (I : SInstr ι) : RInstr ι := ⟨sopToR I.op, I.a, I.b⟩

/-- A program of the model `SProg` is a program of the model `RProg`. -/
def RProg.ofSProg (p : SProg ι κ) : RProg ι κ := ⟨p.body.map sinstrToR, p.out⟩

/-- A program of the library model is a program of the model `RProg`. -/
def RProg.ofProg (p : Prog ι κ) : RProg ι κ := RProg.ofSProg (SProg.ofProg p)

/-- One `relu`. -/
def RProg.relu1 (a : Arg ι) : RProg ι Unit := ⟨[⟨.relu, a, a⟩], fun _ => .reg 0⟩

/-- Rename the inputs of a program. -/
def RProg.mapIn (σ : ι → ι₂) (p : RProg ι κ) : RProg ι₂ κ :=
  ⟨p.body.map (RInstr.rename σ), fun k => (p.out k).rename σ⟩

/-- Reindex the outputs of a program. -/
def RProg.mapOut (τ : κ₂ → κ) (p : RProg ι κ) : RProg ι κ₂ := ⟨p.body, fun k => p.out (τ k)⟩

/-- Sequencing with sharing: run `p`, then run `q` on the inputs together with `p`'s outputs. -/
def RProg.bind (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) : RProg ι ν :=
  let s := p.body.length
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun k => (p.out k).clamp s)
  ⟨p.body ++ q.body.map (RInstr.subst σ s q.body.length),
    fun l => (q.out l).subst σ s q.body.length⟩

theorem rrun_append (v : ι → ℝ) (as bs : List (RInstr ι)) (R : List ℝ) :
    rrun v (as ++ bs) R = rrun v bs (rrun v as R) := by
  induction as generalizing R with
  | nil => rfl
  | cons I is ih => simp only [List.cons_append, rrun]; exact ih _

theorem length_rrun (v : ι → ℝ) (is : List (RInstr ι)) (R : List ℝ) :
    (rrun v is R).length = R.length + is.length := by
  induction is generalizing R with
  | nil => simp [rrun]
  | cons I is ih => simp [rrun, ih]; omega

theorem sopToR_eval (op : SOp) (a b : ℝ) : (sopToR op).eval a b = op.eval a b := by
  cases op <;> rfl

theorem rrun_ofSProg (v : ι → ℝ) (is : List (SInstr ι)) (R : List ℝ) :
    rrun v (is.map sinstrToR) R = srun v is R := by
  induction is generalizing R with
  | nil => rfl
  | cons I is ih =>
    simp only [List.map_cons, rrun, srun]
    rw [ih]
    congr 2
    simp [RInstr.eval, SInstr.eval, sinstrToR, sopToR_eval]

/-- The embedding keeps the value. -/
@[simp] theorem RProg.eval_ofSProg (p : SProg ι κ) (v : ι → ℝ) (k : κ) :
    (RProg.ofSProg p).eval v k = p.eval v k := by
  simp [RProg.ofSProg, RProg.eval, SProg.eval, rrun_ofSProg]

/-- The embedding keeps the cost. -/
@[simp] theorem RProg.cost_ofSProg (p : SProg ι κ) : (RProg.ofSProg p).cost = p.cost := by
  simp [RProg.ofSProg, RProg.cost, SProg.cost]

@[simp] theorem RProg.eval_ofProg (p : Prog ι κ) (v : ι → ℝ) (k : κ) :
    (RProg.ofProg p).eval v k = p.eval v k := by
  simp [RProg.ofProg]

@[simp] theorem RProg.cost_ofProg (p : Prog ι κ) : (RProg.ofProg p).cost = p.cost := by
  simp [RProg.ofProg]

@[simp] theorem RProg.eval_relu1 (a : Arg ι) (v : ι → ℝ) (u : Unit) :
    (RProg.relu1 a).eval v u = relu (a.eval v []) := by
  simp [RProg.relu1, RProg.eval, rrun, Arg.eval, RInstr.eval, ROp.eval]

@[simp] theorem RProg.cost_relu1 (a : Arg ι) : (RProg.relu1 a).cost = 1 := rfl

theorem rrun_rename (σ : ι → ι₂) (v : ι₂ → ℝ) (is : List (RInstr ι)) (R : List ℝ) :
    rrun v (is.map (RInstr.rename σ)) R = rrun (v ∘ σ) is R := by
  induction is generalizing R with
  | nil => rfl
  | cons I is ih =>
    simp only [List.map_cons, rrun]
    rw [ih]
    congr 2
    simp [RInstr.eval, RInstr.rename, Arg.eval_rename]

@[simp] theorem RProg.eval_mapIn (σ : ι → ι₂) (p : RProg ι κ) (v : ι₂ → ℝ) (k : κ) :
    (p.mapIn σ).eval v k = p.eval (v ∘ σ) k := by
  simp [RProg.mapIn, RProg.eval, rrun_rename, Arg.eval_rename]

@[simp] theorem RProg.cost_mapIn (σ : ι → ι₂) (p : RProg ι κ) : (p.mapIn σ).cost = p.cost := by
  simp [RProg.mapIn, RProg.cost]

@[simp] theorem RProg.eval_mapOut (τ : κ₂ → κ) (p : RProg ι κ) (v : ι → ℝ) (k : κ₂) :
    (p.mapOut τ).eval v k = p.eval v (τ k) := rfl

@[simp] theorem RProg.cost_mapOut (τ : κ₂ → κ) (p : RProg ι κ) : (p.mapOut τ).cost = p.cost := rfl

theorem rrun_subst (σ : ι → Arg ι₂) (v : ι₂ → ℝ) (R : List ℝ) (len : ℕ)
    (hσ : ∀ i T, (σ i).eval v (R ++ T) = (σ i).eval v R)
    (is : List (RInstr ι)) (S : List ℝ) (hS : S.length + is.length ≤ len) :
    rrun v (is.map (RInstr.subst σ R.length len)) (R ++ S) =
      R ++ rrun (fun i => (σ i).eval v R) is S := by
  induction is generalizing S with
  | nil => simp [rrun]
  | cons I is ih =>
    simp only [List.map_cons, rrun]
    have hS' : S.length ≤ len := by simp at hS; omega
    have : RInstr.eval v (R ++ S) (RInstr.subst σ R.length len I) =
        RInstr.eval (fun i => (σ i).eval v R) S I := by
      simp only [RInstr.eval, RInstr.subst]
      rw [Arg.eval_subst σ v R S len hS' hσ, Arg.eval_subst σ v R S len hS' hσ]
    rw [this, List.append_assoc]
    exact ih _ (by simp at hS ⊢; omega)

theorem RProg.eval_bind (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) (v : ι → ℝ) (l : ν) :
    (p.bind q).eval v l = q.eval (Sum.elim v (p.eval v)) l := by
  set R := rrun v p.body [] with hR
  have hlen : R.length = p.body.length := by simp [hR, length_rrun]
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun k => (p.out k).clamp p.body.length)
  have hσ : ∀ i T, (σ i).eval v (R ++ T) = (σ i).eval v R := by
    intro i T
    cases i with
    | inl i => rfl
    | inr k =>
      simp only [σ, Sum.elim_inr]
      rw [← hlen, clamp_eval']
      have := clamp_eval' v R [] (p.out k)
      simpa using this.symm
  have hv : (fun i => (σ i).eval v R) = Sum.elim v (p.eval v) := by
    funext i
    cases i with
    | inl i => rfl
    | inr k =>
      simp only [σ, Sum.elim_inr, RProg.eval]
      rw [← hlen]
      have := clamp_eval' v R [] (p.out k)
      simpa using this
  have hrun : rrun v (p.bind q).body [] = R ++ rrun (Sum.elim v (p.eval v)) q.body [] := by
    simp only [RProg.bind]
    rw [← hv]
    have h1 : rrun v (p.body ++ List.map (RInstr.subst σ p.body.length q.body.length) q.body) [] =
        rrun v (List.map (RInstr.subst σ p.body.length q.body.length) q.body) (R ++ []) := by
      rw [List.append_nil, hR, rrun_append]
    rw [h1, ← hlen]
    exact rrun_subst σ v R q.body.length hσ q.body [] (by simp)
  have key := Arg.eval_subst σ v R (rrun (fun i => (σ i).eval v R) q.body []) q.body.length
    (by simp [length_rrun]) hσ (q.out l)
  rw [hlen] at key
  simp only [RProg.eval]
  rw [hrun, ← hv]
  exact key

@[simp] theorem RProg.cost_bind (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) :
    (p.bind q).cost = p.cost + q.cost := by
  simp [RProg.bind, RProg.cost]

end reluModel

/-! ## §B `relu` in the model with square roots -/

/-- `max(0, t) = (t + √(t·t))/2`. -/
theorem relu_eq_sqrt (t : ℝ) : relu t = (t + Real.sqrt (t * t)) / 2 := by
  rw [Real.sqrt_mul_self_eq_abs, relu]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, max_eq_right h]; ring
  · rw [abs_of_nonpos h, max_eq_left h]; ring

section reluSim

variable {ι κ : Type}

/-- **`relu` by four operations of the model `SProg`**: `t·t`, `√`, `t + ·`, `· / 2`. The
argument `a` is an input or a constant (a register reference reads `0`, as in `a.eval v []`). -/
def reluSProg (a : Arg ι) : SProg ι Unit :=
  ⟨[⟨.mul, a.clamp 0, a.clamp 0⟩, ⟨.sqrt, .reg 0, .reg 0⟩, ⟨.add, a.clamp 0, .reg 1⟩,
      ⟨.div, .reg 2, .cst 2⟩], fun _ => .reg 3⟩

theorem clamp0_eval (v : ι → ℝ) (T : List ℝ) (a : Arg ι) :
    (a.clamp 0).eval v T = a.eval v [] := by
  have := clamp_eval' v [] T a
  simpa using this

theorem reluSProg_eval (a : Arg ι) (v : ι → ℝ) (u : Unit) :
    (reluSProg a).eval v u = relu (a.eval v []) := by
  rw [relu_eq_sqrt]
  simp only [reluSProg, SProg.eval, srun, SInstr.eval, SOp.eval, clamp0_eval]
  generalize a.eval v [] = t
  simp [Arg.eval]

theorem reluSProg_cost (a : Arg ι) : (reluSProg a).cost = 4 := rfl

/-! ### The general simulation

Instruction number `j` of an `RProg` becomes the four instructions number `4j, …, 4j+3` of an
`SProg`, and its value is in register `4j + 3`. A `relu` becomes the four operations of
`reluSProg`. Every other instruction becomes three instructions `0 + 0` and the instruction
itself; the three instructions `0 + 0` keep the register numbering uniform. Hence the cost of
the `SProg` is exactly four times the cost of the `RProg`; the bound `4 ·` is not sharp for a
program with few `relu`. -/

/-- The register renumbering `r ↦ 4r + 3`. -/
def tr4 : Arg ι → Arg ι
  | .reg r => .reg (4 * r + 3)
  | .inp i => .inp i
  | .cst q => .cst q

/-- The instruction `0 + 0`. -/
def padI : SInstr ι := ⟨.add, .cst 0, .cst 0⟩

/-- The four `SProg` instructions for instruction number `j`. -/
def simInstr (j : ℕ) : RInstr ι → List (SInstr ι)
  | ⟨.relu, a, _⟩ =>
      [⟨.mul, tr4 a, tr4 a⟩, ⟨.sqrt, .reg (4 * j), .reg (4 * j)⟩,
        ⟨.add, tr4 a, .reg (4 * j + 1)⟩, ⟨.div, .reg (4 * j + 2), .cst 2⟩]
  | ⟨.add, a, b⟩ => [padI, padI, padI, ⟨.add, tr4 a, tr4 b⟩]
  | ⟨.sub, a, b⟩ => [padI, padI, padI, ⟨.sub, tr4 a, tr4 b⟩]
  | ⟨.mul, a, b⟩ => [padI, padI, padI, ⟨.mul, tr4 a, tr4 b⟩]
  | ⟨.div, a, b⟩ => [padI, padI, padI, ⟨.div, tr4 a, tr4 b⟩]
  | ⟨.sqrt, a, b⟩ => [padI, padI, padI, ⟨.sqrt, tr4 a, tr4 b⟩]

/-- The `SProg` instructions for a list of instructions that starts at number `j`. -/
def simBody : ℕ → List (RInstr ι) → List (SInstr ι)
  | _, [] => []
  | j, I :: is => simInstr j I ++ simBody (j + 1) is

/-- The `SProg` that simulates an `RProg`. -/
def RProg.toSProg (p : RProg ι κ) : SProg ι κ := ⟨simBody 0 p.body, fun k => tr4 (p.out k)⟩

/-- The registers `S` of the simulation hold the registers `R` at the places `4r + 3`. -/
def SimRel (R S : List ℝ) : Prop :=
  S.length = 4 * R.length ∧ ∀ r, r < R.length → S.getD (4 * r + 3) 0 = R.getD r 0

theorem tr4_eval (v : ι → ℝ) {R S : List ℝ} (h : SimRel R S) (T : List ℝ) (hT : T.length ≤ 3)
    (a : Arg ι) : (tr4 a).eval v (S ++ T) = a.eval v R := by
  cases a with
  | inp i => rfl
  | cst q => rfl
  | reg r =>
    simp only [tr4, Arg.eval]
    by_cases hr : r < R.length
    · rw [← h.2 r hr]
      have : 4 * r + 3 < S.length := by rw [h.1]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
    · rw [List.getD_eq_default _ _ (by rw [List.length_append, h.1]; omega),
        List.getD_eq_default _ _ (by omega)]

theorem simRel_step {R S : List ℝ} (h : SimRel R S) (x₁ x₂ x₃ y : ℝ) :
    SimRel (R ++ [y]) (S ++ [x₁, x₂, x₃, y]) := by
  refine ⟨by simp [h.1]; omega, ?_⟩
  intro r hr
  simp only [List.length_append, List.length_singleton] at hr
  by_cases hr' : r < R.length
  · have h1 : 4 * r + 3 < S.length := by rw [h.1]; omega
    have h2 := h.2 r hr'
    simp only [List.getD_eq_getElem?_getD] at h2 ⊢
    rw [List.getElem?_append_left h1, List.getElem?_append_left hr']
    exact h2
  · have hr2 : r = R.length := by omega
    subst hr2
    have h1 : S.length ≤ 4 * R.length + 3 := by rw [h.1]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right h1, List.getElem?_append_right (le_refl _)]
    have : 4 * R.length + 3 - S.length = 3 := by rw [h.1]; omega
    simp [this]

theorem srun_simInstr (v : ι → ℝ) {R S : List ℝ} (h : SimRel R S) (I : RInstr ι) :
    ∃ x₁ x₂ x₃, srun v (simInstr R.length I) S = S ++ [x₁, x₂, x₃, I.eval v R] := by
  obtain ⟨op, a, b⟩ := I
  have e0 : ∀ c : Arg ι, (tr4 c).eval v S = c.eval v R := fun c => by
    simpa using tr4_eval v h [] (by simp) c
  have e2 : ∀ (c : Arg ι) (x₁ x₂ : ℝ), (tr4 c).eval v (S ++ [x₁] ++ [x₂]) = c.eval v R :=
    fun c x₁ x₂ => by simpa using tr4_eval v h [x₁, x₂] (by simp) c
  have e3 : ∀ (c : Arg ι) (x₁ x₂ x₃ : ℝ),
      (tr4 c).eval v (S ++ [x₁] ++ [x₂] ++ [x₃]) = c.eval v R :=
    fun c x₁ x₂ x₃ => by simpa using tr4_eval v h [x₁, x₂, x₃] (by simp) c
  have hS := h.1
  cases op
  case relu =>
    refine ⟨a.eval v R * a.eval v R, Real.sqrt (a.eval v R * a.eval v R),
      a.eval v R + Real.sqrt (a.eval v R * a.eval v R), ?_⟩
    simp only [simInstr, srun, SInstr.eval, SOp.eval, e0, e2, RInstr.eval, ROp.eval,
      relu_eq_sqrt]
    simp [Arg.eval, List.getD_eq_getElem?_getD, ← hS]
  all_goals
    refine ⟨0, 0, 0, ?_⟩
    simp only [simInstr, srun, padI, SInstr.eval, SOp.eval, e3, RInstr.eval, ROp.eval]
    simp [Arg.eval]

theorem length_simBody (j : ℕ) (is : List (RInstr ι)) :
    (simBody j is).length = 4 * is.length := by
  induction is generalizing j with
  | nil => rfl
  | cons I is ih =>
    obtain ⟨op, a, b⟩ := I
    simp only [simBody, List.length_append, ih, List.length_cons]
    cases op <;> simp [simInstr] <;> omega

theorem simRel_run (v : ι → ℝ) (is : List (RInstr ι)) {R S : List ℝ} (h : SimRel R S) :
    SimRel (rrun v is R) (srun v (simBody R.length is) S) := by
  induction is generalizing R S with
  | nil => exact h
  | cons I is ih =>
    obtain ⟨x₁, x₂, x₃, hx⟩ := srun_simInstr v h I
    simp only [simBody, rrun, srun_append]
    rw [hx]
    have := ih (simRel_step h x₁ x₂ x₃ (I.eval v R))
    simpa using this

/-- The simulation keeps the value. -/
theorem RProg.eval_toSProg (p : RProg ι κ) (v : ι → ℝ) (k : κ) :
    p.toSProg.eval v k = p.eval v k := by
  have h0 : SimRel ([] : List ℝ) [] := ⟨rfl, fun r hr => by simp at hr⟩
  have h := simRel_run v p.body h0
  have := tr4_eval v h [] (by simp) (p.out k)
  simpa [RProg.toSProg, SProg.eval, RProg.eval] using this

/-- The simulation has four times the cost. -/
theorem RProg.cost_toSProg (p : RProg ι κ) : p.toSProg.cost = 4 * p.cost := by
  simp [RProg.toSProg, SProg.cost, RProg.cost, length_simBody]

/-- **The simulation theorem.** Every program of the model with `relu` has a program of the model
with square roots that has the same values and at most four times the cost. -/
theorem RProg.exists_sProg (p : RProg ι κ) :
    ∃ p' : SProg ι κ, (∀ v k, p'.eval v k = p.eval v k) ∧ p'.cost ≤ 4 * p.cost :=
  ⟨p.toSProg, p.eval_toSProg, le_of_eq p.cost_toSProg⟩

end reluSim

/-! ## §C One network, and one sample of `s_B` -/

section network

variable {ι : Type}

/-- **A matrix–vector product**: the inputs are the vector `z : ℝ^c` and the entries of the
matrix (`r` rows, `c` columns); the outputs are the `r` coordinates of `M z`. Each row is one
`Prog.sumProd`: `c` multiplications and `c − 1` additions. -/
def mulVecProg (r c : ℕ) : Prog (Fin c ⊕ (Fin r × Fin c)) (Fin r) :=
  Prog.par (fun i : Fin r =>
      Prog.sumProd ((List.finRange c).map fun j => (Arg.inp (Sum.inr (i, j)), Arg.inp (Sum.inl j))))
    (List.finRange r)

theorem mulVecProg_eval {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℝ) (z : Fin c → ℝ) (i : Fin r) :
    (mulVecProg r c).eval (Sum.elim z (fun e => M e.1 e.2)) i = M.mulVec z i := by
  rw [mulVecProg, eval_par_mem _ _ _ _ (List.mem_finRange i), eval_sumProd, List.map_map]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_def]
  apply congrArg
  apply List.map_congr_left
  intro j _
  simp [Arg.eval]

theorem mulVecProg_cost (r c : ℕ) : (mulVecProg r c).cost = r * (2 * c - 1) := by
  simp [mulVecProg, cost_par, cost_sumProd]

/-- One `relu` on each of `m` inputs. -/
def reluLayer (m : ℕ) : RProg (Fin m) (Fin m) :=
  ⟨(List.finRange m).map fun i => ⟨.relu, .inp i, .inp i⟩, fun i => .reg i⟩

theorem rrun_reluMap (v : ι → ℝ) (l : List ι) (R : List ℝ) :
    rrun v (l.map fun i => (⟨.relu, .inp i, .inp i⟩ : RInstr ι)) R =
      R ++ l.map fun i => relu (v i) := by
  induction l generalizing R with
  | nil => simp [rrun]
  | cons i l ih =>
    simp only [List.map_cons, rrun]
    rw [ih]
    simp [RInstr.eval, ROp.eval, Arg.eval]

theorem reluLayer_eval {m : ℕ} (v : Fin m → ℝ) (i : Fin m) :
    (reluLayer m).eval v i = relu (v i) := by
  simp [reluLayer, RProg.eval, rrun_reluMap, Arg.eval, List.getD_eq_getElem?_getD]

theorem reluLayer_cost (m : ℕ) : (reluLayer m).cost = m := by
  simp [reluLayer, RProg.cost]

/-- After the program `p`, multiply `p`'s outputs by the matrix whose entries are the inputs
`w (a, b)`. -/
def RProg.linStep {r c : ℕ} (p : RProg ι (Fin c)) (w : Fin r × Fin c → ι) : RProg ι (Fin r) :=
  p.bind (RProg.ofProg ((mulVecProg r c).mapIn (Sum.elim Sum.inr (fun e => Sum.inl (w e)))))

theorem RProg.eval_linStep {r c : ℕ} (p : RProg ι (Fin c)) (w : Fin r × Fin c → ι) (v : ι → ℝ)
    (M : Matrix (Fin r) (Fin c) ℝ) (hM : ∀ e, v (w e) = M e.1 e.2) :
    (p.linStep w).eval v = M.mulVec (p.eval v) := by
  funext i
  rw [RProg.linStep, RProg.eval_bind, RProg.eval_ofProg, BstLean.Cost.eval_mapIn]
  have h : (Sum.elim v (p.eval v) ∘ Sum.elim Sum.inr (fun e => Sum.inl (w e))) =
      Sum.elim (p.eval v) (fun e => M e.1 e.2) := by
    funext j
    cases j with
    | inl j => rfl
    | inr e => exact hM e
  rw [h, mulVecProg_eval]

@[simp] theorem RProg.cost_linStep {r c : ℕ} (p : RProg ι (Fin c)) (w : Fin r × Fin c → ι) :
    (p.linStep w).cost = p.cost + r * (2 * c - 1) := by
  simp [RProg.linStep, mulVecProg_cost]

/-- After the program `p`, one `relu` on each output. -/
def RProg.reluStep {m : ℕ} (p : RProg ι (Fin m)) : RProg ι (Fin m) :=
  p.bind ((reluLayer m).mapIn Sum.inr)

theorem RProg.eval_reluStep {m : ℕ} (p : RProg ι (Fin m)) (v : ι → ℝ) :
    p.reluStep.eval v = reluV (p.eval v) := by
  funext i
  rw [RProg.reluStep, RProg.eval_bind, RProg.eval_mapIn, reluLayer_eval]
  rfl

@[simp] theorem RProg.cost_reluStep {m : ℕ} (p : RProg ι (Fin m)) :
    p.reluStep.cost = p.cost + m := by
  simp [RProg.reluStep, reluLayer_cost]

/-- The index type of the weights of a network: the entries of `M₁`, `M₂`, `M₃`. -/
abbrev MlpW (k m q : ℕ) : Type := (Fin m × Fin k) ⊕ (Fin m × Fin m) ⊕ (Fin q × Fin m)

/-- The weights as one valuation. -/
def mlpW {k m q : ℕ} (θ : MlpParam k m q) : MlpW k m q → ℝ :=
  Sum.elim (fun e => θ.1 e.1 e.2) (Sum.elim (fun e => θ.2.1 e.1 e.2) (fun e => θ.2.2 e.1 e.2))

/-- The inputs of one evaluation of a network: the point `z` and the weights `θ`. -/
def mlpVal {k m q : ℕ} (z : Fin k → ℝ) (θ : MlpParam k m q) : Fin k ⊕ MlpW k m q → ℝ :=
  Sum.elim z (mlpW θ)

/-- After the program `p`, evaluate the network whose weights are the inputs `w ·` at `p`'s
outputs: three matrix–vector products and two layers of `relu`. -/
def RProg.mlpStep {k m q : ℕ} (p : RProg ι (Fin k)) (w : MlpW k m q → ι) : RProg ι (Fin q) :=
  ((((p.linStep (fun e => w (Sum.inl e))).reluStep).linStep
    (fun e => w (Sum.inr (Sum.inl e)))).reluStep).linStep (fun e => w (Sum.inr (Sum.inr e)))

theorem RProg.eval_mlpStep {k m q : ℕ} (p : RProg ι (Fin k)) (w : MlpW k m q → ι) (v : ι → ℝ)
    (θ : MlpParam k m q) (hw : ∀ e, v (w e) = mlpW θ e) :
    (p.mlpStep w).eval v = mlpEval θ (p.eval v) := by
  rw [RProg.mlpStep,
    RProg.eval_linStep _ _ v θ.2.2 (fun e => hw (Sum.inr (Sum.inr e))),
    RProg.eval_reluStep,
    RProg.eval_linStep _ _ v θ.2.1 (fun e => hw (Sum.inr (Sum.inl e))),
    RProg.eval_reluStep,
    RProg.eval_linStep _ _ v θ.1 (fun e => hw (Sum.inl e))]
  rfl

/-- The operation count of one evaluation of a network `ℝ^k → ℝ^q` with two hidden layers of
width `m`: `m(2k − 1)` for `M₁ z`, `m` for the first `relu` layer, `m(2m − 1)` for `M₂ ·`,
`m` for the second `relu` layer, `q(2m − 1)` for `M₃ ·`. (Subtraction in `ℕ`: for `k = 0` the
first term is `0`, and for `m = 0` every term is `0`.) -/
def mlpCost (k m q : ℕ) : ℕ := m * (2 * k - 1) + m + m * (2 * m - 1) + m + q * (2 * m - 1)

theorem RProg.cost_mlpStep {k m q : ℕ} (p : RProg ι (Fin k)) (w : MlpW k m q → ι) :
    (p.mlpStep w).cost = p.cost + mlpCost k m q := by
  simp only [RProg.mlpStep, RProg.cost_linStep, RProg.cost_reluStep, mlpCost]
  omega

/-- The program with no instructions that returns the first block of its inputs. -/
def RProg.inlProg (ι₁ ι₂ : Type) : RProg (ι₁ ⊕ ι₂) ι₁ := ⟨[], fun i => .inp (Sum.inl i)⟩

@[simp] theorem RProg.eval_inlProg {ι₁ ι₂ : Type} (v : ι₁ ⊕ ι₂ → ℝ) (i : ι₁) :
    (RProg.inlProg ι₁ ι₂).eval v i = v (Sum.inl i) := rfl

@[simp] theorem RProg.cost_inlProg (ι₁ ι₂ : Type) : (RProg.inlProg ι₁ ι₂).cost = 0 := rfl

/-- **One evaluation of a network**: the inputs are the point `z : ℝ^k` and the weights
`θ : MlpParam k m q`; the outputs are the `q` coordinates of `mlpEval θ z`. -/
def mlpProg (k m q : ℕ) : RProg (Fin k ⊕ MlpW k m q) (Fin q) :=
  (RProg.inlProg (Fin k) (MlpW k m q)).mlpStep Sum.inr

theorem mlpProg_eval {k m q : ℕ} (z : Fin k → ℝ) (θ : MlpParam k m q) (i : Fin q) :
    (mlpProg k m q).eval (mlpVal z θ) i = mlpEval θ z i := by
  rw [mlpProg, RProg.eval_mlpStep _ Sum.inr (mlpVal z θ) θ (fun _ => rfl)]
  rfl

/-- The exact cost of `mlpProg`. -/
theorem mlpProg_cost_eq (k m q : ℕ) : (mlpProg k m q).cost = mlpCost k m q := by
  simp [mlpProg, RProg.cost_mlpStep]

theorem mlpProg_cost (k m q : ℕ) : (mlpProg k m q).cost ≤ mlpCost k m q :=
  le_of_eq (mlpProg_cost_eq k m q)

/-! ### One sample of `s_B` -/

/-- The inputs of one sample: the point `u`, and the weights of `W`, `A` and `F`. -/
abbrev RSampleIn (r n mW mA mF : ℕ) : Type :=
  Fin (r * n) ⊕ MlpW (r * n) mW n ⊕ MlpW n mA n ⊕ MlpW n mF 1

/-- The inputs as one valuation. -/
def rsampleVal {r n mW mA mF : ℕ} (u : Fin (r * n) → ℝ) (W : MlpParam (r * n) mW n)
    (A : MlpParam n mA n) (F : MlpParam n mF 1) : RSampleIn r n mW mA mF → ℝ :=
  Sum.elim u (Sum.elim (mlpW W) (Sum.elim (mlpW A) (mlpW F)))

/-- After the program `p`, the rescaling `y ↦ y/|y|` (`rescaleProg`) of `p`'s outputs. -/
def RProg.rescaleStep {n : ℕ} (p : RProg ι (Fin n)) : RProg ι (Fin n) :=
  p.bind ((RProg.ofSProg (rescaleProg n)).mapIn Sum.inr)

theorem RProg.eval_rescaleStep {n : ℕ} (p : RProg ι (Fin n)) (v : ι → ℝ) :
    p.rescaleStep.eval v = sphProj (p.eval v) := by
  funext i
  rw [RProg.rescaleStep, RProg.eval_bind, RProg.eval_mapIn, RProg.eval_ofSProg]
  exact rescaleProg_eval _ i

theorem RProg.cost_rescaleStep {n : ℕ} (p : RProg ι (Fin n)) :
    p.rescaleStep.cost ≤ p.cost + (3 * n + 1) := by
  simp only [RProg.rescaleStep, RProg.cost_bind, RProg.cost_mapIn, RProg.cost_ofSProg]
  have := rescaleProg_cost n
  omega

/-- The first two steps of one sample: `W(u)` and the rescaling. -/
def sampleRProgX (r n mW mA mF : ℕ) : RProg (RSampleIn r n mW mA mF) (Fin n) :=
  ((RProg.inlProg (Fin (r * n)) _).mlpStep (fun e => Sum.inr (Sum.inl e))).rescaleStep

/-- **One sample of `s_B`**: `F(A(x))`, `x = W(u)/|W(u)|`, for three ReLU MLPs. The program has
no branching, so it computes `sphProj (W(u))`, which is `0` and not `e0 n` for `W(u) = 0`. -/
def sampleRProg (r n mW mA mF : ℕ) : RProg (RSampleIn r n mW mA mF) Unit :=
  (((sampleRProgX r n mW mA mF).mlpStep (fun e => Sum.inr (Sum.inr (Sum.inl e)))).mlpStep
    (fun e => Sum.inr (Sum.inr (Sum.inr e)))).mapOut (fun _ => 0)

theorem sampleRProgX_eval {r n mW mA mF : ℕ} (u : Fin (r * n) → ℝ) (W : MlpParam (r * n) mW n)
    (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    (sampleRProgX r n mW mA mF).eval (rsampleVal u W A F) = sphProj (mlpEval W u) := by
  rw [sampleRProgX, RProg.eval_rescaleStep,
    RProg.eval_mlpStep _ (fun e => Sum.inr (Sum.inl e)) (rsampleVal u W A F) W (fun _ => rfl)]
  rfl

/-- The value of one sample, with the rescaling `sphProj` (no hypothesis on `W(u)`). -/
theorem sampleRProg_eval {r n mW mA mF : ℕ} (u : Fin (r * n) → ℝ) (W : MlpParam (r * n) mW n)
    (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    (sampleRProg r n mW mA mF).eval (rsampleVal u W A F) () =
      phiN A F (sphProj (mlpEval W u)) := by
  rw [sampleRProg, RProg.eval_mapOut,
    RProg.eval_mlpStep _ (fun e => Sum.inr (Sum.inr (Sum.inr e))) (rsampleVal u W A F) F
      (fun _ => rfl),
    RProg.eval_mlpStep _ (fun e => Sum.inr (Sum.inr (Sum.inl e))) (rsampleVal u W A F) A
      (fun _ => rfl), sampleRProgX_eval]
  rfl

/-- The value of one sample for `W(u) ≠ 0`: the integrand of `Bn` at the point `sphPt (W(u))`. -/
theorem sampleRProg_eval_sphPt {r n mW mA mF : ℕ} (u : Fin (r * n) → ℝ)
    (W : MlpParam (r * n) mW n) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (h : normSq (mlpEval W u) ≠ 0) :
    (sampleRProg r n mW mA mF).eval (rsampleVal u W A F) () =
      phiN A F (sphPt (mlpEval W u)) := by
  simp only [sampleRProg_eval, sphPt, h, ↓reduceIte]

/-- The cost bound of `sampleRProg`. -/
def sampleRCost (r n mW mA mF : ℕ) : ℕ :=
  mlpCost (r * n) mW n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1

theorem sampleRProg_cost (r n mW mA mF : ℕ) :
    (sampleRProg r n mW mA mF).cost ≤ sampleRCost r n mW mA mF := by
  simp only [sampleRProg, sampleRProgX, RProg.cost_mapOut, RProg.cost_mlpStep, sampleRCost]
  have := RProg.cost_rescaleStep
    ((RProg.inlProg (Fin (r * n)) (MlpW (r * n) mW n ⊕ MlpW n mA n ⊕ MlpW n mF 1)).mlpStep
      (k := r * n) (m := mW) (q := n) (fun e => Sum.inr (Sum.inl e)))
  rw [RProg.cost_mlpStep, RProg.cost_inlProg] at this
  omega

end network

end

end BstLean.Part130

#print axioms BstLean.Part130.RProg.eval_bind
#print axioms BstLean.Part130.RProg.cost_bind
#print axioms BstLean.Part130.RProg.eval_ofSProg
#print axioms BstLean.Part130.relu_eq_sqrt
#print axioms BstLean.Part130.reluSProg_eval
#print axioms BstLean.Part130.reluSProg_cost
#print axioms BstLean.Part130.RProg.exists_sProg
#print axioms BstLean.Part130.mulVecProg_eval
#print axioms BstLean.Part130.mulVecProg_cost
#print axioms BstLean.Part130.mlpProg_eval
#print axioms BstLean.Part130.mlpProg_cost
#print axioms BstLean.Part130.sampleRProg_eval
#print axioms BstLean.Part130.sampleRProg_eval_sphPt
#print axioms BstLean.Part130.sampleRProg_cost
