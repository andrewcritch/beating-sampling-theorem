import BstLean.Part105Defs
import BstLean.CostModel

/-!
# Part 105, costs: the evaluation scheme and one sample of `s_B`

Paper source: `solution-plans/option-a.md` (the evaluation scheme for a polynomial map given by
its monomial coefficients; the cost of one sample of `s_B`).

* `evalProg k q d`: a straight-line program in the library model `BstLean.Cost.Prog` that reads a
  point `x : ℝ^k` and monomial coefficients `b` and computes `bwEval b x`. Its cost is at most
  `Ecost k q d = (C − 1 − k) + 2q(C − 1)`, `C = C(k+d, d)`.
* `SProg`: the library model with one more operation, the square root.
* `rescaleProg n`: computes `y/|y|` with at most `3n + 1` operations.
* `sampleProg r n dA dF`: one sample `F(A(W(u)/|W(u)|))`, with cost at most `sampleCost r n dA dF`.
* `hornerProg k d`: a nested Horner scheme for one output, with cost at most `2C − 2`; and
  `sampleProg'` with the count `sampleCost'` of the paper.
-/

namespace BstLean.Part105

open BstLean.Cost

noncomputable section

/-! ## Counting monomials -/

/-- The number of monomials of degree at most `d` in `k` variables is `C(k+d, d)`. -/
theorem card_monoIdx (k d : ℕ) : Fintype.card (MonoIdx k d) = (k + d).choose d := by
  simp only [MonoIdx, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
    ← Nat.choose_symm_add (a := d) (b := k)]
  simp [Nat.add_comm]

/-- The constant monomial. -/
def mono0 (k d : ℕ) : MonoIdx k d := ⟨⟨0, Nat.succ_pos d⟩, Sym.nil⟩

/-- The monomial `x_i` (for `1 ≤ d`). -/
def mono1 (k d : ℕ) (hd : 1 ≤ d) (i : Fin k) : MonoIdx k d :=
  ⟨⟨1, by omega⟩, ⟨{i}, rfl⟩⟩

/-- The monomials of degree at least `2`. -/
def monoBig (k d : ℕ) : Finset (MonoIdx k d) := Finset.univ.filter (fun m => 2 ≤ m.1.val)

/-- There are at least `1 + k` monomials of degree at most `1` (for `1 ≤ d`). -/
theorem card_monoBig_add (k d : ℕ) (hd : 1 ≤ d) :
    (monoBig k d).card + (k + 1) ≤ (k + d).choose d := by
  classical
  rw [← card_monoIdx]
  let f : Option (Fin k) → MonoIdx k d := fun o => o.elim (mono0 k d) (mono1 k d hd)
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j =>
        have := congrArg (fun m : MonoIdx k d => m.1.val) hab
        simp [f, mono0, mono1] at this
    | some i =>
      cases b with
      | none =>
        have := congrArg (fun m : MonoIdx k d => m.1.val) hab
        simp [f, mono0, mono1] at this
      | some j =>
        have := congrArg (fun m : MonoIdx k d => m.2.val) hab
        simp only [f, Option.elim, mono1] at this
        have h2 : i = j := by simpa using this
        rw [h2]
  have himg : (Finset.univ.image f).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hdisj : Disjoint (monoBig k d) (Finset.univ.image f) := by
    apply Finset.disjoint_left.mpr
    intro m hm hm'
    simp only [monoBig, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hm'
    cases o <;> simp [f, mono0, mono1] at hm
  rw [← himg, ← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- For `1 ≤ d`: `k ≤ C − 1`. -/
theorem le_choose_sub_one (k d : ℕ) (hd : 1 ≤ d) : k ≤ (k + d).choose d - 1 := by
  have := card_monoBig_add k d hd
  omega

/-- The number of monomials of degree at least `2` is at most `C − 1 − k` (any `d`). -/
theorem card_monoBig_le (k d : ℕ) : (monoBig k d).card ≤ (k + d).choose d - 1 - k := by
  by_cases hd : 1 ≤ d
  · have := card_monoBig_add k d hd
    omega
  · have : monoBig k d = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m _
      have := m.1.isLt
      omega
    simp [this]

/-! ## Stage 1: all monomials -/

theorem monoVal_deg_zero {k d : ℕ} (x : Fin k → ℝ) (m : MonoIdx k d) (h : m.1.val = 0) :
    monoVal x m = 1 := by
  have he : m.2.val = 0 := Multiset.card_eq_zero.mp (by rw [m.2.property]; exact h)
  change (Multiset.map x m.2.val).prod = 1
  rw [he]
  simp

theorem mono_mem_exists {k d : ℕ} (m : MonoIdx k d) (h : m.1.val ≠ 0) : ∃ a, a ∈ m.2.val := by
  have hp : 0 < Multiset.card m.2.val := by rw [m.2.property]; omega
  exact Multiset.card_pos_iff_exists_mem.mp hp

/-- A variable of a non-constant monomial. -/
def monoHead {k d : ℕ} (m : MonoIdx k d) (h : m.1.val ≠ 0) : Fin k := (mono_mem_exists m h).choose

theorem monoHead_mem {k d : ℕ} (m : MonoIdx k d) (h : m.1.val ≠ 0) : monoHead m h ∈ m.2.val :=
  (mono_mem_exists m h).choose_spec

/-- The monomial `m / x_{monoHead m}`. -/
def monoParent {k d : ℕ} (m : MonoIdx k d) (h : m.1.val ≠ 0) : MonoIdx k d :=
  ⟨⟨m.1.val - 1, by have := m.1.isLt; omega⟩,
    ⟨m.2.val.erase (monoHead m h), by
      rw [Multiset.card_erase_of_mem (monoHead_mem m h), m.2.property]
      rfl⟩⟩

theorem monoParent_deg {k d : ℕ} (m : MonoIdx k d) (h : m.1.val ≠ 0) :
    (monoParent m h).1.val = m.1.val - 1 := rfl

theorem mono_decomp {k d : ℕ} (m : MonoIdx k d) (h : m.1.val ≠ 0) (x : Fin k → ℝ) :
    monoVal x m = x (monoHead m h) * monoVal x (monoParent m h) := by
  unfold monoVal
  conv_lhs => rw [← Multiset.cons_erase (monoHead_mem m h)]
  simp [monoParent]

/-- The monomials of degree exactly `c`. -/
def monoSlots (k d c : ℕ) : Finset (MonoIdx k d) := Finset.univ.filter (fun m => m.1.val = c)

/-- One multiplication: `m = x_{head} · parent`. -/
def monoSlotProg {k d : ℕ} (m : MonoIdx k d) : Prog (Fin k ⊕ MonoIdx k d) Unit :=
  if h : m.1.val = 0 then Prog.ofArgs (fun _ => .cst 1) else
    Prog.op1 .mul (.inp (.inl (monoHead m h))) (.inp (.inr (monoParent m h)))

/-- Stage 1. `monoProg k d c` has the right value at every monomial of degree at most `c + 1`.
A monomial of degree `0` is the constant `1`, a monomial of degree `1` is an input: no operation.
A monomial of degree `j ≥ 2` is one multiplication. -/
def monoProg (k d : ℕ) : ℕ → Prog (Fin k) (MonoIdx k d)
  | 0 => Prog.ofArgs (fun m => if h : m.1.val = 0 then .cst 1 else .inp (monoHead m h))
  | c + 1 => (monoProg k d c).update monoSlotProg (monoSlots k d (c + 2)).toList

theorem monoProg_eval (k d c : ℕ) (x : Fin k → ℝ) (m : MonoIdx k d) (hm : m.1.val ≤ c + 1) :
    (monoProg k d c).eval x m = monoVal x m := by
  induction c generalizing m with
  | zero =>
    simp only [monoProg, eval_ofArgs]
    by_cases h : m.1.val = 0
    · simp [h, Arg.eval, monoVal_deg_zero x m h]
    · simp only [h, dite_false, Arg.eval]
      rw [mono_decomp m h, monoVal_deg_zero x (monoParent m h) (by rw [monoParent_deg]; omega)]
      simp
  | succ c ih =>
    rw [monoProg, eval_update]
    by_cases he : m.1.val = c + 2
    · have hmem : m ∈ (monoSlots k d (c + 2)).toList := by simp [monoSlots, he]
      rw [ite_eq_left hmem]
      have h0 : m.1.val ≠ 0 := by omega
      simp only [monoSlotProg, h0, dite_false, eval_op1, Arg.eval, Sum.elim_inl,
        Sum.elim_inr, Op.eval]
      rw [ih (monoParent m h0) (by rw [monoParent_deg]; omega), ← mono_decomp]
    · have hmem : m ∉ (monoSlots k d (c + 2)).toList := by simp [monoSlots, he]
      rw [ite_eq_right hmem]
      exact ih m (by omega)

theorem monoProg_cost_exact (k d c : ℕ) :
    (monoProg k d c).cost =
      (Finset.univ.filter (fun m : MonoIdx k d => 2 ≤ m.1.val ∧ m.1.val ≤ c + 1)).card := by
  induction c with
  | zero =>
    have : (Finset.univ.filter (fun m : MonoIdx k d => 2 ≤ m.1.val ∧ m.1.val ≤ 0 + 1)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m _
      omega
    rw [this]
    rfl
  | succ c ih =>
    rw [monoProg, cost_update, ih]
    have hs : ((monoSlots k d (c + 2)).toList.map fun m => (monoSlotProg m).cost).sum =
        (monoSlots k d (c + 2)).card := by
      have hh : ((monoSlots k d (c + 2)).toList.map fun m => (monoSlotProg m).cost) =
          (monoSlots k d (c + 2)).toList.map (fun _ => 1) := by
        apply List.map_congr_left
        intro m hm
        have he : m.1.val = c + 2 := by simpa [monoSlots] using hm
        simp [monoSlotProg, show m.1.val ≠ 0 by omega]
      rw [hh]
      simp
    rw [hs]
    have hu : (Finset.univ.filter (fun m : MonoIdx k d => 2 ≤ m.1.val ∧ m.1.val ≤ c + 1 + 1)) =
        (Finset.univ.filter (fun m : MonoIdx k d => 2 ≤ m.1.val ∧ m.1.val ≤ c + 1)) ∪
          monoSlots k d (c + 2) := by
      ext m
      simp only [monoSlots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hd : Disjoint (Finset.univ.filter (fun m : MonoIdx k d => 2 ≤ m.1.val ∧ m.1.val ≤ c + 1))
        (monoSlots k d (c + 2)) := by
      apply Finset.disjoint_left.mpr
      intro m hp hq
      simp only [monoSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      omega
    rw [hu, Finset.card_union_of_disjoint hd]

/-- Stage 1 costs at most `C − 1 − k` multiplications. -/
theorem monoProg_cost (k d c : ℕ) : (monoProg k d c).cost ≤ (k + d).choose d - 1 - k := by
  rw [monoProg_cost_exact]
  refine le_trans (Finset.card_le_card ?_) (card_monoBig_le k d)
  intro m hm
  simp only [monoBig, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  exact hm.1

/-! ## Stage 2: one linear combination per output -/

/-- The non-constant monomials, as a list. -/
def monoRest (k d : ℕ) : List (MonoIdx k d) := (Finset.univ.erase (mono0 k d)).toList

theorem length_monoRest (k d : ℕ) : (monoRest k d).length = (k + d).choose d - 1 := by
  rw [monoRest, Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_monoIdx]

/-- Output `a`: `C − 1` multiplications `b_{a,m} · x^m` (`m` non-constant) and `C − 1`
additions. The inputs are the point, the coefficients and the monomials of stage 1. -/
def outProg {k q d : ℕ} (a : Fin q) : Prog ((Fin k ⊕ CoefIdx k q d) ⊕ MonoIdx k d) Unit :=
  (Prog.par (fun m : MonoIdx k d => Prog.op1 .mul (.inp (.inl (.inr (a, m)))) (.inp (.inr m)))
      (monoRest k d)).bind
    (Prog.sumArgs (.inp (.inl (.inl (.inr (a, mono0 k d)))) ::
      (monoRest k d).map (fun m => .inp (.inr m))))

theorem outProg_eval {k q d : ℕ} (a : Fin q) (x : Fin k → ℝ) (b : CoefIdx k q d → ℝ)
    (M : MonoIdx k d → ℝ) :
    (outProg a).eval (Sum.elim (Sum.elim x b) M) () =
      b (a, mono0 k d) + ∑ m ∈ Finset.univ.erase (mono0 k d), b (a, m) * M m := by
  simp only [outProg, eval_bind, eval_sumArgs, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  refine Eq.trans ?_
    (Finset.sum_map_toList (Finset.univ.erase (mono0 k d)) (fun m => b (a, m) * M m))
  apply congrArg
  apply List.map_congr_left
  intro m hm
  simp only [Function.comp, Arg.eval, Sum.elim_inr]
  rw [eval_par_mem _ _ _ _ hm, eval_op1]
  rfl

theorem outProg_cost {k q d : ℕ} (a : Fin q) :
    (outProg (k := k) (d := d) a).cost = 2 * ((k + d).choose d - 1) := by
  simp only [outProg, cost_bind, cost_par, cost_op1, cost_sumArgs, List.length_cons,
    List.length_map, List.map_const', List.sum_replicate, smul_eq_mul, mul_one, length_monoRest]
  omega

/-! ## Item 1: the evaluation program -/

/-- **The evaluation scheme.** Inputs: the point `x` and the monomial coefficients `b`.
Outputs: the `q` coordinates of `p(x)`. -/
def evalProg (k q d : ℕ) : Prog (Fin k ⊕ CoefIdx k q d) (Fin q) :=
  ((monoProg k d d).mapIn Sum.inl).bind (Prog.par outProg (List.finRange q))

theorem evalProg_eval {k q d : ℕ} (x : Fin k → ℝ) (b : CoefIdx k q d → ℝ) (a : Fin q) :
    (evalProg k q d).eval (Sum.elim x b) a = bwEval b x a := by
  rw [evalProg, eval_bind, eval_par_mem _ _ _ _ (List.mem_finRange a), outProg_eval]
  unfold bwEval
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (mono0 k d)),
    monoVal_deg_zero x (mono0 k d) rfl, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_mapIn]
  have hx : (Sum.elim x b ∘ Sum.inl) = x := rfl
  rw [hx, monoProg_eval k d d x m (by have := m.1.isLt; omega)]

/-- The operation count `E(k, q, d) = (C − 1 − k) + 2q(C − 1)`, `C = C(k+d, d)`. -/
def Ecost (k q d : ℕ) : ℕ := ((k + d).choose d - 1 - k) + 2 * q * ((k + d).choose d - 1)

theorem evalProg_cost (k q d : ℕ) : (evalProg k q d).cost ≤ Ecost k q d := by
  rw [evalProg, cost_bind, cost_mapIn, cost_par]
  simp only [outProg_cost, List.map_const', List.sum_replicate, List.length_finRange,
    smul_eq_mul, Ecost]
  have := monoProg_cost k d d
  nlinarith [this]

/-! ## Item 2: a cost model with a square root -/

section sqrtModel

variable {ι ι₂ κ κ₂ ν : Type}

/-- The operations of the extended model: the four real-RAM operations and the square root. -/
inductive SOp
  | add | sub | mul | div | sqrt

/-- The value of an operation. `sqrt` uses its first argument only. -/
def SOp.eval : SOp → ℝ → ℝ → ℝ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .sqrt, a, _ => Real.sqrt a

/-- One instruction of the extended model. The arguments are those of the library model
(`BstLean.Cost.Arg`: an input, an earlier register, or a rational constant). -/
structure SInstr (ι : Type) where
  op : SOp
  a : Arg ι
  b : Arg ι

/-- **A straight-line program with square roots.** This is the library model
`BstLean.Cost.Prog` with one more operation.

Conventions:
* A program is a finite list of instructions and an output map. Each instruction is one of
  `+ − × ÷ √` on arguments that are inputs, earlier registers or rational constants.
* The cost is the number of instructions: every arithmetic operation costs one and every square
  root costs one. Reading an input, a register or a constant is free.
* Evaluation is total, as in the library model: a register that is not yet computed reads `0`,
  `x / 0 = 0`, and `√x = 0` for `x < 0` (`Real.sqrt`).
* There is no branching. -/
structure SProg (ι κ : Type) where
  body : List (SInstr ι)
  out : κ → Arg ι

/-- The value of an instruction. -/
def SInstr.eval (v : ι → ℝ) (R : List ℝ) (I : SInstr ι) : ℝ :=
  I.op.eval (I.a.eval v R) (I.b.eval v R)

/-- Run a list of instructions, appending each value to the registers. -/
def srun (v : ι → ℝ) : List (SInstr ι) → List ℝ → List ℝ
  | [], R => R
  | I :: is, R => srun v is (R ++ [I.eval v R])

/-- The value of a program at output `k`. -/
def SProg.eval (p : SProg ι κ) (v : ι → ℝ) (k : κ) : ℝ :=
  (p.out k).eval v (srun v p.body [])

/-- The cost of a program: its number of instructions. -/
def SProg.cost (p : SProg ι κ) : ℕ := p.body.length

def SInstr.rename (σ : ι → ι₂) (I : SInstr ι) : SInstr ι₂ := ⟨I.op, I.a.rename σ, I.b.rename σ⟩

def SInstr.subst (σ : ι → Arg ι₂) (shift len : ℕ) (I : SInstr ι) : SInstr ι₂ :=
  ⟨I.op, I.a.subst σ shift len, I.b.subst σ shift len⟩

/-- The embedding of the four library operations. -/
def opToS : Op → SOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

def instrToS (I : Instr ι) : SInstr ι := ⟨opToS I.op, I.a, I.b⟩

/-- A program of the library model is a program of the extended model. -/
def SProg.ofProg (p : Prog ι κ) : SProg ι κ := ⟨p.body.map instrToS, p.out⟩

/-- One square root. -/
def SProg.sqrt1 (a : Arg ι) : SProg ι Unit := ⟨[⟨.sqrt, a, a⟩], fun _ => .reg 0⟩

/-- Rename the inputs of a program. -/
def SProg.mapIn (σ : ι → ι₂) (p : SProg ι κ) : SProg ι₂ κ :=
  ⟨p.body.map (SInstr.rename σ), fun k => (p.out k).rename σ⟩

/-- Reindex the outputs of a program. -/
def SProg.mapOut (τ : κ₂ → κ) (p : SProg ι κ) : SProg ι κ₂ := ⟨p.body, fun k => p.out (τ k)⟩

/-- Sequencing with sharing: run `p`, then run `q` on the inputs together with `p`'s outputs. -/
def SProg.bind (p : SProg ι κ) (q : SProg (ι ⊕ κ) ν) : SProg ι ν :=
  let s := p.body.length
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun k => (p.out k).clamp s)
  ⟨p.body ++ q.body.map (SInstr.subst σ s q.body.length),
    fun l => (q.out l).subst σ s q.body.length⟩

theorem srun_append (v : ι → ℝ) (as bs : List (SInstr ι)) (R : List ℝ) :
    srun v (as ++ bs) R = srun v bs (srun v as R) := by
  induction as generalizing R with
  | nil => rfl
  | cons I is ih => simp only [List.cons_append, srun]; exact ih _

theorem length_srun (v : ι → ℝ) (is : List (SInstr ι)) (R : List ℝ) :
    (srun v is R).length = R.length + is.length := by
  induction is generalizing R with
  | nil => simp [srun]
  | cons I is ih => simp [srun, ih]; omega

theorem opToS_eval (op : Op) (a b : ℝ) : (opToS op).eval a b = op.eval a b := by
  cases op <;> rfl

theorem srun_ofProg (v : ι → ℝ) (is : List (Instr ι)) (R : List ℝ) :
    srun v (is.map instrToS) R = run v is R := by
  induction is generalizing R with
  | nil => rfl
  | cons I is ih =>
    simp only [List.map_cons, srun, run]
    rw [ih]
    congr 2
    simp [SInstr.eval, Instr.eval, instrToS, opToS_eval]

/-- The embedding keeps the value. -/
@[simp] theorem SProg.eval_ofProg (p : Prog ι κ) (v : ι → ℝ) (k : κ) :
    (SProg.ofProg p).eval v k = p.eval v k := by
  simp [SProg.ofProg, SProg.eval, Prog.eval, srun_ofProg]

/-- The embedding keeps the cost. -/
@[simp] theorem SProg.cost_ofProg (p : Prog ι κ) : (SProg.ofProg p).cost = p.cost := by
  simp [SProg.ofProg, SProg.cost, Prog.cost]

@[simp] theorem SProg.eval_sqrt1 (a : Arg ι) (v : ι → ℝ) (u : Unit) :
    (SProg.sqrt1 a).eval v u = Real.sqrt (a.eval v []) := by
  simp [SProg.sqrt1, SProg.eval, srun, Arg.eval, SInstr.eval, SOp.eval]

@[simp] theorem SProg.cost_sqrt1 (a : Arg ι) : (SProg.sqrt1 a).cost = 1 := rfl

theorem srun_rename (σ : ι → ι₂) (v : ι₂ → ℝ) (is : List (SInstr ι)) (R : List ℝ) :
    srun v (is.map (SInstr.rename σ)) R = srun (v ∘ σ) is R := by
  induction is generalizing R with
  | nil => rfl
  | cons I is ih =>
    simp only [List.map_cons, srun]
    rw [ih]
    congr 2
    simp [SInstr.eval, SInstr.rename, Arg.eval_rename]

@[simp] theorem SProg.eval_mapIn (σ : ι → ι₂) (p : SProg ι κ) (v : ι₂ → ℝ) (k : κ) :
    (p.mapIn σ).eval v k = p.eval (v ∘ σ) k := by
  simp [SProg.mapIn, SProg.eval, srun_rename, Arg.eval_rename]

@[simp] theorem SProg.cost_mapIn (σ : ι → ι₂) (p : SProg ι κ) : (p.mapIn σ).cost = p.cost := by
  simp [SProg.mapIn, SProg.cost]

@[simp] theorem SProg.eval_mapOut (τ : κ₂ → κ) (p : SProg ι κ) (v : ι → ℝ) (k : κ₂) :
    (p.mapOut τ).eval v k = p.eval v (τ k) := rfl

@[simp] theorem SProg.cost_mapOut (τ : κ₂ → κ) (p : SProg ι κ) : (p.mapOut τ).cost = p.cost := rfl

theorem srun_subst (σ : ι → Arg ι₂) (v : ι₂ → ℝ) (R : List ℝ) (len : ℕ)
    (hσ : ∀ i T, (σ i).eval v (R ++ T) = (σ i).eval v R)
    (is : List (SInstr ι)) (S : List ℝ) (hS : S.length + is.length ≤ len) :
    srun v (is.map (SInstr.subst σ R.length len)) (R ++ S) =
      R ++ srun (fun i => (σ i).eval v R) is S := by
  induction is generalizing S with
  | nil => simp [srun]
  | cons I is ih =>
    simp only [List.map_cons, srun]
    have hS' : S.length ≤ len := by simp at hS; omega
    have : SInstr.eval v (R ++ S) (SInstr.subst σ R.length len I) =
        SInstr.eval (fun i => (σ i).eval v R) S I := by
      simp only [SInstr.eval, SInstr.subst]
      rw [Arg.eval_subst σ v R S len hS' hσ, Arg.eval_subst σ v R S len hS' hσ]
    rw [this, List.append_assoc]
    exact ih _ (by simp at hS ⊢; omega)

theorem clamp_eval' (v : ι → ℝ) (R T : List ℝ) (a : Arg ι) :
    (a.clamp R.length).eval v (R ++ T) = a.eval v R := by
  cases a with
  | inp i => rfl
  | cst q => rfl
  | reg r =>
    simp only [Arg.clamp]
    split_ifs with h
    · simp only [Arg.eval]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · simp only [Arg.eval]
      rw [List.getD_eq_default _ _ (by omega)]
      simp

theorem SProg.eval_bind (p : SProg ι κ) (q : SProg (ι ⊕ κ) ν) (v : ι → ℝ) (l : ν) :
    (p.bind q).eval v l = q.eval (Sum.elim v (p.eval v)) l := by
  set R := srun v p.body [] with hR
  have hlen : R.length = p.body.length := by simp [hR, length_srun]
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
      simp only [σ, Sum.elim_inr, SProg.eval]
      rw [← hlen]
      have := clamp_eval' v R [] (p.out k)
      simpa using this
  have hrun : srun v (p.bind q).body [] = R ++ srun (Sum.elim v (p.eval v)) q.body [] := by
    simp only [SProg.bind]
    rw [← hv]
    have h1 : srun v (p.body ++ List.map (SInstr.subst σ p.body.length q.body.length) q.body) [] =
        srun v (List.map (SInstr.subst σ p.body.length q.body.length) q.body) (R ++ []) := by
      rw [List.append_nil, hR, srun_append]
    rw [h1, ← hlen]
    exact srun_subst σ v R q.body.length hσ q.body [] (by simp)
  have key := Arg.eval_subst σ v R (srun (fun i => (σ i).eval v R) q.body []) q.body.length
    (by simp [length_srun]) hσ (q.out l)
  rw [hlen] at key
  simp only [SProg.eval]
  rw [hrun, ← hv]
  exact key

@[simp] theorem SProg.cost_bind (p : SProg ι κ) (q : SProg (ι ⊕ κ) ν) :
    (p.bind q).cost = p.cost + q.cost := by
  simp [SProg.bind, SProg.cost]

end sqrtModel

/-! ## Item 3: the rescaling -/

/-- `Σ y_i²`, then the square root, then `1/√·`: `n` multiplications, `n − 1` additions, one
square root and one division. -/
def invNormProg (n : ℕ) : SProg (Fin n) Unit :=
  ((SProg.ofProg (Prog.sumProd ((List.finRange n).map fun i => (Arg.inp i, Arg.inp i)))).bind
      (SProg.sqrt1 (.inp (.inr ())))).bind
    (SProg.ofProg (Prog.op1 .div (.cst 1) (.inp (.inr ()))))

theorem invNormProg_eval {n : ℕ} (y : Fin n → ℝ) (u : Unit) :
    (invNormProg n).eval y u = 1 / Real.sqrt (∑ i, y i ^ 2) := by
  have hs : (Prog.sumProd ((List.finRange n).map fun i => (Arg.inp i, Arg.inp i))).eval y () =
      ∑ i, y i ^ 2 := by
    rw [eval_sumProd, List.map_map, Fin.sum_univ_def]
    apply congrArg
    apply List.map_congr_left
    intro j _
    simp [Arg.eval, pow_two]
  rw [invNormProg, SProg.eval_bind, SProg.eval_ofProg, eval_op1]
  simp only [Op.eval, Arg.eval, Sum.elim_inr, Rat.cast_one]
  rw [SProg.eval_bind, SProg.eval_sqrt1]
  simp only [Arg.eval, Sum.elim_inr, SProg.eval_ofProg]
  rw [hs]

/-- **The rescaling `y ↦ y/|y|`**: `n` multiplications and `n − 1` additions for `Σ y_i²`, one
square root, one division `1/√·`, `n` multiplications. (For `n = 0` the program is empty.) -/
def rescaleProg (n : ℕ) : SProg (Fin n) (Fin n) :=
  if n = 0 then ⟨[], fun _ => .cst 0⟩ else
    (invNormProg n).bind
      (SProg.ofProg
        (Prog.par (fun i : Fin n => Prog.op1 .mul (.inp (.inr ())) (.inp (.inl i)))
          (List.finRange n)))

theorem rescaleProg_eval {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    (rescaleProg n).eval y i = sphProj y i := by
  have hn : n ≠ 0 := fun h => (h ▸ i).elim0
  simp only [rescaleProg, hn, ite_false]
  rw [SProg.eval_bind, SProg.eval_ofProg, eval_par_mem _ _ _ _ (List.mem_finRange i), eval_op1]
  simp only [Op.eval, Arg.eval, Sum.elim_inl, Sum.elim_inr, sphProj, Pi.smul_apply, smul_eq_mul]
  rw [invNormProg_eval]

theorem rescaleProg_cost (n : ℕ) : (rescaleProg n).cost ≤ 3 * n + 1 := by
  by_cases hn : n = 0
  · simp [rescaleProg, hn, SProg.cost]
  · simp only [rescaleProg, invNormProg, hn, ite_false, SProg.cost_bind, SProg.cost_ofProg,
      SProg.cost_sqrt1, cost_sumProd, cost_op1, cost_par, List.length_map, List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
    omega

/-! ## Item 4: one sample of `s_B` -/

/-- The inputs of one sample: the point `u`, and the coefficients of `W`, `A` and `F`. -/
abbrev SampleIn (r n dA dF : ℕ) : Type :=
  Fin (r * n) ⊕ CoefIdx (r * n) n (r * dA) ⊕ CoefIdx n n dA ⊕ CoefIdx n 1 dF

/-- The inputs as one valuation. -/
def sampleVal {r n dA dF : ℕ} (u : Fin (r * n) → ℝ) (W : CoefIdx (r * n) n (r * dA) → ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) : SampleIn r n dA dF → ℝ :=
  Sum.elim u (Sum.elim W (Sum.elim A F))

/-- The first three steps of one sample: `W(u)`, the rescaling, `A(x)`. -/
def sampleProgA (r n dA dF : ℕ) : SProg (SampleIn r n dA dF) (Fin n) :=
  ((SProg.ofProg ((evalProg (r * n) n (r * dA)).mapIn
        (Sum.elim Sum.inl (fun c => Sum.inr (Sum.inl c))))).bind
      ((rescaleProg n).mapIn Sum.inr)).bind
    (SProg.ofProg ((evalProg n n dA).mapIn
      (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inl c)))))))

theorem sampleProgA_eval {r n dA dF : ℕ} (u : Fin (r * n) → ℝ)
    (W : CoefIdx (r * n) n (r * dA) → ℝ) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (i : Fin n) :
    (sampleProgA r n dA dF).eval (sampleVal u W A F) i =
      bwEval A (sphProj (bwEval W u)) i := by
  simp only [sampleProgA, SProg.eval_bind, SProg.eval_ofProg, eval_mapIn]
  have h1 : (Sum.elim (sampleVal u W A F)
      ((((SProg.ofProg ((evalProg (r * n) n (r * dA)).mapIn
        (Sum.elim Sum.inl (fun c => Sum.inr (Sum.inl c))))).bind
          ((rescaleProg n).mapIn Sum.inr))).eval (sampleVal u W A F)) ∘
        (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inl c)))))) =
      Sum.elim (sphProj (bwEval W u)) A := by
    funext j
    cases j with
    | inr c => rfl
    | inl j =>
      simp only [Function.comp, Sum.elim_inl, Sum.elim_inr, SProg.eval_bind, SProg.eval_mapIn]
      have h2 : (Sum.elim (sampleVal u W A F)
          ((SProg.ofProg ((evalProg (r * n) n (r * dA)).mapIn
            (Sum.elim Sum.inl (fun c => Sum.inr (Sum.inl c))))).eval (sampleVal u W A F)) ∘
            Sum.inr) = bwEval W u := by
        funext a
        simp only [Function.comp, Sum.elim_inr, SProg.eval_ofProg, eval_mapIn]
        have h3 : (sampleVal u W A F ∘ Sum.elim Sum.inl (fun c => Sum.inr (Sum.inl c))) =
            Sum.elim u W := by
          funext j
          cases j <;> rfl
        rw [h3, evalProg_eval]
      rw [h2, rescaleProg_eval]
  rw [h1, evalProg_eval]

theorem sampleProgA_cost (r n dA dF : ℕ) :
    (sampleProgA r n dA dF).cost ≤ Ecost (r * n) n (r * dA) + (3 * n + 1) + Ecost n n dA := by
  simp only [sampleProgA, SProg.cost_bind, SProg.cost_ofProg, SProg.cost_mapIn, cost_mapIn]
  have h1 := evalProg_cost (r * n) n (r * dA)
  have h2 := rescaleProg_cost n
  have h3 := evalProg_cost n n dA
  omega

/-- The input renaming for the last step: the point is `A(x)`, the coefficients are those of
`F`. -/
def sampleInF (r n dA dF : ℕ) : Fin n ⊕ CoefIdx n 1 dF → SampleIn r n dA dF ⊕ Fin n :=
  Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inr c))))

theorem sampleInF_comp {r n dA dF : ℕ} (u : Fin (r * n) → ℝ)
    (W : CoefIdx (r * n) n (r * dA) → ℝ) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (z : Fin n → ℝ) :
    (Sum.elim (sampleVal u W A F) z ∘ sampleInF r n dA dF) = Sum.elim z F := by
  funext j
  cases j <;> rfl

/-- **One sample of `s_B`**: `F(A(x))`, `x = W(u)/|W(u)|`, with `F` evaluated by the general
scheme `evalProg`. -/
def sampleProg (r n dA dF : ℕ) : SProg (SampleIn r n dA dF) Unit :=
  ((sampleProgA r n dA dF).bind
    (SProg.ofProg ((evalProg n 1 dF).mapIn (sampleInF r n dA dF)))).mapOut (fun _ => 0)

theorem sampleProg_eval {r n dA dF : ℕ} (u : Fin (r * n) → ℝ)
    (W : CoefIdx (r * n) n (r * dA) → ℝ) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    (sampleProg r n dA dF).eval (sampleVal u W A F) () =
      bwEval F (bwEval A (sphProj (bwEval W u))) 0 := by
  simp only [sampleProg, SProg.eval_mapOut, SProg.eval_bind, SProg.eval_ofProg, eval_mapIn]
  rw [sampleInF_comp, evalProg_eval]
  congr 1
  funext i
  exact sampleProgA_eval u W A F i

/-- The cost bound of `sampleProg`. -/
def sampleCost (r n dA dF : ℕ) : ℕ :=
  Ecost (r * n) n (r * dA) + (3 * n + 1) + Ecost n n dA + Ecost n 1 dF

theorem sampleProg_cost (r n dA dF : ℕ) :
    (sampleProg r n dA dF).cost ≤ sampleCost r n dA dF := by
  simp only [sampleProg, SProg.cost_mapOut, SProg.cost_bind, SProg.cost_ofProg, cost_mapIn,
    sampleCost]
  have h1 := sampleProgA_cost r n dA dF
  have h2 := evalProg_cost n 1 dF
  omega

/-! ## The nested Horner scheme for one output -/

section horner

variable {k q d : ℕ}

/-- The parent of a monomial (a constant monomial is its own parent). -/
def monoPar (m : MonoIdx k d) : MonoIdx k d := if h : m.1.val = 0 then m else monoParent m h

/-- The value of the variable `monoHead m` (and `0` for a constant monomial). -/
def hdVal (x : Fin k → ℝ) (m : MonoIdx k d) : ℝ := if h : m.1.val = 0 then 0 else x (monoHead m h)

/-- The non-constant monomials with parent `m`. -/
def monoChildren (m : MonoIdx k d) : Finset (MonoIdx k d) :=
  Finset.univ.filter (fun m' => m'.1.val ≠ 0 ∧ monoPar m' = m)

/-- The monomials of degree `d − c`. -/
def monoLevel (k d c : ℕ) : Finset (MonoIdx k d) := Finset.univ.filter (fun m => m.1.val + c = d)

theorem hdVal_mul (x : Fin k → ℝ) (m : MonoIdx k d) (h : m.1.val ≠ 0) :
    hdVal x m * monoVal x (monoPar m) = monoVal x m := by
  simp only [hdVal, monoPar, h, dite_false]
  exact (mono_decomp m h x).symm

theorem monoPar_deg (m : MonoIdx k d) (h : m.1.val ≠ 0) : (monoPar m).1.val = m.1.val - 1 := by
  simp only [monoPar, h, dite_false]
  rfl

theorem monoPar_mem_level {c : ℕ} (hc : c < d) (m : MonoIdx k d) (hm : m ∈ monoLevel k d c) :
    monoPar m ∈ monoLevel k d (c + 1) := by
  simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  rw [monoPar_deg m (by omega)]
  omega

theorem level_fiber {c : ℕ} (hc : c < d) (m : MonoIdx k d) (hm : m ∈ monoLevel k d (c + 1)) :
    (monoLevel k d c).filter (fun m' => monoPar m' = m) = monoChildren m := by
  ext m'
  simp only [monoLevel, monoChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := monoPar_deg m' h1
    rw [h2] at this
    omega

/-- One multiplication `x_{head m'} · H(m')`. -/
def hornerMul (m' : MonoIdx k d) : Prog ((Fin k ⊕ CoefIdx k q d) ⊕ MonoIdx k d) Unit :=
  if h : m'.1.val = 0 then Prog.ofArgs (fun _ => .cst 0) else
    Prog.op1 .mul (.inp (.inl (.inl (monoHead m' h)))) (.inp (.inr m'))

theorem hornerMul_eval (x : Fin k → ℝ) (b : CoefIdx k q d → ℝ) (G : MonoIdx k d → ℝ)
    (m' : MonoIdx k d) :
    (hornerMul m').eval (Sum.elim (Sum.elim x b) G) () = hdVal x m' * G m' := by
  by_cases h : m'.1.val = 0
  · simp [hornerMul, hdVal, h, Arg.eval]
  · simp [hornerMul, hdVal, h, Arg.eval, Op.eval]

/-- `H(m) = b_{a,m} + Σ_{m' child of m} x_{head m'} · H(m')`: one multiplication and one
addition for each child. -/
def hornerSlot (a : Fin q) (m : MonoIdx k d) :
    Prog ((Fin k ⊕ CoefIdx k q d) ⊕ MonoIdx k d) Unit :=
  (Prog.par hornerMul (monoChildren m).toList).bind
    (Prog.sumArgs (.inp (.inl (.inl (.inr (a, m)))) ::
      (monoChildren m).toList.map (fun m' => .inp (.inr m'))))

theorem hornerSlot_eval (a : Fin q) (m : MonoIdx k d) (x : Fin k → ℝ) (b : CoefIdx k q d → ℝ)
    (G : MonoIdx k d → ℝ) :
    (hornerSlot a m).eval (Sum.elim (Sum.elim x b) G) () =
      b (a, m) + ∑ m' ∈ monoChildren m, hdVal x m' * G m' := by
  simp only [hornerSlot, eval_bind, eval_sumArgs, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  refine Eq.trans ?_ (Finset.sum_map_toList (monoChildren m) (fun m' => hdVal x m' * G m'))
  apply congrArg
  apply List.map_congr_left
  intro m' hm'
  simp only [Function.comp, Arg.eval, Sum.elim_inr]
  rw [eval_par_mem _ _ _ _ hm', hornerMul_eval]

theorem hornerSlot_cost (a : Fin q) (m : MonoIdx k d) :
    (hornerSlot a m).cost = 2 * (monoChildren m).card := by
  have hh : ((monoChildren m).toList.map fun m' => (hornerMul (q := q) m').cost) =
      (monoChildren m).toList.map (fun _ => 1) := by
    apply List.map_congr_left
    intro m' hm'
    have h0 : m'.1.val ≠ 0 := by
      have := Finset.mem_toList.mp hm'
      simp only [monoChildren, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.1
    simp [hornerMul, h0]
  simp only [hornerSlot, cost_bind, cost_par, cost_sumArgs, List.length_cons, List.length_map]
  rw [hh]
  simp
  omega

/-- The register file of the Horner scheme: after `c` steps, `H(m)` is final for every monomial
of degree at least `d − c`. -/
def hornerReg (a : Fin q) : ℕ → Prog (Fin k ⊕ CoefIdx k q d) (MonoIdx k d)
  | 0 => Prog.ofArgs (fun m => .inp (.inr (a, m)))
  | c + 1 => (hornerReg a c).update (hornerSlot a) (monoLevel k d (c + 1)).toList

theorem hornerReg_inv (a : Fin q) (x : Fin k → ℝ) (b : CoefIdx k q d → ℝ) (c : ℕ) (hc : c ≤ d) :
    ∑ m ∈ Finset.univ.filter (fun m : MonoIdx k d => m.1.val + c < d), b (a, m) * monoVal x m +
      ∑ m ∈ monoLevel k d c, (hornerReg a c).eval (Sum.elim x b) m * monoVal x m =
    bwEval b x a := by
  induction c with
  | zero =>
    unfold bwEval
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun m : MonoIdx k d => m.1.val + 0 < d) (fun m => b (a, m) * monoVal x m)]
    congr 1
    have hL : monoLevel k d 0 =
        Finset.univ.filter (fun m : MonoIdx k d => ¬ (m.1.val + 0 < d)) := by
      ext m
      simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and]
      have := m.1.isLt
      omega
    rw [hL]
    apply Finset.sum_congr rfl
    intro m _
    simp [hornerReg, Arg.eval]
  | succ c ih =>
    have hc' : c < d := by omega
    rw [← ih (by omega)]
    have hsplit : Finset.univ.filter (fun m : MonoIdx k d => m.1.val + c < d) =
        Finset.univ.filter (fun m : MonoIdx k d => m.1.val + (c + 1) < d) ∪
          monoLevel k d (c + 1) := by
      ext m
      simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.univ.filter (fun m : MonoIdx k d => m.1.val + (c + 1) < d))
        (monoLevel k d (c + 1)) := by
      apply Finset.disjoint_left.mpr
      intro m h1 h2
      simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj, add_assoc]
    congr 1
    have hstep : ∀ m ∈ monoLevel k d (c + 1),
        (hornerReg a (c + 1)).eval (Sum.elim x b) m * monoVal x m =
          b (a, m) * monoVal x m +
            ∑ m' ∈ (monoLevel k d c).filter (fun m' => monoPar m' = m),
              (hornerReg a c).eval (Sum.elim x b) m' * monoVal x m' := by
      intro m hm
      have hmem : m ∈ (monoLevel k d (c + 1)).toList := Finset.mem_toList.mpr hm
      rw [hornerReg, eval_update, ite_eq_left hmem, hornerSlot_eval, add_mul, Finset.sum_mul,
        level_fiber hc' m hm]
      congr 1
      apply Finset.sum_congr rfl
      intro m' hm'
      simp only [monoChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hm'
      rw [← hdVal_mul x m' hm'.1, hm'.2]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_fiberwise_of_maps_to (fun m' hm' => monoPar_mem_level hc' m' hm') _

theorem hornerReg_cost (a : Fin q) (c : ℕ) (hc : c ≤ d) :
    (hornerReg (k := k) (d := d) a c).cost =
      2 * (Finset.univ.filter (fun m : MonoIdx k d => d < m.1.val + c)).card := by
  induction c with
  | zero =>
    have : (Finset.univ.filter (fun m : MonoIdx k d => d < m.1.val + 0)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m _
      have := m.1.isLt
      omega
    rw [this]
    rfl
  | succ c ih =>
    have hc' : c < d := by omega
    rw [hornerReg, cost_update, ih (by omega)]
    have hs : ((monoLevel k d (c + 1)).toList.map fun m => (hornerSlot a m).cost).sum =
        2 * (monoLevel k d c).card := by
      simp only [hornerSlot_cost]
      rw [Finset.sum_map_toList,
        Finset.card_eq_sum_card_fiberwise (fun m' hm' => monoPar_mem_level hc' m' hm'),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [level_fiber hc' m hm]
    rw [hs]
    have hu : Finset.univ.filter (fun m : MonoIdx k d => d < m.1.val + (c + 1)) =
        Finset.univ.filter (fun m : MonoIdx k d => d < m.1.val + c) ∪ monoLevel k d c := by
      ext m
      simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hd : Disjoint (Finset.univ.filter (fun m : MonoIdx k d => d < m.1.val + c))
        (monoLevel k d c) := by
      apply Finset.disjoint_left.mpr
      intro m h1 h2
      simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    rw [hu, Finset.card_union_of_disjoint hd]
    ring

theorem eq_mono0 (m : MonoIdx k d) (h : m.1.val = 0) : m = mono0 k d := by
  obtain ⟨⟨j, hj⟩, ⟨s, hs⟩⟩ := m
  simp only at h
  subst h
  have : s = 0 := Multiset.card_eq_zero.mp hs
  subst this
  rfl

/-- **The nested Horner scheme** for the output coordinate `a`: every non-constant monomial
costs one multiplication and one addition. -/
def hornerProg (k q d : ℕ) (a : Fin q) : Prog (Fin k ⊕ CoefIdx k q d) Unit :=
  (hornerReg a d).mapOut (fun _ => mono0 k d)

theorem hornerProg_eval (x : Fin k → ℝ) (b : CoefIdx k q d → ℝ) (a : Fin q) :
    (hornerProg k q d a).eval (Sum.elim x b) () = bwEval b x a := by
  rw [← hornerReg_inv a x b d le_rfl]
  have h1 : Finset.univ.filter (fun m : MonoIdx k d => m.1.val + d < d) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro m _
    omega
  have h2 : monoLevel k d d = {mono0 k d} := by
    ext m
    simp only [monoLevel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact eq_mono0 m (by omega)
    · rintro rfl
      simp [mono0]
  rw [h1, h2, Finset.sum_empty, zero_add, Finset.sum_singleton,
    monoVal_deg_zero x (mono0 k d) rfl, mul_one]
  rfl

theorem hornerProg_cost (k q d : ℕ) (a : Fin q) :
    (hornerProg k q d a).cost ≤ 2 * (k + d).choose d - 2 := by
  rw [hornerProg, cost_mapOut, hornerReg_cost a d le_rfl]
  have hsub : Finset.univ.filter (fun m : MonoIdx k d => d < m.1.val + d) ⊆
      Finset.univ.erase (mono0 k d) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    simp [mono0] at hm
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_monoIdx] at this
  omega

end horner

/-- **One sample of `s_B`, with the Horner scheme for `F`.** -/
def sampleProg' (r n dA dF : ℕ) : SProg (SampleIn r n dA dF) Unit :=
  (sampleProgA r n dA dF).bind
    (SProg.ofProg ((hornerProg n 1 dF 0).mapIn (sampleInF r n dA dF)))

theorem sampleProg'_eval {r n dA dF : ℕ} (u : Fin (r * n) → ℝ)
    (W : CoefIdx (r * n) n (r * dA) → ℝ) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    (sampleProg' r n dA dF).eval (sampleVal u W A F) () =
      bwEval F (bwEval A (sphProj (bwEval W u))) 0 := by
  simp only [sampleProg', SProg.eval_bind, SProg.eval_ofProg, eval_mapIn]
  rw [sampleInF_comp, hornerProg_eval]
  congr 1
  funext i
  exact sampleProgA_eval u W A F i

/-- The cost of one sample of `s_B`, as in the paper. -/
def sampleCost' (r n dA dF : ℕ) : ℕ :=
  Ecost (r * n) n (r * dA) + (3 * n + 1) + Ecost n n dA + (2 * (n + dF).choose dF - 2)

theorem sampleProg'_cost (r n dA dF : ℕ) :
    (sampleProg' r n dA dF).cost ≤ sampleCost' r n dA dF := by
  simp only [sampleProg', SProg.cost_bind, SProg.cost_ofProg, cost_mapIn, sampleCost']
  have h1 := sampleProgA_cost r n dA dF
  have h2 := hornerProg_cost n 1 dF 0
  omega

end

end BstLean.Part105

#print axioms BstLean.Part105.evalProg_eval
#print axioms BstLean.Part105.evalProg_cost
#print axioms BstLean.Part105.le_choose_sub_one
#print axioms BstLean.Part105.SProg.eval_ofProg
#print axioms BstLean.Part105.SProg.cost_ofProg
#print axioms BstLean.Part105.SProg.eval_bind
#print axioms BstLean.Part105.SProg.cost_bind
#print axioms BstLean.Part105.rescaleProg_eval
#print axioms BstLean.Part105.rescaleProg_cost
#print axioms BstLean.Part105.sampleProg_eval
#print axioms BstLean.Part105.sampleProg_cost
#print axioms BstLean.Part105.hornerProg_eval
#print axioms BstLean.Part105.hornerProg_cost
#print axioms BstLean.Part105.sampleProg'_eval
#print axioms BstLean.Part105.sampleProg'_cost
