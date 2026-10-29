import BstLean.Part59Defs
import BstLean.Part53Cost_Shared

namespace BstLean.Part59.TableAux59x

open BstLean.Cost
open BstLean.Part53.CostAux
open BstLean.Part41 (argHeavy Mono)

noncomputable section
set_option backward.isDefEq.respectTransparency false

private def mulSlots59x (k c : ℕ) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun e => e.val = c + 1)

private def mulSlot59x {k : ℕ} (e : Fin (k + 1)) : Prog (Unit ⊕ Fin (k + 1)) Unit :=
  Prog.op1 .add (.inp (.inr ⟨e.val - 1, by have := e.isLt; omega⟩)) (.inp (.inl ()))

def muls59x (k : ℕ) : ℕ → Prog Unit (Fin (k + 1))
  | 0 => Prog.ofArgs (fun _ => .cst 0)
  | c + 1 => (muls59x k c).update mulSlot59x (mulSlots59x k c).toList

lemma muls_clean59x (k c : ℕ) : Clean (muls59x k c) := by
  induction c with
  | zero => simp [muls59x, Clean, Prog.ofArgs, argHeavy]
  | succ c ih =>
    apply clean_update ih
    intro e
    simp [mulSlot59x, Clean, Prog.op1, argHeavy]

lemma muls_eval59x (k c : ℕ) (a : ℝ) (e : Fin (k + 1)) (he : e.val ≤ c) :
    (muls59x k c).eval (fun _ => a) e = (e.val : ℝ) * a := by
  induction c generalizing e with
  | zero =>
    have hz : e.val = 0 := by omega
    simp [muls59x, eval_ofArgs, Arg.eval, hz]
  | succ c ih =>
    rw [muls59x, eval_update]
    by_cases h : e.val = c + 1
    · rw [if_pos (by simp [mulSlots59x, h])]
      simp only [mulSlot59x, eval_op1, Arg.eval, Sum.elim_inr, Sum.elim_inl, Op.eval]
      rw [ih _ (by simp; omega)]
      have he' : e.val - 1 = c := by omega
      change ((e.val - 1 : ℕ) : ℝ) * a + a = (e.val : ℝ) * a
      rw [he', h, Nat.cast_add, Nat.cast_one]
      ring
    · rw [if_neg (by simp [mulSlots59x, h])]
      exact ih e (by omega)

lemma muls_cost59x (k c : ℕ) : (muls59x k c).cost ≤ c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [muls59x, cost_update]
    have hcard : (mulSlots59x k c).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      apply Fin.ext
      have h1 : a.val = c + 1 := (Finset.mem_filter.mp ha).2
      have h2 : b.val = c + 1 := (Finset.mem_filter.mp hb).2
      omega
    have hcost : ((mulSlots59x k c).toList.map fun e => (mulSlot59x e).cost).sum =
        (mulSlots59x k c).card := by simp [mulSlot59x]
    rw [hcost]
    omega

abbrev TableIn59x (n k : ℕ) := (Fin n ⊕ Mono n k) ⊕ Fin (k + 1)
abbrev TableKey59x (n k : ℕ) := Fin n × Fin (k + 1)

private def qSlots59x (n k c : ℕ) : Finset (TableKey59x n k) :=
  Finset.univ.filter (fun s => s.2.val = c + 2)

private def qSlot59x {n k : ℕ} (s : TableKey59x n k) :
    Prog (TableIn59x n k ⊕ TableKey59x n k) Unit :=
  let prev : Fin (k + 1) := ⟨s.2.val - 1, by have := s.2.isLt; omega⟩
  let prev2 : Fin (k + 1) := ⟨s.2.val - 2, by have := s.2.isLt; omega⟩
  let p : Prog (TableIn59x n k ⊕ TableKey59x n k) Unit :=
    Prog.op1 .mul (.inp (.inl (.inl (.inl s.1)))) (.inp (.inr (s.1, prev)))
  let q : Prog (TableIn59x n k ⊕ TableKey59x n k) Unit :=
    Prog.op1 .mul (.inp (.inl (.inr prev))) (.inp (.inr (s.1, prev2)))
  (p.pair q).bind (Prog.op1 .add (.inp (.inr (.inl ()))) (.inp (.inr (.inr ()))))

def table59x (n k : ℕ) : ℕ → Prog (TableIn59x n k) (TableKey59x n k)
  | 0 => Prog.ofArgs (fun s => if s.2.val = 0 then .cst 1 else
      if s.2.val = 1 then .inp (.inl (.inl s.1)) else .cst 0)
  | c + 1 => (table59x n k c).update qSlot59x (qSlots59x n k c).toList

lemma table_clean59x (n k c : ℕ) : Clean (table59x n k c) := by
  induction c with
  | zero =>
    constructor
    · simp [table59x, Prog.ofArgs]
    · intro s; dsimp [table59x, Prog.ofArgs]; split_ifs <;> simp [argHeavy]
  | succ c ih =>
    apply clean_update ih
    intro s
    apply clean_bind
    · apply clean_pair <;> simp [Clean, qSlot59x, Prog.op1, argHeavy]
    · simp [Clean, Prog.op1, argHeavy]

lemma table_eval59x (n k c : ℕ) (v : TableIn59x n k → ℝ) (a : ℝ)
    (ha : ∀ e : Fin (k + 1), v (.inr e) = (e.val : ℝ) * a)
    (s : TableKey59x n k) (hs : s.2.val ≤ c + 1) :
    (table59x n k c).eval v s = qH s.2.val (v (.inl (.inl s.1))) a := by
  induction c generalizing s with
  | zero =>
    have he : s.2.val = 0 ∨ s.2.val = 1 := by omega
    rcases he with he | he
    · rw [table59x, eval_ofArgs, if_pos he]
      simp [Arg.eval, he, qH]
    · rw [table59x, eval_ofArgs, if_neg (by omega), if_pos he]
      simp [Arg.eval, he, qH]
  | succ c ih =>
    rw [table59x, eval_update]
    by_cases he : s.2.val = c + 2
    · rw [if_pos (by simp [qSlots59x, he])]
      simp only [qSlot59x, eval_bind, eval_op1, eval_pair_inl, eval_pair_inr,
        Arg.eval, Sum.elim_inr, Sum.elim_inl, Op.eval, ha]
      rw [ih (s.1, ⟨s.2.val - 1, by have := s.2.isLt; omega⟩) (by simp; omega),
        ih (s.1, ⟨s.2.val - 2, by have := s.2.isLt; omega⟩) (by simp; omega)]
      have hp : s.2.val - 1 = c + 1 := by omega
      have hp2 : s.2.val - 2 = c := by omega
      simp [hp, hp2, he, qH, Nat.cast_add, Nat.cast_one]
    · rw [if_neg (by simp [qSlots59x, he])]
      exact ih s (by omega)

lemma table_cost59x (n k c : ℕ) : (table59x n k c).cost ≤ 3 * n * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [table59x, cost_update]
    have hinj : Set.InjOn Prod.fst (qSlots59x n k c : Set (TableKey59x n k)) := by
      intro a ha b hb hab
      apply Prod.ext hab
      apply Fin.ext
      have h1 : a.2.val = c + 2 := (Finset.mem_filter.mp ha).2
      have h2 : b.2.val = c + 2 := (Finset.mem_filter.mp hb).2
      omega
    have hcard : (qSlots59x n k c).card ≤ n := by
      rw [← Finset.card_image_of_injOn hinj]
      exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    have hcost : ((qSlots59x n k c).toList.map fun s => (qSlot59x s).cost).sum =
        3 * (qSlots59x n k c).card := by
      simp [qSlot59x, cost_bind, cost_pair, Nat.mul_comm]
    rw [hcost]
    nlinarith

end
end BstLean.Part59.TableAux59x
