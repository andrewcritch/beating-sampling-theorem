import BstLean.Part53Cost_Shared
import BstLean.Part59Defs

/-! Weighted tree evaluation with two arithmetic operations per edge. -/
namespace BstLean.Part59.TreeAux59x

open BstLean.Cost
open BstLean.Part53.CostAux
open BstLean.Part41 (argHeavy)

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [DecidableEq α]

/-- Transfer the coefficient of `a` to its parent, and clear `a`. -/
def transfer59x (a b : α) : Prog (α ⊕ α) (α ⊕ α) :=
  let mul := Prog.op1 .mul (.inp (.inl a)) (.inp (.inr a))
  let add := mul.bind (Prog.op1 .add (.inp (.inl (.inr b))) (.inp (.inr ())))
  ⟨add.body, fun i => match i with
    | .inl e => .inp (.inl e)
    | .inr c => if c = a then .cst 0 else if c = b then add.out () else .inp (.inr c)⟩

lemma transfer_cost59x (a b : α) : (transfer59x a b).cost = 2 := by
  simp [transfer59x, Prog.cost, Prog.bind, Prog.op1]

lemma transfer_clean59x (a b : α) : Clean (transfer59x a b) := by
  have h : Clean ((Prog.op1 (ι := α ⊕ α) .mul (.inp (.inl a)) (.inp (.inr a))).bind
      (Prog.op1 .add (.inp (.inl (.inr b))) (.inp (.inr ())))) := by
    apply clean_bind <;> simp [Clean, Prog.op1, argHeavy]
  constructor
  · exact h.1
  · intro i
    cases i with
    | inl e => rfl
    | inr c =>
      dsimp [transfer59x]
      split_ifs
      · simp [argHeavy]
      · exact h.2 ()
      · rfl

lemma transfer_eval_weight59x (a b i : α) (v : α ⊕ α → ℝ) :
    (transfer59x a b).eval v (.inl i) = v (.inl i) := rfl

lemma transfer_eval_coef59x (a b i : α) (v : α ⊕ α → ℝ) :
    (transfer59x a b).eval v (.inr i) =
      if i = a then 0 else if i = b then v (.inr b) + v (.inl a) * v (.inr a)
      else v (.inr i) := by
  unfold transfer59x
  dsimp [Prog.eval]
  split_ifs
  · simp [Arg.eval]
  · change (((Prog.op1 .mul (.inp (.inl a)) (.inp (.inr a))).bind
        (Prog.op1 .add (.inp (.inl (.inr b))) (.inp (.inr ())))).eval v ()) = _
    simp [eval_bind, eval_op1, Arg.eval, Op.eval]
  · rfl

private lemma transfer_sum59x (s : Finset α) (a b : α) (ha : a ∈ s)
    (hb : b ∈ s.erase a) (v : α ⊕ α → ℝ) (W : α → ℝ)
    (hW : W a = v (.inl a) * W b) :
    ∑ i ∈ s.erase a, (transfer59x a b).eval v (.inr i) * W i =
      ∑ i ∈ s, v (.inr i) * W i := by
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hsplit := Finset.sum_erase_add (s := s) (fun i => v (.inr i) * W i) ha
  have hsplit' := Finset.sum_erase_add (s := s.erase a)
    (fun i => v (.inr i) * W i) hb
  have hsplit'' := Finset.sum_erase_add (s := s.erase a)
    (fun i => (transfer59x a b).eval v (.inr i) * W i) hb
  have he : ∑ i ∈ (s.erase a).erase b, (transfer59x a b).eval v (.inr i) * W i =
      ∑ i ∈ (s.erase a).erase b, v (.inr i) * W i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hia := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hib := (Finset.mem_erase.mp hi).1
    rw [transfer_eval_coef59x, if_neg hia, if_neg hib]
  rw [he, transfer_eval_coef59x, if_neg hba, if_pos rfl] at hsplit''
  rw [hW] at hsplit
  nlinarith [hsplit, hsplit', hsplit'']

/-- A downward closed finite tree has an exact evaluator with two operations per edge.
The first input copy contains edge weights; the second contains coefficients. -/
theorem tree_exists59x (root : α) (parent : α → α) (rank : α → ℕ)
    (hrank : ∀ a, a ≠ root → rank (parent a) < rank a)
    (s : Finset α) (hroot : root ∉ s)
    (hclosed : ∀ a ∈ s, parent a = root ∨ parent a ∈ s) :
    ∃ p : Prog (α ⊕ α) Unit, Clean p ∧ p.cost = 2 * s.card ∧
      ∀ (v : α ⊕ α → ℝ) (W : α → ℝ), W root = 1 →
        (∀ a ∈ s, W a = v (.inl a) * W (parent a)) →
        p.eval v () = ∑ a ∈ insert root s, v (.inr a) * W a := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmax⟩ := s.exists_max_image rank hs
      have har : a ≠ root := by intro h; subst a; exact hroot ha
      have hpa : parent a ≠ a := by
        intro he
        have := hrank a har
        rw [he] at this
        omega
      have hclosed' : ∀ b ∈ s.erase a, parent b = root ∨ parent b ∈ s.erase a := by
        intro b hb
        rcases hclosed b (Finset.mem_erase.mp hb).2 with h | h
        · exact Or.inl h
        · right
          apply Finset.mem_erase.mpr
          refine ⟨?_, h⟩
          intro he
          have hbr : b ≠ root := by
            intro he; subst b; exact hroot (Finset.mem_erase.mp hb).2
          have hlt := hrank b hbr
          have hle := hmax b (Finset.mem_erase.mp hb).2
          rw [he] at hlt
          omega
      obtain ⟨q, hq, hcq, heq⟩ := ih (s.erase a) (Finset.erase_ssubset ha)
        (fun h => hroot (Finset.mem_of_mem_erase h)) hclosed'
      let t := transfer59x a (parent a)
      refine ⟨t.bind (q.mapIn Sum.inr), clean_bind (transfer_clean59x _ _)
        (clean_mapIn _ hq), ?_, ?_⟩
      · rw [cost_bind, cost_mapIn, transfer_cost59x, hcq, Finset.card_erase_of_mem ha]
        have := Finset.card_pos.mpr hs
        omega
      · intro v W hW hrel
        rw [eval_bind, eval_mapIn]
        change q.eval (t.eval v) () = _
        rw [heq (t.eval v) W hW (fun b hb => by
          rw [transfer_eval_weight59x]
          exact hrel b (Finset.mem_of_mem_erase hb))]
        have hpar : parent a ∈ (insert root s).erase a := by
          apply Finset.mem_erase.mpr
          refine ⟨hpa, ?_⟩
          rcases hclosed a ha with h | h
          · simp [h]
          · exact Finset.mem_insert_of_mem h
        have herase : (insert root s).erase a = insert root (s.erase a) := by
          rw [Finset.erase_insert_of_ne har.symm]
        rw [← herase]
        exact transfer_sum59x (insert root s) a (parent a)
          (Finset.mem_insert_of_mem ha) hpar v W (hrel a ha)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨Prog.ofArgs (fun _ => .inp (.inr root)), ?_, rfl, ?_⟩
      · simp [Clean, Prog.ofArgs, argHeavy]
      · intro v W hW hrel
        simp [Prog.eval, Prog.ofArgs, Arg.eval, hW]

open BstLean.Part41 (Mono)

private lemma mono_zero59x {n k : ℕ} (a : Mono n k) :
    a.1.val = 0 ↔ a = default := by
  constructor
  · intro h
    have he : a.2.val = 0 := Multiset.card_eq_zero.mp (a.2.property.trans h)
    rcases a with ⟨i, m, hm⟩
    have hi : i = 0 := Fin.ext h
    subst i
    congr 1
    exact Subtype.ext he
  · rintro rfl
    rfl

private lemma mono_mem59x {n k : ℕ} (a : Mono n k) (ha : a ≠ default) :
    ∃ i, i ∈ a.2.val := by
  apply Multiset.card_pos_iff_exists_mem.mp
  rw [a.2.property]
  have := (mono_zero59x a).not.mpr ha
  omega

private def head59x {n k : ℕ} (a : Mono n k) (ha : a ≠ default) : Fin n :=
  (mono_mem59x a ha).choose

private lemma head_mem59x {n k : ℕ} (a : Mono n k) (ha : a ≠ default) :
    head59x a ha ∈ a.2.val := (mono_mem59x a ha).choose_spec

private def parentNZ59x {n k : ℕ} (a : Mono n k) (ha : a ≠ default) : Mono n k :=
  let m := a.2.val.filter (fun i => i ≠ head59x a ha)
  ⟨⟨m.card, lt_of_le_of_lt (by
    exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans a.2.property.le) a.1.isLt⟩,
    ⟨m, rfl⟩⟩

private def parent59x {n k : ℕ} (a : Mono n k) : Mono n k :=
  if ha : a = default then default else parentNZ59x a ha

private lemma parent_rank59x {n k : ℕ} (a : Mono n k) (ha : a ≠ default) :
    (parent59x a).1.val < a.1.val := by
  rw [parent59x, dif_neg ha]
  change (a.2.val.filter (fun i => i ≠ head59x a ha)).card < a.1.val
  apply lt_of_lt_of_eq _ a.2.property
  apply lt_of_not_ge
  intro h
  have he := Multiset.eq_of_le_of_card_le (Multiset.filter_le (fun i => i ≠ head59x a ha) _) h
  have hm := Multiset.mem_filter.mp (he.symm ▸ head_mem59x a ha)
  exact hm.2 rfl

abbrev WeightIn59x (n k : ℕ) := (Fin n × Fin (k + 1)) ⊕ Mono n k

private def edgeIn59x {n k : ℕ} (a : Mono n k) : WeightIn59x n k :=
  if ha : a = default then .inr default else
    .inl (head59x a ha, ⟨a.2.val.count (head59x a ha),
      lt_of_le_of_lt ((Multiset.count_le_card _ _).trans a.2.property.le) a.1.isLt⟩)

def weight59x {n k : ℕ} (Q : Fin n → Fin (k + 1) → ℝ) (a : Mono n k) : ℝ :=
  ∏ i, Q i ⟨a.2.val.count i,
    lt_of_le_of_lt ((Multiset.count_le_card _ _).trans a.2.property.le) a.1.isLt⟩

private lemma weight_root59x {n k : ℕ} (Q : Fin n → Fin (k + 1) → ℝ)
    (hQ : ∀ i, Q i 0 = 1) : weight59x Q default = 1 := by
  change weight59x Q ⟨0, Sym.nil⟩ = 1
  simp [weight59x, Sym.nil, hQ]

private lemma weight_parent59x {n k : ℕ} (Q : Fin n → Fin (k + 1) → ℝ)
    (hQ : ∀ i, Q i 0 = 1) (a : Mono n k) (ha : a ≠ default) :
    weight59x Q a =
      Q (head59x a ha) ⟨a.2.val.count (head59x a ha),
        lt_of_le_of_lt ((Multiset.count_le_card _ _).trans a.2.property.le) a.1.isLt⟩ *
      weight59x Q (parent59x a) := by
  unfold weight59x
  conv_lhs => rw [Finset.prod_eq_mul_prod_sdiff_singleton (head59x a ha) _ (by simp)]
  conv_rhs => arg 2; rw [Finset.prod_eq_mul_prod_sdiff_singleton (head59x a ha) _ (by simp)]
  have hz : (parent59x a).2.val.count (head59x a ha) = 0 := by
    rw [parent59x, dite_eq_right ha]
    change (a.2.val.filter (fun i => i ≠ head59x a ha)).count (head59x a ha) = 0
    exact Multiset.count_filter_of_neg (p := fun i => i ≠ head59x a ha) (by simp)
  have hz' : (⟨(parent59x a).2.val.count (head59x a ha),
      lt_of_le_of_lt ((Multiset.count_le_card _ _).trans (parent59x a).2.property.le)
        (parent59x a).1.isLt⟩ : Fin (k + 1)) = 0 := Fin.ext hz
  rw [hz', hQ, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hih : i ≠ head59x a ha := by simpa using hi
  congr 1
  apply Fin.ext
  rw [parent59x, dite_eq_right ha]
  change a.2.val.count i = (a.2.val.filter (fun i => i ≠ head59x a ha)).count i
  exact (Multiset.count_filter_of_pos (p := fun i => i ≠ head59x a ha) hih).symm

/-- Evaluation with a supplied univariate weight table costs exactly two operations per
nonconstant monomial. The table's degree-zero entries equal `1`. -/
theorem weighted_monomials_exists59x (n k : ℕ) :
    ∃ p : Prog (WeightIn59x n k) Unit, Clean p ∧
      p.cost = 2 * ((n + k).choose k - 1) ∧
      ∀ (v : WeightIn59x n k → ℝ), (∀ i, v (.inl (i, 0)) = 1) →
        p.eval v () = ∑ a : Mono n k, v (.inr a) *
          weight59x (fun i e => v (.inl (i, e))) a := by
  classical
  let s : Finset (Mono n k) := Finset.univ.erase default
  obtain ⟨p, hp, hc, he⟩ := tree_exists59x (default : Mono n k) parent59x
    (fun a => a.1.val) parent_rank59x s (by simp [s]) (by
      intro a ha
      by_cases h : parent59x a = default
      · exact Or.inl h
      · exact Or.inr (by simp [s, h]))
  let embed : Mono n k ⊕ Mono n k → WeightIn59x n k := Sum.elim edgeIn59x Sum.inr
  refine ⟨p.mapIn embed, clean_mapIn _ hp, ?_, ?_⟩
  · rw [cost_mapIn, hc]
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_monomials]
  · intro v hv
    rw [eval_mapIn]
    rw [he (v ∘ embed) (weight59x (fun i e => v (.inl (i, e)))) (weight_root59x _ hv)]
    · have hs : insert (default : Mono n k) s = Finset.univ := by simp [s]
      rw [hs]
      rfl
    · intro a ha
      have h : a ≠ default := by simpa [s] using ha
      simpa [embed, edgeIn59x, h] using weight_parent59x (fun i e => v (.inl (i, e))) hv a h

end
end BstLean.Part59.TreeAux59x
