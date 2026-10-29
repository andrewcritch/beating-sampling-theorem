import BstLean.Part53Cost_Program

namespace BstLean.Part53.CostAux

set_option backward.isDefEq.respectTransparency false

open BstLean.Cost
open BstLean.Part41 (Mono argHeavy heavyCount)
open BstLean.Part36 (monoVal)

noncomputable section

def Clean {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, argHeavy I.a = 0 ∧ argHeavy I.b = 0) ∧
    ∀ o, argHeavy (p.out o) = 0

private lemma heavy_rename {ι ι' : Type} (f : ι → ι') (a : Arg ι) :
    argHeavy (a.rename f) = argHeavy a := by cases a <;> rfl

private lemma heavy_clamp {ι : Type} (s : ℕ) (a : Arg ι) (h : argHeavy a = 0) :
    argHeavy (a.clamp s) = 0 := by
  cases a with
  | inp i => rfl
  | reg r => simp only [Arg.clamp]; split_ifs <;> simp [argHeavy]
  | cst q => exact h

private lemma heavy_subst {ι ι' : Type} (σ : ι → Arg ι') (s len : ℕ)
    (hσ : ∀ i, argHeavy (σ i) = 0) (a : Arg ι) (ha : argHeavy a = 0) :
    argHeavy (a.subst σ s len) = 0 := by
  cases a with
  | inp i => exact hσ i
  | reg r => simp only [Arg.subst]; split_ifs <;> simp [argHeavy]
  | cst q => exact ha

theorem clean_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
    (hp : Clean p) (hq : Clean q) : Clean (p.bind q) := by
  have hf : ∀ i, argHeavy (Sum.elim Arg.inp
      (fun k => (p.out k).clamp p.body.length) i) = 0 := by
    intro i
    cases i with
    | inl i => rfl
    | inr k => exact heavy_clamp _ _ (hp.2 k)
  constructor
  · intro I hI
    simp only [Prog.bind, List.mem_append, List.mem_map] at hI
    rcases hI with hI | ⟨J, hJ, rfl⟩
    · exact hp.1 I hI
    · exact ⟨heavy_subst _ _ _ hf _ (hq.1 J hJ).1,
        heavy_subst _ _ _ hf _ (hq.1 J hJ).2⟩
  · intro o
    exact heavy_subst _ _ _ hf _ (hq.2 o)

theorem clean_mapIn {ι κ ν : Type} (f : ι → ν) {p : Prog ι κ}
    (hp : Clean p) : Clean (p.mapIn f) := by
  constructor
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    simpa [Instr.rename, heavy_rename] using hp.1 J hJ
  · intro o
    exact (heavy_rename _ _).trans (hp.2 o)

theorem clean_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
    (hp : ∀ k, Clean (p k)) (l : List κ) : Clean (Prog.par p l) := by
  induction l with
  | nil => simp [Clean, Prog.par, Prog.ofArgs, argHeavy]
  | cons k l ih =>
    apply clean_bind (hp k)
    constructor
    · exact (clean_mapIn Sum.inl ih).1
    · intro j
      dsimp
      split_ifs
      · rfl
      · exact (clean_mapIn Sum.inl ih).2 j

theorem clean_update {ι κ : Type} [DecidableEq κ] {p : Prog ι κ}
    (hp : Clean p) (q : κ → Prog (ι ⊕ κ) Unit) (hq : ∀ k, Clean (q k))
    (l : List κ) : Clean (p.update q l) := by
  apply clean_bind hp
  constructor
  · exact (clean_par q hq l).1
  · intro k
    dsimp
    split_ifs
    · exact (clean_par q hq l).2 k
    · rfl

theorem clean_pair {ι κ ν : Type} {p : Prog ι κ} {q : Prog ι ν}
    (hp : Clean p) (hq : Clean q) : Clean (p.pair q) := by
  apply clean_bind hp
  constructor
  · exact (clean_mapIn Sum.inl hq).1
  · intro o
    cases o with
    | inl k => rfl
    | inr o => exact (clean_mapIn Sum.inl hq).2 o

theorem clean_sumArgs {ι : Type} (l : List (Arg ι))
    (hl : ∀ a ∈ l, argHeavy a = 0) : Clean (Prog.sumArgs l) := by
  induction l with
  | nil => simp [Clean, Prog.sumArgs, Prog.ofArgs, argHeavy]
  | cons a l ih =>
    cases l with
    | nil => exact ⟨by simp [Prog.sumArgs, Prog.ofArgs], fun _ => hl a (by simp)⟩
    | cons b l =>
      apply clean_bind (ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)))
      have ha := (heavy_rename (Sum.inl : ι → ι ⊕ Unit) a).trans (hl a (by simp))
      simpa [Clean, Prog.op1, argHeavy] using ha

theorem clean_sumProd {ι : Type} (l : List (Arg ι × Arg ι))
    (hl : ∀ ab ∈ l, argHeavy ab.1 = 0 ∧ argHeavy ab.2 = 0) : Clean (Prog.sumProd l) := by
  apply clean_bind
  · apply clean_par
    intro j
    have h := hl (l.get j) (List.get_mem _ _)
    simpa [Clean, Prog.op1, argHeavy] using h
  · apply clean_sumArgs
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rfl

theorem clean_heavy {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : Clean p) : heavyCount p = 0 := by
  unfold heavyCount
  have hb : (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

theorem clean_of_heavy {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : heavyCount p = 0) : Clean p := by
  classical
  unfold heavyCount at hp
  constructor
  · intro I hI
    have hm : argHeavy I.a + argHeavy I.b ∈
        p.body.map (fun J => argHeavy J.a + argHeavy J.b) := List.mem_map.mpr ⟨I, hI, rfl⟩
    have hb := List.le_sum_of_mem hm
    omega
  · intro o
    have ho : argHeavy (p.out o) ≤ ∑ o, argHeavy (p.out o) :=
      Finset.single_le_sum (f := fun o => argHeavy (p.out o))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
    omega

def prodProg {ι : Type} : List (Arg ι) → Prog ι Unit
  | [] => Prog.ofArgs (fun _ => .cst 1)
  | a :: l => (prodProg l).bind (Prog.op1 .mul (a.rename Sum.inl) (.inp (.inr ())))

theorem prodProg_eval {ι : Type} (l : List (Arg ι)) (v : ι → ℝ) :
    (prodProg l).eval v () = (l.map (fun a => a.eval v [])).prod := by
  induction l with
  | nil => simp [prodProg, Arg.eval]
  | cons a l ih =>
    rw [prodProg, eval_bind, eval_op1]
    cases a <;> simp [Op.eval, Arg.rename, Arg.eval, ih]

theorem prodProg_cost {ι : Type} (l : List (Arg ι)) : (prodProg l).cost = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [prodProg, cost_bind, ih]

theorem prodProg_clean {ι : Type} (l : List (Arg ι))
    (hl : ∀ a ∈ l, argHeavy a = 0) : Clean (prodProg l) := by
  induction l with
  | nil => simp [prodProg, Clean, Prog.ofArgs, argHeavy]
  | cons a l ih =>
    apply clean_bind (ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)))
    have ha := (heavy_rename (Sum.inl : ι → ι ⊕ Unit) a).trans (hl a (by simp))
    simpa [Clean, Prog.op1, argHeavy] using ha

def keepBind {ι κ ν : Type} (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν) : Prog ι (κ ⊕ ν) :=
  p.bind ⟨q.body, Sum.elim (fun k => .inp (.inr k)) q.out⟩

theorem keepBind_eval_left {ι κ ν : Type} (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν)
    (v : ι → ℝ) (k : κ) : (keepBind p q).eval v (.inl k) = p.eval v k := by
  rw [keepBind, eval_bind]
  rfl

theorem keepBind_eval_right {ι κ ν : Type} (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν)
    (v : ι → ℝ) (o : ν) :
    (keepBind p q).eval v (.inr o) = q.eval (Sum.elim v (p.eval v)) o := by
  rw [keepBind, eval_bind]
  rfl

theorem keepBind_cost {ι κ ν : Type} (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν) :
    (keepBind p q).cost = p.cost + q.cost := by
  rw [keepBind, cost_bind]
  rfl

theorem keepBind_clean {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
    (hp : Clean p) (hq : Clean q) : Clean (keepBind p q) := by
  apply clean_bind hp
  constructor
  · exact hq.1
  · intro o
    cases o with
    | inl k => rfl
    | inr o => exact hq.2 o

private theorem mono_mem_exists {n k : ℕ} (p : Mono n k) (h : p.1.val ≠ 0) :
    ∃ a, a ∈ p.2.val := by
  have hp : 0 < p.2.val.card := by rw [p.2.property]; omega
  exact Multiset.card_pos_iff_exists_mem.mp hp

private def monoHead {n k : ℕ} (p : Mono n k) (h : p.1.val ≠ 0) : Fin n :=
  (mono_mem_exists p h).choose

private lemma monoHead_mem {n k : ℕ} (p : Mono n k) (h : p.1.val ≠ 0) :
    monoHead p h ∈ p.2.val := (mono_mem_exists p h).choose_spec

private def monoParent {n k : ℕ} (p : Mono n k) (h : p.1.val ≠ 0) : Mono n k :=
  ⟨⟨p.1.val - 1, by have := p.1.isLt; omega⟩,
    ⟨p.2.val.erase (monoHead p h), by
      rw [Multiset.card_erase_of_mem (monoHead_mem p h), p.2.property]
      rfl⟩⟩

private lemma mono_decomp {n k : ℕ} (p : Mono n k) (h : p.1.val ≠ 0)
    (y : Fin n → ℝ) :
    monoVal y p.2.val = y (monoHead p h) * monoVal y (monoParent p h).2.val := by
  conv_lhs => rw [← Multiset.cons_erase (monoHead_mem p h)]
  simp [monoVal, monoParent]

private def monoSlots (n k c : ℕ) : Finset (Mono n k) :=
  Finset.univ.filter (fun p => p.1.val = c)

private def monoSlotProg {n k : ℕ} (p : Mono n k) :
    Prog (Fin n ⊕ Mono n k) Unit :=
  if h : p.1.val = 0 then Prog.ofArgs (fun _ => .cst 1) else
    Prog.op1 .mul (.inp (.inl (monoHead p h))) (.inp (.inr (monoParent p h)))

def monoProg (n k : ℕ) : ℕ → Prog (Fin n) (Mono n k)
  | 0 => Prog.ofArgs (fun _ => .cst 1)
  | c + 1 => (monoProg n k c).update monoSlotProg (monoSlots n k (c + 1)).toList

private theorem monoSlot_clean {n k : ℕ} (p : Mono n k) : Clean (monoSlotProg p) := by
  unfold monoSlotProg
  split_ifs <;> simp [Clean, Prog.ofArgs, Prog.op1, argHeavy]

theorem monoProg_clean (n k c : ℕ) : Clean (monoProg n k c) := by
  induction c with
  | zero => simp [monoProg, Clean, Prog.ofArgs, argHeavy]
  | succ c ih => exact clean_update ih monoSlotProg monoSlot_clean _

theorem monoProg_eval (n k c : ℕ) (y : Fin n → ℝ) (p : Mono n k)
    (hp : p.1.val ≤ c) : (monoProg n k c).eval y p = monoVal y p.2.val := by
  classical
  induction c generalizing p with
  | zero =>
    have he : p.2.val = 0 := Multiset.card_eq_zero.mp (by rw [p.2.property]; omega)
    simp only [monoProg, eval_ofArgs, Arg.eval, Rat.cast_one, monoVal]
    rw [he]
    simp
  | succ c ih =>
    rw [monoProg, eval_update]
    by_cases he : p.1.val = c + 1
    · have hm : p ∈ (monoSlots n k (c + 1)).toList := by simp [monoSlots, he]
      rw [ite_eq_left hm]
      have h0 : p.1.val ≠ 0 := by omega
      simp only [monoSlotProg, h0, dite_false, eval_op1, Arg.eval, Sum.elim_inl,
        Sum.elim_inr, Op.eval]
      rw [ih (monoParent p h0) (by dsimp [monoParent]; omega), ← mono_decomp]
    · have hm : p ∉ (monoSlots n k (c + 1)).toList := by simp [monoSlots, he]
      rw [ite_eq_right hm]
      exact ih p (by omega)

private def monoDone (n k c : ℕ) : Finset (Mono n k) :=
  Finset.univ.filter (fun p => p.1.val ≠ 0 ∧ p.1.val ≤ c)

private theorem monoProg_cost_exact (n k c : ℕ) :
    (monoProg n k c).cost = (monoDone n k c).card := by
  classical
  induction c with
  | zero => simp [monoProg, monoDone, Prog.cost, Prog.ofArgs]
  | succ c ih =>
    rw [monoProg, cost_update, ih]
    have hs : ((monoSlots n k (c + 1)).toList.map fun p => (monoSlotProg p).cost).sum =
        (monoSlots n k (c + 1)).card := by
      have hh : ((monoSlots n k (c + 1)).toList.map fun p => (monoSlotProg p).cost) =
          (monoSlots n k (c + 1)).toList.map (fun _ => 1) := by
        apply List.map_congr_left
        intro p hp
        have he : p.1.val = c + 1 := by simpa [monoSlots] using hp
        simp [monoSlotProg, show p.1.val ≠ 0 by omega]
      rw [hh]
      simp
    rw [hs]
    have hu : monoDone n k (c + 1) = monoDone n k c ∪ monoSlots n k (c + 1) := by
      ext p
      simp only [monoDone, monoSlots, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      omega
    have hd : Disjoint (monoDone n k c) (monoSlots n k (c + 1)) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      simp only [monoDone, monoSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      omega
    rw [hu, Finset.card_union_of_disjoint hd]

theorem monoProg_cost (n k : ℕ) : (monoProg n k k).cost ≤ (n + k).choose k := by
  rw [monoProg_cost_exact, ← card_monomials]
  exact Finset.card_le_card (Finset.subset_univ _)

end
end BstLean.Part53.CostAux
