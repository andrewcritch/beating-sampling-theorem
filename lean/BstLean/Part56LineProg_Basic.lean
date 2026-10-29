import BstLean.Part41Defs

namespace BstLean.Part56
open BstLean.Cost BstLean.Part41
noncomputable section
def Clean {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, argHeavy I.a = 0 ∧ argHeavy I.b = 0) ∧ ∀ o, argHeavy (p.out o) = 0

lemma heavy_rename {ι κ : Type} (f : ι → κ) (a : Arg ι) :
    argHeavy (a.rename f) = argHeavy a := by cases a <;> rfl

lemma heavy_clamp {ι : Type} (s : ℕ) (a : Arg ι) (h : argHeavy a = 0) :
    argHeavy (a.clamp s) = 0 := by
  cases a <;> simp_all [Arg.clamp, argHeavy]
  split_ifs <;> rfl

lemma heavy_subst {ι κ : Type} (f : ι → Arg κ) (s l : ℕ)
    (hf : ∀ i, argHeavy (f i) = 0) (a : Arg ι) (h : argHeavy a = 0) :
    argHeavy (a.subst f s l) = 0 := by
  cases a <;> simp_all [Arg.subst, argHeavy]
  split_ifs <;> rfl

lemma clean_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
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

lemma clean_mapIn {ι κ ν : Type} (f : ι → ν) {p : Prog ι κ}
    (hp : Clean p) : Clean (p.mapIn f) := by
  constructor
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    simpa [Instr.rename, heavy_rename] using hp.1 J hJ
  · intro o
    exact (heavy_rename _ _).trans (hp.2 o)

lemma clean_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
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

lemma clean_sumArgs {ι : Type} (l : List (Arg ι))
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

lemma clean_sumProd {ι : Type} (l : List (Arg ι × Arg ι))
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

lemma clean_heavyCount {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : Clean p) : heavyCount p = 0 := by
  unfold heavyCount
  have hb : (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

def prodArgs {ι : Type} : List (Arg ι) → Prog ι Unit
  | [] => Prog.ofArgs fun _ => .cst 1
  | a :: l => (prodArgs l).bind (Prog.op1 .mul (a.rename Sum.inl) (.inp (.inr ())))

lemma prodArgs_eval {ι : Type} (l : List (Arg ι)) (x : ι → ℝ) :
    (prodArgs l).eval x () = (l.map fun a => a.eval x []).prod := by
  induction l with
  | nil => simp [prodArgs, Arg.eval]
  | cons a l ih =>
    simp only [prodArgs, eval_bind, eval_op1, Op.eval, Arg.eval_rename,
      List.map_cons, List.prod_cons]
    have hi := congrArg (fun z => a.eval x [] * z) ih
    cases a <;> simpa only [Arg.eval, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using hi

lemma prodArgs_cost {ι : Type} (l : List (Arg ι)) : (prodArgs l).cost = l.length := by
  induction l <;> simp_all [prodArgs]

lemma prodArgs_clean {ι : Type} (l : List (Arg ι)) (h : ∀ a ∈ l, argHeavy a = 0) :
    Clean (prodArgs l) := by
  induction l with
  | nil => simp [prodArgs, Clean, Prog.ofArgs, argHeavy]
  | cons a l ih =>
    apply clean_bind (ih (fun b hb => h b (by simp [hb])))
    have ha := (heavy_rename (Sum.inl : ι → ι ⊕ Unit) a).trans (h a (by simp))
    simpa [Clean, Prog.op1, argHeavy] using ha

def sumProgs {ι κ : Type} [Fintype κ] [DecidableEq κ] (p : κ → Prog ι Unit) : Prog ι Unit :=
  (Prog.par p Finset.univ.toList).bind
    (Prog.sumArgs (Finset.univ.toList.map fun j => .inp (.inr j)))

lemma sumProgs_eval {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (p : κ → Prog ι Unit) (x : ι → ℝ) :
    (sumProgs p).eval x () = ∑ j, (p j).eval x () := by
  simp only [sumProgs, eval_bind, eval_sumArgs, List.map_map, Function.comp_def,
    Arg.eval, Sum.elim_inr]
  have he (j : κ) : (Prog.par p Finset.univ.toList).eval x j = (p j).eval x () :=
    eval_par_mem _ _ _ _ (by simp)
  simp_rw [he]
  exact Finset.sum_map_toList _ _

lemma sumProgs_cost {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (p : κ → Prog ι Unit) :
    (sumProgs p).cost ≤ ∑ j, (p j).cost + Fintype.card κ := by
  simp only [sumProgs, cost_bind, cost_par, cost_sumArgs, List.length_map,
    Finset.length_toList, Finset.card_univ]
  rw [Finset.sum_map_toList]
  omega

lemma sumProgs_clean {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (p : κ → Prog ι Unit) (h : ∀ j, Clean (p j)) : Clean (sumProgs p) := by
  apply clean_bind (clean_par _ h _)
  apply clean_sumArgs
  intro a ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  rfl

end
end BstLean.Part56
