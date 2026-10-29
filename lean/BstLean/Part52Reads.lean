import BstLean.CostModel

/-!
# Part 52, wave 1: the inputs a straight-line program reads

Role: `delegations/statements/p52-spec.md`. Report: `delegations/answers/p52-spec-opus.md`.

* `Reads p i`: some instruction of `p` has the argument `inp i`, or some output is `inp i`.
* `eval_congr_reads`: two input vectors that agree on every input read give the same value.
* `eval_update_of_not_reads`: a program that does not read `i` is invariant under a change of input `i`.
* `card_le_of_reads`: a set of inputs that are all read has at most `2·cost + |κ|` elements.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part52

open BstLean.Cost

variable {ι κ : Type}

/-- The program `p` reads input `i`: an instruction or an output has the argument `inp i`. -/
def Reads (p : Prog ι κ) (i : ι) : Prop :=
  (∃ I ∈ p.body, I.a = .inp i ∨ I.b = .inp i) ∨ ∃ o, p.out o = .inp i

theorem Arg.eval_congr (v v' : ι → ℝ) (R : List ℝ) (a : Arg ι)
    (h : ∀ j, a = .inp j → v j = v' j) : a.eval v R = a.eval v' R := by
  cases a with
  | inp j => exact h j rfl
  | reg r => rfl
  | cst q => rfl

theorem run_congr (v v' : ι → ℝ) (is : List (Instr ι))
    (h : ∀ I ∈ is, ∀ j, (I.a = .inp j ∨ I.b = .inp j) → v j = v' j) (R : List ℝ) :
    run v is R = run v' is R := by
  induction is generalizing R with
  | nil => rfl
  | cons I is ih =>
    simp only [run]
    have hI : I.eval v R = I.eval v' R := by
      unfold Instr.eval
      rw [Arg.eval_congr v v' R I.a (fun j hj => h I List.mem_cons_self j (Or.inl hj)),
        Arg.eval_congr v v' R I.b (fun j hj => h I List.mem_cons_self j (Or.inr hj))]
    rw [hI]
    exact ih (fun J hJ j hj => h J (List.mem_cons_of_mem _ hJ) j hj) _

/-- **Inputs not read do not matter.** -/
theorem eval_congr_reads (p : Prog ι κ) (v v' : ι → ℝ) (h : ∀ j, Reads p j → v j = v' j) (o : κ) :
    p.eval v o = p.eval v' o := by
  unfold Prog.eval
  rw [run_congr v v' p.body (fun I hI j hj => h j (Or.inl ⟨I, hI, hj⟩)) []]
  exact Arg.eval_congr v v' _ _ (fun j hj => h j (Or.inr ⟨o, hj⟩))

/-- A program that does not read input `i` is invariant under a change of input `i`. -/
theorem eval_update_of_not_reads [DecidableEq ι] (p : Prog ι κ) (i : ι) (hi : ¬ Reads p i)
    (v : ι → ℝ) (c : ℝ) (o : κ) : p.eval (Function.update v i c) o = p.eval v o := by
  apply eval_congr_reads
  intro j hj
  have : j ≠ i := fun h => hi (h ▸ hj)
  simp [Function.update, this]

/-- **Counting**: a set `S` of inputs that are all read has at most `2·cost + |κ|` elements. -/
theorem card_le_of_reads [Fintype κ] (p : Prog ι κ) (S : Finset ι) (hS : ∀ i ∈ S, Reads p i) :
    S.card ≤ 2 * p.cost + Fintype.card κ := by
  classical
  let g : (Fin p.body.length × Bool) ⊕ κ → Arg ι := fun x =>
    match x with
    | Sum.inl (j, b) => if b then (p.body.get j).a else (p.body.get j).b
    | Sum.inr o => p.out o
  have hsub : S.map ⟨Arg.inp, fun a b h => by cases h; rfl⟩ ⊆ Finset.univ.image g := by
    intro a ha
    simp only [Finset.mem_map] at ha
    obtain ⟨i, hiS, rfl⟩ := ha
    rcases hS i hiS with ⟨I, hI, hab⟩ | ⟨o, ho⟩
    · obtain ⟨j, rfl⟩ := List.get_of_mem hI
      rcases hab with h | h
      · exact Finset.mem_image.mpr ⟨Sum.inl (j, true), Finset.mem_univ _, h⟩
      · exact Finset.mem_image.mpr ⟨Sum.inl (j, false), Finset.mem_univ _, h⟩
    · exact Finset.mem_image.mpr ⟨Sum.inr o, Finset.mem_univ _, ho⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset ((Fin p.body.length × Bool) ⊕ κ))) (f := g)
  rw [Finset.card_map] at h1
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool] at h2
  unfold Prog.cost
  omega

end BstLean.Part52
