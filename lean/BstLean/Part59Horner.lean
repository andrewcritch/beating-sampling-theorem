import BstLean.Part59Defs

/-!
# Part 59, wave 1: The charged baseline is honest: the nested-tree (multivariate Horner) program

Specification: `delegations/answers/p59-spec-opus.md` §3.1.

Suggested route.
* Tree on the monomials `α`, `|α| ≤ k` (`Mono n k`): the parent of `α ≠ 0` is `α − e_j`,
  `j = max{i : α_i > 0}`. Then `S(α) = c_α + Σ_{children γ = α + e_j} y_j S(γ)` and `S(0) = Σ_α c_α y^α`.
  Each of the `C(n+k,k) − 1` edges costs one `mul` and one `add`.
* A convenient induction: on the number of variables `n` and on `k`. With `F_{n,k}(c, y)`:
  `F_{n+1,k} = F_{n,k}(c|_{α_{n}=0}) + y_n · F_{n+1,k−1}(c shifted)` (split on whether the last variable
  occurs). Cost `t(n,k) = t(n−1,k) + t(n,k−1) + 2` with `t(0,k) = t(n,0) = 0`, so `t = 2C(n+k,k) − 2`
  by Pascal's rule. Build the program with `Prog.bind` and `Prog.mapIn` (`CostModel.lean`), and use
  the `eval_bind`/`cost_bind` lemmas there. At `n = 0` or `k = 0` the program is `Prog.ofArgs` (the
  coefficient of the empty monomial).
* `heavyCount pg = 0`: the program uses no constants at all.
* Sanity: `n = 1`, `k = 2`: `c₀ + y(c₁ + y c₂)` costs `4 = 2·3 − 2`.

Replace each `sorry` by a proof. Do not edit the statements or `Part59Defs.lean`. Do not use
`native_decide` or `axiom` anywhere. This file imports `Part59Defs` only; a prover may also import
finished files of Parts 29–58, but no other Part 59 wave-1 file. Name private helpers with the suffix
`59x` or make them `private`, so that `Part59Final` does not see a name clash.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

open BstLean.Part41 (argHeavy)

private def Clean {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, argHeavy I.a = 0 ∧ argHeavy I.b = 0) ∧ ∀ o, argHeavy (p.out o) = 0

private lemma heavy_rename {ι κ : Type} (f : ι → κ) (a : Arg ι) :
    argHeavy (a.rename f) = argHeavy a := by cases a <;> rfl

private lemma heavy_clamp {ι : Type} (s : ℕ) (a : Arg ι) (h : argHeavy a = 0) :
    argHeavy (a.clamp s) = 0 := by
  cases a <;> simp_all [Arg.clamp, argHeavy]
  split_ifs <;> rfl

private lemma heavy_subst {ι κ : Type} (f : ι → Arg κ) (s l : ℕ)
    (hf : ∀ i, argHeavy (f i) = 0) (a : Arg ι) (h : argHeavy a = 0) :
    argHeavy (a.subst f s l) = 0 := by
  cases a <;> simp_all [Arg.subst, argHeavy]
  split_ifs <;> rfl

private lemma clean_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
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

private lemma clean_mapIn {ι κ ν : Type} (f : ι → ν) {p : Prog ι κ}
    (hp : Clean p) : Clean (p.mapIn f) := by
  constructor
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    simpa [Instr.rename, heavy_rename] using hp.1 J hJ
  · intro o
    exact (heavy_rename _ _).trans (hp.2 o)

private lemma clean_heavyCount {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : Clean p) : heavyCount p = 0 := by
  unfold heavyCount
  have hb : (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

private lemma clean_op {ι : Type} (op : Op) (a b : Arg ι)
    (ha : argHeavy a = 0) (hb : argHeavy b = 0) : Clean (Prog.op1 op a b) := by
  simpa [Clean, Prog.op1, argHeavy] using And.intro ha hb

private lemma tree_exists59x {α : Type} [DecidableEq α] (s : Finset (Multiset α))
    (hz : (0 : Multiset α) ∈ s)
    (hc : ∀ m ∈ s, ∀ a ∈ m, m.erase a ∈ s)
    {ι : Type} (c : Multiset α → Arg ι) (y : α → Arg ι)
    (hcl : ∀ m ∈ s, argHeavy (c m) = 0) (hyl : ∀ a, argHeavy (y a) = 0) :
    ∃ p : Prog ι Unit, Clean p ∧
      (∀ v, p.eval v () = ∑ m ∈ s, (c m).eval v [] * (m.map (fun a => (y a).eval v [])).prod) ∧
      p.cost = 2 * s.card - 2 := by
  classical
  induction s using Finset.strongInductionOn generalizing ι with
  | _ s ih =>
    by_cases hs : s = {0}
    · subst s
      refine ⟨Prog.ofArgs (fun _ => c 0), ⟨by simp [Prog.ofArgs], fun _ => hcl 0 hz⟩, ?_, ?_⟩
      · intro v; simp
      · simp
    obtain ⟨m, hm, hmax⟩ := s.exists_max_image Multiset.card ⟨0, hz⟩
    have hm0 : m ≠ 0 := by
      intro he
      apply hs
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hz, ?_⟩
      intro b hb
      have := hmax b hb
      simpa [he] using this
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hm0
    let b := m.erase a
    have hb : b ∈ s := hc m hm a ha
    have hcard : b.card + 1 = m.card := by
      dsimp [b]; rw [Multiset.card_erase_of_mem ha, Nat.pred_eq_sub_one]; have := Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩; omega
    have hbm : b ≠ m := by intro he; rw [he] at hcard; omega
    have hb' : b ∈ s.erase m := Finset.mem_erase.mpr ⟨hbm, hb⟩
    have hz' : (0 : Multiset α) ∈ s.erase m := Finset.mem_erase.mpr ⟨Ne.symm hm0, hz⟩
    have hc' : ∀ q ∈ s.erase m, ∀ j ∈ q, q.erase j ∈ s.erase m := by
      intro q hq j hj
      have hqs := (Finset.mem_erase.mp hq).2
      refine Finset.mem_erase.mpr ⟨?_, hc q hqs j hj⟩
      intro he
      have hqpos := Multiset.card_pos_iff_exists_mem.mpr ⟨j, hj⟩
      have hqe := Multiset.card_erase_of_mem hj
      rw [Nat.pred_eq_sub_one] at hqe
      have hqm := hmax q hqs
      rw [he] at hqe
      omega
    let mul : Prog ι Unit := Prog.op1 .mul (y a) (c m)
    let add : Prog (ι ⊕ Unit) Unit := Prog.op1 .add ((c b).rename Sum.inl) (.inp (.inr ()))
    let step := mul.bind add
    have hstep : Clean step := clean_bind (clean_op _ _ _ (hyl a) (hcl m hm))
      (clean_op _ _ _ ((heavy_rename _ _).trans (hcl b hb)) rfl)
    let c' : Multiset α → Arg (ι ⊕ Unit) := fun q =>
      if q = b then .inp (.inr ()) else (c q).rename Sum.inl
    obtain ⟨p, hp, hev, hcost⟩ := ih (s.erase m) (Finset.erase_ssubset hm) hz' hc'
      c' (fun j => (y j).rename Sum.inl)
      (by intro q hq; dsimp [c']; split_ifs; rfl; exact (heavy_rename _ _).trans (hcl q (Finset.mem_erase.mp hq).2))
      (fun j => (heavy_rename _ _).trans (hyl j))
    refine ⟨step.bind p, clean_bind hstep hp, ?_, ?_⟩
    · intro v
      rw [eval_bind, hev]
      have hsev : step.eval v () = (c b).eval v [] + (y a).eval v [] * (c m).eval v [] := by
        simp only [step, mul, add, eval_bind, eval_op1, Op.eval, Arg.eval_rename]
        cases c b <;> rfl
      have hy : ∀ j, ((y j).rename Sum.inl).eval (Sum.elim v (step.eval v)) [] = (y j).eval v [] := by
        intro j; rw [Arg.eval_rename]; rfl
      simp only [hy]
      have hce : ∀ q, (c' q).eval (Sum.elim v (step.eval v)) [] =
          (c q).eval v [] + if q = b then (y a).eval v [] * (c m).eval v [] else 0 := by
        intro q
        dsimp [c']
        split_ifs with h
        · subst q; simpa [Arg.eval] using hsev
        · rw [Arg.eval_rename]; simp
      simp only [hce, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' (s.erase m) b, ite_eq_left hb']
      have hval : (m.map (fun j => (y j).eval v [])).prod =
          (y a).eval v [] * (b.map (fun j => (y j).eval v [])).prod := by
        conv_lhs => rw [← Multiset.cons_erase ha]
        simp [b]
      rw [← Finset.sum_erase_add _ _ hm, hval]
      ring
    · simp only [cost_bind, step, mul, add, cost_op1, hcost]
      have := Finset.card_erase_add_one hm
      have := Finset.card_pos.mpr ⟨0, hz'⟩
      omega

/-- **The baseline's `f`-program** (the exact cost `costF n k` of Dev's A9 charge). -/
theorem horner59_exists (n k : ℕ) : HornerExact59 n k := by
  classical
  let raw : Mono n k → Multiset (Fin n) := fun q => q.2.1
  have hinj : Function.Injective raw := by
    intro p q h
    apply Sigma.subtype_ext (p := fun i : Fin (k+1) => fun m : Multiset (Fin n) => m.card = i.val) _ h
    apply Fin.ext
    have hp : p.2.1.card = p.1.val := p.2.2
    have hq : q.2.1.card = q.1.val := q.2.2
    change p.2.1 = q.2.1 at h
    rw [h] at hp
    omega
  let s := Finset.univ.image raw
  have mem_s : ∀ m : Multiset (Fin n), m ∈ s ↔ m.card ≤ k := by
    intro m
    constructor
    · intro h
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
      dsimp [raw]
      have hq : q.2.1.card = q.1.val := q.2.2
      change q.2.1.card ≤ k
      omega
    · intro h
      exact Finset.mem_image.mpr ⟨⟨⟨m.card, by omega⟩, ⟨m, rfl⟩⟩, by simp, rfl⟩
  let c : Multiset (Fin n) → Arg (InH n k) := fun m =>
    if h : m.card ≤ k then .inp (.inl ⟨⟨m.card, by omega⟩, ⟨m, rfl⟩⟩) else .cst 0
  have hc : ∀ q : Mono n k, c (raw q) = .inp (.inl q) := by
    intro q
    dsimp [c, raw]
    split_ifs with h
    · apply congrArg (fun q : Mono n k => Arg.inp (Sum.inl q))
      apply hinj
      rfl
    · have hq : q.2.1.card = q.1.val := q.2.2
      change ¬ q.2.1.card ≤ k at h
      have hi := q.1.is_le
      exact False.elim (h (by omega))
  obtain ⟨p, hp, hev, hcost⟩ := tree_exists59x s ((mem_s 0).mpr (by simp))
    (by intro m hm a ha; apply (mem_s _).mpr; have := (mem_s m).mp hm
        exact Multiset.card_erase_le.trans this)
    c (fun i => .inp (.inr i))
    (by intro m hm; dsimp [c]; rw [dite_eq_left ((mem_s m).mp hm)]; rfl)
    (fun _ => rfl)
  refine ⟨p, clean_heavyCount hp, ?_, ?_⟩
  · intro v
    rw [hev]
    dsimp [s]
    rw [Finset.sum_image (fun p _ q _ h => hinj h)]
    simp only [hc, Arg.eval, polyEval, phiM, BstLean.Part36.monoVal]
    rfl
  · rw [hcost]
    have hcard : s.card = (n + k).choose k := by
      dsimp [s]
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
      rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
        ← Nat.choose_symm_add (a := k) (b := n)]
      simp [Nat.add_comm]
    rw [hcard]


end BstLean.Part59
