import BstLean.Part43Main

/-!
# Part 49, file 1: the programs of Option f (every degree, computed surrogate moments)

Specification: `delegations/statements/p49-spec.md`. Report: `delegations/answers/p49-spec-opus.md`.

Conventions.
* `k = d_f`, `d = d_M`. `m(x) = M φ(x)` is Part 36's `mapMD`, `M : CoefIdxD n d → ℝ`.
  `f = f₀ + Σ_{j=1}^k T_j[y^{⊗j}]` is Part 41's `fval k f0 T`, with symmetric `T_j` (`TSymm`).
* A weight index `js = (j, s) : WIdx n k` is a degree `j ≤ k` and an orbit `s` (a multiset of size `j`
  of output coordinates). The used indices are `F49 n k` (`j ≥ 1`).
* `pg49` (the per-`f` program) reads `f₀`, the entries `T_j[word s]` (one per orbit) and the weights
  `W(j, s)`, and returns `f₀ + Σ_{(j,s)} T_j[word s] W(j, s)`. Its cost is `2 |F49|`.
* `pw49 pm` (the per-`(θ, M)` program) first runs a moment program `pm` on `θ` (Part 43's
  `momProg43_exists` with every orbit kept at the levels `(j, 0)`, see `Kall`), then for each
  `(j, s)` the contraction `Σ_{q, a} pm(key(j, q)) ∏_t M_{(word q)_t, a_t}` over the orbits `q` of
  monomials of size `j` and the words `a` of orbit `s`.
* Only the constants `0` and `1` occur (`Clean`).
-/

namespace BstLean.Part49

open MeasureTheory BstLean.Cost
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiM mset wordOf Tens TSymm fval orbSize heavyCount argHeavy Pn baseline)
open BstLean.Part43 (KeyF keys43 IsKey wKeyR BofQ varFQ surrT Kof43 bmin etaQ onceCost MomSpec43)

variable {n d : ℕ}

/-! ## §1 Programs with the constants `0` and `1` only -/

/-- Every argument of the program is an input, a register, or the constant `0` or `1`. -/
def Clean {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, argHeavy I.a = 0 ∧ argHeavy I.b = 0) ∧ ∀ o, argHeavy (p.out o) = 0

lemma heavy_rename {ι κ : Type} (f : ι → κ) (a : Arg ι) :
    argHeavy (a.rename f) = argHeavy a := by
  cases a <;> rfl

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
    · exact ⟨heavy_subst _ _ _ hf _ (hq.1 J hJ).1, heavy_subst _ _ _ hf _ (hq.1 J hJ).2⟩
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

lemma clean_heavyCount {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : Clean p) : heavyCount p = 0 := by
  unfold heavyCount
  have hb : (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

lemma clean_of_heavy {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (h : heavyCount p = 0) : Clean p := by
  unfold heavyCount at h
  have h1 := Nat.eq_zero_of_add_eq_zero_right h
  have h2 := Nat.eq_zero_of_add_eq_zero_left h
  constructor
  · intro I hI
    have := List.sum_eq_zero_iff.mp h1 _ (List.mem_map.mpr ⟨I, hI, rfl⟩)
    omega
  · intro o
    exact (Finset.sum_eq_zero_iff.mp h2) o (Finset.mem_univ o)

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

/-! ## §2 Products of argument lists -/

/-- The product of a list of arguments, by `length − 1` multiplications (the empty product is `1`). -/
noncomputable def prodArgs {ι : Type} : List (Arg ι) → Prog ι Unit
  | [] => .ofArgs fun _ => .cst 1
  | [a] => .ofArgs fun _ => a
  | a :: b :: l => (prodArgs (b :: l)).bind (Prog.op1 .mul (a.rename Sum.inl) (.inp (Sum.inr ())))

theorem eval_prodArgs {ι : Type} (l : List (Arg ι)) (v : ι → ℝ) (u : Unit) :
    (prodArgs l).eval v u = (l.map fun a => a.eval v []).prod := by
  induction l with
  | nil => simp [prodArgs, Arg.eval]
  | cons a l ih =>
    cases l with
    | nil => simp [prodArgs]
    | cons b l =>
      simp only [prodArgs, eval_bind, eval_op1, Op.eval, Arg.eval_rename]
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih]
      cases a <;> rfl

theorem cost_prodArgs {ι : Type} (l : List (Arg ι)) : (prodArgs l).cost = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [prodArgs, cost_bind, cost_op1] at ih ⊢
      rw [ih]
      simp

lemma clean_prodArgs {ι : Type} (l : List (Arg ι))
    (hl : ∀ a ∈ l, argHeavy a = 0) : Clean (prodArgs l) := by
  induction l with
  | nil => simp [Clean, prodArgs, Prog.ofArgs, argHeavy]
  | cons a l ih =>
    cases l with
    | nil => exact ⟨by simp [prodArgs, Prog.ofArgs], fun _ => hl a (by simp)⟩
    | cons b l =>
      apply clean_bind (ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)))
      have ha := (heavy_rename (Sum.inl : ι → ι ⊕ Unit) a).trans (hl a (by simp))
      simpa [Clean, Prog.op1, argHeavy] using ha

/-- The sum of the products of a list of argument lists. -/
noncomputable def sumProdL {ι : Type} (l : List (List (Arg ι))) : Prog ι Unit :=
  (Prog.par (fun j : Fin l.length => prodArgs (l.get j)) (List.finRange l.length)).bind
    (Prog.sumArgs ((List.finRange l.length).map fun j => .inp (Sum.inr j)))

theorem eval_sumProdL {ι : Type} (l : List (List (Arg ι))) (v : ι → ℝ) (u : Unit) :
    (sumProdL l).eval v u = (l.map fun fs => (fs.map fun a => a.eval v []).prod).sum := by
  simp only [sumProdL, eval_bind, eval_sumArgs, List.map_map]
  have : ∀ j : Fin l.length, (Function.comp (fun a => Arg.eval (Sum.elim v
      ((Prog.par (fun j : Fin l.length => prodArgs (l.get j))
        (List.finRange l.length)).eval v)) [] a) (fun j => Arg.inp (Sum.inr j))) j =
      ((l.get j).map fun a => a.eval v []).prod := by
    intro j
    simp only [Function.comp, Arg.eval, Sum.elim_inr]
    rw [eval_par_mem _ _ _ _ (List.mem_finRange j), eval_prodArgs]
    rfl
  rw [List.map_congr_left (fun j _ => this j)]
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

theorem cost_sumProdL {ι : Type} (l : List (List (Arg ι))) :
    (sumProdL l).cost = (l.map fun fs => fs.length - 1).sum + (l.length - 1) := by
  simp only [sumProdL, cost_bind, cost_par, cost_prodArgs, cost_sumArgs, List.length_map,
    List.length_finRange]
  congr 1
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

lemma clean_sumProdL {ι : Type} (l : List (List (Arg ι)))
    (hl : ∀ fs ∈ l, ∀ a ∈ fs, argHeavy a = 0) : Clean (sumProdL l) := by
  apply clean_bind
  · apply clean_par
    intro j
    exact clean_prodArgs _ (hl _ (List.get_mem _ _))
  · apply clean_sumArgs
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rfl

/-! ## §3 Weight indices and the per-`f` program `pg49` -/

/-- A weight index: a degree `j ≤ k` and an orbit `s` of size `j` of output coordinates. -/
abbrev WIdx (n k : ℕ) := Σ j : Fin (k + 1), Sym (Fin n) j

/-- The used weight indices: `1 ≤ j ≤ k`, every orbit. -/
noncomputable def F49 (n k : ℕ) : Finset (WIdx n k) :=
  ((Finset.univ : Finset (Fin (k + 1))).filter fun j => 1 ≤ j.val).sigma fun _ => Finset.univ

lemma mem_F49 {k : ℕ} (js : WIdx n k) : js ∈ F49 n k ↔ 1 ≤ js.1.val := by
  simp [F49]

/-- `|F49| = Σ_{j=1}^k C(n+j−1, j) = C(n+k, k) − 1`, the number of monomials of `f` other than `1`. -/
noncomputable def L49 (n k : ℕ) : ℕ := (F49 n k).card

/-- The inputs of `pg49`: `f₀`, the entries of `T_j` (`j ≤ k`), and the weights. -/
abbrev InG (n k : ℕ) := Unit ⊕ (Σ j : Fin (k + 1), Fin j → Fin n) ⊕ WIdx n k

/-- The input vector of `pg49` for `f = (f₀, T)` and weights `W`. -/
def inpG {k : ℕ} (f0 : ℝ) (T : Tens n) (W : WIdx n k → ℝ) : InG n k → ℝ :=
  Sum.elim (fun _ => f0) (Sum.elim (fun jw => T jw.1 jw.2) W)

/-- **The per-`f` program**: `f₀ + Σ_{(j,s) ∈ F49} T_j[word s] · W(j, s)`. -/
noncomputable def pg49 (n k : ℕ) [Inhabited (Fin n)] : Prog (InG n k) Unit :=
  (Prog.sumProd ((F49 n k).toList.map fun js =>
      ((Arg.inp (Sum.inr (Sum.inl ⟨js.1, wordOf js.1 js.2.1⟩)) : Arg (InG n k)),
        (Arg.inp (Sum.inr (Sum.inr js)) : Arg (InG n k))))).bind
    (Prog.op1 .add (Arg.inp (Sum.inl (Sum.inl ()))) (Arg.inp (Sum.inr ())))

theorem pg49_eval [Inhabited (Fin n)] {k : ℕ} (f0 : ℝ) (T : Tens n) (W : WIdx n k → ℝ) :
    (pg49 n k).eval (inpG f0 T W) () =
      f0 + ∑ js ∈ F49 n k, T js.1 (wordOf js.1 js.2.1) * W js := by
  rw [pg49, eval_bind, eval_op1]
  show f0 + (Prog.sumProd _).eval (inpG f0 T W) () = _
  rw [eval_sumProd, List.map_map, ← Finset.sum_map_toList]
  rfl

theorem pg49_cost [Inhabited (Fin n)] (k : ℕ) (h : 1 ≤ L49 n k) : ((pg49 n k).cost : ℝ) = 2 * L49 n k := by
  simp only [pg49, cost_bind, cost_sumProd, cost_op1, List.length_map, Finset.length_toList]
  unfold L49 at h ⊢
  have : 2 * (F49 n k).card - 1 + 1 = 2 * (F49 n k).card := by omega
  rw [this]
  push_cast
  ring

theorem pg49_clean (n k : ℕ) [Inhabited (Fin n)] : Clean (pg49 n k) := by
  apply clean_bind
  · apply clean_sumProd
    intro ab hab
    obtain ⟨js, _, rfl⟩ := List.mem_map.mp hab
    exact ⟨rfl, rfl⟩
  · exact ⟨by simp [Prog.op1, argHeavy], fun _ => rfl⟩

/-! ## §4 The per-`(θ, M)` program `pw49` -/

/-- The kept sets for Part 43's moment program: every orbit at the levels `(j, 0)`, none elsewhere. -/
noncomputable def Kall (n d : ℕ) : ℕ → ℕ → Finset (Multiset (Mono n d)) := fun j l =>
  if l = 0 then (Finset.univ : Finset (Sym (Mono n d) j)).image Subtype.val else ∅

/-- The key `(j, 0, 0, q)` of Part 43: level `(j, 0)`, trace depth `0`, orbit `q`. -/
def key49 {k : ℕ} (j : Fin (k + 1)) (q : Sym (Mono n d) j) : KeyF n d k :=
  (j, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨j, q⟩)

/-- The words of orbit `s`. -/
noncomputable def orb {j : ℕ} (s : Sym (Fin n) j) : Finset (Fin j → Fin n) := by
  classical
  exact Finset.univ.filter fun a => mset a = s.1

/-- The inputs of `pw49`: `θ` and `M`. -/
abbrev InW (n d : ℕ) := Fin n ⊕ CoefIdxD n d

/-- The terms of weight `(j, s)`: an orbit `q` of `j` monomials and a word `a` of orbit `s`. -/
noncomputable def terms49 {k : ℕ} (js : WIdx n k) : List (Sym (Mono n d) js.1 × (Fin js.1 → Fin n)) :=
  ((Finset.univ : Finset (Sym (Mono n d) js.1)) ×ˢ orb js.2).toList

/-- The factors of one term: the moment weight of `q`, then `M_{(word q)_t, a_t}`, `t < j`. -/
noncomputable def termArgs {k : ℕ} (js : WIdx n k) (qa : Sym (Mono n d) js.1 × (Fin js.1 → Fin n)) :
    List (Arg (InW n d ⊕ KeyF n d k)) :=
  Arg.inp (Sum.inr (key49 js.1 qa.1)) :: List.ofFn (fun t : Fin js.1 =>
    Arg.inp (Sum.inl (Sum.inr ⟨(wordOf js.1 qa.1.1 t).1, ((wordOf js.1 qa.1.1 t).2, qa.2 t)⟩)))

/-- The program of one weight. -/
noncomputable def wProg {k : ℕ} (js : WIdx n k) : Prog (InW n d ⊕ KeyF n d k) Unit :=
  sumProdL ((terms49 js).map (termArgs js))

/-- Stage 2: every used weight. -/
noncomputable def stage2 (n d k : ℕ) : Prog (InW n d ⊕ KeyF n d k) (WIdx n k) := by
  classical
  exact Prog.par (wProg (d := d)) (F49 n k).toList

/-- **The per-`(θ, M)` program**: the moment program on `θ`, then stage 2. -/
noncomputable def pw49 {k : ℕ} (pm : Prog (Fin n) (KeyF n d k)) : Prog (InW n d) (WIdx n k) :=
  (pm.mapIn Sum.inl).bind (stage2 n d k)

/-- The stage-2 cost bound `Σ_{(j,s) ∈ F49} (j + 1) C(N + j − 1, j) n^j`, `N = C(n+d, d)`. -/
noncomputable def Cst49 (n d k : ℕ) : ℕ :=
  ∑ js ∈ F49 n k, (js.1.val + 1) * Fintype.card (Sym (Mono n d) js.1) * n ^ js.1.val

theorem wProg_eval {k : ℕ} (js : WIdx n k) (v : InW n d ⊕ KeyF n d k → ℝ) :
    (wProg js).eval v () =
      ∑ qa ∈ (Finset.univ : Finset (Sym (Mono n d) js.1)) ×ˢ orb js.2,
        v (Sum.inr (key49 js.1 qa.1)) *
          ∏ t : Fin js.1, v (Sum.inl (Sum.inr ⟨(wordOf js.1 qa.1.1 t).1, ((wordOf js.1 qa.1.1 t).2, qa.2 t)⟩)) := by
  simp only [wProg, eval_sumProdL, List.map_map, terms49]
  rw [← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro qa _
  simp only [Function.comp, termArgs, List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn,
    Arg.eval]

theorem wProg_cost {k : ℕ} (js : WIdx n k) :
    (wProg (d := d) js).cost ≤ (js.1.val + 1) * Fintype.card (Sym (Mono n d) js.1) * n ^ js.1.val := by
  classical
  rw [wProg, cost_sumProdL, List.map_map]
  have hlen : ∀ qa ∈ terms49 (d := d) js, (termArgs js qa).length - 1 = js.1.val := by
    intro qa _
    simp [termArgs]
  have hmap : List.map ((fun fs : List (Arg (InW n d ⊕ KeyF n d k)) => fs.length - 1) ∘ termArgs js)
      (terms49 js) = List.map (fun _ => js.1.val) (terms49 js) :=
    List.map_congr_left (fun qa h => hlen qa h)
  rw [hmap]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
  have hT : (terms49 (d := d) js).length ≤ Fintype.card (Sym (Mono n d) js.1) * n ^ js.1.val := by
    simp only [terms49, Finset.length_toList, Finset.card_product, Finset.card_univ]
    apply Nat.mul_le_mul_left
    calc (orb js.2).card ≤ (Finset.univ : Finset (Fin js.1 → Fin n)).card := Finset.card_le_univ _
      _ = n ^ js.1.val := by simp
  have : (terms49 (d := d) js).length * js.1.val + ((terms49 (d := d) js).length - 1) ≤
      (js.1.val + 1) * (terms49 (d := d) js).length := by
    have := Nat.sub_le (terms49 (d := d) js).length 1
    nlinarith
  calc _ ≤ (js.1.val + 1) * (terms49 (d := d) js).length := this
    _ ≤ (js.1.val + 1) * (Fintype.card (Sym (Mono n d) js.1) * n ^ js.1.val) :=
        Nat.mul_le_mul_left _ hT
    _ = _ := by ring

theorem stage2_cost (n d k : ℕ) : (stage2 n d k).cost ≤ Cst49 n d k := by
  classical
  unfold stage2 Cst49
  rw [cost_par]
  rw [Finset.sum_map_toList]
  convert Finset.sum_le_sum (fun js (_ : js ∈ F49 n k) => wProg_cost (d := d) js)

theorem stage2_clean (n d k : ℕ) : Clean (stage2 n d k) := by
  classical
  unfold stage2
  convert clean_par (wProg (d := d)) (fun js => ?_) (F49 n k).toList
  apply clean_sumProdL
  intro fs hfs a ha
  obtain ⟨qa, _, rfl⟩ := List.mem_map.mp hfs
  simp only [termArgs, List.mem_cons, List.mem_ofFn] at ha
  rcases ha with rfl | ⟨t, rfl⟩ <;> rfl

theorem pw49_eval {k : ℕ} (pm : Prog (Fin n) (KeyF n d k)) (θ : Fin n → ℝ) (M : CoefIdxD n d → ℝ)
    (js : WIdx n k) (hjs : js ∈ F49 n k) :
    (pw49 pm).eval (Sum.elim θ M) js =
      ∑ qa ∈ (Finset.univ : Finset (Sym (Mono n d) js.1)) ×ˢ orb js.2,
        pm.eval θ (key49 js.1 qa.1) *
          ∏ t : Fin js.1, M ⟨(wordOf js.1 qa.1.1 t).1, ((wordOf js.1 qa.1.1 t).2, qa.2 t)⟩ := by
  classical
  unfold pw49 stage2
  rw [eval_bind]
  convert (eval_par_mem _ _ _ _ (Finset.mem_toList.mpr hjs)).trans (wProg_eval js _) using 1
  simp only [Sum.elim_inr, Sum.elim_inl, eval_mapIn]
  rfl

theorem pw49_cost {k : ℕ} (pm : Prog (Fin n) (KeyF n d k)) :
    (pw49 pm).cost ≤ pm.cost + Cst49 n d k := by
  unfold pw49
  rw [cost_bind, cost_mapIn]
  exact Nat.add_le_add_left (stage2_cost n d k) _

theorem pw49_clean {k : ℕ} (pm : Prog (Fin n) (KeyF n d k)) (hpm : heavyCount pm = 0) :
    Clean (pw49 pm) :=
  clean_bind (clean_mapIn _ (clean_of_heavy hpm)) (stage2_clean n d k)

end BstLean.Part49
