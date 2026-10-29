import BstLean.Part41Defs


/-!
# Part 41, wave 1: the branch as a program — value and charged count (Lemma `C`, the count)

Paper: Definition `branch` and Lemma `C` of `proofs/option-m/41-arbitrary-degree.tex`.
Specification: `delegations/answers/p41-spec-opus.md`. Do not use `native_decide`.

Routes.
* `contractProg_eval`, `contractProg_cost`: induction on `a` with `eval_bind`, `eval_par_mem`,
  `eval_sumProd`, `cost_par`, `cost_sumProd` of `CostModel`; `Fin.snoc` splits the last slot.
* `gProgL_eval`: `eval_bind` three times. The trace slots give `trL m (T j)`. Group the ordered words `w`
  of `gTC` by their orbit `mset w`: `tr^i H^K` and `tr^{l+i} T_j[M_{w₁}, …]` are constant on an orbit
  (both symmetric, `trL_symm`), an orbit `q` holds `orbSize q` words, and `wordOf _ q` lists `q`;
  orbits with `(tr^i H^K)[q] = 0` contribute `0`.
* `gProgL_cost`: the traces cost `Σ n^{j−2m}(n^m − 1)`; a key costs `C_orb(a) + 1`, one heavy constant,
  and one addition in the final sum. The keys of `(j, l, i)` number at most `C(s, 2i) |K_{j,l}|` (an orbit
  `q` with `(tr^i H^K)[q] ≠ 0` is a sub-multiset of size `s − 2i` of some kept orbit of size `s`). The
  scalars number at most `k`.
-/

namespace BstLean.Part41

open BstLean.Cost

variable {n d : ℕ}

/-- The contraction program computes `A[v₁, …, v_a]`. -/
theorem contractProg_eval {ι : Type} (a : ℕ) (A : (Fin a → Fin n) → Arg ι) (v : Fin a → Fin n → Arg ι)
    (x : ι → ℝ) :
    (contractProg a A v).eval x () = contr (fun w => (A w).eval x []) (fun t c => (v t c).eval x []) := by
  classical
  induction a generalizing ι with
  | zero =>
    have hz : (finZeroElim : Fin 0 → Fin n) = default := Subsingleton.elim _ _
    simp [contractProg, contr, hz]
  | succ a ih =>
    rw [contractProg, eval_bind, ih]
    simp only [contr, Arg.eval_rename]
    simp only [Arg.eval, Sum.elim_inr]
    have hp : ∀ w : Fin a → Fin n,
        (Prog.par (fun w : Fin a → Fin n => Prog.sumProd
          ((List.finRange n).map fun c => (A (Fin.snoc w c), v (Fin.last a) c)))
          Finset.univ.toList).eval x w =
        ∑ c : Fin n, (A (Fin.snoc w c)).eval x [] * (v (Fin.last a) c).eval x [] := by
      intro w
      rw [eval_par_mem _ _ _ _ (by simp), eval_sumProd]
      simp only [List.map_map, Function.comp_def]
      simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
        (List.sum_ofFn (f := fun c : Fin n => (A (Fin.snoc w c)).eval x [] *
          (v (Fin.last a) c).eval x []))
    simp only [hp]
    rw [← (Fin.snocEquiv (fun _ : Fin (a + 1) => Fin n)).sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last, Function.comp_def, Sum.elim_inl, Arg.eval]
    ring

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

private lemma clean_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
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

private lemma clean_sumArgs {ι : Type} (l : List (Arg ι))
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

private lemma clean_sumProd {ι : Type} (l : List (Arg ι × Arg ι))
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

private lemma clean_heavyCount {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : Clean p) : heavyCount p = 0 := by
  unfold heavyCount
  have hb : (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

private lemma contract_clean {ι : Type} (a : ℕ) (A : (Fin a → Fin n) → Arg ι)
    (v : Fin a → Fin n → Arg ι) (hA : ∀ w, argHeavy (A w) = 0)
    (hv : ∀ t c, argHeavy (v t c) = 0) : Clean (contractProg a A v) := by
  classical
  induction a generalizing ι with
  | zero => exact ⟨by simp [contractProg, Prog.ofArgs], fun _ => hA _⟩
  | succ a ih =>
    apply clean_bind
    · apply clean_par
      intro w
      apply clean_sumProd
      intro ab hab
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hab
      exact ⟨hA _, hv _ _⟩
    · apply ih
      · intro w; rfl
      · intro t c; simpa [heavy_rename] using hv (Fin.castSucc t) c

/-- The contraction program has `C_orb(a)` instructions (`n ≥ 2`) and no heavy constant. -/
theorem contractProg_cost {ι : Type} (hn : 2 ≤ n) (a : ℕ) (A : (Fin a → Fin n) → Arg ι)
    (v : Fin a → Fin n → Arg ι) (hA : ∀ w, argHeavy (A w) = 0) (hv : ∀ t c, argHeavy (v t c) = 0) :
    ((contractProg a A v).cost : ℝ) = Corb n a ∧ heavyCount (contractProg a A v) = 0 := by
  classical
  refine ⟨?_, clean_heavyCount (contract_clean a A v hA hv)⟩
  induction a generalizing ι with
  | zero => simp [contractProg, Corb]
  | succ a ih =>
    rw [contractProg, cost_bind, cost_par]
    simp only [cost_sumProd, List.length_map, List.length_finRange]
    have hi := ih (fun w => (Arg.inp (Sum.inr w) : Arg (ι ⊕ (Fin a → Fin n))))
      (fun t c => (v (Fin.castSucc t) c).rename Sum.inl)
      (fun _ => rfl) (fun t c => (heavy_rename _ _).trans (hv _ _))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul,
      Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rw [hi]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hne : (n : ℝ) - 1 ≠ 0 := by linarith
    have hs : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
    rw [hs]
    cases a with
    | zero =>
      simp only [Corb, pow_zero, zero_add, one_ne_zero, ite_false, ite_true, pow_one, add_zero]
      field_simp [hne]
    | succ a =>
      simp only [Corb, Nat.succ_ne_zero, ite_false, pow_succ]
      field_simp [hne]
      ring

private lemma mset_wordOf {α : Type} [Inhabited α] (a : ℕ) (q : Multiset α)
    (hq : q.card = a) : mset (wordOf a q) = q := by
  subst a
  unfold mset wordOf
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun t : Fin q.card => q.toList.getD t.val default) = q.toList := by
    have hh : q.toList.length = q.card := Multiset.length_toList q
    rw [← hh]
    simpa only [List.getD_eq_get, Fin.eta] using List.ofFn_get q.toList
  rw [he, Multiset.coe_toList]

private lemma mset_glue_le {α : Type} (j i : ℕ) (hi : 2 * i ≤ j)
    (c : Fin i → α) (w : Fin (j - 2 * i) → α) : mset w ≤ mset (glue j i c w) := by
  classical
  let e : Fin (j - 2 * i) ↪ Fin j :=
    ⟨fun t => ⟨2 * i + t.val, by omega⟩,
      fun t u h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
  have he : ∀ t, glue j i c w (e t) = w t := by
    intro t
    change (if h : 2 * i + t.val < 2 * i then _ else _) = _
    rw [dite_eq_right (by omega)]
    congr 1
    apply Fin.ext
    change 2 * i + t.val - 2 * i = t.val
    omega
  have hm : (Finset.univ.map e).val.map (glue j i c w) = mset w := by
    simp only [Finset.map_val, Multiset.map_map, Function.comp_def, he, mset]
  rw [← hm]
  exact Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ _))

private lemma trace_support_card (s i l : ℕ) (hi : 2 * i ≤ s)
    (K : Finset (Multiset (Mono n d))) (hK : ∀ o ∈ K, o.card = s) :
    ((Finset.univ : Finset (Sym (Mono n d) (s - 2 * i))).filter
      (fun q => trL i (HKQ (s := s) K l) (wordOf _ q.val) ≠ 0)).card ≤
      s.choose (2 * i) * K.card := by
  classical
  let S := (Finset.univ : Finset (Sym (Mono n d) (s - 2 * i))).filter
      (fun q => trL i (HKQ (s := s) K l) (wordOf _ q.val) ≠ 0)
  let U := K.biUnion fun o => (o.powersetCard (s - 2 * i)).toFinset
  have hsub : S.image Subtype.val ⊆ U := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    have ht := (Finset.mem_filter.mp hq').2
    have hex : ∃ c : Fin i → Mono n d, HKQ K l (glue s i c (wordOf _ q'.val)) ≠ 0 := by
      by_contra h
      push Not at h
      exact ht (by simp [trL, h])
    obtain ⟨c, hc⟩ := hex
    have hk : mset (glue s i c (wordOf _ q'.val)) ∈ K := by
      by_contra h
      simp [HKQ, h] at hc
    apply Finset.mem_biUnion.mpr
    refine ⟨_, hk, ?_⟩
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_powersetCard.mpr
    refine ⟨?_, q'.property⟩
    simpa only [mset_wordOf _ _ q'.property] using
      mset_glue_le s i hi c (wordOf _ q'.val)
  calc
    S.card = (S.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ o ∈ K, (o.powersetCard (s - 2 * i)).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ o ∈ K, s.choose (2 * i) := by
      apply Finset.sum_le_sum
      intro o ho
      calc
        _ ≤ (o.powersetCard (s - 2 * i)).card := Multiset.toFinset_card_le _
        _ = s.choose (s - 2 * i) := by rw [Multiset.card_powersetCard, hK o ho]
        _ = s.choose (2 * i) := Nat.choose_symm hi
    _ = s.choose (2 * i) * K.card := by simp [mul_comm]

private lemma trSlot_cost {k : ℕ} (x : TrTag n) :
    (trSlotProg (d := d) (k := k) x).cost = n ^ x.1.2 - 1 := by
  simp [trSlotProg, cost_sumArgs]

private lemma trSlot_eval {k : ℕ} (x : TrTag n) (hx : x.1.1 ≤ k)
    (v : In41 n d k → ℝ) :
    (trSlotProg (d := d) x).eval v () = trL x.1.2 (Tv v x.1.1) x.2 := by
  classical
  have hj : x.1.1 < k + 1 := by omega
  simp only [trSlotProg, eval_sumArgs, List.map_map, Arg.eval, Function.comp_def,
    Tidx, dite_eq_left hj, Tv, trL]
  simp

private lemma trProg_cost (hn : 2 ≤ n) (k : ℕ) :
    ((trProg n d k).cost : ℝ) =
      ∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2),
        (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) := by
  classical
  have hn' : 1 ≤ n := by omega
  have hs (m : ℕ) : ((n ^ m - 1 : ℕ) : ℝ) = (n : ℝ) ^ m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow m n (by omega)), Nat.cast_pow, Nat.cast_one]
  simp only [trProg, cost_par, trSlots, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def, trSlot_cost]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, Finset.length_toList,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  simp only [Finset.sum_map_toList, Finset.sum_filter, Finset.sum_product]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [← Finset.sum_filter]
  have he : (Finset.Icc 1 k).filter (fun m => 2 * m ≤ j) = Finset.Icc 1 (j / 2) := by
    ext m
    have hjk := (Finset.mem_Icc.mp hj).2
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [he]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.cast_mul, Nat.cast_pow, hs]

private lemma orbit_perm {α : Type} [Fintype α] {s : ℕ} (u w : Fin s → α)
    (h : mset u = mset w) : ∃ σ : Equiv.Perm (Fin s), w ∘ σ = u := by
  classical
  have hcard (a : α) : Fintype.card {t : Fin s // u t = a} =
      Fintype.card {t : Fin s // w t = a} := by
    have hh := congrArg (Multiset.count a) h
    simpa only [mset, Multiset.count_map, Multiset.countP_eq_card_filter,
      ← Finset.filter_val, Fintype.card_subtype, Finset.card_def, eq_comm] using hh
  let e (a : α) := Fintype.equivOfCardEq (hcard a)
  let σ := (Equiv.sigmaFiberEquiv u).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv w))
  refine ⟨σ, ?_⟩
  funext t
  exact (e (u t) ⟨t, rfl⟩).property

private lemma prodX_mset {α : Type} [DecidableEq α] {s : ℕ} (w : Fin s → α) :
    (∏ t, MvPolynomial.X (w t) : MvPolynomial α ℝ) =
      MvPolynomial.monomial (mset w).toFinsupp 1 := by
  induction s with
  | zero => simp [mset, Multiset.toFinsupp_zero]
  | succ s ih =>
    have hm : mset w = mset (fun t : Fin s => w t.castSucc) + {w (Fin.last s)} := by
      simp only [mset, Fin.univ_val_map, List.ofFn_succ', List.concat_eq_append,
        ← Multiset.coe_add, Multiset.coe_singleton]
    rw [Fin.prod_univ_castSucc, ih, hm, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]

private lemma orbit_card {α : Type} [Fintype α] [DecidableEq α] (s : ℕ) (q : Sym α s) :
    (((Finset.univ : Finset (Fin s → α)).filter (fun w => mset w = q.val)).card : ℝ) =
      orbSize q.val := by
  have hpoly : ((∑ a : α, MvPolynomial.X a : MvPolynomial α ℝ) ^ s) =
      ∑ w : Fin s → α, MvPolynomial.monomial (mset w).toFinsupp 1 := by
    rw [← Fin.prod_const, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact prodX_mset w
  have hh := congrArg (fun p : MvPolynomial α ℝ => p.coeff q.val.toFinsupp) hpoly
  have he : ∀ w : Fin s → α, (mset w).toFinsupp = q.val.toFinsupp ↔ mset w = q.val := by
    intro w
    exact Multiset.toFinsupp.injective.eq_iff
  have hn : q.val.toFinsupp.multinomial = orbSize q.val := by
    simp only [Finsupp.multinomial, Multiset.toFinsupp_sum_eq, Finsupp.prod,
      Multiset.toFinsupp_support, Multiset.toFinsupp_apply, orbSize]
  have hs : q.val.toFinsupp.sum (fun _ m => m) = s :=
    (Multiset.toFinsupp_sum_eq _).trans q.property
  simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_sum_X_pow_of_fintype, Multiset.toFinsupp_sum_eq, q.property,
    hs, ite_true, he, hn, Finset.sum_boole] using hh.symm

private lemma sum_by_orbit {α : Type} [Fintype α] [DecidableEq α] [Inhabited α]
    (s : ℕ) (F : (Fin s → α) → ℝ)
    (hF : ∀ u w, mset u = mset w → F u = F w) :
    ∑ w, F w = ∑ q : Sym α s, (orbSize q.val : ℝ) * F (wordOf s q.val) := by
  let f : (Fin s → α) → Sym α s := fun w => ⟨mset w, by simp [mset]⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (f := F) (by simp)]
  apply Finset.sum_congr rfl
  intro q _
  have he : (Finset.univ.filter fun w => f w = q) =
      Finset.univ.filter (fun w => mset w = q.val) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [he]
  calc
    _ = ∑ w ∈ Finset.univ.filter (fun w => mset w = q.val), F (wordOf s q.val) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply hF
      rw [(Finset.mem_filter.mp hw).2, mset_wordOf _ _ q.property]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, orbit_card]

private lemma prog_trL_symm {ι R : Type*} [Fintype ι] [AddCommMonoid R] {j : ℕ} (l : ℕ) (hl : 2 * l ≤ j)
    (A : (Fin j → ι) → R) (hA : IsSymmT A) : IsSymmT (trL l A) := by
  classical
  intro σ w
  let e : Fin (j - 2 * l) ≃ {t : Fin j // 2 * l ≤ t.val} :=
    { toFun := fun t => ⟨⟨2 * l + t.val, by omega⟩, by simp⟩
      invFun := fun t => ⟨t.val.val - 2 * l, by have := t.val.isLt; have := t.property; omega⟩
      left_inv := by intro t; apply Fin.ext; simp
      right_inv := by intro t; apply Subtype.ext; apply Fin.ext; simp; have := t.property; omega }
  let τ := σ.extendDomain e
  unfold trL
  apply Finset.sum_congr rfl
  intro c hc
  have heq : glue j l c (w ∘ σ) = glue j l c w ∘ τ := by
    funext t
    by_cases ht : t.val < 2 * l
    · have hτ : τ t = t := σ.extendDomain_apply_not_subtype e (by omega)
      simp [hτ, glue, ht]
    · let u : Fin (j - 2 * l) := ⟨t.val - 2 * l, by have := t.isLt; omega⟩
      have hu : (e u).val = t := by apply Fin.ext; dsimp [e, u]; omega
      have hτ : τ t = (e (σ u)).val := by
        rw [← hu]
        exact σ.extendDomain_apply_image e u
      simp [glue, ht, hτ, e, u]
  rw [heq]
  exact hA τ (glue j l c w)

private lemma prog_HK_symm {s : ℕ} (K : Finset (Multiset (Mono n d))) (l : ℕ) :
    IsSymmT (HKQ (s := s) K l) := by
  classical
  intro σ w
  have hm : mset (w ∘ σ) = mset w := by
    simp only [mset, Fin.univ_val_map]
    exact Quot.sound (σ.ofFn_comp_perm w)
  unfold HKQ
  rw [hm]
  split_ifs
  · unfold HQ
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    funext a
    congr 1
    exact Equiv.sum_comp σ (fun t => expo (w t) a)
  · rfl

private lemma contr_symm {α : Type} {a : ℕ} (A : (Fin a → Fin n) → ℝ)
    (hA : IsSymmT A) (v : α → Fin n → ℝ) :
    IsSymmT (fun w : Fin a → α => contr A (fun t => v (w t))) := by
  classical
  intro σ w
  unfold contr
  dsimp only
  let e := Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  change A (c ∘ σ) * (∏ t, v (w (σ t)) (c (σ t))) = _
  rw [hA σ c, Equiv.prod_comp σ (fun t => v (w t) (c t))]

private lemma trProg_eval {k : ℕ} (j m : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hm : 1 ≤ m) (hjm : 2 * m ≤ j) (w : Fin (j - 2 * m) → Fin n)
    (v : In41 n d k → ℝ) :
    (trProg n d k).eval v ⟨(j, m), w⟩ = trL m (Tv v j) w := by
  classical
  unfold trProg
  rw [eval_par_mem]
  · exact trSlot_eval _ hjk v
  · unfold trSlots
    apply List.mem_flatMap.mpr
    refine ⟨(j, m), ?_, ?_⟩
    · simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨hj, hjk⟩, ⟨hm, by omega⟩⟩, hjm⟩
    · exact List.mem_map.mpr ⟨w, by simp, rfl⟩

private lemma trArg_eval {k : ℕ} (j m : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hjm : 2 * m ≤ j) (w : Fin (j - 2 * m) → Fin n) (v : In41 n d k → ℝ) :
    (trArg j m w).eval (Sum.elim v ((trProg n d k).eval v)) [] = trL m (Tv v j) w := by
  by_cases hm : m = 0
  · subst m
    have hj' : j < k + 1 := by omega
    have hg : glue j 0 (default : Fin 0 → Fin n) w = w := by
      funext t
      simp [glue]
    simp [trArg, Arg.eval, Tidx, Tv, hj', trL, hg]
  · simp only [trArg, hm, Arg.eval]
    exact trProg_eval j m hj hjk (by omega) hjm w v

private lemma keyProg_eval {k : ℕ} (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (key : Key n d) (hj : 1 ≤ key.1) (hjk : key.1 ≤ k)
    (hl : 2 * (key.2.1 + key.2.2.1) ≤ key.1) (v : In41 n d k → ℝ) :
    (keyProg k K key).eval (Sum.elim v ((trProg n d k).eval v)) () =
      contr (trL (key.2.1 + key.2.2.1) (Tv v key.1))
        (fun t => colM (Mv v) (wordOf _ key.2.2.2 t)) * (wKey K key : ℝ) := by
  rw [keyProg, eval_bind, eval_op1]
  simp only [Op.eval, Arg.eval, Sum.elim_inr]
  rw [contractProg_eval]
  have hA : (fun w => (trArg key.1 (key.2.1 + key.2.2.1) w).eval
      (Sum.elim v ((trProg n d k).eval v)) []) = trL (key.2.1 + key.2.2.1) (Tv v key.1) :=
    funext (fun w => trArg_eval _ _ hj hjk hl w v)
  rw [hA]
  rfl

private lemma gProgL_eval_keys (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (v : In41 n d k → ℝ) :
    (gProgL n d k K).eval v () = f0v v +
      ((keys k K).map fun key => (keyProg k K key).eval
        (Sum.elim v ((trProg n d k).eval v)) ()).sum := by
  classical
  rw [gProgL, eval_bind, eval_bind, eval_sumArgs]
  simp only [List.map_cons, List.sum_cons, Arg.eval, Sum.elim_inl, Sum.elim_inr,
    List.map_map, Function.comp_def, f0v]
  congr 1
  congr 1
  apply List.map_congr_left
  intro key hk
  exact eval_par_mem _ _ _ key hk

private lemma contr_cast_symm {α : Type} {a b : ℕ} (hab : a = b)
    (A : (Fin a → Fin n) → ℝ) (hA : IsSymmT A) (v : α → Fin n → ℝ) :
    IsSymmT (fun w : Fin b → α => contr A (fun t => v (w (Fin.cast hab t)))) := by
  subst b
  exact contr_symm A hA v

set_option maxHeartbeats 400000 in
/-- **The program computes the branch**, for symmetric tensors. -/
theorem gProgL_eval (hn : 1 ≤ n) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) (v : In41 n d k → ℝ) (hT : TSymm k (Tv v)) :
    (gProgL n d k K).eval v () = gTC k K (f0v v) (Tv v) (Mv v) := by
  classical
  have _hn := hn
  have _hK := hK
  rw [gProgL_eval_keys]
  simp only [keys, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    List.flatMap_def, List.map_flatten, List.sum_flatten, Finset.sum_map_toList]
  unfold gTC
  rw [← add_assoc]
  apply congrArg₂ (· + ·)
  · apply congrArg (fun z => f0v v + z)
    apply Finset.sum_congr rfl
    intro j hj
    have hjj := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1)
    have hev := (Finset.mem_filter.mp hj).2
    have hz : j - 2 * (j / 2) = 0 := by obtain ⟨r, rfl⟩ := hev; omega
    rw [keyProg_eval K (j, j / 2, 0, 0) hjj.1 hjj.2 (by dsimp; omega) v]
    have hv : (fun t : Fin (j - 2 * (j / 2 + 0)) => colM (Mv v) (wordOf _ (0 : Multiset (Mono n d)) t)) =
        (fun _ _ => (0 : ℝ)) := by
      funext t
      have := t.isLt
      dsimp at this
      omega
    rw [hv]
    simp only [wKey, ite_eq_left (by omega : 2 * (j / 2) = j),
      Rat.cast_mul]
    simp only [Nat.add_zero]
    ring
  · apply Finset.sum_congr rfl
    intro jl hjl
    have hlev := (Finset.mem_filter.mp hjl)
    have hjj := Finset.mem_Icc.mp (Finset.mem_product.mp hlev.1).1
    have hlt := hlev.2
    have hrange (m : ℕ) (f : ℕ → ℝ) : ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    rw [hrange, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    let s := jl.1 - 2 * jl.2
    let a := s - 2 * i
    have hii : 2 * i ≤ s := by have := Finset.mem_range.mp hi; dsimp [s] at *; omega
    have hli : 2 * (jl.2 + i) ≤ jl.1 := by dsimp [s] at hii; omega
    have ha : jl.1 - 2 * (jl.2 + i) = a := by dsimp [a, s]; omega
    let H := trL i (HKQ (s := s) (K jl.1 jl.2) jl.2)
    let G : (Fin a → Mono n d) → ℝ := fun w =>
      contr (trL (jl.2 + i) (Tv v jl.1)) (fun t => colM (Mv v) (w (Fin.cast ha t)))
    let F : (Fin a → Mono n d) → ℝ := fun w => (H w : ℝ) * G w
    have hH : IsSymmT H := prog_trL_symm i hii _ (prog_HK_symm _ _)
    have hG : IsSymmT G := contr_cast_symm ha _
      (prog_trL_symm _ hli _ (hT _ hjj.1 hjj.2)) (colM (Mv v))
    have hF : ∀ u w, mset u = mset w → F u = F w := by
      intro u w h
      obtain ⟨σ, he⟩ := orbit_perm u w h
      rw [← he]
      dsimp [F]
      rw [hH σ w, hG σ w]
    have hg := sum_by_orbit a F hF
    have hd : (∑ q ∈ (Finset.univ : Finset (Sym (Mono n d) a)).filter
        (fun q => H (wordOf a q.val) ≠ 0), (orbSize q.val : ℝ) * F (wordOf a q.val)) =
        ∑ q : Sym (Mono n d) a, (orbSize q.val : ℝ) * F (wordOf a q.val) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      have hz : H (wordOf a q.val) = 0 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hq
      change (orbSize q.val : ℝ) * ((H (wordOf a q.val) : ℝ) * G (wordOf a q.val)) = 0
      rw [hz]
      simp
    rw [← hd] at hg
    rw [← mul_assoc]
    change (∑ q ∈ (Finset.univ : Finset (Sym (Mono n d) a)).filter
        (fun q => H (wordOf a q.val) ≠ 0),
        (keyProg k K (jl.1, jl.2, i, q.val)).eval (Sum.elim v ((trProg n d k).eval v)) ()) =
      (kapQ n d jl.1 jl.2 : ℝ) * (muQ n d s i : ℝ) * ∑ w, F w
    rw [hg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [keyProg_eval K _ hjj.1 hjj.2 hli v]
    simp only [wKey, ite_eq_right (by omega : ¬ 2 * jl.2 = jl.1),
      Rat.cast_mul, Rat.cast_natCast]
    change G (wordOf a q.val) *
      ((kapQ n d jl.1 jl.2 : ℝ) * (muQ n d s i : ℝ) * (orbSize q.val : ℝ) * (H (wordOf a q.val) : ℝ)) = _
    dsimp only [F]
    ring


private def OutClean {ι κ : Type} (p : Prog ι κ) : Prop := ∀ o, argHeavy (p.out o) = 0

private def bodyH {ι κ : Type} (p : Prog ι κ) : ℕ :=
  (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum

private lemma heavy_subst_eq {ι κ : Type} (f : ι → Arg κ) (s l : ℕ)
    (hf : ∀ i, argHeavy (f i) = 0) (a : Arg ι) :
    argHeavy (a.subst f s l) = argHeavy a := by
  cases a with
  | inp i => exact hf i
  | cst q => rfl
  | reg r => simp only [Arg.subst]; split_ifs <;> simp [argHeavy]

private lemma outClean_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
    (hp : OutClean p) (hq : OutClean q) : OutClean (p.bind q) := by
  intro o
  apply heavy_subst _ _ _ _ _ (hq o)
  intro i
  cases i with
  | inl i => rfl
  | inr k => exact heavy_clamp _ _ (hp k)

private lemma bodyH_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
    (hp : OutClean p) : bodyH (p.bind q) = bodyH p + bodyH q := by
  have hf : ∀ i, argHeavy (Sum.elim Arg.inp
      (fun k => (p.out k).clamp p.body.length) i) = 0 := by
    intro i
    cases i with
    | inl i => rfl
    | inr k => exact heavy_clamp _ _ (hp k)
  simp only [bodyH, Prog.bind, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Instr.subst, heavy_subst_eq _ _ _ hf]

private lemma bodyH_mapIn {ι κ ν : Type} (f : ι → ν) (p : Prog ι κ) :
    bodyH (p.mapIn f) = bodyH p := by
  simp only [bodyH, Prog.mapIn, List.map_map, Function.comp_def, Instr.rename, heavy_rename]

private lemma outClean_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
    (hp : ∀ k, OutClean (p k)) (l : List κ) : OutClean (Prog.par p l) := by
  induction l with
  | nil => simp [OutClean, Prog.par, Prog.ofArgs, argHeavy]
  | cons k l ih =>
    apply outClean_bind (hp k)
    intro j
    dsimp
    split_ifs
    · rfl
    · exact (heavy_rename _ _).trans (ih j)

private lemma bodyH_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
    (hp : ∀ k, OutClean (p k)) (l : List κ) :
    bodyH (Prog.par p l) = (l.map fun k => bodyH (p k)).sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [Prog.par, bodyH_bind (hp k)]
    have h : bodyH
      (⟨((Prog.par p l).mapIn Sum.inl).body,
        fun j => if j = k then Arg.inp (Sum.inr ()) else
          ((Prog.par p l).mapIn Sum.inl).out j⟩ : Prog (ι ⊕ Unit) κ) =
        bodyH (Prog.par p l) := by
      change bodyH ((Prog.par p l).mapIn Sum.inl) = _
      exact bodyH_mapIn _ _
    rw [h, ih]
    rfl

private lemma clean_bodyH {ι κ : Type} {p : Prog ι κ} (hp : Clean p) : bodyH p = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
  simp [(hp.1 I hI).1, (hp.1 I hI).2]

private lemma heavyCount_eq_bodyH {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : OutClean p) : heavyCount p = bodyH p := by simp [heavyCount, bodyH, OutClean] at hp ⊢; exact hp

private lemma trProg_clean (k : ℕ) : Clean (trProg n d k) := by
  classical
  apply clean_par
  intro x
  apply clean_sumArgs
  intro a ha
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
  rfl

private lemma keyProg_outClean (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (key : Key n d) : OutClean (keyProg k K key) := by
  apply outClean_bind
  · apply (contract_clean _ _ _ _ _).2
    · intro w; unfold trArg; split_ifs <;> rfl
    · intro t c; rfl
  · intro o; rfl

private lemma keyProg_bodyH (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (key : Key n d) : bodyH (keyProg k K key) ≤ 1 := by
  have hc : Clean (contractProg (key.1 - 2 * (key.2.1 + key.2.2.1))
      (fun w => trArg (k := k) key.1 (key.2.1 + key.2.2.1) w)
      (fun t c => Arg.inp (Sum.inl (Sum.inl ⟨(wordOf _ key.2.2.2 t).1,
        ((wordOf _ key.2.2.2 t).2, c)⟩)))) := by
    apply contract_clean
    · intro w; unfold trArg; split_ifs <;> rfl
    · intro t c; rfl
  rw [keyProg, bodyH_bind hc.2, clean_bodyH hc]
  simp only [bodyH, Prog.op1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    argHeavy, zero_add, add_zero]
  split_ifs <;> omega

private lemma keyProg_cost (hn : 2 ≤ n) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (key : Key n d) :
    ((keyProg k K key).cost : ℝ) = Corb n (key.1 - 2 * (key.2.1 + key.2.2.1)) + 1 := by
  rw [keyProg, cost_bind, Nat.cast_add, cost_op1, Nat.cast_one]
  rw [(contractProg_cost hn _ _ _ (fun w => by unfold trArg; split_ifs <;> rfl)
    (fun _ _ => rfl)).1]

private lemma gProgL_cost_keys (hn : 2 ≤ n) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) :
    (chargedCost n (gProgL n d k K) : ℝ) ≤ ((trProg n d k).cost : ℝ) +
      ((keys k K).map fun key => Corb n (key.1 - 2 * (key.2.1 + key.2.2.1)) + n + 2).sum := by
  classical
  let q := Prog.par (keyProg k K) (keys k K)
  let r : Prog ((In41 n d k ⊕ TrTag n) ⊕ Key n d) Unit :=
    Prog.sumArgs (Arg.inp (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) ::
      (keys k K).map fun key => Arg.inp (Sum.inr key))
  have hr : Clean r := by
    apply clean_sumArgs
    intro a ha
    simp only [List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨key, _, rfl⟩ <;> rfl
  have hq := outClean_par (keyProg k K) (keyProg_outClean k K) (keys k K)
  have ht := trProg_clean (n := n) (d := d) k
  have hb : bodyH (gProgL n d k K) ≤ (keys k K).length := by
    change bodyH ((trProg n d k).bind (q.bind r)) ≤ _
    rw [bodyH_bind ht.2, clean_bodyH ht, bodyH_bind hq, clean_bodyH hr,
      zero_add, add_zero, bodyH_par _ (keyProg_outClean k K)]
    calc
      _ ≤ ((keys k K).map fun _ => 1).sum := by
        apply List.sum_le_sum
        intro key hkey
        exact keyProg_bodyH k K key
      _ = _ := by simp
  have ho : OutClean (gProgL n d k K) := outClean_bind ht.2 (outClean_bind hq hr.2)
  have hc : ((gProgL n d k K).cost : ℝ) = ((trProg n d k).cost : ℝ) +
      ((keys k K).map fun key => Corb n (key.1 - 2 * (key.2.1 + key.2.2.1)) + 1).sum +
      (keys k K).length := by
    change (((trProg n d k).bind (q.bind r)).cost : ℝ) = _
    simp only [cost_bind, Nat.cast_add]
    dsimp [q, r]
    rw [cost_par, cost_sumArgs]
    simp only [List.length_cons, List.length_map, Nat.add_sub_cancel,
      Nat.cast_list_sum, List.map_map, Function.comp_def, keyProg_cost hn]
    ring
  unfold chargedCost
  rw [Nat.cast_add, Nat.cast_mul, heavyCount_eq_bodyH ho, hc]
  have hbR : (bodyH (gProgL n d k K) : ℝ) ≤ (keys k K).length := by exact_mod_cast hb
  have hh := mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg n)
  have he : ((keys k K).map fun key => Corb n (key.1 - 2 * (key.2.1 + key.2.2.1)) + n + 2).sum =
      ((keys k K).map fun key => Corb n (key.1 - 2 * (key.2.1 + key.2.2.1)) + 1).sum +
      (keys k K).length * ((n : ℝ) + 1) := by
    induction keys k K with
    | nil => simp
    | cons key l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]; rw [ih]; ring
  rw [he]
  linarith

private lemma list_sum_range (m : ℕ) (f : ℕ → ℝ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

set_option maxHeartbeats 50000 in
/-- **The charged count** (Lemma `C`): at most `Σ_{(j,l)} c_s |K_{j,l}|` plus the traces and the scalars. -/
theorem gProgL_cost (hn : 2 ≤ n) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    (chargedCost n (gProgL n d k K) : ℝ) ≤
      ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ((K jl.1 jl.2).card : ℝ) +
        ∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2), (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) +
        k * (n + 3) := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc (a : ℕ) : 0 ≤ Corb n a := by
    unfold Corb
    split_ifs
    · rfl
    · apply div_nonneg
      · apply mul_nonneg (by linarith)
        have hh : 1 ≤ (n : ℝ) ^ a := one_le_pow₀ (by linarith)
        linarith
      · linarith
  have hscalar :
      ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j),
        (Corb n (j - 2 * (j / 2 + 0)) + n + 2) ≤ k * ((n : ℝ) + 3) := by
    have hz : ∀ j ∈ (Finset.Icc 1 k).filter (fun j => Even j), j - 2 * (j / 2) = 0 := by
      intro j hj
      have he := (Finset.mem_filter.mp hj).2
      obtain ⟨m, rfl⟩ := he
      omega
    simp only [add_zero]
    have hsum : (∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j),
        (Corb n (j - 2 * (j / 2)) + n + 2)) =
        (((Finset.Icc 1 k).filter (fun j => Even j)).card : ℝ) * ((n : ℝ) + 2) := by
      calc
        _ = ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j), ((n : ℝ) + 2) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hz j hj]
          simp [Corb]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hcard : ((Finset.Icc 1 k).filter (fun j => Even j)).card ≤ k := by
      calc
        _ ≤ (Finset.Icc 1 k).card := Finset.card_filter_le _ _
        _ = k := by simp
    have hcardR : (((Finset.Icc 1 k).filter (fun j => Even j)).card : ℝ) ≤ k := by exact_mod_cast hcard
    exact (mul_le_mul_of_nonneg_right hcardR (by linarith : 0 ≤ (n : ℝ) + 2)).trans
      (mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) + 2 ≤ n + 3) (Nat.cast_nonneg k))
  have hlevel : ∀ jl ∈ levels k,
      ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1),
        ∑ q ∈ (Finset.univ : Finset (Sym (Mono n d) (jl.1 - 2 * jl.2 - 2 * i))).filter
          (fun q => trL i (HKQ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2) (wordOf _ q.val) ≠ 0),
          (Corb n (jl.1 - 2 * (jl.2 + i)) + n + 2) ≤
      cS n (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card := by
    intro jl hjl
    let s := jl.1 - 2 * jl.2
    have he (i : ℕ) : jl.1 - 2 * (jl.2 + i) = s - 2 * i := by dsimp [s]; omega
    simp only [he, Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ ∑ i ∈ Finset.range (s / 2 + 1),
          ((s.choose (2 * i) * (K jl.1 jl.2).card : ℕ) : ℝ) *
            (Corb n (s - 2 * i) + 2 * n + 8) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : 2 * i ≤ s := by have := Finset.mem_range.mp hi; omega
        have hcard := trace_support_card s i jl.2 hi' (K jl.1 jl.2) (hK jl hjl)
        have hcardR :
            (((Finset.univ : Finset (Sym (Mono n d) (s - 2 * i))).filter
              (fun q => trL i (HKQ (s := s) (K jl.1 jl.2) jl.2) (wordOf _ q.val) ≠ 0)).card : ℝ) ≤
            ((s.choose (2 * i) * (K jl.1 jl.2).card : ℕ) : ℝ) := by exact_mod_cast hcard
        apply mul_le_mul hcardR (by linarith) (by linarith [hc (s - 2 * i)])
        linarith [hc (s - 2 * i)]
      _ ≤ cS n s * (K jl.1 jl.2).card := by
        simp only [Nat.cast_mul]
        have heq :
            (∑ i ∈ Finset.range (s / 2 + 1),
              (s.choose (2 * i) : ℝ) * (K jl.1 jl.2).card * (Corb n (s - 2 * i) + 2 * n + 8)) =
            (∑ i ∈ Finset.range (s / 2 + 1),
              (s.choose (2 * i) : ℝ) * (Corb n (s - 2 * i) + 2 * n + 8)) * (K jl.1 jl.2).card := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [heq, cS, add_mul]
        have hnon : 0 ≤ (n : ℝ) * (K jl.1 jl.2).card := by positivity
        linarith
  have hkeys : ((keys k K).map fun key =>
      Corb n (key.1 - 2 * (key.2.1 + key.2.2.1)) + n + 2).sum ≤
      ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ((K jl.1 jl.2).card : ℝ) +
        k * ((n : ℝ) + 3) := by
    simp only [keys, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.flatMap_def, List.map_flatten, List.sum_flatten,
      Finset.sum_map_toList, list_sum_range]
    have hl := Finset.sum_le_sum hlevel
    linarith only [hscalar, hl]
  have hh := gProgL_cost_keys hn k K
  rw [trProg_cost hn k] at hh
  linarith only [hh, hkeys]

end BstLean.Part41

