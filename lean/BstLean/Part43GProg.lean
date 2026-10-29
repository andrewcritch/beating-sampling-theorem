import BstLean.Part43Defs
import BstLean.Part41Prog

/-!
# Part 43, wave 1: the per-case branch program and the grouping identity

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. The theorem statements match the frozen specification.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* `gProg43_exists`: Part 41's `gProgL` with the constant `wKey K key` replaced by the input
  `Sum.inr key` and the key list `keys43 k K`: stage 1 `trProg` (Part 41), stage 2 one `keyProg`
  per key (`contractProg` then one product), one `sumArgs`. No constant other than `0`, `1` remains.
  The cost follows `Part41Prog.gProgL_cost`: per level `(j, l)` and depth `i` there are at most
  `C(s, 2i) |K j l|` keys (sub-multisets of size `s − 2i` of a kept orbit of size `s`).
* `gTCW_eq`: in `gTCR`, group the words `w` by their orbit `q = mset w`. Both factors are symmetric in
  `w` (`HR_symm`-type argument for `HKR`, `Part41Tensor.trL_symm`, `TSymm`), so `Σ_w = Σ_q |orbit q|
  (value at wordOf q)`. A nonzero `(tr^i H^K)[q]` needs `mset(glue c q) = 2·mset c + q ∈ K`, so `q` is
  below a kept orbit and is a key; keys with zero trace contribute `0`.
-/

namespace BstLean.Part43

set_option backward.isDefEq.respectTransparency false

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

open BstLean.Part41

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

private lemma contr_cast_symm {α : Type} {a b : ℕ} (hab : a = b)
    (A : (Fin a → Fin n) → ℝ) (hA : IsSymmT A) (v : α → Fin n → ℝ) :
    IsSymmT (fun w : Fin b → α => contr A (fun t => v (w (Fin.cast hab t)))) := by
  subst b
  exact contr_symm A hA v


private lemma HKR_symm (μ : Measure (Fin n → ℝ)) {s : ℕ}
    (K : Finset (Multiset (Mono n d))) (l : ℕ) : IsSymmT (HKR μ (s := s) K l) := by
  classical
  intro σ w
  have hm : mset (w ∘ σ) = mset w := by
    simp only [mset, Fin.univ_val_map]
    exact Quot.sound (σ.ofFn_comp_perm w)
  unfold HKR
  rw [hm]
  split_ifs
  · unfold HR
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    exact Equiv.prod_comp σ (fun t => phiM x (w t))
  · rfl

private lemma trace_zero_outside (μ : Measure (Fin n → ℝ)) (s i l : ℕ)
    (hi : 2 * i ≤ s) (K : Finset (Multiset (Mono n d)))
    (q : Sym (Mono n d) (s - 2 * i)) (hq : ¬ ∃ o ∈ K, q.val ≤ o) :
    trL i (HKR μ (s := s) K l) (wordOf _ q.val) = 0 := by
  classical
  unfold trL
  apply Finset.sum_eq_zero
  intro c _
  have hk : mset (glue s i c (wordOf _ q.val)) ∉ K := by
    intro hk
    apply hq
    refine ⟨_, hk, ?_⟩
    simpa only [mset_wordOf _ _ q.property] using
      mset_glue_le s i hi c (wordOf _ q.val)
  exact ite_eq_right hk

private lemma grouped_trace (μ : Measure (Fin n → ℝ)) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (T : Tens n) (hT : TSymm k T)
    (M : CoefIdxD n d → ℝ) (jl : ℕ × ℕ) (hjl : jl ∈ levels k)
    (i : ℕ) (hi : i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1)) :
    (∑ w : Fin (jl.1 - 2 * jl.2 - 2 * i) → Mono n d,
      trL i (HKR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2) w *
        contr (trL (jl.2 + i) (T jl.1))
          (fun t => colM M (w ⟨t.1, by have := t.2; omega⟩))) =
    ∑ q ∈ (Finset.univ : Finset (Sym (Mono n d) (jl.1 - 2 * jl.2 - 2 * i))).filter
      (fun q => ∃ o ∈ K jl.1 jl.2, q.val ≤ o),
      (orbSize q.val : ℝ) * trL i (HKR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2)
        (wordOf _ q.val) * contr (trL (jl.2 + i) (T jl.1))
          (fun t => colM M (wordOf _ q.val ⟨t.1, by have := t.2; omega⟩)) := by
  classical
  have hlev := Finset.mem_filter.mp hjl
  have hj := Finset.mem_Icc.mp (Finset.mem_product.mp hlev.1).1
  have hii : 2 * i ≤ jl.1 - 2 * jl.2 := by have := Finset.mem_range.mp hi; omega
  have hli : 2 * (jl.2 + i) ≤ jl.1 := by omega
  have ha : jl.1 - 2 * (jl.2 + i) = jl.1 - 2 * jl.2 - 2 * i := by omega
  let H := trL i (HKR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2)
  let G := fun w : Fin (jl.1 - 2 * jl.2 - 2 * i) → Mono n d =>
    contr (trL (jl.2 + i) (T jl.1)) (fun t => colM M (w (Fin.cast ha t)))
  have hH : IsSymmT H := prog_trL_symm _ hii _ (HKR_symm _ _ _)
  have hG : IsSymmT G := contr_cast_symm ha _
    (prog_trL_symm _ hli _ (hT _ hj.1 hj.2)) (colM M)
  have hF : ∀ u w, mset u = mset w → H u * G u = H w * G w := by
    intro u w h
    obtain ⟨σ, he⟩ := orbit_perm u w h
    rw [← he, hH σ w, hG σ w]
  have hg := sum_by_orbit _ (fun w => H w * G w) hF
  change (∑ w, H w * G w) = _
  rw [hg]
  symm
  calc
    _ = ∑ q ∈ (Finset.univ : Finset (Sym (Mono n d) (jl.1 - 2 * jl.2 - 2 * i))).filter
        (fun q => ∃ o ∈ K jl.1 jl.2, q.val ≤ o),
        (orbSize q.val : ℝ) * (H (wordOf _ q.val) * G (wordOf _ q.val)) := by
      apply Finset.sum_congr rfl
      intro q _
      dsimp [H, G]
      rw [mul_assoc]
      rfl
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      have hq' : ¬ ∃ o ∈ K jl.1 jl.2, q.val ≤ o := by
        intro h
        exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hz := trace_zero_outside μ (jl.1 - 2 * jl.2) i jl.2 hii (K jl.1 jl.2) q hq'
      change (orbSize q.val : ℝ) * (H (wordOf _ q.val) * G (wordOf _ q.val)) = 0
      dsimp [H]
      erw [hz]
      ring

private lemma suborbit_card (s i : ℕ) (hi : 2 * i ≤ s)
    (K : Finset (Multiset (Mono n d))) (hK : ∀ o ∈ K, o.card = s) :
    ((Finset.univ : Finset (Sym (Mono n d) (s - 2 * i))).filter
      (fun q => ∃ o ∈ K, q.val ≤ o)).card ≤ s.choose (2 * i) * K.card := by
  classical
  let S := (Finset.univ : Finset (Sym (Mono n d) (s - 2 * i))).filter
    (fun q => ∃ o ∈ K, q.val ≤ o)
  let U := K.biUnion fun o => (o.powersetCard (s - 2 * i)).toFinset
  have hsub : S.image Subtype.val ⊆ U := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨o, ho, hle⟩ := (Finset.mem_filter.mp hq').2
    exact Finset.mem_biUnion.mpr ⟨o, ho, Multiset.mem_toFinset.mpr
      (Multiset.mem_powersetCard.mpr ⟨hle, q'.property⟩)⟩
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

private lemma keyF_ext {k : ℕ} {u v : KeyF n d k}
    (hj : u.1.val = v.1.val) (hl : u.2.1.val = v.2.1.val)
    (hi : u.2.2.1.val = v.2.2.1.val)
    (hq : u.2.2.2.2.val = v.2.2.2.2.val) : u = v := by
  rcases u with ⟨j, l, i, a, q⟩
  rcases v with ⟨j', l', i', a', q'⟩
  dsimp at hj hl hi hq
  have hj' := Fin.ext hj
  have hl' := Fin.ext hl
  have hi' := Fin.ext hi
  subst j'; subst l'; subst i'
  have ha : a = a' := Fin.ext (by
    have hc := congrArg Multiset.card hq
    exact q.property.symm.trans (hc.trans q'.property))
  subst a'
  have hq' : q = q' := Subtype.ext hq
  subst q'
  rfl

private def scalarKey43 (k : ℕ) (j : ↥((Finset.Icc 1 k).filter (fun j => Even j))) :
    KeyF n d k :=
  (⟨j.val, by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp j.property).1).2; omega⟩,
    ⟨j.val / 2, by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp j.property).1).2; omega⟩,
    ⟨0, by omega⟩, ⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩)

private def levelKey43 (k : ℕ) (jl : ↥(levels k))
    (i : Fin ((jl.val.1 - 2 * jl.val.2) / 2 + 1))
    (q : Sym (Mono n d) (jl.val.1 - 2 * jl.val.2 - 2 * i.val)) : KeyF n d k :=
  (⟨jl.val.1, by
      have := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp jl.property).1).1).2
      omega⟩,
    ⟨jl.val.2, by
      have := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp jl.property).1).2
      omega⟩,
    ⟨i.val, by
      have := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp jl.property).1).1).2
      have := i.isLt
      omega⟩,
    ⟨⟨jl.val.1 - 2 * jl.val.2 - 2 * i.val, by
      have := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp jl.property).1).1).2
      omega⟩, q⟩)

private lemma scalarKey_mem (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (j : ↥((Finset.Icc 1 k).filter (fun j => Even j))) :
    scalarKey43 (n := n) (d := d) k j ∈ keys43 k K := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Or.inl ?_⟩
  have hj := Finset.mem_Icc.mp (Finset.mem_filter.mp j.property).1
  exact ⟨(Finset.mem_filter.mp j.property).2, hj.1, rfl, rfl, rfl⟩

private lemma levelKey_mem (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (jl : ↥(levels k))
    (i : Fin ((jl.val.1 - 2 * jl.val.2) / 2 + 1))
    (q : Sym (Mono n d) (jl.val.1 - 2 * jl.val.2 - 2 * i.val))
    (hq : ∃ o ∈ K jl.val.1 jl.val.2, q.val ≤ o) :
    levelKey43 k jl i q ∈ keys43 k K := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Or.inr ?_⟩
  refine ⟨jl.property, ?_, rfl, hq⟩
  change 2 * i.val ≤ jl.val.1 - 2 * jl.val.2
  have := i.isLt
  omega

private noncomputable def subOrbits43 (s i : ℕ)
    (K : Finset (Multiset (Mono n d))) : Finset (Sym (Mono n d) (s - 2 * i)) := by
  classical
  exact Finset.univ.filter (fun q => ∃ o ∈ K, q.val ≤ o)

private abbrev KeyEnum43 (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) :=
  (↥((Finset.Icc 1 k).filter (fun j => Even j))) ⊕
    (Σ jl : ↥(levels k), Σ i : Fin ((jl.val.1 - 2 * jl.val.2) / 2 + 1),
      ↥(subOrbits43 (jl.val.1 - 2 * jl.val.2) i.val (K jl.val.1 jl.val.2)))

private def enumKey43 (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) :
    KeyEnum43 k K → KeyF n d k
  | .inl j => scalarKey43 k j
  | .inr ⟨jl, i, q⟩ => levelKey43 k jl i q.val

private lemma enumKey_mem (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (e : KeyEnum43 k K) : enumKey43 k K e ∈ keys43 k K := by
  classical
  rcases e with j | ⟨jl, i, q⟩
  · exact scalarKey_mem k K j
  · exact levelKey_mem k K jl i q.val (Finset.mem_filter.mp q.property).2

private lemma enumKey_injective (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : Function.Injective (enumKey43 k K) := by
  intro u v h
  have hj := congrArg (fun κ : KeyF n d k => κ.1.val) h
  have hl := congrArg (fun κ : KeyF n d k => κ.2.1.val) h
  have hi := congrArg (fun κ : KeyF n d k => κ.2.2.1.val) h
  have hq := congrArg (fun κ : KeyF n d k => κ.2.2.2.2.val) h
  rcases u with j | ⟨jl, i, q⟩ <;> rcases v with j' | ⟨jl', i', q'⟩
  · exact congrArg Sum.inl (Subtype.ext hj)
  · have hlev := (Finset.mem_filter.mp jl'.property).2
    have he := (Finset.mem_filter.mp j.property).2
    obtain ⟨r, hr⟩ := he
    dsimp [enumKey43, scalarKey43, levelKey43] at hj hl
    omega
  · have hlev := (Finset.mem_filter.mp jl.property).2
    have he := (Finset.mem_filter.mp j'.property).2
    obtain ⟨r, hr⟩ := he
    dsimp [enumKey43, scalarKey43, levelKey43] at hj hl
    omega
  · dsimp [enumKey43, levelKey43] at hj hl hi hq
    have hjl : jl = jl' := Subtype.ext (Prod.ext hj hl)
    subst jl'
    have hii : i = i' := Fin.ext hi
    subst i'
    have hqq : q = q' := Subtype.ext (Subtype.ext hq)
    subst q'
    rfl

private lemma enumKey_surjective (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (κ : KeyF n d k) (hκ : κ ∈ keys43 k K) : ∃ e, enumKey43 k K e = κ := by
  classical
  rcases (Finset.mem_filter.mp hκ).2 with h | h
  · rcases h with ⟨he, hj, hl, hi, ha⟩
    let j : ↥((Finset.Icc 1 k).filter (fun j => Even j)) :=
      ⟨κ.1.val, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj, by have := κ.1.isLt; omega⟩, he⟩⟩
    refine ⟨Sum.inl j, ?_⟩
    apply keyF_ext
    · rfl
    · exact hl.symm
    · exact hi.symm
    · change 0 = κ.2.2.2.2.val
      exact (Multiset.card_eq_zero.mp (κ.2.2.2.2.property.trans ha)).symm
  · rcases h with ⟨hjl, hii, ha, hq⟩
    let jl : ↥(levels k) := ⟨(κ.1.val, κ.2.1.val), hjl⟩
    let i : Fin ((jl.val.1 - 2 * jl.val.2) / 2 + 1) := ⟨κ.2.2.1.val, by dsimp [jl]; omega⟩
    let q : Sym (Mono n d) (jl.val.1 - 2 * jl.val.2 - 2 * i.val) :=
      ⟨κ.2.2.2.2.val, κ.2.2.2.2.property.trans ha⟩
    let q' : ↥(subOrbits43 (jl.val.1 - 2 * jl.val.2) i.val (K jl.val.1 jl.val.2)) :=
      ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
    refine ⟨Sum.inr ⟨jl, i, q'⟩, ?_⟩
    exact keyF_ext rfl rfl rfl rfl

private lemma sum_keys43 (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (F : KeyF n d k → ℝ) :
    ∑ κ ∈ keys43 k K, F κ = ∑ e : KeyEnum43 k K, F (enumKey43 k K e) := by
  classical
  symm
  apply Finset.sum_bij (fun e _ => enumKey43 k K e)
  · intro e _; exact enumKey_mem k K e
  · intro e _ e' _ he; exact enumKey_injective k K he
  · intro κ hκ; obtain ⟨e, he⟩ := enumKey_surjective k K κ hκ
    exact ⟨e, Finset.mem_univ _, he⟩
  · intro e _; rfl

private noncomputable def keyProg43 (k : ℕ) (κ : KeyF n d k) :
    Prog (In43 n d k ⊕ TrTag n) Unit :=
  (contractProg (κ.1.1 - 2 * (κ.2.1.1 + κ.2.2.1.1))
    (fun w => (trArg (k := k) κ.1.1 (κ.2.1.1 + κ.2.2.1.1) w).rename
      (Sum.map Sum.inl id))
    (fun t c => Arg.inp (Sum.inl (Sum.inl (Sum.inl
      ⟨(wordOf _ κ.2.2.2.2.1 t).1, ((wordOf _ κ.2.2.2.2.1 t).2, c)⟩))))).bind
    (Prog.op1 Op.mul (Arg.inp (Sum.inr ()))
      (Arg.inp (Sum.inl (Sum.inl (Sum.inr κ)))))

private noncomputable def branchProg43 (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : Prog (In43 n d k) Unit := by
  classical
  exact ((trProg n d k).mapIn Sum.inl).bind
    ((Prog.par (keyProg43 k) (keys43 k K).toList).bind
      (Prog.sumArgs (Arg.inp (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl ()))))) ::
        (keys43 k K).toList.map fun κ => Arg.inp (Sum.inr κ))))

private lemma key_bounds {k : ℕ} (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (κ : KeyF n d k) (hκ : κ ∈ keys43 k K) :
    1 ≤ κ.1.1 ∧ 2 * (κ.2.1.1 + κ.2.2.1.1) ≤ κ.1.1 := by
  classical
  have h : IsKey k K κ := (Finset.mem_filter.mp hκ).2
  rcases h with h | h
  · rcases h with ⟨he, hj, hl, hi, ha⟩
    obtain ⟨r, hr⟩ := he
    omega
  · have hj := (Finset.mem_Icc.mp (Finset.mem_product.mp
      (Finset.mem_filter.mp h.1).1).1).1
    have hl := (Finset.mem_filter.mp h.1).2
    omega

private lemma keyProg43_eval {k : ℕ} (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (κ : KeyF n d k) (hκ : κ ∈ keys43 k K) (v : In43 n d k → ℝ) :
    (keyProg43 k κ).eval
      (Sum.elim v (((trProg n d k).mapIn Sum.inl).eval v)) () =
      termK (Tv (v ∘ Sum.inl)) (Mv (v ∘ Sum.inl)) κ * v (Sum.inr κ) := by
  rw [keyProg43, eval_bind, eval_op1]
  simp only [Op.eval, Arg.eval, Sum.elim_inl, Sum.elim_inr]
  rw [contractProg_eval]
  have hb := key_bounds K κ hκ
  have hA : (fun w => ((trArg (k := k) κ.1.1 (κ.2.1.1 + κ.2.2.1.1) w).rename
        (Sum.map Sum.inl id)).eval
        (Sum.elim v (((trProg n d k).mapIn Sum.inl).eval v)) []) =
      trL (κ.2.1.1 + κ.2.2.1.1) (Tv (v ∘ Sum.inl) κ.1.1) := by
    funext w
    rw [Arg.eval_rename]
    have he : (Sum.elim v (((trProg n d k).mapIn Sum.inl).eval v)) ∘
        Sum.map Sum.inl id = Sum.elim (v ∘ Sum.inl) ((trProg n d k).eval (v ∘ Sum.inl)) := by
      funext x
      cases x <;> simp [eval_mapIn, Function.comp_def]
    rw [he]
    exact trArg_eval _ _ hb.1 (by have := κ.1.isLt; omega) hb.2 _ _
  rw [hA]
  rfl

private lemma branchProg43_spec (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : GSpec43 (branchProg43 k K) K := by
  classical
  intro v
  rw [branchProg43, eval_bind, eval_bind, eval_sumArgs]
  simp only [List.map_cons, List.sum_cons, Arg.eval, Sum.elim_inl, Sum.elim_inr,
    List.map_map, Function.comp_def, gTCW, f0v]
  congr 1
  rw [← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro κ hκ
  rw [eval_par_mem _ _ _ _ hκ, keyProg43_eval K κ (Finset.mem_toList.mp hκ) v]
  exact mul_comm _ _

private lemma keyProg43_clean (k : ℕ) (κ : KeyF n d k) : Clean (keyProg43 k κ) := by
  apply clean_bind
  · apply contract_clean
    · intro w
      rw [heavy_rename]
      unfold trArg
      split_ifs <;> rfl
    · intro t c; rfl
  · exact ⟨by simp [Prog.op1, argHeavy], fun _ => rfl⟩

private lemma branchProg43_clean (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : heavyCount (branchProg43 k K) = 0 := by
  classical
  apply clean_heavyCount
  apply clean_bind
  · apply clean_mapIn
    apply clean_par
    intro x
    apply clean_sumArgs
    intro a ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · apply clean_bind
    · exact clean_par _ (keyProg43_clean k) _
    · apply clean_sumArgs
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · obtain ⟨κ, _, rfl⟩ := List.mem_map.mp ha
        rfl

private lemma keyProg43_cost (hn : 2 ≤ n) (k : ℕ) (κ : KeyF n d k) :
    ((keyProg43 k κ).cost : ℝ) = Corb n (κ.1.1 - 2 * (κ.2.1.1 + κ.2.2.1.1)) + 1 := by
  rw [keyProg43, cost_bind, Nat.cast_add, cost_op1, Nat.cast_one]
  apply congrArg (· + 1)
  apply (contractProg_cost hn _ _ _ _ _).1
  · intro w
    rw [heavy_rename]
    unfold trArg
    split_ifs <;> rfl
  · intro t c; rfl

private lemma branchProg43_cost_keys (hn : 2 ≤ n) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) :
    ((branchProg43 k K).cost : ℝ) =
      ((trProg n d k).cost : ℝ) +
        ∑ κ ∈ keys43 k K, (Corb n (κ.1.1 - 2 * (κ.2.1.1 + κ.2.2.1.1)) + 2) := by
  classical
  rw [branchProg43, cost_bind, cost_bind, cost_mapIn, cost_par, cost_sumArgs]
  simp only [List.length_cons, List.length_map, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_list_sum, List.map_map, Function.comp_def]
  simp_rw [keyProg43_cost hn]
  rw [Finset.sum_map_toList]
  simp only [Finset.length_toList]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

private lemma branchProg43_cost (hn : 2 ≤ n) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    ((branchProg43 k K).cost : ℝ) ≤ gCost43 n k K := by
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
  rw [branchProg43_cost_keys hn, trProg_cost hn, sum_keys43,
    Fintype.sum_sum_type, Fintype.sum_sigma]
  have hs : (∑ j : ↥((Finset.Icc 1 k).filter (fun j => Even j)),
      (Corb n (j.val - 2 * (j.val / 2)) + 2)) ≤
      k * ((n : ℝ) + 3) := by
    have he : ∀ j : ↥((Finset.Icc 1 k).filter (fun j => Even j)),
        j.val - 2 * (j.val / 2) = 0 := by
      intro j
      obtain ⟨r, hr⟩ := (Finset.mem_filter.mp j.property).2
      omega
    simp only [he, Corb, ite_true]
    simp only [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 k).filter (fun j => Even j)).card ≤ k := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hcardR : (((Finset.Icc 1 k).filter (fun j => Even j)).card : ℝ) ≤ k := by
      exact_mod_cast hcard
    nlinarith [show (0 : ℝ) ≤ k by positivity]
  have hl : (∑ jl : ↥(levels k), ∑ e :
      (Σ i : Fin ((jl.val.1 - 2 * jl.val.2) / 2 + 1),
        ↥(subOrbits43 (jl.val.1 - 2 * jl.val.2) i.val (K jl.val.1 jl.val.2))),
      (Corb n ((enumKey43 k K (Sum.inr ⟨jl, e⟩)).1.1 -
        2 * ((enumKey43 k K (Sum.inr ⟨jl, e⟩)).2.1.1 +
          (enumKey43 k K (Sum.inr ⟨jl, e⟩)).2.2.1.1)) + 2)) ≤
      ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ((K jl.1 jl.2).card : ℝ) := by
    rw [← Finset.sum_coe_sort (levels k)]
    apply Finset.sum_le_sum
    intro jl _
    rw [Fintype.sum_sigma]
    simp only [enumKey43, levelKey43, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul]
    let s := jl.val.1 - 2 * jl.val.2
    have he (i : ℕ) : jl.val.1 - 2 * (jl.val.2 + i) = s - 2 * i := by dsimp [s]; omega
    simp only [he]
    calc
      _ ≤ ∑ i : Fin (s / 2 + 1),
          (s.choose (2 * i.val) : ℝ) * ((K jl.val.1 jl.val.2).card : ℝ) *
            (Corb n (s - 2 * i.val) + 2 * n + 8) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : 2 * i.val ≤ s := by have := i.isLt; omega
        have hb := suborbit_card s i.val hi (K jl.val.1 jl.val.2) (hK jl.val jl.property)
        have hbR : ((subOrbits43 s i.val (K jl.val.1 jl.val.2)).card : ℝ) ≤
            (s.choose (2 * i.val) : ℝ) * ((K jl.val.1 jl.val.2).card : ℝ) := by
          exact_mod_cast hb
        apply mul_le_mul hbR (by linarith) (by linarith [hc (s - 2 * i.val)])
        exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ cS n s * ((K jl.val.1 jl.val.2).card : ℝ) := by
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
          (s.choose (2 * i) : ℝ) * ((K jl.val.1 jl.val.2).card : ℝ) *
            (Corb n (s - 2 * i) + 2 * n + 8))]
        have heq : (∑ i ∈ Finset.range (s / 2 + 1),
            (s.choose (2 * i) : ℝ) * ((K jl.val.1 jl.val.2).card : ℝ) *
              (Corb n (s - 2 * i) + 2 * n + 8)) =
            (∑ i ∈ Finset.range (s / 2 + 1),
              (s.choose (2 * i) : ℝ) * (Corb n (s - 2 * i) + 2 * n + 8)) *
                ((K jl.val.1 jl.val.2).card : ℝ) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [heq, cS, add_mul]
        have hnon : 0 ≤ (n : ℝ) * ((K jl.val.1 jl.val.2).card : ℝ) := by positivity
        linarith
  change _ ≤ _
  unfold gCost43
  dsimp only [enumKey43, scalarKey43] at *
  simp only [Nat.add_zero] at *
  linarith only [hs, hl]

/-- **The per-case program**: constants `0`, `1` only; it computes `gTCW` of its weight inputs. -/
theorem gProg43_exists (hn : 2 ≤ n) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    ∃ pg : Prog (In43 n d k) Unit, heavyCount pg = 0 ∧ GSpec43 pg K ∧ (pg.cost : ℝ) ≤ gCost43 n k K := by
  exact ⟨branchProg43 k K, branchProg43_clean k K, branchProg43_spec k K,
    branchProg43_cost hn k K hK⟩

/-- **The grouping identity**: with the weights of `μ`, `gTCW = gTCR μ`. -/
theorem gTCW_eq (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (M : CoefIdxD n d → ℝ) :
    gTCW k K f0 T M (wKeyR μ K) = gTCR μ k K f0 T M := by
  classical
  have _hn := hn
  have _hK := hK
  unfold gTCW gTCR
  rw [sum_keys43, Fintype.sum_sum_type, Fintype.sum_sigma]
  rw [← add_assoc]
  apply congrArg₂ (· + ·)
  · apply congrArg (fun z => f0 + z)
    rw [← Finset.sum_coe_sort ((Finset.Icc 1 k).filter (fun j => Even j))]
    apply Finset.sum_congr rfl
    intro j _
    have he := (Finset.mem_filter.mp j.property).2
    have hz : j.val - 2 * (j.val / 2) = 0 := by obtain ⟨r, hr⟩ := he; omega
    have hv : (fun t : Fin (j.val - 2 * (j.val / 2 + 0)) =>
        colM M (wordOf _ (0 : Multiset (Mono n d)) t)) = (fun _ _ => (0 : ℝ)) := by
      funext t
      have := t.isLt
      dsimp at this
      omega
    change wKeyR μ K (scalarKey43 k j) * termK T M (scalarKey43 k j) = _
    simp only [wKeyR, scalarKey43, termK, Nat.add_zero]
    rw [ite_eq_left (by omega)]
    rw [show (fun t : Fin (j.val - 2 * (j.val / 2)) =>
        colM M (wordOf _ (0 : Multiset (Mono n d)) t)) = (fun _ _ => (0 : ℝ)) by
      simpa only [Nat.add_zero] using hv]
  · rw [← Finset.sum_coe_sort (levels k)]
    apply Finset.sum_congr rfl
    intro jl _
    rw [Fintype.sum_sigma]
    have hlt := (Finset.mem_filter.mp jl.property).2
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val ∈ Finset.range ((jl.val.1 - 2 * jl.val.2) / 2 + 1) :=
      Finset.mem_range.mpr i.isLt
    rw [grouped_trace μ k K T hT M jl.val jl.property i.val hi]
    rw [Finset.mul_sum, Finset.mul_sum]
    erw [← Finset.sum_coe_sort (subOrbits43 (jl.val.1 - 2 * jl.val.2) i.val (K jl.val.1 jl.val.2))]
    apply Finset.sum_congr rfl
    intro q _
    change wKeyR μ K (levelKey43 k jl i q.val) * termK T M (levelKey43 k jl i q.val) = _
    simp only [wKeyR, levelKey43, termK]
    rw [ite_eq_right (by omega)]
    have ha : jl.val.1 - 2 * (jl.val.2 + i.val) = jl.val.1 - 2 * jl.val.2 - 2 * i.val := by omega
    have hw : (fun t : Fin (jl.val.1 - 2 * (jl.val.2 + i.val)) =>
        colM M (wordOf _ q.val.val t)) =
      (fun t => colM M (wordOf _ q.val.val ⟨t.val, by have := t.isLt; omega⟩)) := by
      rfl
    rw [hw]
    ring

end BstLean.Part43

