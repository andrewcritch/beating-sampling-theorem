import BstLean.Part53Defs
import BstLean.Part41Consts
import BstLean.Part41Tensor

/-!
Support for the Part 53 program construction. The program existence result in this file has no
cost bound. The cost bound in `prog53_exists` needs a construction with shared multiset slots.
-/

namespace BstLean.Part53.CostAux

open BstLean.Cost
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (In41 Mv Tv f0v Tens colM contr trL heavyCount)

noncomputable section

private def HasProg {ι : Type} (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ p : Prog ι Unit, ∀ v, p.eval v () = f v

private lemma has_const {ι : Type} (q : ℚ) : HasProg (fun _ : ι → ℝ => (q : ℝ)) :=
  ⟨Prog.ofArgs (fun _ => .cst q), fun _ => rfl⟩

private lemma has_input {ι : Type} (i : ι) : HasProg (fun v : ι → ℝ => v i) :=
  ⟨Prog.ofArgs (fun _ => .inp i), fun _ => rfl⟩

private lemma has_op {ι : Type} (op : Op) {f g : (ι → ℝ) → ℝ}
    (hf : HasProg f) (hg : HasProg g) : HasProg (fun v => op.eval (f v) (g v)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨(p.pair q).bind (Prog.op1 op (.inp (.inr (.inl ())))
    (.inp (.inr (.inr ())))), ?_⟩
  intro v
  simp only [eval_bind, eval_op1, Arg.eval, Sum.elim_inr, eval_pair_inl,
    eval_pair_inr, hp, hq]

private lemma has_add {ι : Type} {f g : (ι → ℝ) → ℝ}
    (hf : HasProg f) (hg : HasProg g) : HasProg (fun v => f v + g v) := has_op .add hf hg

private lemma has_mul {ι : Type} {f g : (ι → ℝ) → ℝ}
    (hf : HasProg f) (hg : HasProg g) : HasProg (fun v => f v * g v) := has_op .mul hf hg

private lemma has_sum {ι α : Type} (s : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ a ∈ s, HasProg (f a)) : HasProg (fun v => ∑ a ∈ s, f a v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (has_const (ι := ι) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      has_add (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

private lemma has_prod {ι α : Type} (s : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ a ∈ s, HasProg (f a)) : HasProg (fun v => ∏ a ∈ s, f a v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (has_const (ι := ι) 1)
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      has_mul (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Inputs of a program that can read only the constant column of `M`. -/
abbrev SmallIn (n k : ℕ) := Fin n ⊕ Unit ⊕ (Σ j : Fin (k + 1), Fin j → Fin n)

def embed (n d k : ℕ) : SmallIn n k → In41 n d k :=
  Sum.elim (fun a => Sum.inl ⟨0, ((default : BstLean.Part41.Mono n d).2, a)⟩)
    (fun f => Sum.inr f)

def smallTF {n k : ℕ} (v : SmallIn n k → ℝ) : Tens n := fun j w =>
  if j = 0 then v (.inr (.inl ()))
  else if h : j < k + 1 then v (.inr (.inr ⟨⟨j, h⟩, w⟩)) else 0

def aq (n d : ℕ) : ℚ :=
  ((∑ j ∈ Finset.range (d + 1), 1 / (j.factorial : ℚ)) - 1) /
    (Fintype.card (CoefIdxD n d) : ℚ)

theorem aq_cast (n d : ℕ) : (aq n d : ℝ) = aH n d := by
  simp only [aq, aH, c0, DD]
  push_cast
  rfl

private lemma smallTF_has {n k : ℕ} (j : ℕ) (w : Fin j → Fin n) :
    HasProg (fun v : SmallIn n k → ℝ => smallTF v j w) := by
  unfold smallTF
  split_ifs with h0 hj
  · exact has_input _
  · exact has_input _
  · simpa using (has_const (ι := SmallIn n k) 0)

private lemma heat_has (n d k c : ℕ) (w : Fin c → Fin n) :
    HasProg (fun v : SmallIn n k → ℝ => heatA k (aH n d) (smallTF v) c w) := by
  classical
  unfold heatA
  apply has_sum
  intro i hi
  apply has_mul
  · have hc := has_const (ι := SmallIn n k)
      (((aq n d / 2) ^ i / (i.factorial : ℚ)) *
        ((c + 2 * i).factorial : ℚ) / (c.factorial : ℚ))
    convert hc using 1
    ext v
    push_cast
    rw [aq_cast]
    ring
  · unfold trL
    apply has_sum
    intro z hz
    exact smallTF_has _ _

private lemma raw_exists (n d k : ℕ) : HasProg (fun v : SmallIn n k → ℝ =>
    fvA k (heatA k (aH n d) (smallTF v)) (fun a => v (.inl a))) := by
  classical
  unfold fvA
  apply has_sum
  intro c hc
  unfold contr
  apply has_sum
  intro w hw
  apply has_mul (heat_has n d k c w)
  apply has_prod
  intro t ht
  exact has_input _

private lemma height_bound (l : List ℚ) :
    ∃ β : ℕ, ∀ q ∈ l, q.num.natAbs < 2 ^ β ∧ q.den < 2 ^ β := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
    obtain ⟨β, hβ⟩ := ih
    let γ := max β (max q.num.natAbs q.den + 1)
    have hb : 2 ^ β ≤ 2 ^ γ := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hn : q.num.natAbs < 2 ^ γ := by
      have h : γ < 2 ^ γ := Nat.lt_two_pow_self
      have hγ := le_max_right β (max q.num.natAbs q.den + 1)
      have hq := le_max_left q.num.natAbs q.den
      omega
    have hd : q.den < 2 ^ γ := by
      have h : γ < 2 ^ γ := Nat.lt_two_pow_self
      have hγ := le_max_right β (max q.num.natAbs q.den + 1)
      have hq := le_max_right q.num.natAbs q.den
      omega
    refine ⟨γ, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hn, hd⟩
    · exact ⟨lt_of_lt_of_le (hβ r hr).1 hb, lt_of_lt_of_le (hβ r hr).2 hb⟩

theorem heavy_mapIn {ι ι' κ : Type} [Fintype κ] (p : Prog ι κ) (f : ι → ι') :
    heavyCount (p.mapIn f) = heavyCount p := by
  have ha (a : Arg ι) : BstLean.Part41.argHeavy (a.rename f) =
      BstLean.Part41.argHeavy a := by cases a <;> rfl
  simp only [heavyCount, Prog.mapIn, List.map_map, Function.comp_def, Instr.rename, ha]

theorem mapIn_constCol (n d k : ℕ) (p : Prog (SmallIn n k) Unit) :
    ConstColOnly (p.mapIn (embed n d k)) := by
  have he (i : SmallIn n k) (α : CoefIdxD n d)
      (h : embed n d k i = Sum.inl α) : α.1 = 0 := by
    cases i with
    | inl a => cases h; rfl
    | inr f => cases h
  have ha (a : Arg (SmallIn n k)) (α : CoefIdxD n d)
      (h : a.rename (embed n d k) = .inp (.inl α)) : α.1 = 0 := by
    cases a with
    | inp i => exact he i α (Arg.inp.inj h)
    | reg r => cases h
    | cst q => cases h
  intro α hα
  rcases hα with ⟨I, hI, h⟩ | ⟨o, h⟩
  · obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    rcases h with h | h
    · exact ha J.a α h
    · exact ha J.b α h
  · exact ha (p.out o) α h

theorem smallTF_embed (n d k : ℕ) (v : In41 n d k → ℝ) :
    smallTF (v ∘ embed n d k) = TF k (f0v v) (Tv v) := by
  funext j w
  by_cases hj0 : j = 0
  · simp [smallTF, TF, hj0, embed, f0v]
  · by_cases hj : j ≤ k
    · have hj' : j < k + 1 := by omega
      simp [smallTF, TF, hj0, hj, hj', Tv, embed]
    · have hj' : ¬ j < k + 1 := by omega
      simp [smallTF, TF, hj0, hj, hj']

/-- An exact program from `0` and `1` exists and reads only the constant column.
This statement does not establish the cost required by `prog53_exists`. -/
theorem uncosted_exists (n d k : ℕ) :
    ∃ p : Prog (In41 n d k) Unit, heavyCount p = 0 ∧ ConstColOnly p ∧
      ∀ v : In41 n d k → ℝ, p.eval v () = g0 n d k (f0v v) (Tv v) (Mv v) := by
  obtain ⟨p, hp⟩ := raw_exists n d k
  obtain ⟨β, hβ⟩ := height_bound (BstLean.Part41.heavyConsts p)
  obtain ⟨p', h0, heval, hcost⟩ := BstLean.Part41.inline_consts p β hβ
  refine ⟨p'.mapIn (embed n d k), ?_, mapIn_constCol n d k p', ?_⟩
  · rw [heavy_mapIn]; exact h0
  · intro v
    rw [eval_mapIn, heval, hp]
    dsimp only
    rw [smallTF_embed]
    rfl

/-- The full family retains tensor symmetry, including its constant term. -/
theorem TF_symm {n k : ℕ} (f0 : ℝ) (T : Tens n)
    (hT : BstLean.Part41.TSymm k T) : ∀ j, BstLean.Part41.IsSymmT (TF k f0 T j) := by
  intro j σ w
  unfold TF
  split_ifs with hj0 hj
  · rfl
  · exact hT j (by omega) hj σ w
  · rfl

/-- The heat family retains tensor symmetry. -/
theorem heatA_symm {n k : ℕ} (v : ℝ) (A : Tens n)
    (hA : ∀ j, BstLean.Part41.IsSymmT (A j)) :
    ∀ c, BstLean.Part41.IsSymmT (heatA k v A c) := by
  classical
  intro c σ w
  unfold heatA
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hdim : c + 2 * i - 2 * i = c := by omega
  let e : Fin (c + 2 * i - 2 * i) ≃ Fin c := finCongr hdim
  let τ := e.trans (σ.trans e.symm)
  have he : (fun t : Fin (c + 2 * i - 2 * i) => (w ∘ σ) ⟨t.1, by omega⟩) =
      (fun t : Fin (c + 2 * i - 2 * i) => w ⟨t.1, by omega⟩) ∘ τ := by
    funext t
    rfl
  rw [he]
  exact BstLean.Part41.trL_symm i (by omega) _ (hA _) τ _

private lemma orbit_perm {α : Type} [Fintype α] {c : ℕ} (u w : Fin c → α)
    (h : BstLean.Part41.mset u = BstLean.Part41.mset w) :
    ∃ σ : Equiv.Perm (Fin c), w ∘ σ = u := by
  classical
  have hcard (a : α) : Fintype.card {t : Fin c // u t = a} =
      Fintype.card {t : Fin c // w t = a} := by
    have hh := congrArg (Multiset.count a) h
    simpa only [BstLean.Part41.mset, Multiset.count_map, Multiset.countP_eq_card_filter,
      ← Finset.filter_val, Fintype.card_subtype, Finset.card_def, eq_comm] using hh
  let e (a : α) := Fintype.equivOfCardEq (hcard a)
  let σ := (Equiv.sigmaFiberEquiv u).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv w))
  refine ⟨σ, ?_⟩
  funext t
  exact (e (u t) ⟨t, rfl⟩).property

theorem mset_wordOf {α : Type} [Inhabited α] (c : ℕ) (q : Multiset α)
    (hq : q.card = c) : BstLean.Part41.mset (BstLean.Part41.wordOf c q) = q := by
  subst c
  unfold BstLean.Part41.mset BstLean.Part41.wordOf
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun t : Fin q.card => q.toList.getD t.val default) = q.toList := by
    have hh : q.toList.length = q.card := Multiset.length_toList q
    rw [← hh]
    simpa only [List.getD_eq_get, Fin.eta] using List.ofFn_get q.toList
  rw [he, Multiset.coe_toList]

theorem symm_mset {α : Type} [Fintype α] {c : ℕ}
    (A : (Fin c → α) → ℝ) (hA : BstLean.Part41.IsSymmT A)
    (u w : Fin c → α) (h : BstLean.Part41.mset u = BstLean.Part41.mset w) : A u = A w := by
  obtain ⟨σ, hσ⟩ := orbit_perm u w h
  rw [← hσ]
  exact hA σ w

/-- Number of ordered words in a multiset orbit. -/
def orbitCount {α : Type} [Fintype α] [DecidableEq α] {c : ℕ} (q : Sym α c) : ℕ :=
  ((Finset.univ : Finset (Fin c → α)).filter
    (fun w => BstLean.Part41.mset w = q.val)).card

private lemma sum_by_orbit {α : Type} [Fintype α] [DecidableEq α] [Inhabited α]
    (c : ℕ) (F : (Fin c → α) → ℝ)
    (hF : ∀ u w, BstLean.Part41.mset u = BstLean.Part41.mset w → F u = F w) :
    ∑ w, F w = ∑ q : Sym α c,
      (orbitCount q : ℝ) * F (BstLean.Part41.wordOf c q.val) := by
  let f : (Fin c → α) → Sym α c := fun w => ⟨BstLean.Part41.mset w,
    by simp [BstLean.Part41.mset]⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (f := F) (by simp)]
  apply Finset.sum_congr rfl
  intro q _
  have he : (Finset.univ.filter fun w => f w = q) =
      Finset.univ.filter (fun w => BstLean.Part41.mset w = q.val) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [he]
  calc
    _ = ∑ w ∈ Finset.univ.filter (fun w => BstLean.Part41.mset w = q.val),
        F (BstLean.Part41.wordOf c q.val) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply hF
      rw [(Finset.mem_filter.mp hw).2, mset_wordOf _ _ q.property]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

/-- Evaluation of a symmetric tensor reduces to a sum over multiset orbits. -/
theorem contr_orbit {n c : ℕ} [Inhabited (Fin n)] (A : (Fin c → Fin n) → ℝ)
    (hA : BstLean.Part41.IsSymmT A) (y : Fin n → ℝ) :
    contr A (fun _ => y) = ∑ q : Sym (Fin n) c, (orbitCount q : ℝ) *
      (A (BstLean.Part41.wordOf c q.val) *
        ∏ t, y (BstLean.Part41.wordOf c q.val t)) := by
  classical
  apply sum_by_orbit
  intro u w huw
  obtain ⟨σ, hσ⟩ := orbit_perm u w huw
  rw [← hσ, hA σ w]
  congr 1
  exact Equiv.prod_comp σ (fun t => y (w t))

/-- Multiset expansion of the program value. -/
theorem g0_orbit {n d k : ℕ} [Inhabited (Fin n)] (f0 : ℝ) (T : Tens n)
    (hT : BstLean.Part41.TSymm k T) (M : CoefIdxD n d → ℝ) :
    g0 n d k f0 T M = ∑ c ∈ Finset.range (k + 1),
      ∑ q : Sym (Fin n) c, (orbitCount q : ℝ) *
        (heatA k (aH n d) (TF k f0 T) c (BstLean.Part41.wordOf c q.val) *
          ∏ t, colM M default (BstLean.Part41.wordOf c q.val t)) := by
  classical
  unfold g0 fvA
  apply Finset.sum_congr rfl
  intro c hc
  exact contr_orbit _ (heatA_symm _ _ (TF_symm f0 T hT) c) _

/-- Add the pair of equal indices for the next trace. -/
def traceExtend {n j i : ℕ} (h : 2 * (i + 1) ≤ j) (a : Fin n)
    (w : Fin (j - 2 * (i + 1)) → Fin n) : Fin (j - 2 * i) → Fin n := fun t =>
  if ht : t.val < 2 then a else w ⟨t.val - 2, by have := t.isLt; omega⟩

/-- An iterated trace is obtained from the preceding trace with `n` summands.
The statement does not require tensor symmetry. -/
theorem trace_succ {n j i : ℕ} (A : (Fin j → Fin n) → ℝ)
    (h : 2 * (i + 1) ≤ j) (w : Fin (j - 2 * (i + 1)) → Fin n) :
    trL (i + 1) A w = ∑ a : Fin n, trL i A (traceExtend h a w) := by
  classical
  unfold trL
  rw [← (Fin.snocEquiv (fun _ : Fin (i + 1) => Fin n)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  funext t
  simp only [BstLean.Part41.glue, Fin.snocEquiv_apply]
  by_cases h1 : t.val < 2 * i
  · have h2 : t.val < 2 * (i + 1) := by omega
    rw [dite_eq_left h2, dite_eq_left h1]
    have ht : t.val / 2 < i := by omega
    simp [Fin.snoc, ht]
  · by_cases h2 : t.val < 2 * (i + 1)
    · rw [dite_eq_left h2, dite_eq_right h1]
      have ht : ¬t.val / 2 < i := by omega
      simp only [Fin.snoc, ht, dite_false, cast_eq, traceExtend]
      rw [dite_eq_left (by simp; omega)]
    · rw [dite_eq_right h2, dite_eq_right h1]
      simp only [traceExtend]
      rw [dite_eq_right (by simp; omega)]
      congr 1

/-- The number of monomials of degree at most `k`. -/
theorem card_monomials (n k : ℕ) :
    Fintype.card (BstLean.Part41.Mono n k) = (n + k).choose k := by
  simp only [BstLean.Part41.Mono, Fintype.card_sigma,
    Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
    ← Nat.choose_symm_add (a := k) (b := n)]
  simp [Nat.add_comm]

/-- The orders that can occur in nonzero-depth trace slots have the required binomial bound. -/
theorem trace_orders_count (n k : ℕ) (hk : 2 ≤ k) :
    (∑ c ∈ Finset.range (k - 1), Fintype.card (Sym (Fin n) c)) ≤
      (n + k - 1).choose (k - 2) := by
  simp only [Sym.card_sym_eq_multichoose, Fintype.card_fin]
  have he : k - 1 = (k - 2) + 1 := by omega
  rw [he, Nat.sum_range_multichoose]
  rw [← Nat.choose_symm_add (a := k - 2) (b := n)]
  apply Nat.choose_le_choose
  omega

end
end BstLean.Part53.CostAux
