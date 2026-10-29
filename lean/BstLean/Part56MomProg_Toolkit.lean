import BstLean.Part56MomProg_Scalar
import BstLean.Part41Consts

/-! Program combinators adapted from Parts 50 and 43. -/
namespace BstLean.Part56.MomProg
open BstLean.Cost
open BstLean.Part41 (heavyCount)

def Clean {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, BstLean.Part41.argHeavy I.a = 0 ∧ BstLean.Part41.argHeavy I.b = 0) ∧
    ∀ o, BstLean.Part41.argHeavy (p.out o) = 0

lemma heavy_rename {ι κ : Type} (f : ι → κ) (a : Arg ι) :
    BstLean.Part41.argHeavy (a.rename f) = BstLean.Part41.argHeavy a := by
  cases a <;> rfl

lemma heavy_clamp {ι : Type} (s : ℕ) (a : Arg ι)
    (h : BstLean.Part41.argHeavy a = 0) : BstLean.Part41.argHeavy (a.clamp s) = 0 := by
  cases a <;> simp_all [Arg.clamp, BstLean.Part41.argHeavy]
  split_ifs <;> rfl

lemma heavy_subst {ι κ : Type} (f : ι → Arg κ) (s l : ℕ)
    (hf : ∀ i, BstLean.Part41.argHeavy (f i) = 0) (a : Arg ι)
    (h : BstLean.Part41.argHeavy a = 0) :
    BstLean.Part41.argHeavy (a.subst f s l) = 0 := by
  cases a <;> simp_all [Arg.subst, BstLean.Part41.argHeavy]
  split_ifs <;> rfl

lemma clean_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
    (hp : Clean p) (hq : Clean q) : Clean (p.bind q) := by
  have hf : ∀ i, BstLean.Part41.argHeavy (Sum.elim Arg.inp
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
  | nil => simp [Clean, Prog.par, Prog.ofArgs, BstLean.Part41.argHeavy]
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
  have hb : (p.body.map fun I => BstLean.Part41.argHeavy I.a +
      BstLean.Part41.argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

lemma clean_sumArgs {ι : Type} (l : List (Arg ι))
    (hl : ∀ a ∈ l, BstLean.Part41.argHeavy a = 0) : Clean (Prog.sumArgs l) := by
  induction l with
  | nil => simp [Clean, Prog.sumArgs, Prog.ofArgs, BstLean.Part41.argHeavy]
  | cons a l ih =>
    cases l with
    | nil => exact ⟨by simp [Prog.sumArgs, Prog.ofArgs], fun _ => hl a (by simp)⟩
    | cons b l =>
      apply clean_bind (ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)))
      have ha := (heavy_rename (Sum.inl : ι → ι ⊕ Unit) a).trans (hl a (by simp))
      simpa [Clean, Prog.op1, BstLean.Part41.argHeavy] using ha

lemma clean_sumProd {ι : Type} (l : List (Arg ι × Arg ι))
    (hl : ∀ ab ∈ l, BstLean.Part41.argHeavy ab.1 = 0 ∧
      BstLean.Part41.argHeavy ab.2 = 0) : Clean (Prog.sumProd l) := by
  apply clean_bind
  · apply clean_par
    intro j
    have h := hl (l.get j) (List.get_mem _ _)
    simpa [Clean, Prog.op1, BstLean.Part41.argHeavy] using h
  · apply clean_sumArgs
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rfl

def HasProg {ι κ : Type} (f : (ι → ℝ) → κ → ℝ) (c : ℕ) : Prop :=
  ∃ p : Prog ι κ, Clean p ∧ (∀ v k, p.eval v k = f v k) ∧ p.cost ≤ c

lemma hp_args {ι κ : Type} (a : κ → Arg ι)
    (ha : ∀ k, BstLean.Part41.argHeavy (a k) = 0) :
    HasProg (fun v k => (a k).eval v []) 0 :=
  ⟨Prog.ofArgs a, ⟨by simp [Prog.ofArgs], ha⟩, fun _ _ => rfl, le_rfl⟩

lemma hp_op {ι : Type} (op : Op) (a b : Arg ι)
    (ha : BstLean.Part41.argHeavy a = 0) (hb : BstLean.Part41.argHeavy b = 0) :
    HasProg (fun v (_ : Unit) => op.eval (a.eval v []) (b.eval v [])) 1 := by
  refine ⟨Prog.op1 op a b, ?_, ?_, le_rfl⟩
  · simpa [Clean, Prog.op1, BstLean.Part41.argHeavy] using And.intro ha hb
  · intro v k; exact eval_op1 _ _ _ _ _

lemma hp_bind {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ}
    {g : ((ι ⊕ κ) → ℝ) → ν → ℝ} {a b : ℕ}
    (hf : HasProg f a) (hg : HasProg g b) :
    HasProg (fun v => g (Sum.elim v (f v))) (a + b) := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  obtain ⟨q, hq, eq, cq⟩ := hg
  refine ⟨p.bind q, clean_bind hp hq, ?_, ?_⟩
  · intro v k
    rw [eval_bind, eq]
    have he : p.eval v = f v := funext (ep v)
    rw [he]
  · rw [cost_bind]; omega

lemma hp_par {ι κ : Type} [Fintype κ] [DecidableEq κ]
    {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : ∀ k, HasProg (fun v (_ : Unit) => f v k) c) :
    HasProg f (Fintype.card κ * c) := by
  classical
  choose p hp ep cp using hf
  refine ⟨Prog.par p Finset.univ.toList, clean_par p hp _, ?_, ?_⟩
  · intro v k
    rw [eval_par_mem _ _ _ _ (by simp), ep]
  · rw [cost_par]
    calc
      _ ≤ (Finset.univ.toList.map fun _ : κ => c).sum := by
        apply List.sum_le_sum
        intro k _; exact cp k
      _ = _ := by simp

lemma hp_dot {ι κ : Type} [Fintype κ] (a b : κ → Arg ι)
    (ha : ∀ k, BstLean.Part41.argHeavy (a k) = 0) (hb : ∀ k, BstLean.Part41.argHeavy (b k) = 0) :
    HasProg (fun v (_ : Unit) => ∑ k, (a k).eval v [] * (b k).eval v [])
      (2 * Fintype.card κ - 1) := by
  classical
  let l := Finset.univ.toList.map fun k => (a k, b k)
  refine ⟨Prog.sumProd l, ?_, ?_, ?_⟩
  · apply clean_sumProd
    intro ab hab
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hab
    exact ⟨ha k, hb k⟩
  · intro v k
    simp [eval_sumProd, l, List.map_map, Function.comp_def, Finset.sum_map_toList]
  · simp [l, cost_sumProd]

lemma hp_sum {ι κ : Type} [Fintype κ] (a : κ → Arg ι)
    (ha : ∀ k, BstLean.Part41.argHeavy (a k) = 0) :
    HasProg (fun v (_ : Unit) => ∑ k, (a k).eval v []) (Fintype.card κ - 1) := by
  classical
  let l := Finset.univ.toList.map a
  refine ⟨Prog.sumArgs l, ?_, ?_, ?_⟩
  · apply clean_sumArgs
    intro b hb
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact ha k
  · intro v k
    simp [eval_sumArgs, l, List.map_map, Function.comp_def, Finset.sum_map_toList]
  · simp [l, cost_sumArgs]

lemma hp_mono {ι κ : Type} {f : (ι → ℝ) → κ → ℝ} {a b : ℕ}
    (hf : HasProg f a) (h : a ≤ b) : HasProg f b := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  exact ⟨p, hp, ep, cp.trans h⟩

lemma hp_congr {ι κ : Type} {f g : (ι → ℝ) → κ → ℝ} {a : ℕ}
    (hf : HasProg f a) (h : ∀ v k, f v k = g v k) : HasProg g a := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  exact ⟨p, hp, fun v k => (ep v k).trans (h v k), cp⟩

lemma hp_pair {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ}
    {g : (ι → ℝ) → ν → ℝ} {a b : ℕ}
    (hf : HasProg f a) (hg : HasProg g b) :
    HasProg (fun v => Sum.elim (f v) (g v)) (a + b) := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  obtain ⟨q, hq, eq, cq⟩ := hg
  refine ⟨p.pair q, ?_, ?_, ?_⟩
  · apply clean_bind hp
    constructor
    · exact (clean_mapIn Sum.inl hq).1
    · intro k
      cases k with
      | inl k => rfl
      | inr k => exact (clean_mapIn Sum.inl hq).2 k
  · intro v k; cases k <;> simp [ep, eq]
  · rw [cost_pair]; omega


lemma hp_mapOut {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : HasProg f c) (r : ν → κ) : HasProg (fun v k => f v (r k)) c := by
  obtain ⟨p, hp, he, hc⟩ := hf
  exact ⟨p.mapOut r, ⟨hp.1, fun k => hp.2 (r k)⟩, fun v k => he v (r k), hc⟩

lemma hp_mapIn {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : HasProg f c) (r : ι → ν) : HasProg (fun v k => f (v ∘ r) k) c := by
  obtain ⟨p, hp, he, hc⟩ := hf
  exact ⟨p.mapIn r, clean_mapIn r hp, fun v k => by rw [eval_mapIn, he],
    by simpa using hc⟩

lemma hp_keep {ι κ : Type} {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : HasProg f c) : HasProg (fun v => Sum.elim v (f v)) c := by
  obtain ⟨p, hp, he, hc⟩ := hf
  let q : Prog (ι ⊕ κ) (ι ⊕ κ) := Prog.ofArgs Arg.inp
  refine ⟨p.bind q, clean_bind hp ?_, ?_, ?_⟩
  · simp [q, Clean, Prog.ofArgs, BstLean.Part41.argHeavy]
  · intro v k
    rw [eval_bind]
    cases k <;> simp [q, Arg.eval, he]
  · simpa [q] using hc

lemma hp_seq {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ} {g : (κ → ℝ) → ν → ℝ} {a b : ℕ}
    (hf : HasProg f a) (hg : HasProg g b) : HasProg (fun v => g (f v)) (a + b) := by
  have h := hp_bind hf (hp_mapIn hg (Sum.inr : κ → ι ⊕ κ))
  exact hp_congr h (fun v k => by simp [Function.comp_def])

lemma hp_parS {ι κ : Type} [Fintype κ] [DecidableEq κ]
    {f : (ι → ℝ) → κ → ℝ} (c : κ → ℕ)
    (hf : ∀ k, HasProg (fun v (_ : Unit) => f v k) (c k)) :
    HasProg f (∑ k, c k) := by
  classical
  choose p hp ep cp using hf
  refine ⟨Prog.par p Finset.univ.toList, clean_par p hp _, ?_, ?_⟩
  · intro v k
    rw [eval_par_mem _ _ _ _ (by simp), ep]
  · rw [cost_par]
    calc
      _ ≤ (Finset.univ.toList.map fun k : κ => c k).sum := by
        apply List.sum_le_sum
        intro k _; exact cp k
      _ = _ := by rw [Finset.sum_map_toList]

lemma hp_parL {ι κ : Type} [DecidableEq κ] {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (l : List κ) (hf : ∀ k ∈ l, HasProg (fun v (_ : Unit) => f v k) c) :
    HasProg (fun v k => if k ∈ l then f v k else 0) (l.length * c) := by
  classical
  have hf' : ∀ k, ∃ p : Prog ι Unit, Clean p ∧ (∀ v u, p.eval v u = if k ∈ l then f v k else 0) ∧
      p.cost ≤ if k ∈ l then c else 0 := by
    intro k
    by_cases hk : k ∈ l
    · obtain ⟨p, hp, ep, cp⟩ := hf k hk
      exact ⟨p, hp, fun v u => by simp [hk, ep], by simp [hk, cp]⟩
    · refine ⟨Prog.ofArgs (fun _ => .cst 0), ⟨by simp [Prog.ofArgs], fun _ => rfl⟩, ?_, by simp⟩
      intro v u; simp [hk, Arg.eval]
  choose p hp ep cp using hf'
  refine ⟨Prog.par p l, clean_par p hp _, ?_, ?_⟩
  · intro v k
    by_cases hk : k ∈ l
    · rw [eval_par_mem _ _ _ _ hk, ep]
    · rw [eval_par_not_mem _ _ _ _ hk]; simp [hk]
  · rw [cost_par]
    calc
      _ ≤ (l.map fun _ => c).sum := by
        apply List.sum_le_sum
        intro k hk
        have := cp k
        simp only [hk, ite_true] at this
        exact this
      _ = _ := by simp

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

lemma hp_consts {ι κ : Type} [Fintype κ] (q : κ → ℚ) (β : ℕ)
    (hq : ∀ k, (q k).num.natAbs < 2 ^ β ∧ (q k).den < 2 ^ β) :
    HasProg (fun (_ : ι → ℝ) k => (q k : ℝ)) (4 * β * Fintype.card κ) := by
  classical
  let p : Prog ι κ := Prog.ofArgs (fun k => .cst (q k))
  have hb : ∀ r ∈ BstLean.Part41.heavyConsts p, r.num.natAbs < 2 ^ β ∧ r.den < 2 ^ β := by
    intro r hr
    simp only [BstLean.Part41.heavyConsts, p, Prog.ofArgs, List.flatMap_nil, List.nil_append,
      List.mem_filterMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hr
    obtain ⟨a, ⟨k, rfl⟩, ha⟩ := hr
    by_cases h : q k = 0 ∨ q k = 1
    · simp [h] at ha
    · simp only [h, ite_false, Option.some.injEq] at ha
      subst ha; exact hq k
  obtain ⟨p', hp', he, hc⟩ := BstLean.Part41.inline_consts p β hb
  refine ⟨p', clean_of_heavy hp', fun v k => by rw [he]; rfl, ?_⟩
  have hh : heavyCount p ≤ Fintype.card κ := by
    unfold heavyCount
    simp only [p, Prog.ofArgs, List.map_nil, List.sum_nil, zero_add]
    calc
      _ ≤ ∑ _k : κ, 1 := by
        apply Finset.sum_le_sum; intro k _
        simp only [BstLean.Part41.argHeavy]; split_ifs <;> omega
      _ = _ := by simp
  have : p.cost = 0 := rfl
  calc
    _ ≤ p.cost + 4 * β * heavyCount p := hc
    _ ≤ _ := by rw [this, zero_add]; exact Nat.mul_le_mul_left _ hh

/-! ## Uniform sphere moments and the surrogate moments -/
lemma hp_nat {ι : Type} (N : ℕ) : HasProg (fun (_ : ι → ℝ) (_ : Unit) => (N : ℝ)) N := by
  induction N with
  | zero =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.cst (ι := ι) 0) (fun _ => rfl))
      (fun v u => by simp [Arg.eval])
  | succ N ih =>
    have h := hp_bind ih (hp_op .add (Arg.inp (Sum.inr ())) (Arg.cst 1) rfl rfl)
    exact hp_congr h (fun v u => by simp [Arg.eval, Op.eval])

lemma hp_listprod {ι : Type} (l : List ι) :
    HasProg (fun (b : ι → ℝ) (_ : Unit) => (l.map b).prod) l.length := by
  induction l with
  | nil =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.cst (ι := ι) 1) (fun _ => rfl))
      (fun v u => by simp [Arg.eval])
  | cons a l ih =>
    have h := hp_bind ih (hp_op .mul (Arg.inp (Sum.inl a)) (Arg.inp (Sum.inr ())) rfl rfl)
    exact hp_mono (hp_congr h (fun v u => by simp [Arg.eval, Op.eval])) (by simp)

lemma hp_bprod {ι : Type} {t : ℕ} (c : Fin t → ι) :
    HasProg (fun (b : ι → ℝ) (_ : Unit) => ∏ r, b (c r)) t := by
  have h := hp_listprod (List.ofFn c)
  refine hp_mono (hp_congr h ?_) (by simp)
  intro b u
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

lemma hp_op2 {ι : Type} (op : Op) {f g : (ι → ℝ) → ℝ} {a b : ℕ}
    (hf : HasProg (fun v (_ : Unit) => f v) a) (hg : HasProg (fun v (_ : Unit) => g v) b) :
    HasProg (fun v (_ : Unit) => op.eval (f v) (g v)) (a + b + 1) := by
  have h := hp_bind (hp_pair hf hg)
    (hp_op op (Arg.inp (Sum.inr (Sum.inl ()))) (Arg.inp (Sum.inr (Sum.inr ()))) rfl rfl)
  exact hp_congr h (fun v u => by simp [Arg.eval])

lemma hp_const1 {ι : Type} (q : ℚ) (β : ℕ) (hq : q.num.natAbs < 2 ^ β ∧ q.den < 2 ^ β) :
    HasProg (fun (_ : ι → ℝ) (_ : Unit) => (q : ℝ)) (4 * β) := by
  have h := hp_consts (ι := ι) (κ := Unit) (fun _ => q) β (fun _ => hq)
  simpa using h

lemma hp_sumF {ι κ : Type} [Fintype κ] [DecidableEq κ] {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : ∀ k, HasProg (fun v (_ : Unit) => f v k) c) :
    HasProg (fun v (_ : Unit) => ∑ k, f v k) (Fintype.card κ * c + (Fintype.card κ - 1)) := by
  have h := hp_seq (hp_par hf) (hp_sum (ι := κ) (κ := κ) (fun k => Arg.inp k) (fun _ => rfl))
  exact hp_congr h (fun v u => by simp [Arg.eval])

def tab {ι κ : Type} (f : (ι → ℝ) → ℕ → κ → ℝ) (K : ℕ)
    (v : ι → ℝ) (a : ℕ × κ) : ℝ := if a.1 ≤ K then f v a.1 a.2 else 0

lemma hp_table {ι κ : Type} (f : (ι → ℝ) → ℕ → κ → ℝ)
    (g : ℕ → ((ι ⊕ (ℕ × κ)) → ℝ) → κ → ℝ) (c0 : ℕ) (c : ℕ → ℕ)
    (h0 : HasProg (fun v => f v 0) c0)
    (K : ℕ) (hs : ∀ k, k < K → HasProg (g k) (c k))
    (he : ∀ k, k < K → ∀ v a, g k (Sum.elim v (tab f k v)) a = f v (k + 1) a) :
    HasProg (tab f K) (c0 + ∑ k ∈ Finset.range K, c k) := by
  classical
  induction K with
  | zero =>
    have hz := hp_bind h0 (hp_args (fun a : ℕ × κ =>
      if a.1 = 0 then Arg.inp (Sum.inr a.2) else Arg.cst 0)
      (by intro a; split_ifs <;> rfl))
    apply hp_mono (hp_congr hz ?_) (by simp)
    intro v a
    simp only [Arg.eval, tab]
    by_cases h : a.1 = 0 <;> simp [h]
  | succ K ih =>
    obtain ⟨q, hq, eq, cq⟩ := hs K (by omega)
    let r : Prog (ι ⊕ (ℕ × κ)) (ℕ × κ) :=
      (q.bind (Prog.ofArgs (fun a : ℕ × κ =>
        if a.1 = K + 1 then Arg.inp (Sum.inr a.2)
        else Arg.inp (Sum.inl (Sum.inr a)))))
    have hr : Clean r := by
      apply clean_bind hq
      refine ⟨by simp [Prog.ofArgs], ?_⟩
      intro a
      change BstLean.Part41.argHeavy (if a.1 = K + 1 then Arg.inp (Sum.inr a.2)
        else Arg.inp (Sum.inl (Sum.inr a))) = 0
      split_ifs <;> rfl
    have er (v : (ι ⊕ (ℕ × κ)) → ℝ) (a : ℕ × κ) :
        r.eval v a = if a.1 = K + 1 then g K v a.2 else v (Sum.inr a) := by
      simp only [r, eval_bind, eval_ofArgs]
      split_ifs <;> simp [Arg.eval, eq]
    have hz : HasProg (fun v a => if a.1 = K + 1 then g K v a.2 else v (Sum.inr a))
        (c K) := ⟨r, hr, er, by simpa [r] using cq⟩
    have hi := ih (fun k hk => hs k (by omega)) (fun k hk => he k (by omega))
    apply hp_mono (hp_congr (hp_bind hi hz) ?_) (by rw [Finset.sum_range_succ]; omega)
    intro v a
    by_cases h : a.1 = K + 1
    · simp only [h, ite_true, he K (by omega), tab]
      simp
    · simp only [h, ite_false, Sum.elim_inr, tab]
      have hh : a.1 ≤ K + 1 ↔ a.1 ≤ K := by omega
      simp only [hh]

lemma hp_bool_pair {ι : Type} {f g : (ι → ℝ) → ℝ} {a b : ℕ}
    (hf : HasProg (fun v (_ : Unit) => f v) a)
    (hg : HasProg (fun v (_ : Unit) => g v) b) :
    HasProg (fun v (t : Bool) => if t then g v else f v) (a + b) := by
  exact hp_congr (hp_mapOut (hp_pair hf hg)
    (fun t => if t then Sum.inr () else Sum.inl ()))
    (by intro v t; cases t <;> rfl)


end BstLean.Part56.MomProg
