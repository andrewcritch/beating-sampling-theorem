import BstLean.Part59Defs
import BstLean.Part53Cost_Constants

/-! Exact constant-column evaluation. This helper does not supply the Prop C cost bound. -/
namespace BstLean.Part59.ProgAux59x

set_option backward.isDefEq.respectTransparency false

open BstLean.Cost
open BstLean.Part41 (Mono heavyCount)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part53.CostAux (aq aq_cast heavy_mapIn)

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

/-- Reduced input type: coordinates of the constant column and polynomial coefficients. -/
abbrev SmallIn59x (n k : ℕ) := Fin n ⊕ Mono n k

def embed59x (n d k : ℕ) : SmallIn59x n k → In59 n d k :=
  Sum.elim (fun i => Sum.inl ⟨0, ((default : Mono n d).2, i)⟩) Sum.inr

private lemma q_has (n d k e : ℕ) (i : Fin n) :
    HasProg (fun v : SmallIn59x n k → ℝ => qH e (v (.inl i)) (BstLean.Part53.aH n d)) := by
  induction e using Nat.twoStepInduction with
  | zero => simpa [qH] using (has_const (ι := SmallIn59x n k) 1)
  | one => simpa [qH] using (has_input (ι := SmallIn59x n k) (.inl i))
  | more e ih ih' =>
    apply has_add
    · exact has_mul (has_input (ι := SmallIn59x n k) (.inl i)) ih'
    · apply has_mul
      · have h := has_const (ι := SmallIn59x n k) (((e : ℚ) + 1) * aq n d)
        convert h using 1
        ext v
        push_cast
        rw [aq_cast]
      · exact ih

private lemma raw_exists (n d k : ℕ) :
    HasProg (fun v : SmallIn59x n k → ℝ =>
      ∑ α : Mono n k, v (.inr α) *
        ∏ i : Fin n, qH (α.2.1.count i) (v (.inl i)) (BstLean.Part53.aH n d)) := by
  classical
  apply has_sum
  intro α hα
  apply has_mul (has_input (ι := SmallIn59x n k) (.inr α))
  apply has_prod
  intro i hi
  exact q_has n d k _ i

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

lemma mapIn_constCol59x (n d k : ℕ) (p : Prog (SmallIn59x n k) Unit) :
    ConstColOnly59 (p.mapIn (embed59x n d k)) := by
  have he (i : SmallIn59x n k) (α : CoefIdxD n d)
      (h : embed59x n d k i = Sum.inl α) : α.1 = 0 := by
    cases i with
    | inl a => cases h; rfl
    | inr f => cases h
  have ha (a : Arg (SmallIn59x n k)) (α : CoefIdxD n d)
      (h : a.rename (embed59x n d k) = .inp (.inl α)) : α.1 = 0 := by
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

/-- Exact evaluation from `0` and `1`, with constant-column inputs only. No cost bound. -/
theorem uncosted_exists59x (n d k : ℕ) :
    ∃ p : Prog (In59 n d k) Unit, heavyCount p = 0 ∧ ConstColOnly59 p ∧
      ∀ v : In59 n d k → ℝ, p.eval v () = g0Q n d k (cv59 v) (Mv59 v) := by
  obtain ⟨p, hp⟩ := raw_exists n d k
  obtain ⟨β, hβ⟩ := height_bound (BstLean.Part41.heavyConsts p)
  obtain ⟨p', h0, heval, hcost⟩ := BstLean.Part41.inline_consts p β hβ
  refine ⟨p'.mapIn (embed59x n d k), ?_, mapIn_constCol59x n d k p', ?_⟩
  · rw [heavy_mapIn]; exact h0
  · intro v
    rw [eval_mapIn, heval, hp]
    rfl

end
end BstLean.Part59.ProgAux59x
