import BstLean.Part74LineDefs
import BstLean.Part74Tab33

/-!
# Part 74: the input stage of the moment program at a general size

`hInpG`: for every `(d, k)` there is a constant `B` such that, for all `n`, `K`, a program with the
constants `0`, `1` only and cost `≤ B (n + K + 1)` maps `(t, v)` to `inpG d k n K t v`: the power
sums `p_e(v)`, `e ≤ 2dk + 2`; the table sums `W_{c,q}`, `c ≤ q ≤ degD d k`; and `Z_0`.
-/

namespace BstLean.Part74

open BstLean.Cost BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part69
open BstLean.Part69.Ex69p

namespace TabG

/-! ## Expression helpers -/

/-- Renaming of variables. -/
def renE {α β : Type} (f : α → β) : Ex69p α → Ex69p β
  | .var a => .var (f a)
  | .zero => .zero
  | .one => .one
  | .bin o e g => .bin o (renE f e) (renE f g)

lemma renE_eval {α β : Type} (f : α → β) (e : Ex69p α) (y : β → ℝ) :
    (renE f e).eval y = e.eval (y ∘ f) := by
  induction e with
  | var a => rfl
  | zero => rfl
  | one => rfl
  | bin o e g he hg => simp only [renE, Ex69p.eval, he, hg]

lemma renE_size {α β : Type} (f : α → β) (e : Ex69p α) : (renE f e).size = e.size := by
  induction e with
  | var a => rfl
  | zero => rfl
  | one => rfl
  | bin o e g he hg => simp only [renE, Ex69p.size, he, hg]

/-- The numeral `k`. -/
def natE {α : Type} : ℕ → Ex69p α
  | 0 => 0
  | k + 1 => natE k + 1

lemma natE_eval {α : Type} (y : α → ℝ) (k : ℕ) : (natE k : Ex69p α).eval y = k := by
  induction k with
  | zero => simp [natE]
  | succ k ih => simp [natE, ih]

/-- `Π_{i<c} (J − i)`. -/
def descE {α : Type} (J : Ex69p α) : ℕ → Ex69p α
  | 0 => 1
  | c + 1 => descE J c * (J - natE c)

lemma descE_eval {α : Type} (J : Ex69p α) (y : α → ℝ) (j : ℕ) (hJ : J.eval y = j) (c : ℕ) :
    (descE J c).eval y = (j.descFactorial c : ℝ) := by
  induction c with
  | zero => simp [descE]
  | succ c ih =>
    simp only [descE, Ex69p.eval_mul, Ex69p.eval_sub, ih, natE_eval, hJ]
    rw [desc_succ74]

/-- `Π_{i<q} (X + 2i)`. -/
def denE {α : Type} (X : Ex69p α) : ℕ → Ex69p α
  | 0 => 1
  | q + 1 => denE X q * (X + natE (2 * q))

lemma denE_eval {α : Type} (X : Ex69p α) (y : α → ℝ) (q : ℕ) :
    (denE X q).eval y = ∏ i ∈ Finset.range q, (X.eval y + 2 * (i : ℝ)) := by
  induction q with
  | zero => simp [denE]
  | succ q ih => simp [denE, ih, natE_eval, Finset.prod_range_succ]

/-! ## The table -/

/-- The index of the state. -/
abbrev SG (D : ℕ) := Fin 7 ⊕ (Fin (D + 1) × Fin (D + 1))

/-- The state of the recurrence at step `j`. -/
noncomputable def stG (n D : ℕ) (x : InM56 n → ℝ) (j : ℕ) : SG D → ℝ :=
  Sum.elim
    ![x (Sum.inl ()) ^ j / (j.factorial : ℝ), U69 n j, U69 n (j + 1), (j : ℝ) + 1,
      (n : ℝ) + 2 * ((j : ℝ) + 1), 2 * ((j : ℝ) + 1) + 1, Z69 n j (x (Sum.inl ())) 0]
    (fun cq => W74 n j (x (Sum.inl ())) cq.1 cq.2)

/-- The initial state, from `N = n`. -/
def eInitG (D : ℕ) : SG D → Ex69p Unit :=
  let N : Ex69p Unit := var ()
  let two : Ex69p Unit := 1 + 1
  Sum.elim ![1, 1, 1 / N, 1, N + two, two + 1, 1]
    (fun cq => if (cq.1 : ℕ) = 0 then 1 / denE N cq.2 else 0)

/-- One step of the recurrence, over abstract variables: the previous row and `T`. -/
def eStepA (D : ℕ) : SG D → Ex69p (SG D ⊕ Unit) :=
  let R : Fin 7 → Ex69p (SG D ⊕ Unit) := fun i => var (Sum.inl (Sum.inl i))
  let T : Ex69p (SG D ⊕ Unit) := var (Sum.inr ())
  let two : Ex69p (SG D ⊕ Unit) := 1 + 1
  let c := R 0 * T / R 3
  let base := c * R 2
  Sum.elim ![c, R 2, R 2 * R 5 / R 4, R 3 + 1, R 4 + two, R 5 + two, R 6 + base]
    (fun cq => var (Sum.inl (Sum.inr cq)) + base * descE (R 3) cq.1 / denE (R 4) cq.2)

/-- The renaming to row `k` of the table. -/
def renG (n D k : ℕ) : SG D ⊕ Unit → InM56 n ⊕ (ℕ × SG D)
  | Sum.inl s => Sum.inr (k, s)
  | Sum.inr _ => Sum.inl (Sum.inl ())

/-- One step of the recurrence, reading row `k` of the table. -/
def eStepG (n D k : ℕ) (o : SG D) : Ex69p (InM56 n ⊕ (ℕ × SG D)) := renE (renG n D k) (eStepA D o)

lemma hInitG (n D : ℕ) :
    HasProg (fun x => stG n D x 0) (n + ∑ o, (eInitG D o).size) := by
  have h := hp_seq (hp_nat (ι := InM56 n) n)
    (hp_parS (f := fun (y : Unit → ℝ) o => (eInitG D o).eval y) _ (fun o => hp (eInitG D o)))
  refine hp_congr h ?_
  intro x o
  have u0 : U69 n 0 = 1 := by simp [U69]
  have u1 : U69 n 1 = 1 / (n : ℝ) := by simp [U69]
  have z : ∀ l, Z69 n 0 (x (Sum.inl ())) l = U69 n l := by intro l; simp [Z69]
  rcases o with i | ⟨c, q⟩
  · fin_cases i <;> simp [eInitG, stG, z, u0, u1] <;> (try ring_nf)
  · simp only [eInitG, stG, Sum.elim_inr]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc]
      simp [W74, hc, u0, denE_eval]
    · rw [if_neg hc]
      obtain ⟨c', hc'⟩ := Nat.exists_eq_succ_of_ne_zero hc
      simp [W74, hc']

lemma hStepA (n D k : ℕ) (x : InM56 n → ℝ) (z : SG D ⊕ Unit → ℝ)
    (hz : ∀ s, z (Sum.inl s) = stG n D x k s) (hT : z (Sum.inr ()) = x (Sum.inl ())) (o : SG D) :
    (eStepA D o).eval z = stG n D x (k + 1) o := by
  have e : ∀ i : Fin 7, z (Sum.inl (Sum.inl i)) = stG n D x k (Sum.inl i) := fun i => hz _
  rcases o with i | ⟨c, q⟩
  · fin_cases i
    · simp [eStepA, e, hT, stG, c69_succ]
    · simp [eStepA, e, hT, stG]
    · simp [eStepA, e, hT, stG, U69_succ (j := k + 1)]; ring
    · simp [eStepA, e, hT, stG]
    · simp [eStepA, e, hT, stG]; ring
    · simp [eStepA, e, hT, stG]; ring
    · simp [eStepA, e, hT, stG, Z69_succ, c69_succ]
  · have hJ : (var (Sum.inl (Sum.inl 3)) : Ex69p (SG D ⊕ Unit)).eval z = ((k + 1 : ℕ) : ℝ) := by
      simp [e, stG]
    simp only [eStepA, Sum.elim_inr, Ex69p.eval_add, Ex69p.eval_mul, Ex69p.eval_div,
      Ex69p.eval_var, descE_eval _ z (k + 1) hJ, denE_eval, hz, e, hT]
    simp only [stG, Sum.elim_inr, Sum.elim_inl, W74_succ]
    simp

lemma hStepG (n D k : ℕ) (x : InM56 n → ℝ) (o : SG D) :
    (eStepG n D k o).eval (Sum.elim x (tab (stG n D) k x)) = stG n D x (k + 1) o := by
  unfold eStepG
  rw [renE_eval]
  exact hStepA n D k x _ (fun s => by simp [renG, tab]) (by simp [renG]) o

lemma hTabG (n D K : ℕ) :
    HasProg (tab (stG n D) K) (n + ∑ o, (eInitG D o).size + K * ∑ o, (eStepA D o).size) := by
  have h := hp_table (stG n D) (fun k y i => (eStepG n D k i).eval y)
    (n + ∑ o, (eInitG D o).size) (fun _ => ∑ o, (eStepA D o).size) (hInitG n D) K
    (fun k _ => by
      have := hp_parS (f := fun (y : InM56 n ⊕ (ℕ × SG D) → ℝ) o => (eStepG n D k o).eval y) _
        (fun o => hp (eStepG n D k o))
      simpa [eStepG, renE_size] using this)
    (fun k _ x i => hStepG n D k x i)
  exact hp_mono h (by simp)

/-! ## The output stage -/

/-- The output stage, from the inputs and the table. -/
noncomputable def gOutG (d k n K : ℕ) (y : InM56 n ⊕ (ℕ × SG (degD d k)) → ℝ) : VG d k → ℝ :=
  Sum.elim (fun e => ∑ i, y (Sum.inl (Sum.inr i)) ^ (e : ℕ))
    (Sum.elim (fun cq => if (cq.1 : ℕ) ≤ (cq.2 : ℕ) then y (Sum.inr (K, Sum.inr cq)) else 0)
      (fun _ => y (Sum.inr (K, Sum.inl 6))))

/-- The cost of each output. -/
def cOutG (d k n : ℕ) : VG d k → ℕ :=
  Sum.elim (fun e => n * (e : ℕ) + (n - 1)) (fun _ => 0)

lemma hOutG (d k n K : ℕ) : HasProg (gOutG d k n K) (∑ o, cOutG d k n o) := by
  refine hp_parS (f := gOutG d k n K) (cOutG d k n) ?_
  intro o
  rcases o with e | cq | u
  · have h := hp_sumF (f := fun (y : InM56 n ⊕ (ℕ × SG (degD d k)) → ℝ) (i : Fin n) =>
        y (Sum.inl (Sum.inr i)) ^ (e : ℕ)) (c := (e : ℕ)) (fun i => by
      have := hp (powE (var (Sum.inl (Sum.inr i)) :
        Ex69p (InM56 n ⊕ (ℕ × SG (degD d k)))) (e : ℕ))
      rw [powE_size] at this
      exact hp_congr this (fun y u => by simp [powE_eval]))
    refine hp_mono (hp_congr h (fun y u => by simp [gOutG])) ?_
    simp [cOutG]
  · by_cases hc : (cq.1 : ℕ) ≤ (cq.2 : ℕ)
    · exact hp_mono (hp_congr (hp (var (Sum.inr (K, Sum.inr cq)) :
        Ex69p (InM56 n ⊕ (ℕ × SG (degD d k))))) (fun y u => by
          simp only [gOutG, Sum.elim_inr, Sum.elim_inl]; rw [if_pos hc]; simp)) (by simp)
    · exact hp_mono (hp_congr (hp (0 : Ex69p (InM56 n ⊕ (ℕ × SG (degD d k)))))
        (fun y u => by
          simp only [gOutG, Sum.elim_inr, Sum.elim_inl]; rw [if_neg hc]; simp)) (by simp)
  · exact hp_mono (hp_congr (hp (var (Sum.inr (K, Sum.inl 6)) :
      Ex69p (InM56 n ⊕ (ℕ × SG (degD d k))))) (fun y u => by simp [gOutG])) (by simp)

lemma cOutG_sum (d k n : ℕ) :
    ∑ o, cOutG d k n o ≤ (2 * d * k + 3) * (2 * d * k + 3) * n := by
  rw [Fintype.sum_sum_type]
  simp only [cOutG, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
  calc ∑ e : Fin (2 * d * k + 3), (n * (e : ℕ) + (n - 1))
      ≤ ∑ _e : Fin (2 * d * k + 3), n * (2 * d * k + 3) := by
        apply Finset.sum_le_sum
        intro e _
        calc n * (e : ℕ) + (n - 1) ≤ n * ((e : ℕ) + 1) := by rw [mul_add]; omega
          _ ≤ n * (2 * d * k + 3) := Nat.mul_le_mul_left _ e.2
    _ = (2 * d * k + 3) * (2 * d * k + 3) * n := by
        simp [Finset.sum_const, Finset.card_univ]; ring

/-- The constant of `hInpG`. -/
def BG (d k : ℕ) : ℕ :=
  ∑ o, (eInitG (degD d k) o).size + ∑ o, (eStepA (degD d k) o).size +
    (2 * d * k + 3) * (2 * d * k + 3) + 1

end TabG

open TabG

/-- **The input stage at `(d, k)`**: constants `0`, `1` only, cost `≤ BG d k · (n + K + 1)`. -/
theorem hInpG_explicit (d k n K : ℕ) :
    HasProg (fun (x : InM56 n → ℝ) => inpG d k n K (x (Sum.inl ())) (fun i => x (Sum.inr i)))
      (BG d k * (n + K + 1)) := by
  have h := hp_bind (hTabG n (degD d k) K) (hOutG d k n K)
  refine hp_mono (hp_congr h ?_) ?_
  · intro x o
    rcases o with e | cq | u
    · simp [gOutG, inpG, pw]
    · by_cases hc : (cq.1 : ℕ) ≤ (cq.2 : ℕ)
      · simp only [gOutG, inpG, Sum.elim_inr, Sum.elim_inl]
        rw [if_pos hc, if_pos hc]
        simp [tab, stG]
      · simp only [gOutG, inpG, Sum.elim_inr, Sum.elim_inl]
        rw [if_neg hc, if_neg hc]
    · simp [gOutG, inpG, tab, stG]
  · have h1 := cOutG_sum d k n
    unfold BG
    set a := ∑ o, (eInitG (degD d k) o).size
    set b := ∑ o, (eStepA (degD d k) o).size
    set E := (2 * d * k + 3) * (2 * d * k + 3)
    have : (a + b + E + 1) * (n + K + 1) =
        n + a + K * b + E * n + (a * n + a * K + b * n + b + E * K + E + K + 1) := by ring
    omega

theorem hInpG (d k : ℕ) : ∃ B : ℕ, ∀ n K : ℕ,
    HasProg (fun (x : InM56 n → ℝ) => inpG d k n K (x (Sum.inl ())) (fun i => x (Sum.inr i)))
      (B * (n + K + 1)) :=
  ⟨BG d k, fun n K => hInpG_explicit d k n K⟩

theorem hInpG_val (d k n K : ℕ) (t : ℝ) (v : Fin n → ℝ) :
    (fun (x : InM56 n → ℝ) => inpG d k n K (x (Sum.inl ())) (fun i => x (Sum.inr i)))
      (inRK t v) = inpG d k n K t v := by
  simp [inRK]

end BstLean.Part74

#print axioms BstLean.Part74.hInpG
