import BstLean.Part74GenDefs
import BstLean.Part74Prog24

/-!
# Part 74: the input stage of the moment program at `(3, 3)`

`hInp33`: a program with the constants `0`, `1` only, of cost `≤ 154 n + 238 K + 35`, that maps
`(t, v)` to `inp33 n K t v`: the power sums `p_e(v)`, `e ≤ 16`; the table sums `W_{c,q}`,
`c ≤ q ≤ 4`; and `Z_0`.
-/

namespace BstLean.Part74

open BstLean.Cost BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part69
open BstLean.Part69.Ex69p

/-! ## The table -/

/-- The state of the recurrence at step `j`. -/
noncomputable def st33 (n : ℕ) (x : InM56 n → ℝ) (j : ℕ) : Fin 22 → ℝ :=
  ![x (Sum.inl ()) ^ j / (j.factorial : ℝ), U69 n j, U69 n (j + 1), (j : ℝ) + 1,
    (n : ℝ) + 2 * ((j : ℝ) + 1), 2 * ((j : ℝ) + 1) + 1,
    Z69 n j (x (Sum.inl ())) 0,
    W74 n j (x (Sum.inl ())) 0 0,
    W74 n j (x (Sum.inl ())) 0 1, W74 n j (x (Sum.inl ())) 1 1,
    W74 n j (x (Sum.inl ())) 0 2, W74 n j (x (Sum.inl ())) 1 2, W74 n j (x (Sum.inl ())) 2 2,
    W74 n j (x (Sum.inl ())) 0 3, W74 n j (x (Sum.inl ())) 1 3, W74 n j (x (Sum.inl ())) 2 3,
    W74 n j (x (Sum.inl ())) 3 3,
    W74 n j (x (Sum.inl ())) 0 4, W74 n j (x (Sum.inl ())) 1 4, W74 n j (x (Sum.inl ())) 2 4,
    W74 n j (x (Sum.inl ())) 3 4, W74 n j (x (Sum.inl ())) 4 4]

/-- The initial state, from `N = n`. -/
def eInit33 : Fin 22 → Ex69p Unit :=
  let N : Ex69p Unit := var ()
  let two : Ex69p Unit := 1 + 1
  ![1, 1, 1 / N, 1, N + two, two + 1, 1,
    1,
    1 / N, 0,
    1 / (N * (N + two)), 0, 0,
    1 / (N * (N + two) * (N + (two + two))), 0, 0, 0,
    1 / (N * (N + two) * (N + (two + two)) * (N + (two + two + two))), 0, 0, 0, 0]

/-- One step of the recurrence, reading row `k` of the table. -/
def eStep33 (n k : ℕ) : Fin 22 → Ex69p (InM56 n ⊕ (ℕ × Fin 22)) :=
  let R : Fin 22 → Ex69p (InM56 n ⊕ (ℕ × Fin 22)) := fun i => var (Sum.inr (k, i))
  let T : Ex69p (InM56 n ⊕ (ℕ × Fin 22)) := var (Sum.inl (Sum.inl ()))
  let two : Ex69p (InM56 n ⊕ (ℕ × Fin 22)) := 1 + 1
  let c := R 0 * T / R 3
  let base := c * R 2
  let D1 := R 4
  let D2 := R 4 * (R 4 + two)
  let D3 := R 4 * (R 4 + two) * (R 4 + (two + two))
  let D4 := R 4 * (R 4 + two) * (R 4 + (two + two)) * (R 4 + (two + two + two))
  let f1 := R 3
  let f2 := R 3 * (R 3 - 1)
  let f3 := R 3 * (R 3 - 1) * (R 3 - two)
  let f4 := R 3 * (R 3 - 1) * (R 3 - two) * (R 3 - (two + 1))
  ![c, R 2, R 2 * R 5 / R 4, R 3 + 1, R 4 + two, R 5 + two,
    R 6 + base,
    R 7 + base,
    R 8 + base / D1, R 9 + base * f1 / D1,
    R 10 + base / D2, R 11 + base * f1 / D2, R 12 + base * f2 / D2,
    R 13 + base / D3, R 14 + base * f1 / D3, R 15 + base * f2 / D3, R 16 + base * f3 / D3,
    R 17 + base / D4, R 18 + base * f1 / D4, R 19 + base * f2 / D4, R 20 + base * f3 / D4,
    R 21 + base * f4 / D4]

set_option maxHeartbeats 3200000 in
lemma hInit33 (n : ℕ) :
    HasProg (fun x => st33 n x 0) (n + ∑ o, (eInit33 o).size) := by
  have h := hp_seq (hp_nat (ι := InM56 n) n) (hpv eInit33)
  refine hp_congr h ?_
  intro x i
  have u0 : U69 n 0 = 1 := by simp [U69]
  have u1 : U69 n 1 = 1 / (n : ℝ) := by simp [U69]
  have z : ∀ l, Z69 n 0 (x (Sum.inl ())) l = U69 n l := by intro l; simp [Z69]
  fin_cases i <;>
    simp [eInit33, st33, z, u0, u1, W74, Finset.prod_range_succ] <;> (try ring_nf) <;> (try simp)

lemma hStep33 (n k : ℕ) (x : InM56 n → ℝ) (i : Fin 22) :
    (eStep33 n k i).eval (Sum.elim x (tab (st33 n) k x)) = st33 n x (k + 1) i := by
  have e : ∀ j, (Sum.elim x (tab (st33 n) k x)) (Sum.inr (k, j)) = st33 n x k j := by
    intro j; simp [tab]
  have hd3 := desc3_74 (k + 1)
  have hd4 := desc4_74 (k + 1)
  push_cast at hd3 hd4
  have hW33 := W74_succ n k (x (Sum.inl ())) 3 3
  have hW34 := W74_succ n k (x (Sum.inl ())) 3 4
  have hW44 := W74_succ n k (x (Sum.inl ())) 4 4
  rw [hd3] at hW33 hW34
  rw [hd4] at hW44
  fin_cases i
  · simp [eStep33, e, st33, c69_succ]
  · simp [eStep33, e, st33]
  · simp [eStep33, e, st33, U69_succ (j := k + 1)]; ring
  · simp [eStep33, e, st33]
  · simp [eStep33, e, st33]; ring
  · simp [eStep33, e, st33]; ring
  · simp [eStep33, e, st33, Z69_succ, c69_succ]
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, hW33, Finset.prod_range_succ]; ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, W74_succ, Finset.prod_range_succ]; try ring
  · simp [eStep33, e, st33, hW34, Finset.prod_range_succ]; ring
  · simp [eStep33, e, st33, hW44, Finset.prod_range_succ]; ring

lemma size_step33 (n k : ℕ) : ∑ o, (eStep33 n k o).size = 238 := by
  simp [eStep33, Fin.sum_univ_succ]

lemma size_init33 : ∑ o, (eInit33 o).size = 35 := by
  simp [eInit33, Fin.sum_univ_succ]

lemma hTab33 (n K : ℕ) : HasProg (tab (st33 n) K) (n + 35 + 238 * K) := by
  have h0 := hInit33 n
  rw [size_init33] at h0
  have h := hp_table (st33 n) (fun k y i => (eStep33 n k i).eval y) (n + 35) (fun _ => 238) h0 K
    (fun k _ => by have := hpv (eStep33 n k); rwa [size_step33] at this)
    (fun k _ x i => hStep33 n k x i)
  exact hp_mono h (by simp; omega)

/-! ## The output stage -/

/-- `X^e` as an expression. -/
def powE {α : Type} (X : Ex69p α) : ℕ → Ex69p α
  | 0 => 1
  | e + 1 => powE X e * X

lemma powE_eval {α : Type} (X : Ex69p α) (y : α → ℝ) (e : ℕ) :
    (powE X e).eval y = X.eval y ^ e := by
  induction e with
  | zero => simp [powE]
  | succ e ih => simp [powE, ih, pow_succ]

lemma powE_size {α : Type} (a : α) (e : ℕ) : (powE (var a) e).size = e := by
  induction e with
  | zero => simp [powE]
  | succ e ih => simp [powE, ih]

/-- The column of `W_{c,q}` in the table (`c ≤ q`). -/
def idxW (c q : Fin 5) : Fin 22 :=
  (![![7, 8, 10, 13, 17], ![0, 9, 11, 14, 18], ![0, 0, 12, 15, 19], ![0, 0, 0, 16, 20],
    ![0, 0, 0, 0, 21]] : Fin 5 → Fin 5 → Fin 22) c q

/-- The output stage, from the inputs and the table. -/
noncomputable def gOut33 (n K : ℕ) (y : InM56 n ⊕ (ℕ × Fin 22) → ℝ) : V33 → ℝ :=
  Sum.elim (fun e => ∑ i, y (Sum.inl (Sum.inr i)) ^ (e : ℕ))
    (Sum.elim (fun cq => if (cq.1 : ℕ) ≤ (cq.2 : ℕ) then y (Sum.inr (K, idxW cq.1 cq.2)) else 0)
      (fun _ => y (Sum.inr (K, 6))))

/-- The cost of each output. -/
def cOut33 (n : ℕ) : V33 → ℕ :=
  Sum.elim (fun e => n * (e : ℕ) + (n - 1)) (fun _ => 0)

lemma hOut33 (n K : ℕ) : HasProg (gOut33 n K) (∑ k, cOut33 n k) := by
  refine hp_parS (f := gOut33 n K) (cOut33 n) ?_
  intro o
  rcases o with e | cq | u
  · have h := hp_sumF (f := fun (y : InM56 n ⊕ (ℕ × Fin 22) → ℝ) (i : Fin n) =>
        y (Sum.inl (Sum.inr i)) ^ (e : ℕ)) (c := (e : ℕ)) (fun i => by
      have := hp (powE (var (Sum.inl (Sum.inr i)) : Ex69p (InM56 n ⊕ (ℕ × Fin 22))) (e : ℕ))
      rw [powE_size] at this
      exact hp_congr this (fun y u => by simp [powE_eval]))
    refine hp_mono (hp_congr h (fun y u => by simp [gOut33])) ?_
    simp [cOut33]
  · by_cases hc : (cq.1 : ℕ) ≤ (cq.2 : ℕ)
    · exact hp_mono (hp_congr (hp (var (Sum.inr (K, idxW cq.1 cq.2)) :
        Ex69p (InM56 n ⊕ (ℕ × Fin 22)))) (fun y u => by
          simp only [gOut33, Sum.elim_inr, Sum.elim_inl]; rw [if_pos hc]; simp)) (by simp)
    · exact hp_mono (hp_congr (hp (0 : Ex69p (InM56 n ⊕ (ℕ × Fin 22))))
        (fun y u => by
          simp only [gOut33, Sum.elim_inr, Sum.elim_inl]; rw [if_neg hc]; simp)) (by simp)
  · exact hp_mono (hp_congr (hp (var (Sum.inr (K, 6)) :
      Ex69p (InM56 n ⊕ (ℕ × Fin 22)))) (fun y u => by simp [gOut33])) (by simp)

lemma cOut33_sum (n : ℕ) : ∑ k, cOut33 n k ≤ 153 * n := by
  simp [cOut33, Fin.sum_univ_succ]
  omega

lemma tabW33 (n K : ℕ) (x : InM56 n → ℝ) (c q : Fin 5) (h : (c : ℕ) ≤ (q : ℕ)) :
    tab (st33 n) K x (K, idxW c q) = W74 n K (x (Sum.inl ())) c q := by
  fin_cases c <;> fin_cases q <;> first
    | (exfalso; revert h; decide)
    | simp [tab, st33, idxW]

/-- The input vector as a function of the program inputs. -/
noncomputable def inpX33 (n K : ℕ) (x : InM56 n → ℝ) : V33 → ℝ :=
  inp33 n K (x (Sum.inl ())) (fun i => x (Sum.inr i))

/-- **The input stage at `(3, 3)`**: constants `0`, `1` only, cost `≤ 154 n + 238 K + 35`. -/
theorem hInp33 (n K : ℕ) :
    HasProg (fun (x : InM56 n → ℝ) => inp33 n K (x (Sum.inl ())) (fun i => x (Sum.inr i)))
      (154 * n + 238 * K + 35) := by
  have h := hp_bind (hTab33 n K) (hOut33 n K)
  refine hp_mono (hp_congr h ?_) (by have := cOut33_sum n; omega)
  intro x k
  rcases k with e | cq | u
  · simp [gOut33, inp33, pw]
  · by_cases hc : (cq.1 : ℕ) ≤ (cq.2 : ℕ)
    · simp only [gOut33, inp33, Sum.elim_inr, Sum.elim_inl]
      rw [if_pos hc, if_pos hc]
      exact tabW33 n K x cq.1 cq.2 hc
    · simp only [gOut33, inp33, Sum.elim_inr, Sum.elim_inl]
      rw [if_neg hc, if_neg hc]
  · simp [gOut33, inp33, tab, st33]

theorem hInp33_val (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) :
    (fun (x : InM56 n → ℝ) => inp33 n K (x (Sum.inl ())) (fun i => x (Sum.inr i))) (inRK t v) =
      inp33 n K t v := by
  simp [inRK]

end BstLean.Part74

#print axioms BstLean.Part74.hInp33
