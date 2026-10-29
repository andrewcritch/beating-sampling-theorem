import BstLean.Part74Defs
import BstLean.Part69Prog
import BstLean.Part61MomProg_Newton

/-!
# Part 74: the single-use moment program at `(d_M, d_f) = (2, 4)`

`momProg74_24_nat`: a program with the constants `0`, `1` only that maps `inRK t v` to
`out74 r q (ET74 n K t v) (ET2_74 n K t v)`, `r = newt61 N (Z₁/Z₀)`, `q = Σ v_i⁴`.

Construction: a table recurrence computes `t^j/j!`, `U_j`, `U_{j+1}` and the partial sums `Z_0`,
`Z_1`, `W_{c,2}` (`c ≤ 2`), `W_{c,4}` (`c ≤ 4`); a second stage computes `a = Z_1/Z_0`, `Σ v_i⁴`,
`Σ v_i⁶`; then the Newton node; then the constant-size formulas.
-/

namespace BstLean.Part74

open BstLean.Cost BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part61
open BstLean.Part69
open BstLean.Part69.Ex69p

/-! ## Small lemmas -/

lemma desc_succ74 (j c : ℕ) :
    ((j.descFactorial (c + 1) : ℕ) : ℝ) = (j.descFactorial c : ℝ) * ((j : ℝ) - c) := by
  rw [Nat.descFactorial_succ]
  by_cases h : c ≤ j
  · push_cast [Nat.cast_sub h]; ring
  · have h0 : j.descFactorial c = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

lemma desc1_74 (j : ℕ) : ((j.descFactorial 1 : ℕ) : ℝ) = j := by simp

lemma desc2_74 (j : ℕ) : ((j.descFactorial 2 : ℕ) : ℝ) = j * ((j : ℝ) - 1) := by
  rw [desc_succ74, desc1_74]; norm_num

lemma desc3_74 (j : ℕ) :
    ((j.descFactorial 3 : ℕ) : ℝ) = j * ((j : ℝ) - 1) * ((j : ℝ) - 2) := by
  rw [desc_succ74, desc2_74]; norm_num

lemma desc4_74 (j : ℕ) :
    ((j.descFactorial 4 : ℕ) : ℝ) = j * ((j : ℝ) - 1) * ((j : ℝ) - 2) * ((j : ℝ) - 3) := by
  rw [desc_succ74, desc3_74]; norm_num

lemma W74_succ (n j : ℕ) (T : ℝ) (c q : ℕ) :
    W74 n (j + 1) T c q = W74 n j T c q +
      T ^ j / (j.factorial : ℝ) * T / ((j : ℝ) + 1) * U69 n (j + 1) *
        ((j + 1).descFactorial c : ℝ) /
        ∏ i ∈ Finset.range q, ((n : ℝ) + 2 * ((j : ℝ) + 1) + 2 * (i : ℝ)) := by
  unfold W74
  rw [Finset.sum_range_succ, c69_succ]
  push_cast
  rfl

/-! ## The table -/

/-- The state of the recurrence at step `j`. -/
noncomputable def st74 (n : ℕ) (x : InM56 n → ℝ) (j : ℕ) : Fin 16 → ℝ :=
  ![x (Sum.inl ()) ^ j / (j.factorial : ℝ), U69 n j, U69 n (j + 1), (j : ℝ) + 1,
    (n : ℝ) + 2 * ((j : ℝ) + 1), 2 * ((j : ℝ) + 1) + 1,
    Z69 n j (x (Sum.inl ())) 0, Z69 n j (x (Sum.inl ())) 1,
    W74 n j (x (Sum.inl ())) 0 2, W74 n j (x (Sum.inl ())) 1 2, W74 n j (x (Sum.inl ())) 2 2,
    W74 n j (x (Sum.inl ())) 0 4, W74 n j (x (Sum.inl ())) 1 4, W74 n j (x (Sum.inl ())) 2 4,
    W74 n j (x (Sum.inl ())) 3 4, W74 n j (x (Sum.inl ())) 4 4]

/-- The initial state, from `N = n`. -/
def eInit74 : Fin 16 → Ex69p Unit :=
  let N : Ex69p Unit := var ()
  let two : Ex69p Unit := 1 + 1
  ![1, 1, 1 / N, 1, N + two, two + 1, 1, 1 / N,
    1 / (N * (N + two)), 0, 0,
    1 / (N * (N + two) * (N + (two + two)) * (N + (two + two + two))), 0, 0, 0, 0]

/-- One step of the recurrence, reading row `k` of the table. -/
def eStep74 (n k : ℕ) : Fin 16 → Ex69p (InM56 n ⊕ (ℕ × Fin 16)) :=
  let R : Fin 16 → Ex69p (InM56 n ⊕ (ℕ × Fin 16)) := fun i => var (Sum.inr (k, i))
  let T : Ex69p (InM56 n ⊕ (ℕ × Fin 16)) := var (Sum.inl (Sum.inl ()))
  let two : Ex69p (InM56 n ⊕ (ℕ × Fin 16)) := 1 + 1
  let c := R 0 * T / R 3
  let base := c * R 2
  let D2 := R 4 * (R 4 + two)
  let D4 := R 4 * (R 4 + two) * (R 4 + (two + two)) * (R 4 + (two + two + two))
  let f1 := R 3
  let f2 := R 3 * (R 3 - 1)
  let f3 := R 3 * (R 3 - 1) * (R 3 - two)
  let f4 := R 3 * (R 3 - 1) * (R 3 - two) * (R 3 - (two + 1))
  ![c, R 2, R 2 * R 5 / R 4, R 3 + 1, R 4 + two, R 5 + two,
    R 6 + base, R 7 + c * (R 2 * R 5 / R 4),
    R 8 + base / D2, R 9 + base * f1 / D2, R 10 + base * f2 / D2,
    R 11 + base / D4, R 12 + base * f1 / D4, R 13 + base * f2 / D4, R 14 + base * f3 / D4,
    R 15 + base * f4 / D4]

lemma hInit74 (n : ℕ) :
    HasProg (fun x => st74 n x 0) (n + ∑ o, (eInit74 o).size) := by
  have h := hp_seq (hp_nat (ι := InM56 n) n) (hpv eInit74)
  refine hp_congr h ?_
  intro x i
  have u0 : U69 n 0 = 1 := by simp [U69]
  have u1 : U69 n 1 = 1 / (n : ℝ) := by simp [U69]
  have z : ∀ l, Z69 n 0 (x (Sum.inl ())) l = U69 n l := by intro l; simp [Z69]
  fin_cases i <;>
    simp [eInit74, st74, z, u0, u1, W74, Finset.prod_range_succ] <;> (try ring_nf) <;> (try simp)

lemma hStep74 (n k : ℕ) (x : InM56 n → ℝ) (i : Fin 16) :
    (eStep74 n k i).eval (Sum.elim x (tab (st74 n) k x)) = st74 n x (k + 1) i := by
  have e : ∀ j, (Sum.elim x (tab (st74 n) k x)) (Sum.inr (k, j)) = st74 n x k j := by
    intro j; simp [tab]
  have hd3 := desc3_74 (k + 1)
  have hd4 := desc4_74 (k + 1)
  push_cast at hd3 hd4
  fin_cases i
  · simp [eStep74, e, st74, c69_succ]
  · simp [eStep74, e, st74]
  · simp [eStep74, e, st74, U69_succ (j := k + 1)]; ring
  · simp [eStep74, e, st74]
  · simp [eStep74, e, st74]; ring
  · simp [eStep74, e, st74]; ring
  · simp [eStep74, e, st74, Z69_succ, c69_succ]
  · simp [eStep74, e, st74, Z69_succ, c69_succ, U69_succ (j := k + 1)]; left; ring
  · simp [eStep74, e, st74, W74_succ, Finset.prod_range_succ]; ring
  · simp [eStep74, e, st74, W74_succ, Finset.prod_range_succ]; ring
  · simp [eStep74, e, st74, W74_succ, Finset.prod_range_succ]; ring
  · simp [eStep74, e, st74, W74_succ, Finset.prod_range_succ]; ring
  · simp [eStep74, e, st74, W74_succ, Finset.prod_range_succ]; ring
  · simp [eStep74, e, st74, W74_succ, Finset.prod_range_succ]; ring
  · have hW := W74_succ n k (x (Sum.inl ())) 3 4
    rw [hd3] at hW
    simp [eStep74, e, st74, hW, Finset.prod_range_succ]; ring
  · have hW := W74_succ n k (x (Sum.inl ())) 4 4
    rw [hd4] at hW
    simp [eStep74, e, st74, hW, Finset.prod_range_succ]; ring

lemma size_step74 (n k : ℕ) : ∑ o, (eStep74 n k o).size = 167 := by
  simp [eStep74, Fin.sum_univ_succ]

lemma size_init74 : ∑ o, (eInit74 o).size = 26 := by
  simp [eInit74, Fin.sum_univ_succ]

lemma hTab74 (n K : ℕ) : HasProg (tab (st74 n) K) (n + 26 + 167 * K) := by
  have h0 := hInit74 n
  rw [size_init74] at h0
  have h := hp_table (st74 n) (fun k y i => (eStep74 n k i).eval y) (n + 26) (fun _ => 167) h0 K
    (fun k _ => by have := hpv (eStep74 n k); rwa [size_step74] at this)
    (fun k _ x i => hStep74 n k x i)
  exact hp_mono h (by simp; omega)

/-! ## Stage B: `a = Z₁/Z₀`, `Σ v_i⁴`, `Σ v_i⁶` -/

/-- Stage B values, from the inputs and the table. -/
noncomputable def gB74 (n K : ℕ) (y : InM56 n ⊕ (ℕ × Fin 16) → ℝ) : Fin 3 → ℝ :=
  ![y (Sum.inr (K, 7)) / y (Sum.inr (K, 6)),
    ∑ i, y (Sum.inl (Sum.inr i)) ^ 4, ∑ i, y (Sum.inl (Sum.inr i)) ^ 6]

lemma hB74 (n K : ℕ) : HasProg (gB74 n K) (10 * n + 1) := by
  have h := hp_parS (f := gB74 n K) ![1, 4 * n, 6 * n] (by
    intro o
    fin_cases o
    · exact hp_mono (hp_congr (hp ((var (Sum.inr (K, 7)) : Ex69p (InM56 n ⊕ (ℕ × Fin 16))) /
        var (Sum.inr (K, 6)))) (fun y u => by simp [gB74])) (by simp)
    · have h := hp_sumF (f := fun (y : InM56 n ⊕ (ℕ × Fin 16) → ℝ) (i : Fin n) =>
          y (Sum.inl (Sum.inr i)) ^ 4) (c := 3) (fun i => by
        let X : Ex69p (InM56 n ⊕ (ℕ × Fin 16)) := var (Sum.inl (Sum.inr i))
        exact hp_mono (hp_congr (hp (X * X * (X * X))) (fun y u => by simp [X]; ring)) (by simp [X]))
      refine hp_mono (hp_congr h (fun y u => by simp [gB74])) ?_
      simp; omega
    · have h := hp_sumF (f := fun (y : InM56 n ⊕ (ℕ × Fin 16) → ℝ) (i : Fin n) =>
          y (Sum.inl (Sum.inr i)) ^ 6) (c := 5) (fun i => by
        let X : Ex69p (InM56 n ⊕ (ℕ × Fin 16)) := var (Sum.inl (Sum.inr i))
        exact hp_mono (hp_congr (hp (X * X * X * (X * X * X))) (fun y u => by simp [X]; ring))
          (by simp [X]))
      refine hp_mono (hp_congr h (fun y u => by simp [gB74])) ?_
      simp; omega)
  refine hp_mono h ?_
  simp [Fin.sum_univ_succ]; omega

/-! ## Stage C: the constant-size formulas -/

/-- The variables of stage C: inputs and table, stage B, the node. -/
abbrev V74 (n : ℕ) := ((InM56 n ⊕ (ℕ × Fin 16)) ⊕ Fin 3) ⊕ Unit

/-- Stage C: the outputs `r, 1, m₁, m₂`. -/
def eCx74 (n K : ℕ) : Fin 4 → Ex69p (V74 n) :=
  let r : Ex69p (V74 n) := var (Sum.inr ())
  let q : Ex69p (V74 n) := var (Sum.inl (Sum.inr 1))
  let Rr : Ex69p (V74 n) := var (Sum.inl (Sum.inr 2))
  let tb : Fin 16 → Ex69p (V74 n) := fun i => var (Sum.inl (Sum.inl (Sum.inr (K, i))))
  let two : Ex69p (V74 n) := 1 + 1
  let three : Ex69p (V74 n) := two + 1
  let four : Ex69p (V74 n) := two + two
  let six : Ex69p (V74 n) := three + three
  let twelve : Ex69p (V74 n) := six + six
  let c16 : Ex69p (V74 n) := four * four
  let c24 : Ex69p (V74 n) := twelve + twelve
  let c28 : Ex69p (V74 n) := c24 + four
  let c32 : Ex69p (V74 n) := c16 + c16
  let Nn : Ex69p (V74 n) := var (Sum.inl (Sum.inl (Sum.inr (0, 4)))) - two
  let eT := (three * Nn * tb 8 + twelve * tb 9 + four * q * tb 10) / tb 6
  let eT2 := (three * Nn * (three * Nn + c32) * tb 11 + c24 * (three * Nn + c32) * tb 12 +
    c24 * (Nn * q + c28 * q + six) * tb 13 + c32 * (three * q + four * Rr) * tb 14 +
    c16 * (q * q) * tb 15) / tb 6
  let cK := three / two - r * r - r * r * (r * r) * (1 + q) / two
  ![r, 1, cK + eT / two, cK * cK + cK * eT + eT2 / four]

lemma size_C74 (n K : ℕ) : ∑ o, (eCx74 n K o).size = 296 := by
  simp [eCx74, Fin.sum_univ_succ]

/-- The output selector. -/
def sel74 : Unit ⊕ Fin 3 → Fin 4
  | Sum.inl _ => 0
  | Sum.inr l => l.succ

/-- The node as a function of the stage-B outputs. -/
lemma hNewt74 (n : ℕ) :
    HasProg (fun (w : (InM56 n ⊕ (ℕ × Fin 16)) ⊕ Fin 3 → ℝ) (_ : Unit) =>
      newt61 (newtN61 n) (w (Sum.inr 0))) (4 * newtN61 n) :=
  hp_congr (hp_mapIn (BstLean.Part61.MomProgAux.hp_newton (newtN61 n))
    (fun _ : Unit => (Sum.inr 0 : (InM56 n ⊕ (ℕ × Fin 16)) ⊕ Fin 3))) (fun _ _ => rfl)

/-- **The moment program at `(d, k) = (2, 4)`**: constants `0`, `1` only, cost
`≤ 11 n + 167 K + 4 ⌊log₂ n⌋ + 327`, and value `out74 r (Σ v_i⁴) (ET74) (ET2_74)` with
`r = newt61 N (Z₁/Z₀)`. -/
theorem momProg74_24_nat (n K : ℕ) :
    ∃ pm : Prog (InM56 n) (OutK61 4), BstLean.Part41.heavyCount pm = 0 ∧
      (∀ (t : ℝ) (v : Fin n → ℝ) o,
        pm.eval (inRK t v) o = out74 (newt61 (newtN61 n) (a69 n K t)) (pw v 4) (ET74 n K t v)
          (ET2_74 n K t v) o) ∧
      pm.cost ≤ 11 * n + 167 * K + 4 * Nat.log 2 n + 327 := by
  have hC := hpv (eCx74 n K)
  rw [size_C74] at hC
  have h := hp_mapOut (hp_bind (hTab74 n K)
    (hp_seq (hp_keep (hB74 n K)) (hp_bind (hNewt74 n) hC))) sel74
  obtain ⟨p, hp, ep, cp⟩ := h
  refine ⟨p, clean_heavyCount hp, ?_, ?_⟩
  · intro t v o
    rw [ep]
    rcases o with u | l
    · simp [sel74, eCx74, out74, gB74, tab, st74, a69, inRK]
    · fin_cases l
      · simp [sel74, eCx74, out74]
      · simp [sel74, eCx74, out74, gB74, tab, st74, a69, inRK, pw, ET74, cK74]
        ring
      · simp [sel74, eCx74, out74, gB74, tab, st74, a69, inRK, pw, ET74, ET2_74, cK74]
        ring
  · refine cp.trans ?_
    have h1 : newtN61 n = Nat.log 2 n + 1 := rfl
    rw [h1]
    omega

end BstLean.Part74

#print axioms BstLean.Part74.momProg74_24_nat
