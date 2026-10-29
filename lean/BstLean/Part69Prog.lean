import BstLean.Part69Defs
import BstLean.Part56MomProg_Toolkit

/-!
# Part 69: a clean straight-line program for the weights `w69`

`momProg69_exists`: a program with no heavy constants, of cost linear in `K` and `n`, that maps
`inRK t v` to the weight vector `w69 n K t v`.

Construction: a table recurrence (Toolkit `hp_table`) computes `t^j/j!`, `U_j, U_{j+1}, U_{j+2}`
and the partial sums `Z_0, Z_1, Z_2` for `j ≤ K`; a second stage computes `a, b, q, r, n`; a third
stage evaluates the constant-size formulas `A69, H69, R69/𝒟`; outputs select per key.
-/

namespace BstLean.Part69

open BstLean.Cost BstLean.Part56 BstLean.Part56.MomProg

/-! ## Arithmetic expressions over the constants `0`, `1` -/

/-- Arithmetic expressions with variables in `α` and the constants `0`, `1`. -/
inductive Ex69p (α : Type) where
  | var : α → Ex69p α
  | zero : Ex69p α
  | one : Ex69p α
  | bin : Op → Ex69p α → Ex69p α → Ex69p α

namespace Ex69p

variable {α : Type}

/-- Value of an expression. -/
noncomputable def eval (x : α → ℝ) : Ex69p α → ℝ
  | var a => x a
  | zero => 0
  | one => 1
  | bin o e f => o.eval (eval x e) (eval x f)

/-- Number of operations of an expression (as a tree). -/
def size : Ex69p α → ℕ
  | var _ => 0
  | zero => 0
  | one => 0
  | bin _ e f => size e + size f + 1

instance : Add (Ex69p α) := ⟨bin .add⟩
instance : Sub (Ex69p α) := ⟨bin .sub⟩
instance : Mul (Ex69p α) := ⟨bin .mul⟩
instance : Div (Ex69p α) := ⟨bin .div⟩
instance : One (Ex69p α) := ⟨one⟩
instance : Zero (Ex69p α) := ⟨zero⟩

@[simp] lemma eval_var (x : α → ℝ) (a : α) : eval x (var a) = x a := rfl
@[simp] lemma eval_zero (x : α → ℝ) : eval x (0 : Ex69p α) = 0 := rfl
@[simp] lemma eval_one (x : α → ℝ) : eval x (1 : Ex69p α) = 1 := rfl
@[simp] lemma eval_add (x : α → ℝ) (e f : Ex69p α) : eval x (e + f) = eval x e + eval x f := rfl
@[simp] lemma eval_sub (x : α → ℝ) (e f : Ex69p α) : eval x (e - f) = eval x e - eval x f := rfl
@[simp] lemma eval_mul (x : α → ℝ) (e f : Ex69p α) : eval x (e * f) = eval x e * eval x f := rfl
@[simp] lemma eval_div (x : α → ℝ) (e f : Ex69p α) : eval x (e / f) = eval x e / eval x f := rfl

@[simp] lemma size_var (a : α) : size (var a) = 0 := rfl
@[simp] lemma size_zero : size (0 : Ex69p α) = 0 := rfl
@[simp] lemma size_one : size (1 : Ex69p α) = 0 := rfl
@[simp] lemma size_add (e f : Ex69p α) : size (e + f) = size e + size f + 1 := rfl
@[simp] lemma size_sub (e f : Ex69p α) : size (e - f) = size e + size f + 1 := rfl
@[simp] lemma size_mul (e f : Ex69p α) : size (e * f) = size e + size f + 1 := rfl
@[simp] lemma size_div (e f : Ex69p α) : size (e / f) = size e + size f + 1 := rfl

lemma hp (e : Ex69p α) : HasProg (fun x (_ : Unit) => e.eval x) e.size := by
  induction e with
  | var a =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.inp a) (fun _ => rfl)) (fun x u => rfl)
  | zero =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.cst (ι := α) 0) (fun _ => rfl))
      (fun x u => by simp [Arg.eval, eval])
  | one =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.cst (ι := α) 1) (fun _ => rfl))
      (fun x u => by simp [Arg.eval, eval])
  | bin o e f he hf => exact hp_op2 o he hf

lemma hpv {k : ℕ} (es : Fin k → Ex69p α) :
    HasProg (fun x o => (es o).eval x) (∑ o, (es o).size) :=
  hp_parS _ (fun o => hp (es o))

end Ex69p

open Ex69p

/-! ## The table: `t^j/j!`, `U_j, U_{j+1}, U_{j+2}`, `j+1`, `Z_0, Z_1, Z_2` (up to `j`), and
`n + 2(j+2)`, `2(j+2)+1` -/

/-- The state of the recurrence at step `j`. -/
noncomputable def st69p (n : ℕ) (x : InM56 n → ℝ) (j : ℕ) : Fin 10 → ℝ :=
  ![x (Sum.inl ()) ^ j / (j.factorial : ℝ), U69 n j, U69 n (j + 1), U69 n (j + 2), (j : ℝ) + 1,
    Z69 n j (x (Sum.inl ())) 0, Z69 n j (x (Sum.inl ())) 1, Z69 n j (x (Sum.inl ())) 2,
    (n : ℝ) + 2 * ((j : ℝ) + 2), 2 * ((j : ℝ) + 2) + 1]

/-- The initial state, from `N = n`. -/
def eInit69p : Fin 10 → Ex69p Unit :=
  let N : Ex69p Unit := var ()
  ![1, 1, 1 / N, (1 / N) * ((1 + 1 + 1) / (N + (1 + 1))), 1, 1, 1 / N,
    (1 / N) * ((1 + 1 + 1) / (N + (1 + 1))), N + (1 + 1 + 1 + 1), 1 + 1 + 1 + 1 + 1]

/-- One step of the recurrence, reading row `k` of the table. -/
def eStep69p (n k : ℕ) : Fin 10 → Ex69p (InM56 n ⊕ (ℕ × Fin 10)) :=
  let R : Fin 10 → Ex69p (InM56 n ⊕ (ℕ × Fin 10)) := fun i => var (Sum.inr (k, i))
  let T : Ex69p (InM56 n ⊕ (ℕ × Fin 10)) := var (Sum.inl (Sum.inl ()))
  let c := R 0 * T / R 4
  ![c, R 2, R 3, R 3 * R 9 / R 8, R 4 + 1, R 5 + c * R 2, R 6 + c * R 3,
    R 7 + c * (R 3 * R 9 / R 8), R 8 + (1 + 1), R 9 + (1 + 1)]

lemma U69_succ (n j : ℕ) :
    U69 n (j + 1) = U69 n j * ((2 * (j : ℝ) + 1) / ((n : ℝ) + 2 * (j : ℝ))) := by
  unfold U69; rw [Finset.prod_range_succ]

lemma c69_succ (T : ℝ) (j : ℕ) :
    T ^ (j + 1) / ((j + 1).factorial : ℝ) = T ^ j / (j.factorial : ℝ) * T / ((j : ℝ) + 1) := by
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.factorial_succ, pow_succ]; push_cast
  rw [div_mul_eq_mul_div, div_div, mul_comm ((j : ℝ) + 1)]

lemma Z69_succ (n j : ℕ) (T : ℝ) (l : ℕ) :
    Z69 n (j + 1) T l = Z69 n j T l +
      T ^ (j + 1) / ((j + 1).factorial : ℝ) * U69 n (j + 1 + l) := by
  unfold Z69; rw [Finset.sum_range_succ]

lemma hInit69p (n : ℕ) :
    HasProg (fun x => st69p n x 0) (n + ∑ o, (eInit69p o).size) := by
  have h := hp_seq (hp_nat (ι := InM56 n) n) (hpv eInit69p)
  refine hp_congr h ?_
  intro x i
  have u0 : U69 n 0 = 1 := by simp [U69]
  have u1 : U69 n 1 = 1 / (n : ℝ) := by simp [U69]
  have u2 : U69 n 2 = 1 / (n : ℝ) * (3 / ((n : ℝ) + 2)) := by
    simp [U69, Finset.prod_range_succ]; norm_num; rw [inv_mul_eq_div, div_div, mul_comm]
  have z : ∀ l, Z69 n 0 (x (Sum.inl ())) l = U69 n l := by intro l; simp [Z69]
  fin_cases i <;> simp [eInit69p, st69p, z, u0, u1, u2] <;> ring_nf <;> simp

lemma hStep69p (n k : ℕ) (x : InM56 n → ℝ) (i : Fin 10) :
    (eStep69p n k i).eval (Sum.elim x (tab (st69p n) k x)) = st69p n x (k + 1) i := by
  have e : ∀ j, (Sum.elim x (tab (st69p n) k x)) (Sum.inr (k, j)) = st69p n x k j := by
    intro j; simp [tab]
  fin_cases i
  · simp [eStep69p, e, st69p, c69_succ]
  · simp [eStep69p, e, st69p]
  · simp [eStep69p, e, st69p]
  · simp [eStep69p, e, st69p, U69_succ (j := k + 2)]; push_cast; ring
  · simp [eStep69p, e, st69p]
  · simp [eStep69p, e, st69p, Z69_succ, c69_succ]
  · simp [eStep69p, e, st69p, Z69_succ, c69_succ]
  · simp [eStep69p, e, st69p, Z69_succ, c69_succ, U69_succ (j := k + 2)]; left; ring
  · simp [eStep69p, e, st69p]; push_cast; ring
  · simp [eStep69p, e, st69p]; push_cast; ring

lemma size_step69p (n k : ℕ) : ∑ o, (eStep69p n k o).size = 23 := by
  simp [eStep69p, Fin.sum_univ_succ]

lemma size_init69p : ∑ o, (eInit69p o).size = 24 := by
  simp [eInit69p, Fin.sum_univ_succ]

lemma hTab69p (n K : ℕ) : HasProg (tab (st69p n) K) (n + 24 + 23 * K) := by
  have h0 := hInit69p n
  rw [size_init69p] at h0
  have h := hp_table (st69p n) (fun k y i => (eStep69p n k i).eval y) (n + 24) (fun _ => 23) h0 K
    (fun k _ => by have := hpv (eStep69p n k); rwa [size_step69p] at this)
    (fun k _ x i => hStep69p n k x i)
  exact hp_mono h (by simp; omega)

/-! ## Stage B: `a, b, q, r, n` -/

/-- Stage B values, from the inputs and the table. -/
noncomputable def gB69p (n K : ℕ) (y : InM56 n ⊕ (ℕ × Fin 10) → ℝ) : Fin 5 → ℝ :=
  ![y (Sum.inr (K, 6)) / y (Sum.inr (K, 5)), y (Sum.inr (K, 7)) / y (Sum.inr (K, 5)),
    ∑ i, y (Sum.inl (Sum.inr i)) ^ 4, ∑ i, y (Sum.inl (Sum.inr i)) ^ 6,
    y (Sum.inr (0, 8)) - 4]

lemma hB69p (n K : ℕ) : HasProg (gB69p n K) (10 * n + 6) := by
  have h := hp_parS (f := gB69p n K) ![1, 1, 4 * n, 6 * n, 4] (by
    intro o
    fin_cases o
    · exact hp_mono (hp_congr (hp ((var (Sum.inr (K, 6)) : Ex69p (InM56 n ⊕ (ℕ × Fin 10))) /
        var (Sum.inr (K, 5)))) (fun y u => by simp [gB69p])) (by simp)
    · exact hp_mono (hp_congr (hp ((var (Sum.inr (K, 7)) : Ex69p (InM56 n ⊕ (ℕ × Fin 10))) /
        var (Sum.inr (K, 5)))) (fun y u => by simp [gB69p])) (by simp)
    · have h := hp_sumF (f := fun (y : InM56 n ⊕ (ℕ × Fin 10) → ℝ) (i : Fin n) =>
          y (Sum.inl (Sum.inr i)) ^ 4) (c := 3) (fun i => by
        let X : Ex69p (InM56 n ⊕ (ℕ × Fin 10)) := var (Sum.inl (Sum.inr i))
        exact hp_mono (hp_congr (hp (X * X * (X * X))) (fun y u => by simp [X]; ring)) (by simp [X]))
      refine hp_mono (hp_congr h (fun y u => by simp [gB69p])) ?_
      simp; omega
    · have h := hp_sumF (f := fun (y : InM56 n ⊕ (ℕ × Fin 10) → ℝ) (i : Fin n) =>
          y (Sum.inl (Sum.inr i)) ^ 6) (c := 5) (fun i => by
        let X : Ex69p (InM56 n ⊕ (ℕ × Fin 10)) := var (Sum.inl (Sum.inr i))
        exact hp_mono (hp_congr (hp (X * X * X * (X * X * X))) (fun y u => by simp [X]; ring))
          (by simp [X]))
      refine hp_mono (hp_congr h (fun y u => by simp [gB69p])) ?_
      simp; omega
    · exact hp_mono (hp_congr (hp ((var (Sum.inr (0, 8)) : Ex69p (InM56 n ⊕ (ℕ × Fin 10))) -
        (1 + 1 + 1 + 1))) (fun y u => by simp [gB69p]; norm_num)) (by simp))
  refine hp_mono h ?_
  simp [Fin.sum_univ_succ]; omega

lemma gB69p_val (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) :
    gB69p n K (Sum.elim (inRK t v) (tab (st69p n) K (inRK t v))) =
      ![a69 n K t, b69 n K t, q69 v, r69 v, (n : ℝ)] := by
  funext o
  fin_cases o <;> simp [gB69p, tab, st69p, a69, b69, q69, r69, inRK]; ring

/-! ## Stage C: the constant-size formulas -/

/-- Stage C: outputs `0, 1, a, A, H, R/𝒟` from `(a, b, q, r, n)`. -/
def eC69p : Fin 6 → Ex69p (Fin 5) :=
  let a : Ex69p (Fin 5) := var 0
  let b : Ex69p (Fin 5) := var 1
  let q : Ex69p (Fin 5) := var 2
  let r : Ex69p (Fin 5) := var 3
  let N : Ex69p (Fin 5) := var 4
  let two : Ex69p (Fin 5) := 1 + 1
  let three : Ex69p (Fin 5) := 1 + 1 + 1
  let four : Ex69p (Fin 5) := two + two
  let six : Ex69p (Fin 5) := three + three
  let m := N - 1
  let Ew := q * a + (1 - q) * (1 - a) / m
  let Esw := q * b + (1 - q) * (a - b) / m
  let Ew2 := q * q * b + (two * q * (1 - q) + four * (r - q * q)) * (a - b) / m +
    ((1 - q) * (1 - q) + two * (q - two * r + q * q)) * (1 - two * a + b) / (m * (N + 1))
  let Eq4 := q * b + six * (1 - q) * (a - b) / m +
    three * (N - two + q) * (1 - two * a + b) / (m * (N + 1))
  let Esq := b + two * Esw + Ew2
  let A := (a + Ew) / (1 + q)
  let H := Esq / ((1 + q) * (1 + q))
  let R := three / two - a + Eq4 / two - Esq / (two * (1 + q))
  let DD := N * (N + 1) * (N + two) / two
  ![0, 1, a, A, H, R / DD]

lemma size_C69p : ∑ o, (eC69p o).size = 164 := by
  simp [eC69p, Fin.sum_univ_succ]

/-- The output selector, following the case split of `wF69`. -/
def sel69p (κ : KeyRK 2 2) : Fin 6 :=
  if (κ.1.2 : ℕ) = 0 then
    (if cnt69 κ 1 = 0 ∧ cnt69 κ 2 = 0 then 1
     else if cnt69 κ 1 = 0 ∧ cnt69 κ 2 = 1 then 3
     else if cnt69 κ 1 = 2 ∧ cnt69 κ 2 = 0 then 2
     else if cnt69 κ 1 = 0 ∧ cnt69 κ 2 = 2 then 4
     else 0)
  else if (κ.1.1 : ℕ) = 2 ∧ (κ.1.2 : ℕ) = 1 then 5
  else 0

lemma sel69p_val (n : ℕ) (a b q r : ℝ) (κ : KeyRK 2 2) :
    (eC69p (sel69p κ)).eval ![a, b, q, r, (n : ℝ)] = wF69 n a b q r κ := by
  unfold sel69p wF69 momC69
  split_ifs <;>
    simp [eC69p, A69, H69, R69, Ew69, Esw69, Ew2_69, Eq4_69, Esq69] <;> ring

/-! ## The program -/

/-- A clean program (no constants other than `0`, `1`) of cost `≤ 11 n + 23 K + 194` that maps
`inRK t v` to the weights `w69 n K t v`. -/
theorem momProg69_exists_nat (n K : ℕ) :
    ∃ pm : Prog (BstLean.Part56.InM56 n) (BstLean.Part56.KeyRK 2 2),
      BstLean.Part41.heavyCount pm = 0 ∧
      (∀ (t : ℝ) (v : Fin n → ℝ) κ, pm.eval (BstLean.Part56.inRK t v) κ = w69 n K t v κ) ∧
      pm.cost ≤ 11 * n + 23 * K + 194 := by
  have hC := hpv eC69p
  rw [size_C69p] at hC
  have h := hp_mapOut (hp_seq (hp_bind (hTab69p n K) (hB69p n K)) hC) sel69p
  obtain ⟨p, hp, ep, cp⟩ := h
  refine ⟨p, clean_heavyCount hp, ?_, by omega⟩
  intro t v κ
  rw [ep]
  simp only
  rw [gB69p_val]
  exact sel69p_val n _ _ _ _ κ

theorem momProg69_exists (n K : ℕ) (hn : 2 ≤ n) :
    ∃ pm : Prog (BstLean.Part56.InM56 n) (BstLean.Part56.KeyRK 2 2),
      BstLean.Part41.heavyCount pm = 0 ∧
      (∀ (t : ℝ) (v : Fin n → ℝ), 0 ≤ t → ∀ κ,
        pm.eval (BstLean.Part56.inRK t v) κ = w69 n K t v κ) ∧
      (pm.cost : ℝ) ≤ 100 * ((K : ℝ) + (n : ℝ) + 1) := by
  obtain ⟨pm, h1, h2, h3⟩ := momProg69_exists_nat n K
  refine ⟨pm, h1, fun t v _ κ => h2 t v κ, ?_⟩
  have h4 : pm.cost ≤ 100 * (K + n + 1) := by omega
  exact_mod_cast h4

end BstLean.Part69

#print axioms BstLean.Part69.momProg69_exists
