import BstLean.Part84Defs
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Part 84, helper `Fourth`: a fourth-moment constant of single-exponential size at every degree

`fourth84 : Fourth84 h (K84 h)` with `K84 h = (51/10)^(2h) = (2601/100)^h`.

Route. `HR c` is Mathlib's Hermite polynomial over `ℝ`; `He c x = (HR c).eval x` (`He_eq`).
`LG p = E p(x)` under `N(0,1)`. Gaussian integration by parts `LG (X p) = LG p'` (`LG_ibp`) and
`HR_{a+1} = X HR_a − HR_a'`, `HR_b' = b HR_{b−1}` give the recursion (`M4_rec`)
`M(a+1,b,c,d) = b M(a,b−1,c,d) + c M(a,b,c−1,d) + d M(a,b,c,d−1)` for
`M(a,b,c,d) = E He_a He_b He_c He_d`. Induction on `a+b+c+d`, with the largest index first, gives
`M(a,b,c,d)² ≤ 3^{a+b+c+d} a! b! c! d!` (`P4_all`), thus `E He_c⁴ ≤ (c!)² (3^c)²` (`He4_le_nine`).
The criterion `KCrit h (51/10) γ84` follows with `γ84 c = γ5 c` for `c ≤ 6` and `3^c` otherwise.

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part84

open MeasureTheory ProbabilityTheory Polynomial
open scoped Nat
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part62 (KCrit γ5 γ5_nonneg E4_le_γ5 fourth_moment_kappa He hco int_poly1' int_pow1')

/-! ## Hermite polynomials over `ℝ` -/

/-- Mathlib's probabilists' Hermite polynomial, over `ℝ`. -/
noncomputable def HR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

lemma HR_zero : HR 0 = 1 := by simp [HR]

lemma HR_succ (n : ℕ) : HR (n + 1) = X * HR n - derivative (HR n) := by
  simp [HR, hermite_succ, Polynomial.derivative_map]

lemma HR_deriv_succ (n : ℕ) : derivative (HR (n + 1)) = C ((n : ℝ) + 1) * HR n := by
  induction n with
  | zero => simp [HR_succ, HR_zero]
  | succ n ih =>
    rw [HR_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih, derivative_C_mul]
    have := HR_succ n
    rw [this]
    simp only [map_add, map_one, Nat.cast_add, Nat.cast_one]
    ring

lemma HR_deriv (b : ℕ) : derivative (HR b) = C (b : ℝ) * HR (b - 1) := by
  cases b with
  | zero => simp [HR_zero]
  | succ n => rw [HR_deriv_succ]; simp

lemma fact_two_mul (j : ℕ) : (2 * j)! = 2 ^ j * j ! * (2 * j - 1)‼ := by
  cases j with
  | zero => simp
  | succ k =>
    have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    have h2 := Nat.doubleFactorial_two_mul (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h2 ⊢
    rw [h1, h2]
    simp

lemma hco_eq (c b : ℕ) (hb : b ≤ c) : hco c b = (((hermite c).coeff b : ℤ) : ℝ) := by
  rw [coeff_hermite]
  have hev : Even (c + b) ↔ Even (c - b) := by
    rw [Nat.even_add, Nat.even_sub hb]
  unfold hco
  by_cases he : Even (c - b)
  · rw [if_pos ⟨hb, he⟩, if_pos (hev.mpr he)]
    obtain ⟨j, hj⟩ := he
    have h1 : (c - b) / 2 = j := by omega
    have h2 : c - b - 1 = 2 * j - 1 := by omega
    have hF : (c - b)! = 2 ^ j * j ! * (2 * j - 1)‼ := by
      rw [← fact_two_mul]; congr 1; omega
    have K : (2 * j - 1)‼ * c.choose b * (b ! * 2 ^ j * j !) = c ! := by
      rw [← Nat.choose_mul_factorial_mul_factorial hb, hF]; ring
    have KR := congrArg (Nat.cast : ℕ → ℝ) K
    push_cast at KR
    rw [h1, h2]
    push_cast
    rw [div_eq_iff (by positivity)]
    linear_combination (-(-1 : ℝ) ^ j) * KR
  · rw [if_neg (fun h => he h.2), if_neg (fun h => he (hev.mp h))]
    simp

lemma He_eq (c : ℕ) (x : ℝ) : He c x = (HR c).eval x := by
  have hdeg : (HR c).natDegree < c + 1 := by
    have := natDegree_map_le (f := Int.castRingHom ℝ) (p := hermite c)
    rw [natDegree_hermite] at this
    unfold HR; omega
  rw [eval_eq_sum_range' hdeg, He]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b ≤ c := by have := Finset.mem_range.mp hb; omega
  rw [hco_eq c b hb', HR, coeff_map]
  simp

/-! ## The Gaussian functional and integration by parts -/

/-- `LG p = E p(x)`, `x ∼ N(0,1)`. -/
noncomputable def LG (p : ℝ[X]) : ℝ := ∫ x, p.eval x ∂gaussianReal 0 1

lemma LG_add (p q : ℝ[X]) : LG (p + q) = LG p + LG q := by
  unfold LG; simp only [eval_add]
  exact integral_add (int_poly1' p) (int_poly1' q)

lemma LG_sub (p q : ℝ[X]) : LG (p - q) = LG p - LG q := by
  unfold LG; simp only [eval_sub]
  exact integral_sub (int_poly1' p) (int_poly1' q)

lemma LG_C_mul (a : ℝ) (p : ℝ[X]) : LG (C a * p) = a * LG p := by
  unfold LG; simp only [eval_mul, eval_C]
  exact integral_const_mul _ _

lemma LG_one : LG 1 = 1 := by
  unfold LG; simp

lemma LG_monomial (n : ℕ) (a : ℝ) : LG (monomial n a) = a * gaussMom n := by
  unfold LG; simp only [eval_monomial]
  rw [integral_const_mul, gaussMom_eq]

lemma gaussMom_succ (n : ℕ) : gaussMom (n + 1) = (n : ℝ) * gaussMom (n - 1) := by
  cases n with
  | zero => simp [gaussMom]
  | succ m =>
    show gaussMom (m + 2) = ((m + 1 : ℕ) : ℝ) * gaussMom m
    unfold gaussMom
    have h : Even (m + 2) ↔ Even m := by simp [Nat.even_add]
    simp only [h]
    split_ifs with hn
    · rw [show m + 2 - 1 = m + 1 by omega, Nat.doubleFactorial_add_one]
      push_cast
      rfl
    · ring

/-- Gaussian integration by parts on polynomials: `E x p(x) = E p'(x)`. -/
lemma LG_ibp (p : ℝ[X]) : LG (X * p) = LG (derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, LG_add, derivative_add, LG_add, hp, hq]
  | monomial n a =>
    rw [X_mul_monomial, derivative_monomial, LG_monomial, LG_monomial, gaussMom_succ]
    ring

lemma LG_HR_succ (a : ℕ) (G : ℝ[X]) : LG (HR (a + 1) * G) = LG (HR a * derivative G) := by
  have e : HR (a + 1) * G = X * (HR a * G) - derivative (HR a) * G := by rw [HR_succ]; ring
  rw [e, LG_sub, LG_ibp, derivative_mul, LG_add]
  ring

/-! ## The four-fold moments -/

/-- `M(a,b,c,d) = E He_a He_b He_c He_d`. -/
noncomputable def M4 (a b c d : ℕ) : ℝ := LG (HR a * HR b * HR c * HR d)

lemma M4_rec (a b c d : ℕ) : M4 (a + 1) b c d =
    b * M4 a (b - 1) c d + c * M4 a b (c - 1) d + d * M4 a b c (d - 1) := by
  unfold M4
  rw [show HR (a + 1) * HR b * HR c * HR d = HR (a + 1) * (HR b * HR c * HR d) by ring,
    LG_HR_succ, derivative_mul, derivative_mul, HR_deriv b, HR_deriv c, HR_deriv d,
    show HR a * ((C (b : ℝ) * HR (b - 1) * HR c + HR b * (C (c : ℝ) * HR (c - 1))) * HR d +
        HR b * HR c * (C (d : ℝ) * HR (d - 1))) =
      C (b : ℝ) * (HR a * HR (b - 1) * HR c * HR d) + C (c : ℝ) * (HR a * HR b * HR (c - 1) * HR d)
        + C (d : ℝ) * (HR a * HR b * HR c * HR (d - 1)) by ring,
    LG_add, LG_add, LG_C_mul, LG_C_mul, LG_C_mul]

/-- The bound `M(a,b,c,d)² ≤ 3^{a+b+c+d} a! b! c! d!`. -/
def P4 (a b c d : ℕ) : Prop :=
  M4 a b c d ^ 2 ≤ (3 : ℝ) ^ (a + b + c + d) * ((a ! : ℝ) * b ! * c ! * d !)

lemma P4_swap12 {a b c d : ℕ} (h : P4 b a c d) : P4 a b c d := by
  unfold P4 at h ⊢
  have e1 : M4 a b c d = M4 b a c d := by unfold M4; congr 1; ring
  rw [e1, show a + b + c + d = b + a + c + d by omega,
    show ((a ! : ℝ) * b ! * c ! * d !) = ((b ! : ℝ) * a ! * c ! * d !) by ring]
  exact h

lemma P4_swap13 {a b c d : ℕ} (h : P4 c b a d) : P4 a b c d := by
  unfold P4 at h ⊢
  have e1 : M4 a b c d = M4 c b a d := by unfold M4; congr 1; ring
  rw [e1, show a + b + c + d = c + b + a + d by omega,
    show ((a ! : ℝ) * b ! * c ! * d !) = ((c ! : ℝ) * b ! * a ! * d !) by ring]
  exact h

lemma P4_swap14 {a b c d : ℕ} (h : P4 d b c a) : P4 a b c d := by
  unfold P4 at h ⊢
  have e1 : M4 a b c d = M4 d b c a := by unfold M4; congr 1; ring
  rw [e1, show a + b + c + d = d + b + c + a by omega,
    show ((a ! : ℝ) * b ! * c ! * d !) = ((d ! : ℝ) * b ! * c ! * a !) by ring]
  exact h

lemma term_bd (k A : ℕ) (hb : k + 1 ≤ A) (m R : ℝ) (hR : 0 ≤ R) (h : m ^ 2 ≤ R * k !) :
    (((k + 1 : ℕ) : ℝ) * m) ^ 2 ≤ A * (R * ((k + 1)! : ℝ)) := by
  have hA : ((k + 1 : ℕ) : ℝ) ≤ A := by exact_mod_cast hb
  have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Nat.factorial_succ]
  push_cast at hA hk ⊢
  have h0 : (0 : ℝ) ≤ R * k ! := by positivity
  calc (((k : ℝ) + 1) * m) ^ 2 = ((k : ℝ) + 1) ^ 2 * m ^ 2 := by ring
    _ ≤ ((k : ℝ) + 1) ^ 2 * (R * k !) := by gcongr
    _ = ((k : ℝ) + 1) * (((k : ℝ) + 1) * (R * k !)) := by ring
    _ ≤ (A : ℝ) * (((k : ℝ) + 1) * (R * k !)) := by gcongr
    _ = _ := by ring

lemma P4_step (a b c d : ℕ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a)
    (ih : ∀ a' b' c' d', a' + b' + c' + d' < a + b + c + d → P4 a' b' c' d') : P4 a b c d := by
  cases a with
  | zero =>
    obtain rfl : b = 0 := by omega
    obtain rfl : c = 0 := by omega
    obtain rfl : d = 0 := by omega
    unfold P4 M4
    simp [HR_zero, LG_one]
  | succ a' =>
    unfold P4
    set Q : ℝ := (3 : ℝ) ^ (a' + 1 + b + c + d) * (((a' + 1)! : ℝ) * b ! * c ! * d !) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have t1 : ((b : ℝ) * M4 a' (b - 1) c d) ^ 2 ≤ Q / 9 := by
      cases b with
      | zero => simp; positivity
      | succ k =>
        have h := ih a' k c d (by omega)
        unfold P4 at h
        have := term_bd k (a' + 1) hb (M4 a' k c d)
          ((3 : ℝ) ^ (a' + k + c + d) * ((a' ! : ℝ) * c ! * d !)) (by positivity)
          (by rw [show (3 : ℝ) ^ (a' + k + c + d) * ((a' ! : ℝ) * c ! * d !) * k ! =
            (3 : ℝ) ^ (a' + k + c + d) * ((a' ! : ℝ) * k ! * c ! * d !) by ring]; exact h)
        refine this.trans (le_of_eq ?_)
        rw [hQ, show a' + 1 + (k + 1) + c + d = (a' + k + c + d) + 2 by ring, pow_add,
          Nat.factorial_succ a']
        push_cast; ring
    have t2 : ((c : ℝ) * M4 a' b (c - 1) d) ^ 2 ≤ Q / 9 := by
      cases c with
      | zero => simp; positivity
      | succ k =>
        have h := ih a' b k d (by omega)
        unfold P4 at h
        have := term_bd k (a' + 1) hc (M4 a' b k d)
          ((3 : ℝ) ^ (a' + b + k + d) * ((a' ! : ℝ) * b ! * d !)) (by positivity)
          (by rw [show (3 : ℝ) ^ (a' + b + k + d) * ((a' ! : ℝ) * b ! * d !) * k ! =
            (3 : ℝ) ^ (a' + b + k + d) * ((a' ! : ℝ) * b ! * k ! * d !) by ring]; exact h)
        refine this.trans (le_of_eq ?_)
        rw [hQ, show a' + 1 + b + (k + 1) + d = (a' + b + k + d) + 2 by ring, pow_add,
          Nat.factorial_succ a']
        push_cast; ring
    have t3 : ((d : ℝ) * M4 a' b c (d - 1)) ^ 2 ≤ Q / 9 := by
      cases d with
      | zero => simp; positivity
      | succ k =>
        have h := ih a' b c k (by omega)
        unfold P4 at h
        have := term_bd k (a' + 1) hd (M4 a' b c k)
          ((3 : ℝ) ^ (a' + b + c + k) * ((a' ! : ℝ) * b ! * c !)) (by positivity)
          (by rw [show (3 : ℝ) ^ (a' + b + c + k) * ((a' ! : ℝ) * b ! * c !) * k ! =
            (3 : ℝ) ^ (a' + b + c + k) * ((a' ! : ℝ) * b ! * c ! * k !) by ring]; exact h)
        refine this.trans (le_of_eq ?_)
        rw [hQ, show a' + 1 + b + c + (k + 1) = (a' + b + c + k) + 2 by ring, pow_add,
          Nat.factorial_succ a']
        push_cast; ring
    rw [M4_rec]
    nlinarith [sq_nonneg ((b : ℝ) * M4 a' (b - 1) c d - (c : ℝ) * M4 a' b (c - 1) d),
      sq_nonneg ((b : ℝ) * M4 a' (b - 1) c d - (d : ℝ) * M4 a' b c (d - 1)),
      sq_nonneg ((c : ℝ) * M4 a' b (c - 1) d - (d : ℝ) * M4 a' b c (d - 1))]

theorem P4_all : ∀ (s a b c d : ℕ), a + b + c + d = s → P4 a b c d := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro a b c d hs
    have ih : ∀ a' b' c' d', a' + b' + c' + d' < a + b + c + d → P4 a' b' c' d' :=
      fun a' b' c' d' h => IH _ (hs ▸ h) a' b' c' d' rfl
    have hmax : (b ≤ a ∧ c ≤ a ∧ d ≤ a) ∨ (a ≤ b ∧ c ≤ b ∧ d ≤ b) ∨ (b ≤ c ∧ a ≤ c ∧ d ≤ c) ∨
        (b ≤ d ∧ c ≤ d ∧ a ≤ d) := by omega
    rcases hmax with h | h | h | h
    · exact P4_step a b c d h.1 h.2.1 h.2.2 ih
    · exact P4_swap12 (P4_step b a c d h.1 h.2.1 h.2.2
        (fun a' b' c' d' hh => ih a' b' c' d' (by omega)))
    · exact P4_swap13 (P4_step c b a d h.1 h.2.1 h.2.2
        (fun a' b' c' d' hh => ih a' b' c' d' (by omega)))
    · exact P4_swap14 (P4_step d b c a h.1 h.2.1 h.2.2
        (fun a' b' c' d' hh => ih a' b' c' d' (by omega)))

/-- **(★)** `E He_c⁴ ≤ (c!)² (3^c)²`, for every `c`. -/
theorem He4_le_nine (c : ℕ) :
    ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤ (c ! : ℝ) ^ 2 * ((3 : ℝ) ^ c) ^ 2 := by
  have e : ∫ x, He c x ^ 4 ∂gaussianReal 0 1 = M4 c c c c := by
    unfold M4 LG
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [eval_mul, ← He_eq]; ring
  rw [e]
  have h := P4_all _ c c c c rfl
  unfold P4 at h
  have h2 : M4 c c c c ^ 2 ≤ ((c ! : ℝ) ^ 2 * ((3 : ℝ) ^ c) ^ 2) ^ 2 := by
    refine h.trans (le_of_eq ?_)
    rw [show c + c + c + c = c * 4 by ring, pow_mul]; ring
  exact (abs_le_of_sq_le_sq' h2 (by positivity)).2

/-! ## The criterion at `κ = 51/10` -/

/-- `γ84 c = γ5 c` for `c ≤ 6` and `3^c` otherwise. -/
noncomputable def γ84 (c : ℕ) : ℝ := if c ≤ 6 then γ5 c else (3 : ℝ) ^ c

lemma γ84_nonneg (c : ℕ) : 0 ≤ γ84 c := by
  unfold γ84; split
  · exact γ5_nonneg c
  · positivity

lemma term84_nonneg (c : ℕ) : 0 ≤ γ84 c / (51 / 10 : ℝ) ^ c :=
  div_nonneg (γ84_nonneg c) (by positivity)

lemma sum84_six : ∑ c ∈ Finset.Icc 1 6, γ84 c / (51 / 10 : ℝ) ^ c +
    17 / 7 * (10 / 17 : ℝ) ^ 7 ≤ 7 / 10 := by
  norm_num [Finset.sum_Icc_succ_top, γ84, γ5]

lemma sum84_ge (h : ℕ) (hh : 6 ≤ h) : ∑ c ∈ Finset.Icc 1 h, γ84 c / (51 / 10 : ℝ) ^ c +
    17 / 7 * (10 / 17 : ℝ) ^ (h + 1) ≤ 7 / 10 := by
  induction h, hh using Nat.le_induction with
  | base => exact sum84_six
  | succ h hh ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have e : γ84 (h + 1) / (51 / 10 : ℝ) ^ (h + 1) = (10 / 17 : ℝ) ^ (h + 1) := by
      unfold γ84
      rw [if_neg (by omega), ← div_pow]; norm_num
    rw [e, pow_succ (10 / 17 : ℝ) (h + 1)]
    linarith

lemma sum84_le (h : ℕ) : ∑ c ∈ Finset.Icc 1 h, γ84 c / (51 / 10 : ℝ) ^ c ≤ 7 / 10 := by
  rcases le_total 6 h with hh | hh
  · have := sum84_ge h hh
    have : (0 : ℝ) ≤ 17 / 7 * (10 / 17 : ℝ) ^ (h + 1) := by positivity
    linarith
  · have hle : ∑ c ∈ Finset.Icc 1 h, γ84 c / (51 / 10 : ℝ) ^ c ≤
        ∑ c ∈ Finset.Icc 1 6, γ84 c / (51 / 10 : ℝ) ^ c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hh)
        (fun c _ _ => term84_nonneg c)
    have := sum84_six
    have : (0 : ℝ) ≤ 17 / 7 * (10 / 17 : ℝ) ^ 7 := by positivity
    linarith

theorem kcrit84 (h : ℕ) : KCrit h (51 / 10) γ84 := by
  refine ⟨by norm_num, γ84_nonneg, fun c hc => ?_, ?_⟩
  · have hc1 := (Finset.mem_Icc.mp hc).1
    unfold γ84
    split
    · next h6 => exact E4_le_γ5 c (Finset.mem_Icc.mpr ⟨hc1, h6⟩)
    · exact He4_le_nine c
  · have h0 : 0 ≤ ∑ c ∈ Finset.Icc 1 h, γ84 c / (51 / 10 : ℝ) ^ c :=
      Finset.sum_nonneg fun c _ => term84_nonneg c
    have h1 := sum84_le h
    nlinarith

/-! ## The headline -/

/-- The fourth-moment constant `(51/10)^(2h)`. -/
noncomputable def K84 (h : ℕ) : ℝ := (51 / 10 : ℝ) ^ (2 * h)

lemma K84_nonneg (h : ℕ) : 0 ≤ K84 h := by unfold K84; positivity

lemma K84_pos (h : ℕ) : 0 < K84 h := by unfold K84; positivity

lemma K84_eq (h : ℕ) : K84 h = (2601 / 100 : ℝ) ^ h := by
  unfold K84; rw [pow_mul]; norm_num

/-- **Fourth moment at every degree**: `E P⁴ ≤ (51/10)^(2h) (E P²)²` for `deg P ≤ h`. -/
theorem fourth84 (h : ℕ) : Fourth84 h (K84 h) := by
  intro ι _ P hP
  exact fourth_moment_kappa h (51 / 10) γ84 (kcrit84 h) ι P hP

end BstLean.Part84
