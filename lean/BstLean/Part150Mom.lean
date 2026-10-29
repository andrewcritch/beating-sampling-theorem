import BstLean.Part150Defs

/-!
# Part 150, item 1: the moments and the characteristic function of the binomial atoms

Role: `delegations/statements/p150-spec.md`, item 1. Paper source: `onW45-opus-prover.md` §1,
`onW25c-cx.md` §3.

* `walkMean_const`, `walkMean_add`, `walkMean_const_mul`: `walkMean` is a mean.
* `walkMean_lin`, `walkMean_sq`, `walkMean_pow4`: `E(S_J + a) = a`, `E(S_J + a)² = J + a²`,
  `E(S_J + a)⁴ = 3J² − 2J + 6Ja² + a⁴`.
* `walkMean_cos`, `walkMean_sin`: `E cos(u S_J + c) = cos(u)^J cos c`,
  `E sin(u S_J + c) = cos(u)^J sin c`.
* `binW_sum`, `binMean_id`, `binMean_sq`, `binMean_pow4`: total weight `1`, mean `0`, second
  moment `1`, fourth moment `3 − 2/J` (`J ≥ 1`).
* `binMean_cos`, `binMean_sin`: `E cos(t(x + Z_J)) = cos(tx)·cos(t/√J)^J` and the same for `sin`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open Finset

theorem walkMean_add (J : ℕ) (f g : ℝ → ℝ) :
    walkMean J (fun k => f k + g k) = walkMean J f + walkMean J g := by
  unfold walkMean
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem walkMean_sub (J : ℕ) (f g : ℝ → ℝ) :
    walkMean J (fun k => f k - g k) = walkMean J f - walkMean J g := by
  unfold walkMean
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem walkMean_const_mul (J : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    walkMean J (fun k => c * f k) = c * walkMean J f := by
  unfold walkMean
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

theorem walkMean_const (J : ℕ) (c : ℝ) : walkMean J (fun _ => c) = c := by
  induction J with
  | zero => simp [walkMean]
  | succ J ih => rw [walkMean_succ, ih]; ring

theorem walkMean_mono (J : ℕ) {f g : ℝ → ℝ} (h : ∀ k, f k ≤ g k) : walkMean J f ≤ walkMean J g := by
  unfold walkMean
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h _) (by positivity)

theorem walkMean_lin (J : ℕ) (a : ℝ) : walkMean J (fun k => k + a) = a := by
  induction J generalizing a with
  | zero => simp [walkMean]
  | succ J ih =>
    rw [walkMean_succ]
    have e1 : (fun k : ℝ => k + 1 + a) = fun k => k + (1 + a) := by funext k; ring
    have e2 : (fun k : ℝ => k - 1 + a) = fun k => k + (a - 1) := by funext k; ring
    rw [e1, e2, ih, ih]; ring

theorem walkMean_sq (J : ℕ) (a : ℝ) : walkMean J (fun k => (k + a) ^ 2) = J + a ^ 2 := by
  induction J generalizing a with
  | zero => simp [walkMean]
  | succ J ih =>
    rw [walkMean_succ]
    have e1 : (fun k : ℝ => (k + 1 + a) ^ 2) = fun k => (k + (1 + a)) ^ 2 := by funext k; ring
    have e2 : (fun k : ℝ => (k - 1 + a) ^ 2) = fun k => (k + (a - 1)) ^ 2 := by funext k; ring
    rw [e1, e2, ih, ih]; push_cast; ring

theorem walkMean_pow4 (J : ℕ) (a : ℝ) :
    walkMean J (fun k => (k + a) ^ 4) = 3 * (J : ℝ) ^ 2 - 2 * J + 6 * J * a ^ 2 + a ^ 4 := by
  induction J generalizing a with
  | zero => simp [walkMean]
  | succ J ih =>
    rw [walkMean_succ]
    have e1 : (fun k : ℝ => (k + 1 + a) ^ 4) = fun k => (k + (1 + a)) ^ 4 := by funext k; ring
    have e2 : (fun k : ℝ => (k - 1 + a) ^ 4) = fun k => (k + (a - 1)) ^ 4 := by funext k; ring
    rw [e1, e2, ih, ih]; push_cast; ring

theorem walkMean_cos (J : ℕ) (u c : ℝ) :
    walkMean J (fun k => Real.cos (u * k + c)) = Real.cos u ^ J * Real.cos c := by
  induction J generalizing c with
  | zero => simp [walkMean]
  | succ J ih =>
    rw [walkMean_succ]
    have e1 : (fun k : ℝ => Real.cos (u * (k + 1) + c)) = fun k => Real.cos (u * k + (c + u)) := by
      funext k; ring_nf
    have e2 : (fun k : ℝ => Real.cos (u * (k - 1) + c)) = fun k => Real.cos (u * k + (c - u)) := by
      funext k; ring_nf
    rw [e1, e2, ih, ih, Real.cos_add, Real.cos_sub]; ring

theorem walkMean_sin (J : ℕ) (u c : ℝ) :
    walkMean J (fun k => Real.sin (u * k + c)) = Real.cos u ^ J * Real.sin c := by
  induction J generalizing c with
  | zero => simp [walkMean]
  | succ J ih =>
    rw [walkMean_succ]
    have e1 : (fun k : ℝ => Real.sin (u * (k + 1) + c)) = fun k => Real.sin (u * k + (c + u)) := by
      funext k; ring_nf
    have e2 : (fun k : ℝ => Real.sin (u * (k - 1) + c)) = fun k => Real.sin (u * k + (c - u)) := by
      funext k; ring_nf
    rw [e1, e2, ih, ih, Real.sin_add, Real.sin_sub]; ring

/-! ## The binomial mean -/

theorem binMean_add (J : ℕ) (f g : ℝ → ℝ) :
    binMean J (fun z => f z + g z) = binMean J f + binMean J g := by
  simp only [binMean_eq_walk]; exact walkMean_add J _ _

theorem binMean_sub (J : ℕ) (f g : ℝ → ℝ) :
    binMean J (fun z => f z - g z) = binMean J f - binMean J g := by
  simp only [binMean_eq_walk]; exact walkMean_sub J _ _

theorem binMean_const_mul (J : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    binMean J (fun z => c * f z) = c * binMean J f := by
  simp only [binMean_eq_walk]; exact walkMean_const_mul J c _

theorem binMean_const (J : ℕ) (c : ℝ) : binMean J (fun _ => c) = c := by
  simp only [binMean_eq_walk]; exact walkMean_const J c

theorem binMean_mono (J : ℕ) {f g : ℝ → ℝ} (h : ∀ z, f z ≤ g z) : binMean J f ≤ binMean J g := by
  simp only [binMean_eq_walk]; exact walkMean_mono J fun k => h _

theorem binMean_abs_le (J : ℕ) (f : ℝ → ℝ) : |binMean J f| ≤ binMean J (fun z => |f z|) := by
  unfold binMean
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
  rw [abs_mul, abs_of_nonneg (binW_nonneg J j)]

/-- The total weight is `1`. -/
theorem binW_sum (J : ℕ) : ∑ j ∈ range (J + 1), binW J j = 1 := by
  have h := binMean_const J 1
  simpa [binMean] using h

/-- Mean `0`. -/
theorem binMean_id (J : ℕ) : binMean J (fun z => z) = 0 := by
  rw [binMean_eq_walk]
  have e : (fun k : ℝ => k / √(J : ℝ)) = fun k => (√(J : ℝ))⁻¹ * (k + 0) := by
    funext k; rw [add_zero, div_eq_inv_mul]
  rw [e, walkMean_const_mul, walkMean_lin, mul_zero]

/-- Second moment `1`. -/
theorem binMean_sq {J : ℕ} (hJ : 1 ≤ J) : binMean J (fun z => z ^ 2) = 1 := by
  rw [binMean_eq_walk]
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have e : (fun k : ℝ => (k / √(J : ℝ)) ^ 2) = fun k => (J : ℝ)⁻¹ * (k + 0) ^ 2 := by
    funext k; rw [add_zero, div_pow, Real.sq_sqrt hJ0.le]; ring
  rw [e, walkMean_const_mul, walkMean_sq]
  field_simp
  ring

/-- Fourth moment `3 − 2/J`. -/
theorem binMean_pow4 {J : ℕ} (hJ : 1 ≤ J) : binMean J (fun z => z ^ 4) = 3 - 2 / (J : ℝ) := by
  rw [binMean_eq_walk]
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have e : (fun k : ℝ => (k / √(J : ℝ)) ^ 4) = fun k => ((J : ℝ) ^ 2)⁻¹ * (k + 0) ^ 4 := by
    funext k
    have : √(J : ℝ) ^ 4 = (J : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hJ0.le]
    rw [add_zero, div_pow, this]; ring
  rw [e, walkMean_const_mul, walkMean_pow4]
  field_simp
  ring

/-- `E (a + s Z_J) = a`. -/
theorem binMean_affine (J : ℕ) (a s : ℝ) : binMean J (fun z => a + s * z) = a := by
  rw [binMean_add, binMean_const, binMean_const_mul, binMean_id]; ring

/-- `E (a + s Z_J)² = a² + s²`. -/
theorem binMean_affine_sq {J : ℕ} (hJ : 1 ≤ J) (a s : ℝ) :
    binMean J (fun z => (a + s * z) ^ 2) = a ^ 2 + s ^ 2 := by
  have e : (fun z : ℝ => (a + s * z) ^ 2) = fun z => (a ^ 2 + (2 * a * s) * z) + s ^ 2 * z ^ 2 := by
    funext z; ring
  rw [e, binMean_add, binMean_add, binMean_const, binMean_const_mul, binMean_const_mul,
    binMean_id, binMean_sq hJ]; ring

/-- The characteristic function, cosine part: `E cos(t(x + Z_J)) = cos(tx)·cos(t/√J)^J`. -/
theorem binMean_cos (J : ℕ) (t x : ℝ) :
    binMean J (fun z => Real.cos (t * (x + z))) = Real.cos (t / √(J : ℝ)) ^ J * Real.cos (t * x) := by
  rw [binMean_eq_walk, ← walkMean_cos]
  congr 1; funext k; congr 1; ring

/-- The characteristic function, sine part: `E sin(t(x + Z_J)) = sin(tx)·cos(t/√J)^J`. -/
theorem binMean_sin (J : ℕ) (t x : ℝ) :
    binMean J (fun z => Real.sin (t * (x + z))) = Real.cos (t / √(J : ℝ)) ^ J * Real.sin (t * x) := by
  rw [binMean_eq_walk, ← walkMean_sin]
  congr 1; funext k; congr 1; ring

end BstLean.Part150
