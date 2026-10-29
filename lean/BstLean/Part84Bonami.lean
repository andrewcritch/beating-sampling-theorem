import BstLean.Part84Fourth
import BstLean.Part82Hyper

/-!
# Part 84, helper `Bonami`: the sharp fourth-moment constant `9^h` at every degree

`fourth84_nine : Fourth84 h (9 ^ h)`: for a polynomial `P` of total degree `≤ h` in independent
standard Gaussian variables, `E P⁴ ≤ 9^h (E P²)²`.

Route. The induction on the variables is that of `Part82.HypAux.fm3_main` (thus of
`Part62HyperK.fmK_main`), with the one-dimensional inequality at `κ = 3` proved at EVERY degree
(`oneD9`): for `q = Σ_c u_c He_c`, `E q⁴ ≤ (Σ_c 3^c c! u_c²)²`.

One-dimensional proof (`oneD_poly`). Write `a_k = E q^{(k)} = k! u_k`, `t_k = a_k² / k!`.
* Parseval (`parseval`, from `Part62.fischer_sq`): `E p² = Σ_c (E p^{(c)})² / c!`.
* Applied to `p = q²` with the Leibniz rule:
  `E q⁴ = Σ_m (Σ_{k ≤ m} C(m,k) E[q^{(m−k)} q^{(k)}])² / m!`.
* Cauchy–Schwarz: `E[q^{(i)} q^{(j)}]² ≤ E (q^{(i)})² · E (q^{(j)})²`, and Parseval again gives
  `E (q^{(i)})² = i! N_i` with `N_i = Σ_k C(k,i) t_k`.
* Cauchy–Schwarz in `k` with weights `C(m,k)` (`Σ_k C(m,k) = 2^m`, `C(m,k) (m−k)! k! = m!`):
  the `m`-th term is `≤ 2^m Σ_{k ≤ m} N_{m−k} N_k`.
* Summation: `E q⁴ ≤ (Σ_i 2^i N_i)² = (Σ_k t_k Σ_i C(k,i) 2^i)² = (Σ_k 3^k t_k)²`.

The helper lemmas `gpi` … `gauss_rename_integral` are copied from `Part62HyperK.lean` /
`Part82Hyper.lean`, where they are private.

No `sorry`, `native_decide` or `axiom`.
-/

set_option linter.unusedSimpArgs false

namespace BstLean.Part84.Bonami

open MeasureTheory ProbabilityTheory Polynomial
open scoped Nat
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part36 (lap1 lap1_eq_zero)
open BstLean.Part62 (fischer_sq int_pow1' int_poly1' cs1)

/-! ## The Gaussian functional: linearity, Cauchy–Schwarz -/

lemma LG_zero : LG 0 = 0 := by unfold LG; simp

lemma LG_sum {β : Type*} (S : Finset β) (f : β → ℝ[X]) : LG (∑ b ∈ S, f b) = ∑ b ∈ S, LG (f b) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [LG_zero]
  | insert b S hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, LG_add, ih]

lemma LG_cs (p r : ℝ[X]) : LG (p * r) ^ 2 ≤ LG (p * p) * LG (r * r) := by
  have h := cs1 (fun x => p.eval x) (fun x => r.eval x)
    (by have := int_poly1' (p * p); simpa [sq] using this)
    (by have := int_poly1' (r * r); simpa [sq] using this)
    (by have := int_poly1' (p * r); simpa using this)
  unfold LG
  simpa [sq] using h

lemma LG_sq_nonneg (p : ℝ[X]) : 0 ≤ LG (p * p) := by
  unfold LG
  exact integral_nonneg fun x => by rw [eval_mul]; exact mul_self_nonneg _

/-! ## Hermite coefficients as expectations of derivatives -/

/-- `E (x^b)^{(c)} = c! · lap1 b c`. -/
lemma LG_deriv_pow (b c : ℕ) : LG (derivative^[c] (X ^ b : ℝ[X])) = (c ! : ℝ) * lap1 b c := by
  rw [iterate_derivative_X_pow_eq_smul, smul_eq_C_mul, LG_C_mul, ← monomial_one_right_eq_X_pow,
    LG_monomial, one_mul]
  unfold lap1 gaussMom
  by_cases hcb : c ≤ b
  · by_cases he : Even (b - c)
    · rw [if_pos he, if_pos ⟨hcb, he⟩]
      obtain ⟨j, hj⟩ := he
      have h1 : (b - c) / 2 = j := by omega
      have h2 : b - c - 1 = 2 * j - 1 := by omega
      have hF : (b - c)! = 2 ^ j * j ! * (2 * j - 1)‼ := by
        rw [← fact_two_mul]; congr 1; omega
      have K := Nat.factorial_mul_descFactorial hcb
      rw [hF] at K
      have KR := congrArg (Nat.cast : ℕ → ℝ) K
      push_cast at KR
      rw [h1, h2]
      have hc0 : (c ! : ℝ) ≠ 0 := by positivity
      have hj0 : ((2 : ℝ) ^ j * (j ! : ℝ)) ≠ 0 := by positivity
      field_simp
      linear_combination KR
    · rw [if_neg he, if_neg (fun h => he h.2)]; simp
  · have hn : ¬ (c ≤ b ∧ Even (b - c)) := fun h => hcb h.1
    have : b.descFactorial c = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hn, this]

/-- `E p^{(c)} = c! Σ_b p_b lap1 b c`. -/
lemma LG_deriv (p : ℝ[X]) (D : ℕ) (hp : p.natDegree < D) (c : ℕ) :
    LG (derivative^[c] p) = (c ! : ℝ) * ∑ b ∈ Finset.range D, p.coeff b * lap1 b c := by
  have e : derivative^[c] p =
      ∑ b ∈ Finset.range D, C (p.coeff b) * derivative^[c] (X ^ b : ℝ[X]) := by
    conv_lhs => rw [as_sum_range' p D hp]
    rw [iterate_derivative_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← C_mul_X_pow_eq_monomial, iterate_derivative_C_mul]
  rw [e, LG_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LG_C_mul, LG_deriv_pow]; ring

/-- **Parseval**: `E p² = Σ_c (E p^{(c)})² / c!`. -/
lemma parseval (p : ℝ[X]) (s : ℕ) (hp : p.natDegree ≤ s) :
    LG (p * p) = ∑ c ∈ Finset.range (s + 1), LG (derivative^[c] p) ^ 2 / (c ! : ℝ) := by
  have h := fischer_sq s (fun b => p.coeff b)
  have e : LG (p * p) = ∫ x, (∑ b ∈ Finset.range (s + 1), p.coeff b * x ^ b) ^ 2 ∂gaussianReal 0 1 := by
    unfold LG
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [eval_mul, ← sq, eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  rw [e, h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LG_deriv p (s + 1) (Nat.lt_succ_of_le hp) c]
  have hc0 : (c ! : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Two summation lemmas -/

lemma shift_sum (D i : ℕ) (G : ℕ → ℝ) (hG : ∀ c, D ≤ i + c → G c = 0) :
    ∑ k ∈ Finset.range D, (if i ≤ k then G (k - i) else 0) = ∑ c ∈ Finset.range D, G c := by
  have h1 := Finset.sum_range_add (fun k => if i ≤ k then G (k - i) else 0) i D
  have h2 := Finset.sum_range_add (fun k => if i ≤ k then G (k - i) else 0) D i
  rw [add_comm i D, h2] at h1
  have z1 : ∑ x ∈ Finset.range i, (if i ≤ D + x then G (D + x - i) else 0) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with h
    · exact hG _ (by omega)
    · rfl
  have z2 : ∑ k ∈ Finset.range i, (if i ≤ k then G (k - i) else 0) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [if_neg (by have := Finset.mem_range.mp hx; omega)]
  have z3 : ∑ x ∈ Finset.range D, (if i ≤ i + x then G (i + x - i) else 0) =
      ∑ c ∈ Finset.range D, G c :=
    Finset.sum_congr rfl fun x _ => by rw [if_pos (by omega), Nat.add_sub_cancel_left]
  rw [z1, z2, z3] at h1
  linarith

lemma conv_le (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (M : ℕ) :
    ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range (m + 1), g (m - k) * g k ≤
      (∑ i ∈ Finset.range M, g i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_sigma']
  have hinj : Set.InjOn (fun x : (_ : ℕ) × ℕ => (x.1 - x.2, x.2))
      ((Finset.range M).sigma fun m => Finset.range (m + 1) : Finset ((_ : ℕ) × ℕ)) := by
    rintro ⟨m, k⟩ hx ⟨m', k'⟩ hx' h
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range] at hx hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    have : m = m' := by omega
    subst this; rfl
  rw [← Finset.sum_image (f := fun y : ℕ × ℕ => g y.1 * g y.2) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_range, Finset.mem_product] at hy ⊢
    obtain ⟨⟨m, k⟩, ⟨hm, hk⟩, rfl⟩ := hy
    simp only at hm hk ⊢
    omega
  · intro y _ _
    exact mul_nonneg (hg _) (hg _)

lemma three_pow_sum (k M : ℕ) (hk : k < M) :
    ∑ i ∈ Finset.range M, (2 : ℝ) ^ i * (k.choose i : ℝ) = 3 ^ k := by
  have h := add_pow (2 : ℝ) 1 k
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at h
  rw [h]
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show k + 1 ≤ M by omega))]
  · exact Finset.sum_congr rfl fun i _ => by ring
  · intro i _ hi
    have : k < i := by simp at hi; omega
    rw [Nat.choose_eq_zero_of_lt this]; simp


/-! ## The one-dimensional inequality at `κ = 3`, every degree -/

/-- **One-dimensional (2,4)-hypercontractivity, polynomial form**: with `a_k = E q^{(k)}`,
`E q⁴ ≤ (Σ_k 3^k a_k² / k!)²`. -/
theorem oneD_poly (q : ℝ[X]) (s : ℕ) (hq : q.natDegree ≤ s) :
    LG ((q * q) * (q * q)) ≤
      (∑ k ∈ Finset.range (s + 1), (3 : ℝ) ^ k * (LG (derivative^[k] q) ^ 2 / (k ! : ℝ))) ^ 2 := by
  set a : ℕ → ℝ := fun k => LG (derivative^[k] q) with ha
  set t : ℕ → ℝ := fun k => a k ^ 2 / (k ! : ℝ) with ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => by simp only [ht]; positivity
  set N : ℕ → ℝ := fun i => ∑ k ∈ Finset.range (s + 1), (k.choose i : ℝ) * t k with hN
  have hN0 : ∀ i, 0 ≤ N i := fun i =>
    Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (ht0 k)
  have ha0 : ∀ k, s < k → a k = 0 := fun k hk => by
    simp only [ha]; rw [iterate_derivative_eq_zero (lt_of_le_of_lt hq hk), LG_zero]
  -- second moments of the derivatives
  have hn2 : ∀ i, LG (derivative^[i] q * derivative^[i] q) = (i ! : ℝ) * N i := by
    intro i
    rw [parseval (derivative^[i] q) s
      ((natDegree_iterate_derivative q i).trans ((Nat.sub_le _ _).trans hq))]
    have e1 : ∀ c, derivative^[c] (derivative^[i] q) = derivative^[c + i] q :=
      fun c => (Function.iterate_add_apply _ c i q).symm
    simp_rw [e1]
    rw [← shift_sum (s + 1) i (fun c => a (c + i) ^ 2 / (c ! : ℝ))
      (fun c hc => by rw [ha0 _ (by omega)]; simp)]
    simp only [hN]; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hik
    · rw [Nat.sub_add_cancel hik]
      have K := Nat.choose_mul_factorial_mul_factorial hik
      have KR := congrArg (Nat.cast : ℕ → ℝ) K
      push_cast at KR
      simp only [ht]
      have h1 : ((k - i)! : ℝ) ≠ 0 := by positivity
      have h2 : (k ! : ℝ) ≠ 0 := by positivity
      rw [← KR]
      have h3 : (k.choose i : ℝ) ≠ 0 := by
        have := Nat.choose_pos hik; positivity
      have h4 : (i ! : ℝ) ≠ 0 := by positivity
      field_simp
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hL : ∀ i j, LG (derivative^[i] q * derivative^[j] q) ^ 2 ≤
      ((i ! : ℝ) * N i) * ((j ! : ℝ) * N j) := by
    intro i j; rw [← hn2, ← hn2]; exact LG_cs _ _
  -- the `m`-th Hermite coefficient of `q²`
  have hm : ∀ m, LG (derivative^[m] (q * q)) ^ 2 / (m ! : ℝ) ≤
      ∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ (m - k) * N (m - k)) * ((2 : ℝ) ^ k * N k) := by
    intro m
    have e : LG (derivative^[m] (q * q)) = ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * LG (derivative^[m - k] q * derivative^[k] q) := by
      rw [iterate_derivative_mul, LG_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [nsmul_eq_mul, ← C_eq_natCast, LG_C_mul]
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range (m + 1))
      (r := fun k => (m.choose k : ℝ) * LG (derivative^[m - k] q * derivative^[k] q))
      (f := fun k => (m.choose k : ℝ))
      (g := fun k => (m.choose k : ℝ) * LG (derivative^[m - k] q * derivative^[k] q) ^ 2)
      (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => le_of_eq (by ring))
    have h2 : ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) = 2 ^ m := by
      exact_mod_cast Nat.sum_range_choose m
    have h3 : ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * LG (derivative^[m - k] q * derivative^[k] q) ^ 2 ≤
        (m ! : ℝ) * ∑ k ∈ Finset.range (m + 1), N (m - k) * N k := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
      have K := Nat.choose_mul_factorial_mul_factorial hk'
      have KR := congrArg (Nat.cast : ℕ → ℝ) K
      push_cast at KR
      calc (m.choose k : ℝ) * LG (derivative^[m - k] q * derivative^[k] q) ^ 2
          ≤ (m.choose k : ℝ) * ((((m - k)! : ℝ) * N (m - k)) * ((k ! : ℝ) * N k)) :=
            mul_le_mul_of_nonneg_left (hL _ _) (by positivity)
        _ = _ := by rw [← KR]; ring
    rw [e, div_le_iff₀ (by positivity)]
    calc _ ≤ _ := hcs
      _ ≤ 2 ^ m * ((m ! : ℝ) * ∑ k ∈ Finset.range (m + 1), N (m - k) * N k) := by
          rw [h2]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
        have : (2 : ℝ) ^ m = 2 ^ (m - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
        rw [this]; ring
  -- Parseval for `q²`
  have hdeg : (q * q).natDegree ≤ 2 * s := natDegree_mul_le.trans (by omega)
  rw [parseval (q * q) (2 * s) hdeg]
  calc ∑ c ∈ Finset.range (2 * s + 1), LG (derivative^[c] (q * q)) ^ 2 / (c ! : ℝ)
      ≤ ∑ m ∈ Finset.range (2 * s + 1), ∑ k ∈ Finset.range (m + 1),
          ((2 : ℝ) ^ (m - k) * N (m - k)) * ((2 : ℝ) ^ k * N k) :=
        Finset.sum_le_sum fun m _ => hm m
    _ ≤ (∑ i ∈ Finset.range (2 * s + 1), (2 : ℝ) ^ i * N i) ^ 2 :=
        conv_le (fun i => (2 : ℝ) ^ i * N i) (fun i => mul_nonneg (by positivity) (hN0 i)) _
    _ = _ := by
      congr 1
      simp only [hN, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← three_pow_sum k (2 * s + 1) (by have := Finset.mem_range.mp hk; omega),
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- **The one-dimensional weighted fourth moment at `κ = 3`, every degree**, in the form of
`Part62.oneD_weighted`: for `q = Σ_{b ≤ s} ρ_b x^b` and `u_c = Σ_b ρ_b lap1 b c`,
`E q⁴ ≤ (Σ_{c ≤ s} 3^c c! u_c²)²`. -/
theorem oneD9 (s : ℕ) (ρ : ℕ → ℝ) :
    ∫ x, (∑ b ∈ Finset.range (s + 1), ρ b * x ^ b) ^ 4 ∂gaussianReal 0 1 ≤
      (∑ c ∈ Finset.range (s + 1), (3 : ℝ) ^ c * (c.factorial : ℝ) *
        (∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c) ^ 2) ^ 2 := by
  set q : ℝ[X] := ∑ b ∈ Finset.range (s + 1), C (ρ b) * X ^ b with hq
  have hdeg : q.natDegree ≤ s := by
    apply natDegree_sum_le_of_forall_le
    intro b hb
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hb; omega)
  have hcoeff : ∀ b ∈ Finset.range (s + 1), q.coeff b = ρ b := by
    intro b hb
    simp only [hq, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hne; simp [hne.symm]
    · intro h; exact absurd hb h
  have hev : ∀ x : ℝ, q.eval x = ∑ b ∈ Finset.range (s + 1), ρ b * x ^ b := by
    intro x; simp [hq, eval_finsetSum]
  have h := oneD_poly q s hdeg
  have e : LG ((q * q) * (q * q)) =
      ∫ x, (∑ b ∈ Finset.range (s + 1), ρ b * x ^ b) ^ 4 ∂gaussianReal 0 1 := by
    unfold LG
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [eval_mul, hev]; ring
  rw [← e]
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LG_deriv q (s + 1) (by omega) c, Finset.sum_congr rfl (fun b hb => by rw [hcoeff b hb])]
  have hc0 : (c ! : ℝ) ≠ 0 := by positivity
  field_simp

end BstLean.Part84.Bonami

namespace BstLean.Part84.Bonami

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part36 (lap1 lap1_eq_zero)
open BstLean.Part62 (fischer_sq int_pow1')
open BstLean.Part82.HypAux (κ3)

/-! ## The induction on the variables (as in `Part82.HypAux.fm3_main`, every degree) -/

private lemma gpi {κ : Type*} [Fintype κ] (P : MvPolynomial κ ℝ) (r : ℕ) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ r) (stdGauss κ) := by
  have := gauss_poly_integrable (P ^ r); simpa only [map_pow] using this

/-- Cauchy–Schwarz for Gaussian polynomials. -/
private lemma poly_cs {κ : Type*} [Fintype κ] (U V : MvPolynomial κ ℝ) :
    (∫ z, MvPolynomial.eval z U * MvPolynomial.eval z V ∂stdGauss κ) ^ 2 ≤
      (∫ z, (MvPolynomial.eval z U) ^ 2 ∂stdGauss κ) * (∫ z, (MvPolynomial.eval z V) ^ 2 ∂stdGauss κ) := by
  have hUV : Integrable (fun z => MvPolynomial.eval z U * MvPolynomial.eval z V) (stdGauss κ) := by
    have := gauss_poly_integrable (U * V); simpa only [map_mul] using this
  have hquad (t : ℝ) : 0 ≤ (∫ z, (MvPolynomial.eval z U) ^ 2 ∂stdGauss κ) * (t * t) +
      (2 * ∫ z, MvPolynomial.eval z U * MvPolynomial.eval z V ∂stdGauss κ) * t +
      (∫ z, (MvPolynomial.eval z V) ^ 2 ∂stdGauss κ) := by
    have h : 0 ≤ ∫ z, (t * MvPolynomial.eval z U + MvPolynomial.eval z V) ^ 2 ∂stdGauss κ :=
      integral_nonneg fun z => sq_nonneg _
    have he : (fun z => (t * MvPolynomial.eval z U + MvPolynomial.eval z V) ^ 2) = fun z =>
        (t ^ 2 * (MvPolynomial.eval z U) ^ 2 + (2 * t) * (MvPolynomial.eval z U * MvPolynomial.eval z V)) +
          (MvPolynomial.eval z V) ^ 2 := by funext z; ring
    have i1 : Integrable (fun z => t ^ 2 * (MvPolynomial.eval z U) ^ 2) (stdGauss κ) :=
      (gpi U 2).const_mul _
    have i2 : Integrable (fun z => (2 * t) * (MvPolynomial.eval z U * MvPolynomial.eval z V))
      (stdGauss κ) := hUV.const_mul _
    have i12 : Integrable (fun z => t ^ 2 * (MvPolynomial.eval z U) ^ 2 +
      (2 * t) * (MvPolynomial.eval z U * MvPolynomial.eval z V)) (stdGauss κ) := i1.add i2
    rw [he, integral_add i12 (gpi V 2), integral_add i1 i2, integral_const_mul,
      integral_const_mul] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

private noncomputable def splitQ {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (b : ℕ) : MvPolynomial ι ℝ :=
  ∑ m ∈ P.support.filter (fun m => m none = b), MvPolynomial.monomial m.some (P.coeff m)

private lemma splitQ_degree {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (s b : ℕ) (hdeg : P.totalDegree ≤ s) :
    (splitQ P b).totalDegree ≤ s - b := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  obtain ⟨hm, hb⟩ := Finset.mem_filter.mp hm
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have hsum := m.sum_option_index (fun _ k => k) (by simp) (by simp)
  have hle := (MvPolynomial.le_totalDegree hm).trans hdeg
  simp only [hb] at hsum
  simp only [Function.id_def]
  omega

private lemma splitQ_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (s : ℕ) (hdeg : P.totalDegree ≤ s) (z : ι → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun o => o.elim x z) P =
      ∑ b ∈ Finset.range (s + 1), x ^ b * MvPolynomial.eval z (splitQ P b) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [MvPolynomial.eval_sum]
  have hmono : ∀ m ∈ P.support, MvPolynomial.eval (fun o => o.elim x z)
      (MvPolynomial.monomial m (P.coeff m)) =
        x ^ m none * (P.coeff m * (m.some.prod fun i k => z i ^ k)) := by
    intro m _
    have hp := m.prod_option_index (fun o k => (o.elim x z) ^ k) (by simp) (by simp [pow_add])
    simp only [MvPolynomial.eval_monomial]
    rw [hp]
    simp only [Option.elim_none, Option.elim_some]
    ring
  rw [Finset.sum_congr rfl hmono]
  simp only [splitQ, MvPolynomial.eval_sum, MvPolynomial.eval_monomial, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m => m none) (t := Finset.range (s + 1))]
  · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m hm => ?_
    rw [(Finset.mem_filter.mp hm).2]
  · intro m hm
    have hsum := m.sum_option_index (fun _ k => k) (by simp) (by simp)
    have hle := (MvPolynomial.le_totalDegree hm).trans hdeg
    rw [Finset.mem_range]
    omega

/-- Fubini on `stdGauss (Option ι) = stdGauss ι ⊗ N(0,1)`. -/
private lemma option_integral {ι : Type*} [Fintype ι] (Q : MvPolynomial (Option ι) ℝ) :
    (∫ z, MvPolynomial.eval z Q ∂stdGauss (Option ι)) =
      ∫ z, ∫ x : ℝ, MvPolynomial.eval (fun o => o.elim x z) Q ∂gaussianReal 0 1 ∂stdGauss ι := by
  let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
  have hm : ((stdGauss ι).prod (gaussianReal 0 1)).map e = stdGauss (Option ι) :=
    Measure.pi_map_piOptionEquivProd (fun _ => gaussianReal 0 1)
  have hi := gauss_poly_integrable Q
  rw [← hm] at hi ⊢
  have hip := (integrable_map_equiv e _).mp hi
  change Integrable (fun p => MvPolynomial.eval (e p) Q) ((stdGauss ι).prod (gaussianReal 0 1)) at hip
  rw [integral_map_equiv, integral_prod _ hip]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with x
  have he : e (z, x) = (fun o => o.elim x z) := by
    funext i
    cases i <;> rfl
  rw [he]


private lemma option_inner_integrable {ι : Type*} [Fintype ι] (Q : MvPolynomial (Option ι) ℝ) :
    Integrable (fun z => ∫ x : ℝ, MvPolynomial.eval (fun o => o.elim x z) Q ∂gaussianReal 0 1)
      (stdGauss ι) := by
  let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
  have hm : ((stdGauss ι).prod (gaussianReal 0 1)).map e = stdGauss (Option ι) :=
    Measure.pi_map_piOptionEquivProd (fun _ => gaussianReal 0 1)
  have hi := gauss_poly_integrable Q
  rw [← hm] at hi
  have hip := (integrable_map_equiv e _).mp hi
  change Integrable (fun p => MvPolynomial.eval (e p) Q) ((stdGauss ι).prod (gaussianReal 0 1)) at hip
  have := hip.integral_prod_left
  have he : ∀ z x, e (z, x) = (fun o => o.elim x z) := fun z x => by
    funext i
    cases i <;> rfl
  simp_rw [he] at this
  exact this

private lemma gauss_rename_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (P : MvPolynomial κ ℝ) (r : ℕ) :
    (∫ z, (MvPolynomial.eval z (MvPolynomial.rename e.symm P)) ^ r ∂stdGauss ι) =
      ∫ z, (MvPolynomial.eval z P) ^ r ∂stdGauss κ := by
  simp_rw [MvPolynomial.eval_rename]
  have hh := (measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e).integral_comp'
    (fun z => (MvPolynomial.eval z P) ^ r)
  have he (z : ι → ℝ) : MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e z = z ∘ e.symm := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [MeasurableEquiv.piCongrLeft_apply_apply]
  simpa only [he, stdGauss] using hh


lemma fm9_main :
    ∀ (ι : Type) [Fintype ι], ∀ [DecidableEq ι] (s : ℕ),
    ∀ P : MvPolynomial ι ℝ, P.totalDegree ≤ s →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        (κ3 ^ 2) ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ κ3 ^ 2 := by norm_num [κ3]
  apply Fintype.induction_empty_option (P := fun ι => ∀ [DecidableEq ι] (s : ℕ),
    ∀ P : MvPolynomial ι ℝ, P.totalDegree ≤ s →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        (κ3 ^ 2) ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2)
  · intro α β instβ e ih instDec s P hdeg
    let : Fintype α := Fintype.ofEquiv β e.symm
    classical
    have hh := ih s (MvPolynomial.rename e.symm P)
      ((MvPolynomial.totalDegree_rename_le _ _).trans hdeg)
    simpa only [gauss_rename_integral] using hh
  · intro instDec s P hdeg
    have hp : P = MvPolynomial.C (P.coeff 0) := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      subst m
      simp
    rw [hp]
    simp only [MvPolynomial.eval_C, integral_const, probReal_univ, one_smul]
    exact le_of_eq (by ring) |>.trans
      (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hk1))
  · intro α instα ih instDec s P hdeg
    classical
    have hκ30 : 0 ≤ κ3 := by norm_num [κ3]
    have hκ3pow : ∀ m : ℕ, κ3 ^ (2 * m) = (κ3 ^ 2) ^ m := fun m => pow_mul κ3 2 m
    set R : ℕ → MvPolynomial α ℝ := fun c =>
      ∑ b ∈ Finset.range (s + 1), MvPolynomial.C (lap1 b c) * splitQ P b with hR
    have hRdeg : ∀ c, c ≤ s → (R c).totalDegree ≤ s - c := by
      intro c hc
      apply MvPolynomial.totalDegree_finsetSum_le
      intro b hb
      by_cases hbc : b < c
      · rw [lap1_eq_zero (Or.inl hbc)]; simp
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact (splitQ_degree P s b hdeg).trans (by omega)
    have hRev : ∀ (z : α → ℝ) c, MvPolynomial.eval z (R c) =
        ∑ b ∈ Finset.range (s + 1), MvPolynomial.eval z (splitQ P b) * lap1 b c := by
      intro z c
      simp only [hR, map_sum, map_mul, MvPolynomial.eval_C]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hPx : ∀ (z : α → ℝ) (x : ℝ), MvPolynomial.eval (fun o => o.elim x z) P =
        ∑ b ∈ Finset.range (s + 1), MvPolynomial.eval z (splitQ P b) * x ^ b := by
      intro z x
      rw [splitQ_eval P s hdeg]
      exact Finset.sum_congr rfl fun b _ => by ring
    set Y2 : ℕ → ℝ := fun c => ∫ z, (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α with hY2
    have hY20 : ∀ c, 0 ≤ Y2 c := fun c => integral_nonneg fun _ => sq_nonneg _
    -- second moment
    have h2 : ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss (Option α) =
        ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c := by
      have h := option_integral (P ^ 2)
      simp only [map_pow] at h
      rw [h]
      have hin : ∀ z : α → ℝ, ∫ x, (MvPolynomial.eval (fun o => o.elim x z) P) ^ 2 ∂gaussianReal 0 1 =
          ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * (MvPolynomial.eval z (R c)) ^ 2 := by
        intro z
        simp_rw [hPx, hRev]
        exact fischer_sq s (fun b => MvPolynomial.eval z (splitQ P b))
      simp_rw [hin]
      rw [integral_finsetSum _ fun c _ => (gpi _ 2).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
    -- fourth moment, one variable at a time
    set w : ℕ → ℝ := fun c => κ3 ^ c * (c.factorial : ℝ) with hw
    have hw0 : ∀ c, 0 ≤ w c := fun c => by simp only [hw]; positivity
    set Q : MvPolynomial α ℝ :=
      (∑ c ∈ Finset.range (s + 1), MvPolynomial.C (w c) * R c ^ 2) ^ 2 with hQ
    have hQev : ∀ z : α → ℝ, MvPolynomial.eval z Q =
        (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 := by
      intro z; simp [hQ, map_sum]
    have h4 : ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss (Option α) ≤
        ∫ z, (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 ∂stdGauss α := by
      have h := option_integral (P ^ 4)
      simp only [map_pow] at h
      rw [h]
      have hiQ : Integrable (fun z : α → ℝ =>
          (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2) (stdGauss α) := by
        have := gauss_poly_integrable Q
        simpa only [hQev] using this
      have hiL := option_inner_integrable (P ^ 4)
      simp only [map_pow] at hiL
      refine integral_mono hiL hiQ fun z => ?_
      simp only
      simp_rw [hPx]
      refine (oneD9 s (fun b => MvPolynomial.eval z (splitQ P b))).trans
        (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hRev]
    -- pairwise bound
    have hpair : ∀ a ∈ Finset.range (s + 1), ∀ c ∈ Finset.range (s + 1),
        ∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α ≤
          (κ3 ^ (s - a) * Y2 a) * (κ3 ^ (s - c) * Y2 c) := by
      intro a ha c hc
      have ha' : a ≤ s := by have := Finset.mem_range.mp ha; omega
      have hc' : c ≤ s := by have := Finset.mem_range.mp hc; omega
      have hIa := ih (s - a) (R a) (hRdeg a ha')
      have hIc := ih (s - c) (R c) (hRdeg c hc')
      have hcs := poly_cs (R a ^ 2) (R c ^ 2)
      simp only [map_pow] at hcs
      have e4 : ∀ (Rr : MvPolynomial α ℝ), (fun z => ((MvPolynomial.eval z) Rr ^ 2) ^ 2) =
          fun z => (MvPolynomial.eval z Rr) ^ 4 := fun Rr => by funext z; ring
      rw [e4, e4] at hcs
      have hsq : (∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α) ^ 2
          ≤ ((κ3 ^ (s - a) * Y2 a) * (κ3 ^ (s - c) * Y2 c)) ^ 2 := by
        refine hcs.trans ?_
        have h4a : 0 ≤ ∫ z, (MvPolynomial.eval z (R a)) ^ 4 ∂stdGauss α :=
          integral_nonneg fun _ => by positivity
        have e : ((κ3 ^ (s - a) * Y2 a) * (κ3 ^ (s - c) * Y2 c)) ^ 2 =
            ((κ3 ^ 2) ^ (s - a) * Y2 a ^ 2) * ((κ3 ^ 2) ^ (s - c) * Y2 c ^ 2) := by
          rw [← hκ3pow, ← hκ3pow]; ring
        rw [e]
        exact mul_le_mul hIa hIc (integral_nonneg fun _ => by positivity) (by positivity)
      exact (abs_le_of_sq_le_sq' hsq (by have := hY20 a; have := hY20 c; positivity)).2
    -- expand and close
    have hexp : ∫ z, (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 ∂stdGauss α
        = ∑ a ∈ Finset.range (s + 1), ∑ c ∈ Finset.range (s + 1), (w a * w c) *
          ∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α := by
      have e : ∀ z : α → ℝ, (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 =
          ∑ a ∈ Finset.range (s + 1), ∑ c ∈ Finset.range (s + 1), (w a * w c) *
            ((MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2) := by
        intro z; rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      have hi : ∀ a c, Integrable (fun z : α → ℝ =>
          (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2) (stdGauss α) := by
        intro a c
        have := gauss_poly_integrable (R a ^ 2 * R c ^ 2)
        simpa only [map_mul, map_pow] using this
      simp_rw [e]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => (hi a c).const_mul _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun c _ => (hi a c).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
    have hbound : ∑ a ∈ Finset.range (s + 1), ∑ c ∈ Finset.range (s + 1), (w a * w c) *
          ∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α ≤
        (∑ c ∈ Finset.range (s + 1), w c * (κ3 ^ (s - c) * Y2 c)) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
      have := mul_le_mul_of_nonneg_left (hpair a ha c hc) (mul_nonneg (hw0 a) (hw0 c))
      refine this.trans (le_of_eq ?_)
      ring
    have hfold : ∑ c ∈ Finset.range (s + 1), w c * (κ3 ^ (s - c) * Y2 c) =
        κ3 ^ s * ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' : c ≤ s := by have := Finset.mem_range.mp hc; omega
      have : κ3 ^ c * κ3 ^ (s - c) = κ3 ^ s := by rw [← pow_add]; congr 1; omega
      simp only [hw]
      rw [← this]; ring
    rw [h2]
    calc ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss (Option α)
        ≤ _ := h4
      _ = _ := hexp
      _ ≤ _ := hbound
      _ = (κ3 ^ s * ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c) ^ 2 := by rw [hfold]
      _ = (κ3 ^ 2) ^ s * (∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm s 2, hκ3pow]


/-- **The sharp Bonami fourth-moment constant at every degree**: `E P⁴ ≤ 9^h (E P²)²` for a
polynomial `P` of total degree `≤ h` in independent standard Gaussian variables. -/
theorem _root_.BstLean.Part84.fourth84_nine (h : ℕ) : Fourth84 h ((9 : ℝ) ^ h) := by
  intro ι _ P hP
  classical
  have hh := fm9_main ι h P hP
  have e : ((κ3 : ℝ) ^ 2) = 9 := by norm_num [κ3]
  rwa [e] at hh

end BstLean.Part84.Bonami
