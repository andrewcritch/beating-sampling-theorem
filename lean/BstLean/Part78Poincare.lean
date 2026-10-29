import BstLean.Part78Defs
import BstLean.Part48Var
import BstLean.Part62Gram

/-!
# Part 78: the Gaussian Poincaré inequality for polynomials

`poincareMv : PoincareMv`, that is `Var P ≤ Σ_α E (∂_α P)²` under `stdGauss ι`.

Induction on the variables (`Fintype.induction_empty_option`). In the step, the new variable is
expanded in the Hermite basis with `Part62.fischer_sq`:
`E_x P(x,z)² = Σ_c c! R_c(z)²`, `E_x P = R_0`, `E_x (∂_x P)² = Σ_c c! (c+1)² R_{c+1}²`,
`E_x (∂_i P)² = Σ_c c! (∂_i R_c)²`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part78

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part36 (lap1 lap1_eq_zero lap1_zero)
open BstLean.Part62 (fischer_sq int_pow1')

private lemma gpi {κ : Type*} [Fintype κ] (P : MvPolynomial κ ℝ) (r : ℕ) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ r) (stdGauss κ) := by
  have := gauss_poly_integrable (P ^ r); simpa only [map_pow] using this

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

private lemma lap1_lower (b c : ℕ) :
    (c + 1 : ℝ) * lap1 (b + 1) (c + 1) = (b + 1 : ℝ) * lap1 b c := by
  unfold lap1
  simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]
  split_ifs with h
  · rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hc : (c.factorial : ℝ) ≠ 0 := by positivity
    have hs : (((b - c) / 2).factorial : ℝ) ≠ 0 := by positivity
    have hp : (2 : ℝ) ^ ((b - c) / 2) ≠ 0 := by positivity
    have hc1 : (c + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  · simp

/-! ## The new variable as a polynomial variable -/

section alg
variable {α : Type*}

open MvPolynomial in
private lemma opt_eval_sum (P : MvPolynomial (Option α) ℝ) (N : ℕ)
    (hN : (optionEquivLeft ℝ α P).natDegree ≤ N) (z : α → ℝ) (x : ℝ) :
    eval (fun o => o.elim x z) P =
      ∑ b ∈ Finset.range (N + 1), eval z ((optionEquivLeft ℝ α P).coeff b) * x ^ b := by
  rw [optionEquivLeft_elim_eval, Polynomial.eval_eq_sum_range' (n := N + 1)
    (lt_of_le_of_lt (Polynomial.natDegree_map_le) (by omega))]
  simp [Polynomial.coeff_map]

open MvPolynomial in
private lemma opt_pderiv_none (P : MvPolynomial (Option α) ℝ) :
    optionEquivLeft ℝ α (pderiv none P) = Polynomial.derivative (optionEquivLeft ℝ α P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p o hp =>
    cases o with
    | none => simp [Derivation.leibniz, hp]; ring
    | some j => simp [Derivation.leibniz, hp, pderiv_X]; ring

open MvPolynomial in
private lemma opt_pderiv_some (i : α) (P : MvPolynomial (Option α) ℝ) (b : ℕ) :
    (optionEquivLeft ℝ α (pderiv (some i) P)).coeff b =
      pderiv i ((optionEquivLeft ℝ α P).coeff b) := by
  classical
  induction P using MvPolynomial.induction_on generalizing b with
  | C a => simp [Polynomial.coeff_C]; split_ifs <;> simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p o hp =>
    cases o with
    | none =>
      cases b with
      | zero => simp [Derivation.leibniz, pderiv_X]
      | succ b => simp [Derivation.leibniz, pderiv_X, hp]
    | some j =>
      simp [Derivation.leibniz, pderiv_X, hp, Polynomial.coeff_mul_C, Pi.single_apply]
      split_ifs <;> simp

end alg

/-! ## The induction -/

private lemma poincare_aux : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι - (∫ z, (MvPolynomial.eval z P) ^ 1 ∂stdGauss ι) ^ 2 ≤
      ∑ a, ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv a P)) ^ 2 ∂stdGauss ι := by
  apply Fintype.induction_empty_option (P := fun ι => ∀ P : MvPolynomial ι ℝ,
    ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι - (∫ z, (MvPolynomial.eval z P) ^ 1 ∂stdGauss ι) ^ 2 ≤
      ∑ a, ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv a P)) ^ 2 ∂stdGauss ι)
  · intro α β instβ e ih P
    let : Fintype α := Fintype.ofEquiv β e.symm
    have hh := ih (MvPolynomial.rename e.symm P)
    rw [gauss_rename_integral, gauss_rename_integral] at hh
    refine hh.trans (le_of_eq ?_)
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MvPolynomial.pderiv_rename e.symm.injective, gauss_rename_integral]
  · intro P
    have hp : P = MvPolynomial.C (P.coeff 0) := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      subst m
      simp
    rw [hp]
    simp
  · intro α instα ih P
    classical
    set p := MvPolynomial.optionEquivLeft ℝ α P with hp
    set N := p.natDegree with hN
    set R : ℕ → MvPolynomial α ℝ := fun c =>
      ∑ b ∈ Finset.range (N + 1), MvPolynomial.C (lap1 b c) * p.coeff b with hR
    have hRev : ∀ (z : α → ℝ) c, MvPolynomial.eval z (R c) =
        ∑ b ∈ Finset.range (N + 1), MvPolynomial.eval z (p.coeff b) * lap1 b c := by
      intro z c
      simp only [hR, map_sum, map_mul, MvPolynomial.eval_C]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hPx : ∀ (z : α → ℝ) (x : ℝ), MvPolynomial.eval (fun o => o.elim x z) P =
        ∑ b ∈ Finset.range (N + 1), MvPolynomial.eval z (p.coeff b) * x ^ b :=
      fun z x => opt_eval_sum P N le_rfl z x
    set Y : ℕ → ℝ := fun c => ∫ z, (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α with hY
    have hY0 : ∀ c, 0 ≤ Y c := fun c => integral_nonneg fun _ => sq_nonneg _
    -- second moment
    have h2 : ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss (Option α) =
        ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) * Y c := by
      have h := option_integral (P ^ 2)
      simp only [map_pow] at h
      rw [h]
      have hin : ∀ z : α → ℝ, ∫ x, (MvPolynomial.eval (fun o => o.elim x z) P) ^ 2 ∂gaussianReal 0 1 =
          ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) * (MvPolynomial.eval z (R c)) ^ 2 := by
        intro z
        simp_rw [hPx, hRev]
        exact fischer_sq N (fun b => MvPolynomial.eval z (p.coeff b))
      simp_rw [hin]
      rw [integral_finsetSum _ fun c _ => (gpi _ 2).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
    -- mean
    have h1 : ∫ z, (MvPolynomial.eval z P) ^ 1 ∂stdGauss (Option α) =
        ∫ z, (MvPolynomial.eval z (R 0)) ^ 1 ∂stdGauss α := by
      simp only [pow_one]
      rw [option_integral P]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      simp_rw [hPx, hRev]
      rw [integral_finsetSum _ fun b _ => (int_pow1' b).const_mul _]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul, gaussMom_eq, lap1_zero]
    -- derivative in the new variable
    have hD0 : ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv none P)) ^ 2 ∂stdGauss (Option α) =
        ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) * ((c + 1 : ℝ) ^ 2 * Y (c + 1)) := by
      have h := option_integral ((MvPolynomial.pderiv none P) ^ 2)
      simp only [map_pow] at h
      rw [h]
      have hin : ∀ z : α → ℝ, ∫ x, (MvPolynomial.eval (fun o => o.elim x z)
          (MvPolynomial.pderiv none P)) ^ 2 ∂gaussianReal 0 1 =
          ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) *
            ((c + 1 : ℝ) ^ 2 * (MvPolynomial.eval z (R (c + 1))) ^ 2) := by
        intro z
        have hx : ∀ x : ℝ, MvPolynomial.eval (fun o => o.elim x z) (MvPolynomial.pderiv none P) =
            ∑ b ∈ Finset.range (N + 1),
              (MvPolynomial.eval z (p.coeff (b + 1)) * (b + 1 : ℝ)) * x ^ b := by
          intro x
          rw [opt_eval_sum _ N (by
            rw [opt_pderiv_none]; exact (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _))]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [opt_pderiv_none, Polynomial.coeff_derivative]
          simp only [map_mul, map_add, map_natCast, map_one]
          rfl
        simp_rw [hx]
        rw [fischer_sq]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        rw [← mul_pow]
        congr 1
        have hsh : MvPolynomial.eval z (R (c + 1)) = ∑ b ∈ Finset.range (N + 1),
            MvPolynomial.eval z (p.coeff (b + 1)) * lap1 (b + 1) (c + 1) := by
          rw [hRev]
          have h1 := Finset.sum_range_succ'
            (fun b => MvPolynomial.eval z (p.coeff b) * lap1 b (c + 1)) (N + 1)
          have h2 := Finset.sum_range_succ
            (fun b => MvPolynomial.eval z (p.coeff b) * lap1 b (c + 1)) (N + 1)
          simp only [lap1_eq_zero (a := 0) (c := c + 1) (Or.inl (by omega)), mul_zero,
            add_zero] at h1
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < N + 1 by omega),
            map_zero, zero_mul, add_zero] at h2
          rw [← h2, h1]
        rw [hsh, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have := lap1_lower b c
        linear_combination (-(MvPolynomial.eval z (p.coeff (b + 1)))) * this
      simp_rw [hin]
      rw [integral_finsetSum _ fun c _ => ((gpi _ 2).const_mul _).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul, integral_const_mul]
    -- derivative in an old variable
    have hDi : ∀ i : α,
        ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv (some i) P)) ^ 2 ∂stdGauss (Option α) =
        ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) *
          ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv i (R c))) ^ 2 ∂stdGauss α := by
      intro i
      have h := option_integral ((MvPolynomial.pderiv (some i) P) ^ 2)
      simp only [map_pow] at h
      rw [h]
      have hin : ∀ z : α → ℝ, ∫ x, (MvPolynomial.eval (fun o => o.elim x z)
          (MvPolynomial.pderiv (some i) P)) ^ 2 ∂gaussianReal 0 1 =
          ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) *
            (MvPolynomial.eval z (MvPolynomial.pderiv i (R c))) ^ 2 := by
        intro z
        have hx : ∀ x : ℝ, MvPolynomial.eval (fun o => o.elim x z)
            (MvPolynomial.pderiv (some i) P) =
            ∑ b ∈ Finset.range (N + 1),
              MvPolynomial.eval z (MvPolynomial.pderiv i (p.coeff b)) * x ^ b := by
          intro x
          rw [opt_eval_sum _ N (by
            rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
            intro m hm
            rw [opt_pderiv_some, Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero])]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [opt_pderiv_some]
        simp_rw [hx]
        rw [fischer_sq]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 2
        simp only [hR, map_sum, Derivation.leibniz, MvPolynomial.pderiv_C, smul_eq_mul]
        exact Finset.sum_congr rfl fun b _ => by simp [mul_comm]
      simp_rw [hin]
      rw [integral_finsetSum _ fun c _ => (gpi _ 2).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
    rw [h2, h1, Fintype.sum_option, hD0]
    simp_rw [hDi]
    have hih := ih (R 0)
    have hA : ∑ c ∈ Finset.range N, ((c + 1).factorial : ℝ) * Y (c + 1) ≤
        ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) * ((c + 1 : ℝ) ^ 2 * Y (c + 1)) := by
      rw [Finset.sum_range_succ]
      have hlast : 0 ≤ (N.factorial : ℝ) * ((N + 1 : ℝ) ^ 2 * Y (N + 1)) := by
        have := hY0 (N + 1); positivity
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (le_add_of_nonneg_right hlast)
      rw [Nat.factorial_succ]
      push_cast
      have hc : (0 : ℝ) ≤ (c.factorial : ℝ) * Y (c + 1) := mul_nonneg (by positivity) (hY0 _)
      have hc2 : (1 : ℝ) ≤ (c + 1 : ℝ) := by have : (0 : ℝ) ≤ c := Nat.cast_nonneg c; linarith
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hc2), mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hc2))
        (by linarith : (0 : ℝ) ≤ (c + 1 : ℝ))]
    have hB : ∑ i : α, ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv i (R 0))) ^ 2 ∂stdGauss α ≤
        ∑ i : α, ∑ c ∈ Finset.range (N + 1), (c.factorial : ℝ) *
          ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv i (R c))) ^ 2 ∂stdGauss α := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := Finset.single_le_sum (f := fun c => (c.factorial : ℝ) *
          ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv i (R c))) ^ 2 ∂stdGauss α)
        (fun c _ => mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
        (Finset.mem_range.mpr (Nat.succ_pos N))
      simpa using this
    rw [Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
    linarith

/-- **Gaussian Poincaré inequality for polynomials**: `Var P ≤ Σ_α E (∂_α P)²`. -/
theorem poincareMv : PoincareMv := by
  intro ι _ P
  refine le_trans (le_of_eq ?_) (poincare_aux ι P)
  simp only [pow_one]
  set m := ∫ w, MvPolynomial.eval w P ∂stdGauss ι with hm
  have hi := gauss_poly_integrable P
  have e : ∀ z : ι → ℝ, (MvPolynomial.eval z P - m) ^ 2 =
      (MvPolynomial.eval z P) ^ 2 - (2 * m) * MvPolynomial.eval z P + m ^ 2 := fun z => by ring
  simp_rw [e]
  have i1 : Integrable (fun z => (2 * m) * MvPolynomial.eval z P) (stdGauss ι) := hi.const_mul _
  have i2 : Integrable (fun z => (MvPolynomial.eval z P) ^ 2 - (2 * m) * MvPolynomial.eval z P)
      (stdGauss ι) := (gpi P 2).sub i1
  rw [integral_add i2 (integrable_const _), integral_sub (gpi P 2) i1, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul]
  rw [← hm]; ring

end BstLean.Part78

#print axioms BstLean.Part78.poincareMv
