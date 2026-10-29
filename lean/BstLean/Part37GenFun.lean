import BstLean.Part37Defs
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Part 37, wave 1: the program's series recurrence computes the multinomial coefficients

Paper: `37-explicit-22-bingham-ball.tex`, Lemma `series`, paragraph "Computation". Specification:
`delegations/answers/p37-spec-opus.md`, §2. Pure algebra (no measure theory). The identity is
`∏ᵢ (1 − 2θᵢ s)^{−1/2 − αᵢ} · ∏ᵢ (2αᵢ − 1)!! = Σ_κ ∏ᵢ θᵢ^{κᵢ} (2(αᵢ + κᵢ) − 1)!!/κᵢ! · s^{|κ|}`, with
`exp(Σ_j 2^{j−1} p_j s^j / j) = ∏ᵢ (1 − 2θᵢ s)^{−1/2}`. A route: `PowerSeries` over `ℝ`, or a direct
induction on `n` (split off the last coordinate) and on the list `w`.

Provers: replace each `sorry` by a proof. Do not edit `Part37Defs.lean` or any statement in this file,
and do not use `native_decide` anywhere.
-/

namespace BstLean.Part37

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (SphereProd floorY4 rawQ Dc)

variable {n : ℕ}

/-- The table is stable: later rows keep earlier entries. -/
theorem phiTab_stable (θ : Fin n → ℝ) (K k : ℕ) (hk : k ≤ K) : phiTab θ K k = phi0 θ k := by
  induction K with
  | zero =>
      have : k = 0 := by omega
      subst k
      rfl
  | succ K ih =>
      by_cases h : k ≤ K
      · simpa only [phiTab, ite_eq_left h] using ih h
      · have : k = K + 1 := by omega
        subst k
        rfl

/-- The recurrence `(k+1) a_{k+1} = Σ_{j ≤ k} 2^j p_{j+1} a_{k−j}`. -/
theorem phi0_succ (θ : Fin n → ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * phi0 θ (k + 1) =
      ∑ j ∈ Finset.range (k + 1), 2 ^ j * psum θ (j + 1) * phi0 θ (k - j) := by
  have hden : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold phi0
  simp only [phiTab, ite_eq_right (by omega : ¬ k + 1 ≤ k)]
  rw [mul_div_cancel₀ _ hden]
  apply Finset.sum_congr rfl
  intro j hj
  rw [phiTab_stable θ k (k - j) (Nat.sub_le _ _)]
  rfl

private lemma odd_df_succ (a : ℕ) :
    ((2 * (a + 1) - 1).doubleFactorial : ℝ) =
      (2 * (a : ℝ) + 1) * ((2 * a - 1).doubleFactorial : ℝ) := by
  have he : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  rw [he, Nat.doubleFactorial_add_one]
  push_cast
  ring

private noncomputable def coord (t : ℝ) (a : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => t ^ k * ((2 * (a + k) - 1).doubleFactorial : ℝ) /
    (k.factorial : ℝ)

private noncomputable def geom (c : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => c ^ k

private lemma coord_step (t : ℝ) (a k : ℕ) :
    ((k : ℝ) + 1) * PowerSeries.coeff (k + 1) (coord t a) =
      t * (2 * ((a : ℝ) + k) + 1) * PowerSeries.coeff k (coord t a) := by
  simp only [coord, PowerSeries.coeff_mk]
  rw [show a + (k + 1) = (a + k) + 1 by omega, odd_df_succ,
    Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma geom_inverse (c : ℝ) :
    geom c * (1 - PowerSeries.C c * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale c) (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  simpa [geom, PowerSeries.rescale_mk, PowerSeries.rescale_X] using h

private lemma coord_ode (t : ℝ) (a : ℕ) :
    PowerSeries.derivative (coord t a) =
      PowerSeries.C (t * (2 * (a : ℝ) + 1)) * geom (2 * t) * coord t a := by
  have h : (1 - PowerSeries.C (2 * t) * PowerSeries.X) *
      PowerSeries.derivative (coord t a) = PowerSeries.C (t * (2 * (a : ℝ) + 1)) *
        coord t a := by
    ext k
    cases k with
    | zero =>
        simp only [sub_mul, one_mul, mul_assoc, map_sub,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
          PowerSeries.coeff_derivative, Nat.cast_zero, zero_add,
          mul_one, mul_zero, sub_zero]
        simpa only [Nat.cast_zero, zero_add, add_zero, one_mul, mul_assoc] using coord_step t a 0
    | succ k =>
        simp only [sub_mul, one_mul, mul_assoc, map_sub,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative, Nat.cast_add, Nat.cast_one]
        have h := coord_step t a (k + 1)
        have h' := coord_step t a k
        simp only [Nat.cast_add, Nat.cast_one] at h h'
        nlinarith
  have he := congrArg (fun z => geom (2 * t) * z) h
  simpa only [← mul_assoc, geom_inverse, one_mul, mul_comm (geom (2 * t))
    (PowerSeries.C (t * (2 * (a : ℝ) + 1)))] using he

private lemma coeff_mul_range (f g : PowerSeries ℝ) (k : ℕ) :
    PowerSeries.coeff k (f * g) = ∑ j ∈ Finset.range (k + 1),
      PowerSeries.coeff j f * PowerSeries.coeff (k - j) g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma ode_unique (p f g : PowerSeries ℝ)
    (hf : PowerSeries.derivative f = p * f)
    (hg : PowerSeries.derivative g = p * g)
    (h0 : PowerSeries.coeff 0 f = PowerSeries.coeff 0 g) : f = g := by
  ext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact h0
    | succ k =>
      have he : PowerSeries.coeff k (p * f) = PowerSeries.coeff k (p * g) := by
        rw [coeff_mul_range, coeff_mul_range]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (k - j) (by omega)]
      rw [← hf, ← hg, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at he
      exact mul_right_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0) (by simpa using he)

private lemma coord_prod_coeff (θ : Fin n → ℝ) (w : List (Fin n)) (k : ℕ) :
    PowerSeries.coeff k (∏ i, coord (θ i) (w.count i)) = phiCoef θ w k := by
  classical
  rw [PowerSeries.coeff_prod]
  unfold phiCoef
  apply Finset.sum_bij (fun a _ => fun i => a i)
  · intro a ha
    apply Finset.Nat.mem_antidiagonalTuple.mpr
    exact (Finset.mem_finsuppAntidiag.mp ha).1
  · intro a ha b hb he
    exact DFunLike.ext _ _ (congrFun he)
  · intro a ha
    refine ⟨Finsupp.equivFunOnFinite.symm a, ?_, ?_⟩
    · apply Finset.mem_finsuppAntidiag.mpr
      constructor
      · simpa using Finset.Nat.mem_antidiagonalTuple.mp ha
      · exact Finset.subset_univ _
    · simp
  · intro a ha
    simp only [coord, PowerSeries.coeff_mk]

private lemma prod_ode (s : Finset (Fin n)) (f p : Fin n → PowerSeries ℝ)
    (h : ∀ i ∈ s, PowerSeries.derivative (f i) = p i * f i) :
    PowerSeries.derivative (∏ i ∈ s, f i) = (∑ i ∈ s, p i) * ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, PowerSeries.derivative.leibniz]
    rw [h i (Finset.mem_insert_self _ _), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    simp only [smul_eq_mul]
    ring

private lemma base_ode (θ : Fin n → ℝ) :
    PowerSeries.derivative (∏ i, coord (θ i) 0) =
      (PowerSeries.mk (fun j => 2 ^ j * psum θ (j + 1))) * ∏ i, coord (θ i) 0 := by
  have h := prod_ode Finset.univ (fun i => coord (θ i) 0)
    (fun i => PowerSeries.C (θ i) * geom (2 * θ i)) (by
      intro i hi
      simpa using coord_ode (θ i) 0)
  have hp : (∑ i, PowerSeries.C (θ i) * geom (2 * θ i)) =
      PowerSeries.mk (fun j => 2 ^ j * psum θ (j + 1)) := by
    ext j
    simp only [map_sum, PowerSeries.coeff_C_mul, geom, PowerSeries.coeff_mk,
      mul_pow, psum, Finset.mul_sum, pow_succ]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hp] at h
  exact h

private lemma phi0_ode (θ : Fin n → ℝ) :
    PowerSeries.derivative (PowerSeries.mk (phi0 θ)) =
      (PowerSeries.mk (fun j => 2 ^ j * psum θ (j + 1))) * PowerSeries.mk (phi0 θ) := by
  ext k
  rw [PowerSeries.coeff_derivative, coeff_mul_range]
  simp only [PowerSeries.coeff_mk]
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using phi0_succ θ k

/-- `a_k` is the multinomial coefficient for `w = []`. -/
theorem phi0_eq_phiCoef (θ : Fin n → ℝ) (k : ℕ) : phi0 θ k = phiCoef θ [] k := by
  have he : PowerSeries.mk (phi0 θ) = ∏ i, coord (θ i) 0 := by
    apply ode_unique _ _ _ (phi0_ode θ) (base_ode θ)
    simp [coord, phi0, phiTab, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := congrArg (PowerSeries.coeff k) he
  rw [← coord_prod_coeff θ [] k]
  simpa only [PowerSeries.coeff_mk, List.count_nil] using h

/-- One factor `(1 − 2θᵢ s)^{−1}` per list entry. -/
theorem phiW_cons (θ : Fin n → ℝ) (i : Fin n) (w : List (Fin n)) :
    phiW θ (i :: w) = mulGeom (2 * θ i) (phiW θ w) := by
  rfl

private lemma geom_derivative (c : ℝ) :
    PowerSeries.derivative (geom c) = PowerSeries.C c * geom c ^ 2 := by
  have h := PowerSeries.derivative.leibniz_of_mul_eq_one (geom_inverse c)
  simp only [map_sub, PowerSeries.derivative_one, PowerSeries.derivative.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul,
    mul_one, mul_zero, add_zero, zero_sub] at h
  rw [h]
  ring

private lemma coord_raise (t : ℝ) (a : ℕ) :
    coord t (a + 1) = PowerSeries.C (2 * (a : ℝ) + 1) * geom (2 * t) * coord t a := by
  apply ode_unique (PowerSeries.C (t * (2 * ((a + 1 : ℕ) : ℝ) + 1)) * geom (2 * t))
    _ _ (coord_ode t (a + 1))
  · rw [PowerSeries.derivative.leibniz, PowerSeries.derivative.leibniz,
      PowerSeries.derivative_C, geom_derivative, coord_ode]
    simp only [smul_eq_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
      map_mul, map_add, map_ofNat, map_one]
    ring
  · simp only [coord, PowerSeries.coeff_mk, pow_zero, Nat.add_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      geom, PowerSeries.constantCoeff_mk, mul_one]
    exact odd_df_succ a

private lemma coord_prod_cons (θ : Fin n → ℝ) (i : Fin n) (w : List (Fin n)) :
    (∏ j, coord (θ j) ((i :: w).count j)) =
      PowerSeries.C (2 * (w.count i : ℝ) + 1) * geom (2 * θ i) *
        ∏ j, coord (θ j) (w.count j) := by
  classical
  have hp (j : Fin n) : coord (θ j) ((i :: w).count j) =
      (if j = i then PowerSeries.C (2 * (w.count i : ℝ) + 1) * geom (2 * θ i)
        else 1) * coord (θ j) (w.count j) := by
    by_cases hj : j = i
    · subst j
      simpa [List.count_cons, Nat.add_comm] using coord_raise (θ i) (w.count i)
    · simp [hj, Ne.symm hj]
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp

private lemma dfC_cons (i : Fin n) (w : List (Fin n)) :
    dfC (i :: w) = (2 * (w.count i : ℝ) + 1) * dfC w := by
  classical
  have hp (j : Fin n) : ((2 * (i :: w).count j - 1).doubleFactorial : ℝ) =
      (if j = i then 2 * (w.count i : ℝ) + 1 else 1) *
        ((2 * w.count j - 1).doubleFactorial : ℝ) := by
    by_cases hj : j = i
    · subst j
      simpa [List.count_cons, Nat.add_comm] using odd_df_succ (w.count i)
    · simp [hj, Ne.symm hj]
  unfold dfC
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp

private lemma geom_mul_mk (c : ℝ) (a : ℕ → ℝ) :
    geom c * PowerSeries.mk a = PowerSeries.mk (mulGeom c a) := by
  ext k
  simp only [coeff_mul_range, geom, PowerSeries.coeff_mk, mulGeom]

/-- **The program computes the series coefficients.** -/
theorem phiW_eq_phiCoef (θ : Fin n → ℝ) (w : List (Fin n)) (k : ℕ) :
    dfC w * phiW θ w k = phiCoef θ w k := by
  have hp : (∏ i, coord (θ i) (w.count i)) =
      PowerSeries.C (dfC w) * PowerSeries.mk (phiW θ w) := by
    induction w with
    | nil =>
      simp only [List.count_nil, dfC, Nat.mul_zero, Nat.zero_sub,
        Nat.doubleFactorial, Nat.cast_one, Finset.prod_const_one, map_one, one_mul]
      ext j
      simpa only [phiW, List.foldr_nil, PowerSeries.coeff_mk, List.count_nil] using
        (coord_prod_coeff θ [] j).trans (phi0_eq_phiCoef θ j).symm
    | cons i w ih =>
      rw [coord_prod_cons, ih, dfC_cons, map_mul, phiW_cons]
      rw [← geom_mul_mk]
      ring
  rw [← coord_prod_coeff θ w k, hp, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

end BstLean.Part37
