import Mathlib

/-!
# Part 29, layer L4 (F3b-1): products of coordinates under the standard Gaussian

Under the standard Gaussian product measure on `Fin D → ℝ`, the expectation of a product of coordinates
`∏_{r < R} z_{τ r}` factorizes over the distinct indices: it is `∏_i g(#{r | τ r = i})`, where `g k` is the
`k`-th moment of `N(0,1)`: `0` for odd `k`, `(k-1)!!` for even `k`.
-/

namespace BstLean.Part29

open MeasureTheory ProbabilityTheory

/-- The `k`-th moment of `N(0,1)`: `0` for odd `k`, `(k - 1)!!` for even `k`. -/
def gaussMom (k : ℕ) : ℝ := if Even k then ((k - 1).doubleFactorial : ℝ) else 0

private lemma exp_deriv : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
    (fun t => t) * (fun t => Real.exp (t ^ 2 / 2)) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
  simpa [mul_comm] using h.exp.deriv

private lemma exp_rec (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
      (n + 1 : ℝ) * iteratedDeriv n (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  rw [iteratedDeriv_succ', exp_deriv,
    iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  simp [iteratedDeriv_fun_id_zero,
    Finset.mem_range, Nat.choose_one_right]

private lemma mom_rec (n : ℕ) : gaussMom (n + 2) = (n + 1 : ℝ) * gaussMom n := by
  unfold gaussMom
  have h : Even (n + 2) ↔ Even n := by simp [Nat.even_add]
  simp only [h]
  split_ifs with hn
  · rw [show n + 2 - 1 = n + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

/-- The one-dimensional moments. -/
theorem gaussMom_eq (k : ℕ) : ∫ x, x ^ k ∂(gaussianReal 0 1) = gaussMom k := by
  have hm (j : ℕ) : (∫ x, x ^ j ∂(gaussianReal 0 1)) =
      iteratedDeriv j (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
    have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) (by simp) j
    rw [mgf_fun_id_gaussianReal] at h
    simpa using h.symm
  rw [hm]
  induction k using Nat.twoStepInduction with
  | zero => simp [gaussMom]
  | one => rw [iteratedDeriv_one, exp_deriv]; norm_num [gaussMom]
  | more n ih ih' => rw [exp_rec, mom_rec, ih]

/-- Integrability of every product of coordinates. -/
theorem gaussProd_integrable (D R : ℕ) (τ : Fin R → Fin D) :
    Integrable (fun z : Fin D → ℝ => ∏ r, z (τ r)) (Measure.pi fun _ : Fin D => gaussianReal 0 1) := by
  classical
  have hp (z : Fin D → ℝ) : (∏ r, z (τ r)) =
      ∏ i, z i ^ (Finset.univ.filter fun r => τ r = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  exact Integrable.fintype_prod (f := fun i x => x ^
    (Finset.univ.filter fun r => τ r = i).card) (fun i =>
      integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) _)

/-- **The product-moment formula.** -/
theorem gaussProd_moment (D R : ℕ) (τ : Fin R → Fin D) :
    ∫ z, ∏ r, z (τ r) ∂(Measure.pi fun _ : Fin D => gaussianReal 0 1) =
      ∏ i, gaussMom (Finset.univ.filter fun r => τ r = i).card := by
  classical
  have hp (z : Fin D → ℝ) : (∏ r, z (τ r)) =
      ∏ i, z i ^ (Finset.univ.filter fun r => τ r = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  rw [integral_fintype_prod_eq_prod (f := fun (i : Fin D) (x : ℝ) => x ^
    (Finset.univ.filter fun r => τ r = i).card)]
  simp_rw [gaussMom_eq]

end BstLean.Part29
