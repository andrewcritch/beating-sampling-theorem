import BstLean.Part162LG

/-!
# Part 162: the even Gaussian moments

Role: `delegations/statements/p162-spec.md`, item 1 (the constant `c_p = (π/2)ν_{2p}`). Do not use
`sorry`, `native_decide` or `axiom`.

* **`gmom_even`**: `E g^{2k} = ∏_{j<k}(2j + 1) = (2k − 1)!!`, from the moment generating function
  `e^{t²/2}` (`iteratedDeriv_mgf_zero`).
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real

lemma gexp_iter_eq (k : ℕ) :
    iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = ∏ j ∈ Finset.range k, (2 * j + 1 : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, gexp_deriv_rec, ih, Finset.prod_range_succ]
    push_cast; ring

/-- **The even Gaussian moments**: `E g^{2k} = ∏_{j<k}(2j + 1) = (2k − 1)!!` (so
`c_q = (π/2)((2q − 1)!!)^{1/(2q)}`, the paper's `c_p = (π/2)ν_{2p}`). -/
theorem gmom_even (k : ℕ) : gmom (2 * k) = ∏ j ∈ Finset.range k, (2 * j + 1 : ℝ) := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) (2 * k)
  rw [mgf_fun_id_gaussianReal] at h
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul] at h
  change iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
    ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 at h
  unfold gmom
  have e : ∫ x : ℝ, |x| ^ (2 * k) ∂gaussianReal 0 1 = ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 := by
    congr 1; funext x; exact pow_abs_two_mul x
  rw [e, ← h, gexp_iter_eq]

end BstLean.Part162

open BstLean.Part162 in
#print axioms gmom_even
