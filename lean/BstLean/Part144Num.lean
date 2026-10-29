import BstLean.Part144Block2

/-!
# Part 144, numeric bounds of `κ = φ(√5)/(2√5)`

Role: `delegations/statements/p144-spec.md` (numerics for item 2, `sampleFails144` with a larger
`k_0`). `φ = gaussianPDFReal 0 1` is the standard Gaussian density.

* `exp_half_bounds`: `1.6487212 ≤ exp(1/2) ≤ 1.6487213`.
* `kappa5_eq`: `φ(√5)/(2√5) = 1/(√(2π)·exp(5/2)·(2√5))`.
* `kappa5_lower`, `kappa5_upper`: `0.007322 ≤ φ(√5)/(2√5) ≤ 0.007323`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144
open MeasureTheory ProbabilityTheory Set
open BstLean.Part131

lemma exp_half_bounds :
    (16487212 : ℝ) / 10000000 ≤ Real.exp (1 / 2) ∧ Real.exp (1 / 2) ≤ 16487213 / 10000000 := by
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  constructor
  · by_contra hc
    have hc' : Real.exp (1 / 2) < 16487212 / 10000000 := not_le.mp hc
    nlinarith
  · by_contra hc
    have hc' : (16487213 : ℝ) / 10000000 < Real.exp (1 / 2) := not_le.mp hc
    nlinarith

lemma exp_five_half_bounds :
    (1218249 : ℝ) / 100000 ≤ Real.exp (5 / 2) ∧ Real.exp (5 / 2) ≤ 1218250 / 100000 := by
  obtain ⟨h1, h2⟩ := exp_half_bounds
  have e : Real.exp (5 / 2) = Real.exp (1 / 2) ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  constructor
  · refine le_trans ?_ (pow_le_pow_left₀ (by norm_num) h1 5)
    norm_num
  · refine le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h2 5) ?_
    norm_num

lemma sqrt_two_pi_bounds :
    (2506627 : ℝ) / 1000000 ≤ √(2 * Real.pi) ∧ √(2 * Real.pi) ≤ 2506629 / 1000000 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  constructor
  · rw [Real.le_sqrt' (by norm_num)]
    norm_num at h1 ⊢
    linarith
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num at h2 ⊢
    linarith

lemma sqrt_five_bounds :
    (2236067 : ℝ) / 1000000 ≤ √5 ∧ √5 ≤ 2236068 / 1000000 := by
  constructor
  · rw [Real.le_sqrt' (by norm_num)]
    norm_num
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num

lemma kappa5_eq :
    gaussianPDFReal 0 1 (Real.sqrt 5) / (2 * Real.sqrt 5) =
      1 / (√(2 * Real.pi) * Real.exp (5 / 2) * (2 * √5)) := by
  have hs : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h5 : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  rw [pdf_eq, Real.sq_sqrt (by norm_num), Real.exp_neg]
  field_simp

/-- `0.007322 ≤ φ(√5)/(2√5)`. -/
theorem kappa5_lower :
    (7322 : ℝ) / 1000000 ≤ gaussianPDFReal 0 1 (Real.sqrt 5) / (2 * Real.sqrt 5) := by
  obtain ⟨_, hE⟩ := exp_five_half_bounds
  obtain ⟨_, hS⟩ := sqrt_two_pi_bounds
  obtain ⟨_, hR⟩ := sqrt_five_bounds
  have hs : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h5 : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hE0 : 0 < Real.exp (5 / 2) := Real.exp_pos _
  rw [kappa5_eq, le_div_iff₀ (by positivity)]
  have hprod : √(2 * Real.pi) * Real.exp (5 / 2) * (2 * √5) ≤
      2506629 / 1000000 * (1218250 / 100000) * (2 * (2236068 / 1000000)) :=
    mul_le_mul (mul_le_mul hS hE hE0.le (by norm_num)) (by linarith) (by positivity)
      (by norm_num)
  have := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 7322 / 1000000)
  refine this.trans ?_
  norm_num

/-- `φ(√5)/(2√5) ≤ 0.007323`. -/
theorem kappa5_upper :
    gaussianPDFReal 0 1 (Real.sqrt 5) / (2 * Real.sqrt 5) ≤ (7323 : ℝ) / 1000000 := by
  obtain ⟨hE, _⟩ := exp_five_half_bounds
  obtain ⟨hS, _⟩ := sqrt_two_pi_bounds
  obtain ⟨hR, _⟩ := sqrt_five_bounds
  have hs : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h5 : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hE0 : 0 < Real.exp (5 / 2) := Real.exp_pos _
  rw [kappa5_eq, div_le_iff₀ (by positivity)]
  have hprod : (2506627 : ℝ) / 1000000 * (1218249 / 100000) * (2 * (2236067 / 1000000)) ≤
      √(2 * Real.pi) * Real.exp (5 / 2) * (2 * √5) :=
    mul_le_mul (mul_le_mul hS hE (by norm_num) hs.le) (by linarith) (by norm_num)
      (by positivity)
  have := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 7323 / 1000000)
  refine le_trans ?_ this
  norm_num

end BstLean.Part144

open BstLean.Part144 in
#print axioms kappa5_lower
open BstLean.Part144 in
#print axioms kappa5_upper
