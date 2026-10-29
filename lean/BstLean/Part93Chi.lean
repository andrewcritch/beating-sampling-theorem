import BstLean.Part93Defs

/-!
# Part 93, task H7: chi-square Chernoff tails (`ChiUp93`, `ChiLo93`) and two corollaries.
-/

namespace BstLean.Part93

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part56.LowLaplace (gaussian_square_exp gaussian_square_exp_integrable)

section chi
variable {ι : Type} [Fintype ι]

private lemma exp_sum_eq_prod (u : ℝ) (Z : ι → ℝ) :
    Real.exp (u * ∑ i, Z i ^ 2) = ∏ i, Real.exp (u * Z i ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

/-- Integrability of `exp(u ‖Z‖²)`, `u < 1/2`. -/
theorem chi_exp_integrable (u : ℝ) (hu : u < 1 / 2) :
    Integrable (fun Z : ι → ℝ => Real.exp (u * ∑ i, Z i ^ 2)) (stdGauss ι) := by
  simp_rw [exp_sum_eq_prod]
  unfold stdGauss
  exact Integrable.fintype_prod (f := fun (_ : ι) (z : ℝ) => Real.exp (u * z ^ 2))
    (fun _ => gaussian_square_exp_integrable u hu)

/-- `E exp(u ‖Z‖²) = exp(−d ln(1 − 2u)/2)`, `u < 1/2`. -/
theorem chi_mgf (u : ℝ) (hu : u < 1 / 2) :
    (∫ Z : ι → ℝ, Real.exp (u * ∑ i, Z i ^ 2) ∂stdGauss ι) =
      Real.exp (-((Fintype.card ι : ℝ) * Real.log (1 - 2 * u) / 2)) := by
  simp_rw [exp_sum_eq_prod]
  unfold stdGauss
  rw [integral_fintype_prod_eq_pow (fun z : ℝ => Real.exp (u * z ^ 2)),
    gaussian_square_exp u hu]
  have hpos : 0 < 1 - 2 * u := by linarith
  rw [← Real.exp_log (by positivity : 0 < (Real.sqrt (1 - 2 * u))⁻¹),
    ← Real.exp_nat_mul, Real.log_inv, Real.log_sqrt hpos.le]
  congr 1
  ring

end chi

/-- **Upper chi-square tail.** -/
theorem chiUp93 : ChiUp93 := by
  intro ι _ x hx
  have h1x : 0 < 1 + x := by linarith
  set u : ℝ := x / (2 * (1 + x)) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : 1 - 2 * u = (1 + x)⁻¹ := by rw [hu]; field_simp; ring
  have hu1 : u < 1 / 2 := by
    have : 0 < (1 + x)⁻¹ := inv_pos.mpr h1x
    linarith
  have hc := measure_ge_le_exp_mul_mgf (μ := stdGauss ι)
    (X := fun Z : ι → ℝ => ∑ i, Z i ^ 2) ((1 + x) * (Fintype.card ι : ℝ)) hu0
    (chi_exp_integrable u hu1)
  have hm : mgf (fun Z : ι → ℝ => ∑ i, Z i ^ 2) (stdGauss ι) u =
      Real.exp (-((Fintype.card ι : ℝ) * Real.log (1 - 2 * u) / 2)) := chi_mgf u hu1
  rw [hm, ← Real.exp_add, hu2, Real.log_inv] at hc
  have he : -u * ((1 + x) * (Fintype.card ι : ℝ)) +
      -((Fintype.card ι : ℝ) * -Real.log (1 + x) / 2) =
      -((Fintype.card ι : ℝ) * (x - Real.log (1 + x)) / 2) := by
    rw [hu]; field_simp; ring
  rw [he] at hc
  rw [← ENNReal.ofReal_toReal (measure_ne_top (stdGauss ι) _)]
  exact ENNReal.ofReal_le_ofReal hc

/-- **Lower chi-square tail.** -/
theorem chiLo93 : ChiLo93 := by
  intro ι _ x hx hx1
  have h1x : 0 < 1 - x := by linarith
  set u : ℝ := -(x / (2 * (1 - x))) with hu
  have hu0 : u ≤ 0 := by
    have : 0 ≤ x / (2 * (1 - x)) := by positivity
    linarith
  have hu2 : 1 - 2 * u = (1 - x)⁻¹ := by rw [hu]; field_simp; ring
  have hu1 : u < 1 / 2 := by linarith
  have hc := measure_le_le_exp_mul_mgf (μ := stdGauss ι)
    (X := fun Z : ι → ℝ => ∑ i, Z i ^ 2) ((1 - x) * (Fintype.card ι : ℝ)) hu0
    (chi_exp_integrable u hu1)
  have hm : mgf (fun Z : ι → ℝ => ∑ i, Z i ^ 2) (stdGauss ι) u =
      Real.exp (-((Fintype.card ι : ℝ) * Real.log (1 - 2 * u) / 2)) := chi_mgf u hu1
  rw [hm, ← Real.exp_add, hu2, Real.log_inv] at hc
  have he : -u * ((1 - x) * (Fintype.card ι : ℝ)) +
      -((Fintype.card ι : ℝ) * -Real.log (1 - x) / 2) =
      -((Fintype.card ι : ℝ) * (-x - Real.log (1 - x)) / 2) := by
    rw [hu]; field_simp; ring
  rw [he] at hc
  rw [← ENNReal.ofReal_toReal (measure_ne_top (stdGauss ι) _)]
  exact ENNReal.ofReal_le_ofReal hc

/-- `x − ln(1 + x) ≥ x²/3` on `[0, 1/2]`. -/
theorem sub_log_one_add_ge (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    x ^ 2 / 3 ≤ x - Real.log (1 + x) := by
  have hw : 0 ≤ x - x ^ 2 / 3 := by nlinarith
  have h1 := Real.quadratic_le_exp_of_nonneg hw
  have h2 : 1 + x ≤ Real.exp (x - x ^ 2 / 3) := by
    refine le_trans ?_ h1
    have h3 : x ^ 2 / 3 ≤ (x - x ^ 2 / 3) ^ 2 / 2 := by
      have h4 : (x - x ^ 2 / 3) ^ 2 = x ^ 2 * (1 - x / 3) ^ 2 := by ring
      have h5 : (2 : ℝ) / 3 ≤ (1 - x / 3) ^ 2 := by nlinarith
      rw [h4]
      nlinarith [sq_nonneg x]
    linarith
  have h6 := Real.log_le_log (by linarith : (0 : ℝ) < 1 + x) h2
  rw [Real.log_exp] at h6
  linarith

/-- `−x − ln(1 − x) ≥ x²/2` on `[0, 1)`. -/
theorem neg_sub_log_one_sub_ge (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    x ^ 2 / 2 ≤ -x - Real.log (1 - x) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_nonneg hx]; exact hx1)
  have h := sum_le_hasSum (Finset.range 2)
    (fun i _ => by positivity : ∀ i ∉ Finset.range 2, (0 : ℝ) ≤ x ^ (i + 1) / ((i : ℝ) + 1)) hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- **Corollary, upper tail**: `Pr(‖Z‖² ≥ (1 + x) d) ≤ exp(−d x²/6)` for `0 < x ≤ 1/2`. -/
theorem chiUp93_sq (ι : Type) [Fintype ι] (x : ℝ) (hx : 0 < x) (hx2 : x ≤ 1 / 2) :
    stdGauss ι {Z | (1 + x) * (Fintype.card ι : ℝ) ≤ ∑ i, Z i ^ 2} ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card ι : ℝ) * x ^ 2 / 6))) := by
  refine (chiUp93 ι x hx).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have h := sub_log_one_add_ge x hx.le hx2
  have hd : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h hd]

/-- **Corollary, lower tail**: `Pr(‖Z‖² ≤ (1 − x) d) ≤ exp(−d x²/4)` for `0 < x < 1`. -/
theorem chiLo93_sq (ι : Type) [Fintype ι] (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    stdGauss ι {Z | ∑ i, Z i ^ 2 ≤ (1 - x) * (Fintype.card ι : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card ι : ℝ) * x ^ 2 / 4))) := by
  refine (chiLo93 ι x hx hx1).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have h := neg_sub_log_one_sub_ge x hx.le hx1
  have hd : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h hd]

end BstLean.Part93

#print axioms BstLean.Part93.chiUp93
#print axioms BstLean.Part93.chiLo93
#print axioms BstLean.Part93.chiUp93_sq
#print axioms BstLean.Part93.chiLo93_sq
