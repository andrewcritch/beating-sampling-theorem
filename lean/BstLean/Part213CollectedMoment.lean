import BstLean.Part213Radius

/-! The collected location polynomial has the exact plane-radius second
moment. The energy polynomial has the exact first moment. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real
open BstLean.Part186.RA

noncomputable def radiusPolynomial (a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  a + b * planeRadius p + c * planeRadius p ^ 2

noncomputable def collectedSecond (a b c : ℝ) : ℝ :=
  a ^ 2 + 2 * a * b * √(π / 2) + 2 * (b ^ 2 + 2 * a * c) +
    6 * b * c * √(π / 2) + 8 * c ^ 2

/-- Every polynomial order has a finite expansion in exact radius moments. -/
theorem radius_polynomial_power (a b c : ℝ) (k : ℕ) :
    Integrable (fun p => radiusPolynomial a b c p ^ k) ρ2 ∧
    (∫ p, radiusPolynomial a b c p ^ k ∂ρ2) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (a ^ i * (k.choose i : ℝ) *
          (b ^ j * ((k - i).choose j : ℝ) * c ^ (k - i - j))) *
          ((1 / 2 : ℝ) ^ (-((j + 2 * (k - i - j) : ℕ) + 2 : ℝ) / 2) *
            (1 / 2) * Gamma (((j + 2 * (k - i - j) : ℕ) + 2 : ℝ) / 2)) := by
  have he : ∀ p, radiusPolynomial a b c p ^ k =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (a ^ i * (k.choose i : ℝ) *
          (b ^ j * ((k - i).choose j : ℝ) * c ^ (k - i - j))) *
          planeRadius p ^ (j + 2 * (k - i - j)) := by
    intro p
    unfold radiusPolynomial
    rw [show a + b * planeRadius p + c * planeRadius p ^ 2 =
      a + (b * planeRadius p + c * planeRadius p ^ 2) by ring, add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_pow, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, mul_pow, ← pow_mul, pow_add]
    ring
  have hi : ∀ i j, Integrable (fun p =>
      (a ^ i * (k.choose i : ℝ) *
        (b ^ j * ((k - i).choose j : ℝ) * c ^ (k - i - j))) *
        planeRadius p ^ (j + 2 * (k - i - j))) ρ2 :=
    fun i j => (planeRadius_integrable _).const_mul _
  simp_rw [he]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => hi i j]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, planeRadius_gamma]

lemma planeRadius_second : ∫ p, planeRadius p ^ 2 ∂ρ2 = 2 := by
  simp_rw [planeRadius_sq]
  exact ER1

lemma planeRadius_fourth : ∫ p, planeRadius p ^ 4 ∂ρ2 = 8 := by
  have he : (fun p => planeRadius p ^ 4) = fun p => RR p ^ 2 := by
    funext p
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, planeRadius_sq]
  rw [he]
  exact ER2

/-- The polynomial mean uses the exact first and second radius moments. -/
theorem radius_polynomial_mean (a b c : ℝ) :
    Integrable (radiusPolynomial a b c) ρ2 ∧
    (∫ p, radiusPolynomial a b c p ∂ρ2) = a + b * √(π / 2) + 2 * c := by
  have i1 : Integrable planeRadius ρ2 := by simpa using planeRadius_integrable 1
  have i2 := planeRadius_integrable 2
  have ia : Integrable (fun p => a + b * planeRadius p) ρ2 :=
    (integrable_const a).add (i1.const_mul b)
  refine ⟨((integrable_const a).add (i1.const_mul b)).add (i2.const_mul c), ?_⟩
  unfold radiusPolynomial
  rw [integral_add ia (i2.const_mul c),
    integral_add (integrable_const a) (i1.const_mul b), integral_const_mul,
    integral_const_mul, planeRadius_mean, planeRadius_second]
  simp
  ring

/-- This is the exact collected location squared `L²` norm in the paper. -/
theorem radius_polynomial_second (a b c : ℝ) :
    Integrable (fun p => radiusPolynomial a b c p ^ 2) ρ2 ∧
    (∫ p, radiusPolynomial a b c p ^ 2 ∂ρ2) = collectedSecond a b c := by
  have i1 : Integrable planeRadius ρ2 := by simpa using planeRadius_integrable 1
  have i2 := planeRadius_integrable 2
  have i3 := planeRadius_integrable 3
  have i4 := planeRadius_integrable 4
  have he : (fun p => radiusPolynomial a b c p ^ 2) =
      fun p => a ^ 2 + (2 * a * b) * planeRadius p +
        (b ^ 2 + 2 * a * c) * planeRadius p ^ 2 +
        (2 * b * c) * planeRadius p ^ 3 + c ^ 2 * planeRadius p ^ 4 := by
    funext p
    unfold radiusPolynomial
    ring
  rw [he]
  have i01 : Integrable (fun p => a ^ 2 + (2 * a * b) * planeRadius p) ρ2 :=
    (integrable_const (a ^ 2)).add (i1.const_mul (2 * a * b))
  have i012 : Integrable (fun p => a ^ 2 + (2 * a * b) * planeRadius p +
      (b ^ 2 + 2 * a * c) * planeRadius p ^ 2) ρ2 :=
    i01.add (i2.const_mul (b ^ 2 + 2 * a * c))
  have i0123 : Integrable (fun p => a ^ 2 + (2 * a * b) * planeRadius p +
      (b ^ 2 + 2 * a * c) * planeRadius p ^ 2 + (2 * b * c) * planeRadius p ^ 3) ρ2 :=
    i012.add (i3.const_mul (2 * b * c))
  refine ⟨i0123.add (i4.const_mul (c ^ 2)), ?_⟩
  rw [integral_add i0123 (i4.const_mul (c ^ 2)),
    integral_add i012 (i3.const_mul (2 * b * c)),
    integral_add i01 (i2.const_mul (b ^ 2 + 2 * a * c)),
    integral_add (integrable_const (a ^ 2)) (i1.const_mul (2 * a * b)),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    planeRadius_mean, planeRadius_second, planeRadius_third, planeRadius_fourth]
  unfold collectedSecond
  simp
  ring

/-- Nonnegative coefficient bounds preserve the collected second moment. -/
theorem collectedSecond_mono {a b c A B C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) :
    collectedSecond a b c ≤ collectedSecond A B C := by
  have hA0 := ha.trans hA
  have hB0 := hb.trans hB
  have hC0 := hc.trans hC
  unfold collectedSecond
  gcongr

#print axioms radius_polynomial_mean
#print axioms radius_polynomial_second
#print axioms collectedSecond_mono
end BstLean.Part213
