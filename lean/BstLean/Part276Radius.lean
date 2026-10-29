import BstLean.Part252RadiusPolynomial

/-! A weighted Jensen enclosure of the order-sixteen plane-radius polynomial root.
It is a Minkowski-type bound with explicit rational radius norms. -/
namespace BstLean.Part276
open MeasureTheory Real
open BstLean.Part186.RA
open BstLean.Part213 BstLean.Part223

theorem radius_moment16 : (∫ p, planeRadius p ^ 16 ∂ρ2) = 2 ^ 8 * (8 : ℕ).factorial := by
  rw [planeRadius_gamma]
  norm_num only
  have hg := Gamma_nat_eq_factorial 8
  norm_num only [Nat.cast_ofNat] at hg
  rw [hg]
  norm_num [rpow_neg, rpow_natCast, Nat.factorial]

theorem radius_moment32 : (∫ p, planeRadius p ^ 32 ∂ρ2) = 2 ^ 16 * (16 : ℕ).factorial := by
  rw [planeRadius_gamma]
  norm_num only
  have hg := Gamma_nat_eq_factorial 16
  norm_num only [Nat.cast_ofNat] at hg
  rw [hg]
  norm_num [rpow_neg, rpow_natCast, Nat.factorial]

/-- Pointwise weighted power-mean bound. -/
theorem radius_polynomial_pointwise {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (p : ℝ × ℝ) :
    radiusPolynomial a b c p ^ 16 ≤
      (a + 14 / 5 * b + 14 * c) ^ 15 *
        (a + 14 / 5 * b * ((5 / 14) ^ 16 * planeRadius p ^ 16) +
          14 * c * ((1 / 14) ^ 16 * planeRadius p ^ 32)) := by
  set K := a + 14 / 5 * b + 14 * c with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set r := planeRadius p with hr
  have hr0 : 0 ≤ r := sqrt_nonneg _
  let w : Fin 3 → ℝ := ![a / K, 14 / 5 * b / K, 14 * c / K]
  let z : Fin 3 → ℝ := ![K, K * (5 / 14 * r), K * (1 / 14 * r ^ 2)]
  have hw : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    fin_cases i <;> simp [w] <;> positivity
  have hw1 : ∑ i ∈ Finset.univ, w i = 1 := by
    simp only [Fin.sum_univ_three, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hz : ∀ i ∈ Finset.univ, 0 ≤ z i := by
    intro i _
    fin_cases i <;> simp [z] <;> positivity
  have hJ := Real.pow_arith_mean_le_arith_mean_pow Finset.univ w z hw hw1 hz 16
  simp only [Fin.sum_univ_three, w, z, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hJ
  have hl : a / K * K + 14 / 5 * b / K * (K * (5 / 14 * r)) +
      14 * c / K * (K * (1 / 14 * r ^ 2)) = radiusPolynomial a b c p := by
    unfold radiusPolynomial
    rw [← hr]
    field_simp
  rw [hl] at hJ
  refine hJ.trans (le_of_eq ?_)
  have hr32 : r ^ 32 = (r ^ 2) ^ 16 := by ring
  rw [hr32]
  field_simp

theorem radius_polynomial_root_sharp {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    radiusPolynomialRoot16 a b c ≤ a + 14 / 5 * b + 14 * c := by
  set K := a + 14 / 5 * b + 14 * c with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) hK0.le
  rw [radiusPolynomialRoot16_pow]
  have i16 := planeRadius_integrable 16
  have i32 := planeRadius_integrable 32
  have hi : Integrable (fun p => K ^ 15 *
      (a + 14 / 5 * b * ((5 / 14) ^ 16 * planeRadius p ^ 16) +
        14 * c * ((1 / 14) ^ 16 * planeRadius p ^ 32))) ρ2 :=
    (((integrable_const a).add ((i16.const_mul _).const_mul _)).add
      ((i32.const_mul _).const_mul _)).const_mul _
  calc
    _ ≤ ∫ p, K ^ 15 *
        (a + 14 / 5 * b * ((5 / 14) ^ 16 * planeRadius p ^ 16) +
          14 * c * ((1 / 14) ^ 16 * planeRadius p ^ 32)) ∂ρ2 :=
      integral_mono (radius_polynomial_power a b c 16).1 hi
        (radius_polynomial_pointwise ha hb hc)
    _ = K ^ 15 * (a + 14 / 5 * b * ((5 / 14) ^ 16 * (2 ^ 8 * (8 : ℕ).factorial)) +
          14 * c * ((1 / 14) ^ 16 * (2 ^ 16 * (16 : ℕ).factorial))) := by
      rw [integral_const_mul]
      congr 1
      have j1 : Integrable (fun p => 14 / 5 * b * ((5 / 14 : ℝ) ^ 16 * planeRadius p ^ 16)) ρ2 :=
        (i16.const_mul _).const_mul _
      have j2 : Integrable (fun p => 14 * c * ((1 / 14 : ℝ) ^ 16 * planeRadius p ^ 32)) ρ2 :=
        (i32.const_mul _).const_mul _
      have j0 : Integrable (fun p => a + 14 / 5 * b * ((5 / 14 : ℝ) ^ 16 * planeRadius p ^ 16)) ρ2 :=
        (integrable_const a).add j1
      rw [integral_add j0 j2, integral_add (integrable_const a) j1, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul,
        radius_moment16, radius_moment32]
      simp
    _ ≤ K ^ 15 * K := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0.le 15)
      rw [hK]
      have h1 : (5 / 14 : ℝ) ^ 16 * (2 ^ 8 * (8 : ℕ).factorial) ≤ 1 := by
        norm_num [Nat.factorial]
      have h2 : (1 / 14 : ℝ) ^ 16 * (2 ^ 16 * (16 : ℕ).factorial) ≤ 1 := by
        norm_num [Nat.factorial]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 14 / 5 * b),
        mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 14 * c)]
    _ = K ^ 16 := by ring

end BstLean.Part276
