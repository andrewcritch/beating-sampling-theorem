import BstLean.Part291Cap
import BstLean.Part291Weighted
import BstLean.Part219Rotation

namespace BstLean.BlueprintLow
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188 BstLean.Part229

theorem direction_gradient_first {n : ℕ} (D : Design n) (c : Ret n) {M : ℝ}
    (hM : DirectionMoment D c M) :
    Integrable (BstLean.Part151.gradSq (centreCoordinate D c)) (stdGauss (Fin n)) ∧
    (∫ ξ, BstLean.Part151.gradSq (centreCoordinate D c) ξ ∂stdGauss (Fin n)) ≤ M / n := by
  have hp : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let g := BstLean.Part151.gradSq (centreCoordinate D c)
  have hg := BstLean.Part151.measurable_gradSq (centreCoordinate D c)
  have hg0 : ∀ ξ, 0 ≤ g ξ := BstLean.Part151.gradSq_nonneg _
  have hmn : 0 ≤ M / (n : ℝ) := div_nonneg hM.1 (Nat.cast_nonneg _)
  have hgn : eLpNorm g (12 : ℕ) (stdGauss (Fin n)) ≤ ENNReal.ofReal (M / n) := by
    apply BstLean.Part219.norm_le_of_moment (p := 12) (by norm_num)
      hg.aestronglyMeasurable hg0 hmn
    rw [← ofReal_integral_eq_lintegral_ofReal hM.2.1
      (ae_of_all _ fun ξ => pow_nonneg (hg0 ξ) _)]
    exact ENNReal.ofReal_le_ofReal hM.2.2
  have hgn1 : eLpNorm g (1 : ℕ) (stdGauss (Fin n)) ≤ ENNReal.ofReal (M / n) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : ((1 : ℕ) : ℝ≥0∞) ≤ (12 : ℕ))).trans hgn
  simpa only [pow_one] using BstLean.Part219.moment_of_norm (p := 1) (by norm_num)
    hg.aestronglyMeasurable hg0 hmn hgn1

/-- Poincare applied to the actual capped weight gives F6 M/n. Its derivative
is the existing fderiv convention, including the cap boundary. -/
theorem weight_variance_network {n : ℕ} (hn : 6 ≤ n) (D : Design n) (c : Ret n)
    {a d M : ℝ} (hτ : 0 < D.tau0 c) (hd : 0 < d) (had : d ≤ a)
    (hM : DirectionMoment D c M) :
    (∫ ξ, (weight a d (centreCoordinate D c ξ) -
      ∫ ζ, weight a d (centreCoordinate D c ζ) ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n)) ≤ (a - d) / d ^ 3 * (M / n) := by
  let v := coordinateVector D c
  let f := hiddenScalar c.2.1.1.1 c.2.1.1.2 1 v
  let K := hiddenScalarConstant c.2.1.1.1 c.2.1.1.2 1 v
  have hK : 0 ≤ K := hiddenScalarConstant_nonneg _ _ (by norm_num) _
  have hf := hiddenScalar_lip c.2.1.1.1 c.2.1.1.2 (by norm_num : (0 : ℝ) ≤ 1) v
  have hfb := hiddenScalar_bound c.2.1.1.1 c.2.1.1.2 (by norm_num : (0 : ℝ) ≤ 1) v
  have he : sphereScalar c.1.2 (D.tau0 c) f = centreCoordinate D c :=
    coordinate_as_sphereScalar D c
  have he1 : sphereScalar c.1.2 (D.tau0 c) (fun _ => (1 : ℝ)) = fun _ => 1 := rfl
  have hF : 0 ≤ (a - d) / d ^ 3 := by positivity
  have hmn : 0 ≤ M / (n : ℝ) := div_nonneg hM.1 (Nat.cast_nonneg _)
  obtain ⟨_, hiB⟩ := capped_energies_integrable (by omega : 4 ≤ n) c.1.2
    hτ hd hK zero_le_one hK (le_refl (0 : ℝ)) f (fun _ => 1) hf
    (by intro x y; simp) hfb (by intro x hx; norm_num)
  rw [he, he1] at hiB
  have hg := direction_gradient_first D c hM
  have hB : (∫ ξ, capEnergy a d (centreCoordinate D c) (fun _ => 1) ξ
      ∂stdGauss (Fin n)) ≤ (a - d) / d ^ 3 * (M / n) := by
    have hpt : ∀ ξ, capEnergy a d (centreCoordinate D c) (fun _ => 1) ξ ≤
        (a - d) / d ^ 3 * BstLean.Part151.gradSq (centreCoordinate D c) ξ := by
      intro ξ
      rw [(energy_formulas a d (centreCoordinate D c) (fun _ => 1) ξ).2, one_mul]
      exact mul_le_mul_of_nonneg_right (capSlope_sq_bound hd had)
        (normSq_nonneg _)
    have h := integral_mono hiB (hg.1.const_mul ((a - d) / d ^ 3)) hpt
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hg.2 hF)
  have h := capped_covariance hn c.1.2 hτ hd hK zero_le_one hK (le_refl (0 : ℝ))
    f (fun _ => 1) hf (by intro x y; simp) hfb (by intro x hx; norm_num)
    (N := 0) (C := (a - d) / d ^ 3 * (M / n)) (le_refl 0) (mul_nonneg hF hmn)
    (by rw [he1]; simp [projectedEnergy, gradientVector, normSq])
    (by simpa only [he, he1] using hB)
  simpa only [he, he1, mul_one, sqrt_zero, zero_add, sq_sqrt (mul_nonneg hF hmn)] using h.2

end BstLean.BlueprintLow
