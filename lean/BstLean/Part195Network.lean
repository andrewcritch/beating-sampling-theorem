import BstLean.Part195Rotation
import BstLean.Part195Singular
import BstLean.Part188Mass

/-! The rotation inequalities use Part188's actual centre coordinate and gradient. -/
namespace BstLean.Part195
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part157 (Design Ret)
open BstLean.Part188 (centreCoordinate centrePhi centrePhi_eq centrePhi_lip DirectionMoment)

/-- A supplied moment of the actual directional gradient gives the centred coordinate moment.
This theorem supplies no probability charge for that gradient moment. -/
theorem centreCoordinate_even {n q : ℕ} (hq : 1 ≤ q) (hn : 2 * q + 1 < n)
    (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hi : Integrable (fun ξ => BstLean.Part151.gradSq (centreCoordinate D c) ξ ^ q)
      (stdGauss (Fin n))) :
    ∫ ξ, |centreCoordinate D c ξ -
      ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)| ^ (2 * q) ∂stdGauss (Fin n) ≤
    rotationConstant q ^ (2 * q) *
      ∫ ξ, BstLean.Part151.gradSq (centreCoordinate D c) ξ ^ q ∂stdGauss (Fin n) := by
  obtain ⟨K, hK, hΦ⟩ := centrePhi_lip (by omega) D c hb
  apply rotation_singular_even hq c.1.2 hτ hK hΦ
    (fun ξ => BstLean.Part151.gradSq_nonneg _ ξ) hi
  · rw [centrePhi_eq]
    exact ae_of_all _ fun _ => le_rfl
  · exact (BstLean.Part153.invMoment_le hn c.1.2 hτ).1
  · exact BstLean.Part153.ae_normSq_ne (by omega) c.1.2 hτ.ne'

/-- Part188's directional interface supplies the paper order-24 rotation bound from `n = 26`. -/
theorem direction_moment24 {n : ℕ} (hn : 26 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M : ℝ}
    (hM : DirectionMoment D c M) :
    ∫ ξ, |centreCoordinate D c ξ -
      ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)| ^ 24 ∂stdGauss (Fin n) ≤
      rotationConstant 12 ^ 24 * (M / n) ^ 12 := by
  have h := centreCoordinate_even (q := 12) (by norm_num) (by omega)
    D c hτ hb hM.2.1
  exact h.trans (mul_le_mul_of_nonneg_left hM.2.2
    (pow_nonneg (rotationConstant_nonneg 12) _))

/-- The order-24 norm bound has the paper constant and uses the same stand-in distribution. -/
theorem direction_norm24 {n : ℕ} (hn : 26 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M : ℝ}
    (hM : DirectionMoment D c M) :
    BstLean.Part161.momN (stdGauss (Fin n)) 24
      (fun ξ => centreCoordinate D c ξ -
        ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)) ≤
      rotationConstant 12 * √(M / n) := by
  have hmn : 0 ≤ M / (n : ℝ) := div_nonneg hM.1 (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by norm_num : (24 : ℕ) ≠ 0)
    (mul_nonneg (rotationConstant_nonneg 12) (Real.sqrt_nonneg _))
  have hs : √(M / (n : ℝ)) ^ 24 = (M / n) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, Real.sq_sqrt hmn]
  rw [BstLean.Part161.momN_pow _ (by norm_num), mul_pow, hs]
  exact direction_moment24 hn D c hτ hb hM

/-- The totalized coordinate is zero when the computed centre is zero. -/
lemma centreCoordinate_zero {n : ℕ} (D : Design n) (c : Ret n)
    (hb : D.bA c.1 c.2.1.1 = 0) : centreCoordinate D c = fun _ => 0 := by
  funext ξ
  simp [centreCoordinate, hb]

/-- The directional norm bound includes the zero-centre convention. -/
theorem direction_norm24_all {n : ℕ} (hn : 26 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) {M : ℝ} (hM : DirectionMoment D c M) :
    BstLean.Part161.momN (stdGauss (Fin n)) 24
      (fun ξ => centreCoordinate D c ξ -
        ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)) ≤
      rotationConstant 12 * √(M / n) := by
  by_cases hb : 0 < normSq (D.bA c.1 c.2.1.1)
  · exact direction_norm24 hn D c hτ hb hM
  · have hz : normSq (D.bA c.1 c.2.1.1) = 0 :=
      le_antisymm (not_lt.mp hb) (normSq_nonneg _)
    rw [centreCoordinate_zero D c (BstLean.Part130.normSq_eq_zero hz)]
    simp only [integral_zero, sub_zero, BstLean.Part161.momN, abs_zero, zero_pow
      (by norm_num : (24 : ℕ) ≠ 0)]
    rw [Real.zero_rpow (by norm_num : (((24 : ℕ) : ℝ)⁻¹) ≠ 0)]
    exact mul_nonneg (rotationConstant_nonneg 12) (Real.sqrt_nonneg (M / (n : ℝ)))

end BstLean.Part195
#print axioms BstLean.Part195.centreCoordinate_even
#print axioms BstLean.Part195.direction_moment24
#print axioms BstLean.Part195.direction_norm24
#print axioms BstLean.Part195.direction_norm24_all
