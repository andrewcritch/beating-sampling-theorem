import BstLean.Part291WeightVariance
import BstLean.Part291ReciprocalMoments
import BstLean.Part222MassOrders

namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part188

/-- The order-two term in RW uses the sharp Gaussian Poincare constant one. -/
theorem centreCoordinate_variance_network {n : ℕ} (hn : 6 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M : ℝ}
    (hM : DirectionMoment D c M) :
    Integrable (fun ξ => (centreCoordinate D c ξ - ∫ ζ, centreCoordinate D c ζ
      ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    (∫ ξ, (centreCoordinate D c ξ - ∫ ζ, centreCoordinate D c ζ
      ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)) ≤ M / n := by
  obtain ⟨K, hK, hΦ⟩ := centrePhi_lip (by omega) D c hb
  have hg := direction_gradient_first D c hM
  have h := BstLean.Part153.lemmaS_grad c.1.2 hτ hK hΦ hg.1
    (by rw [centrePhi_eq]; exact ae_of_all _ fun _ => le_rfl)
    (invMoment_two_le hn c.1.2 hτ).1 (ae_normSq_ne (by omega) c.1.2 hτ.ne')
  change Integrable (fun ξ => (centreCoordinate D c ξ - ∫ ζ, centreCoordinate D c ζ
      ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧ _ at h
  exact ⟨h.1, h.2.trans hg.2⟩

theorem centreCoordinate_absolute_first {n : ℕ} (hn : 6 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M : ℝ}
    (hM : DirectionMoment D c M) :
    Integrable (fun ξ => |centreCoordinate D c ξ - ∫ ζ, centreCoordinate D c ζ
      ∂stdGauss (Fin n)|) (stdGauss (Fin n)) ∧
    (∫ ξ, |centreCoordinate D c ξ - ∫ ζ, centreCoordinate D c ζ
      ∂stdGauss (Fin n)| ∂stdGauss (Fin n)) ≤ √(M / n) := by
  have hp : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hv := centreCoordinate_variance_network hn D c hτ hb hM
  have h := BstLean.Part132.integral_abs_le_sqrt
    ((measurable_centreCoordinate D c).sub measurable_const) hv.1
  exact ⟨h.1, h.2.trans (sqrt_le_sqrt hv.2)⟩

/-- The full centre and ordinary covariance event supply the second moment
used by GB, in unscaled hidden-vector units. -/
theorem residual_second_from_sources {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {N xi : ℝ} (hN : 0 ≤ N) (hcov : COV_at D c N) (hcen : CENTRE_at D c xi)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1) :
    (∫ ξ, residualTest D c v ξ ^ 2 ∂stdGauss (Fin n)) ≤ N + xi := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have h := Cr_at hn D c hN hcov hcen v
  change 2 / (mA n : ℝ) * (∫ ξ, residualTest D c v ξ ^ 2 ∂stdGauss (Fin n)) ≤
    (N + xi) * (2 / (n : ℝ)) / n * normSq v at h
  rw [hv, mul_one, hm] at h
  have he : (N + xi) * (2 / (n : ℝ)) / n = 2 / (n : ℝ) ^ 2 * (N + xi) := by ring
  rw [he] at h
  exact le_of_mul_le_mul_left h (by positivity)

noncomputable def rwD2 (m s : ℝ) : ℝ :=
  2 * m * s + (BstLean.Part195.rotationConstant 2 * s) ^ 2

noncomputable def rwD4 (m s : ℝ) : ℝ :=
  2 * m * (BstLean.Part195.rotationConstant 2 * s) +
    (BstLean.Part195.rotationConstant 4 * s) ^ 2

structure RWDeficitMoments {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (m s : ℝ) : Prop where
  first_integrable : Integrable (fun x => max (f x ^ 2 - m ^ 2) 0) μ
  second_integrable : Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ 2) μ
  fourth_integrable : Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ 4) μ
  first : (∫ x, max (f x ^ 2 - m ^ 2) 0 ∂μ) ≤ 2 * m * s + s ^ 2
  second : (∫ x, (max (f x ^ 2 - m ^ 2) 0) ^ 2 ∂μ) ≤ rwD2 m s ^ 2
  fourth : (∫ x, (max (f x ^ 2 - m ^ 2) 0) ^ 4 ∂μ) ≤ rwD4 m s ^ 4

theorem rw_deficit_network {n : ℕ} (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M m : ℝ}
    (hM : DirectionMoment D c M)
    (hmean0 : 0 ≤ ∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n))
    (hmean : (∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n)) ≤ m) :
    RWDeficitMoments (stdGauss (Fin n)) (centreCoordinate D c) m (√(M / n)) := by
  have hp : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let μ := stdGauss (Fin n)
  let f := centreCoordinate D c
  let b := ∫ ξ, f ξ ∂μ
  let s := √(M / (n : ℝ))
  have hs : 0 ≤ s := sqrt_nonneg _
  have hm0 : 0 ≤ m := hmean0.trans hmean
  have hmn : 0 ≤ M / (n : ℝ) := div_nonneg hM.1 (Nat.cast_nonneg _)
  have hs2 : s ^ 2 = M / n := sq_sqrt hmn
  have hc2 := BstLean.Part195.rotationConstant_nonneg 2
  have hc4 := BstLean.Part195.rotationConstant_nonneg 4
  have hf := measurable_centreCoordinate D c
  have hvar := centreCoordinate_variance_network (by omega) D c hτ hb hM
  have habs := centreCoordinate_absolute_first (by omega) D c hτ hb hM
  have h4 := BstLean.Part222.directional_moment_even hn (p := 2) (by norm_num) (by norm_num)
    D c hτ hb hM
  have h8 := BstLean.Part222.directional_moment_even hn (p := 4) (by norm_num) (by norm_num)
    D c hτ hb hM
  have hb4 : (∫ ξ, |f ξ - b| ^ 4 ∂μ) ≤ (BstLean.Part195.rotationConstant 2 * s) ^ 4 := by
    simpa only [mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs2] using h4.2
  have hb8 : (∫ ξ, |f ξ - b| ^ 8 ∂μ) ≤ (BstLean.Part195.rotationConstant 4 * s) ^ 8 := by
    simpa only [mul_pow, show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hs2] using h8.2
  have hD2 := square_deficit_moment μ f hf (p := 2) (by norm_num) hmean0 hmean hs
    (mul_nonneg hc2 hs) (by simpa only [sq_abs] using hvar.1) h4.1
    (by simpa only [sq_abs, hs2] using hvar.2) hb4
  have hD4 := square_deficit_moment μ f hf (p := 4) (by norm_num) hmean0 hmean
    (mul_nonneg hc2 hs) (mul_nonneg hc4 hs) h4.1 h8.1 hb4 hb8
  have hDm : Measurable (fun ξ => max (f ξ ^ 2 - m ^ 2) 0) :=
    ((hf.pow_const 2).sub measurable_const).max measurable_const
  have hDi := (BstLean.Part132.integral_abs_le_sqrt hDm hD2.1).1
  have hiD : Integrable (fun ξ => max (f ξ ^ 2 - m ^ 2) 0) μ := by
    have hpos ξ : (0 : ℝ) ≤ max (f ξ ^ 2 - m ^ 2) 0 := le_max_right _ _
    simpa only [abs_of_nonneg (hpos _)] using hDi
  refine ⟨hiD, hD2.1, hD4.1, ?_, hD2.2, hD4.2⟩
  have hpt : ∀ ξ, max (f ξ ^ 2 - m ^ 2) 0 ≤ 2 * m * |f ξ - b| + (f ξ - b) ^ 2 :=
    fun ξ => square_deficit_bound hmean0 hmean
  have hh := integral_mono hiD ((habs.1.const_mul (2 * m)).add hvar.1) hpt
  simp only [Pi.add_apply] at hh
  rw [integral_add (habs.1.const_mul (2 * m)) hvar.1, integral_const_mul] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left habs.2 (by positivity))
    (hvar.2.trans_eq hs2.symm))

end BstLean.BlueprintLow
