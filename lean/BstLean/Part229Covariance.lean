import BstLean.Part229Split
import BstLean.Part188Poincare

/-! Poincare for the capped scalar test under the actual stand-in distribution. -/
namespace BstLean.Part229
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part188
open BstLean.Part148 (EuLip)

lemma sphereScalar_measurable {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    {f : (Fin n → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : EuLip f L) :
    Measurable (sphereScalar c τ f) := by
  exact (hf.continuous hL).measurable.comp
    (measurable_sphPt.comp (by fun_prop))

theorem capped_energies_integrable {n : ℕ} (hn : 4 ≤ n) (c : Fin n → ℝ)
    {τ a d R S Lf Lz : ℝ} (hτ : 0 < τ) (hd : 0 < d) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hLf : 0 ≤ Lf) (hLz : 0 ≤ Lz) (f z : (Fin n → ℝ) → ℝ)
    (hf : EuLip f Lf) (hz : EuLip z Lz)
    (hfb : ∀ x, nrm x ≤ 1 → |f x| ≤ R)
    (hzb : ∀ x, nrm x ≤ 1 → |z x| ≤ S) :
    Integrable (projectedEnergy a d (sphereScalar c τ f) (sphereScalar c τ z))
      (stdGauss (Fin n)) ∧
    Integrable (capEnergy a d (sphereScalar c τ f) (sphereScalar c τ z))
      (stdGauss (Fin n)) := by
  have hn1 : 1 ≤ n := by omega
  have hfm := sphereScalar_measurable c τ hLf hf
  have hzm := sphereScalar_measurable c τ hLz hz
  have hwp := (weight_continuous a hd).measurable.comp hfm
  have hsp := (capSlope_measurable a d).comp hfm
  have hmA : Measurable (projectedEnergy a d (sphereScalar c τ f) (sphereScalar c τ z)) := by
    unfold projectedEnergy
    exact (continuous_normSq.measurable).comp
      (hwp.smul (gradientVector_measurable _))
  have hmB : Measurable (capEnergy a d (sphereScalar c τ f) (sphereScalar c τ z)) := by
    unfold capEnergy
    exact (continuous_normSq.measurable).comp
      ((hzm.mul hsp).smul (gradientVector_measurable _))
  have hi := (invMoment_one_le hn c hτ).1
  have hne := ae_normSq_ne hn1 c hτ.ne'
  constructor
  · refine Integrable.mono' (hi.const_mul ((√d)⁻¹ ^ 2 * (τ ^ 2 * Lz ^ 2)))
      hmA.aestronglyMeasurable ?_
    filter_upwards [hne] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ projectedEnergy a d
      (sphereScalar c τ f) (sphereScalar c τ z) ξ from normSq_nonneg _),
      (energy_formulas _ _ _ _ _).1]
    have hw := pow_le_pow_left₀ (Real.sqrt_nonneg _) (weight_le (a := a)
      (f := sphereScalar c τ f ξ) hd) 2
    have hg := gradSq_sph_le c τ hLz hz ξ hξ
    have hh := mul_le_mul hw hg (normSq_nonneg _) (sq_nonneg _)
    convert hh using 1 <;> first | rfl |
      simp only [sphereScalar, gradientVector, normSq, mul_assoc]
  · refine Integrable.mono' (hi.const_mul ((S * (R / (d * √d))) ^ 2 * (τ ^ 2 * Lf ^ 2)))
      hmB.aestronglyMeasurable ?_
    filter_upwards [hne] with ξ hξ
    have hunit : nrm (sphPt (c + τ • ξ)) ≤ 1 :=
      (nrm_of_normSq_one_cr (normSq_sphPt hn1 _)).le
    have hs := capSlope_bound (a := a) hd hR (hfb _ hunit)
    have hzbound := hzb _ hunit
    have hc : |sphereScalar c τ z ξ * capSlope a d (sphereScalar c τ f ξ)| ≤
        S * (R / (d * √d)) := by
      rw [abs_mul]
      exact mul_le_mul hzbound hs (abs_nonneg _) hS
    have hc2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
    rw [sq_abs] at hc2
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ capEnergy a d
      (sphereScalar c τ f) (sphereScalar c τ z) ξ from normSq_nonneg _),
      (energy_formulas _ _ _ _ _).2]
    have hg := gradSq_sph_le c τ hLf hf ξ hξ
    have hh := mul_le_mul hc2 hg (normSq_nonneg _) (sq_nonneg _)
    convert hh using 1 <;> first | rfl |
      simp only [sphereScalar, gradientVector, normSq, mul_assoc]

lemma sqrt_pair_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A B : X → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x)
    (hA : Integrable A μ) (hB : Integrable B μ) :
    Integrable (fun x => √(A x) * √(B x)) μ := by
  refine Integrable.mono' (hA.abs.add hB.abs)
    ((Real.continuous_sqrt.measurable.comp hAm).mul
      (Real.continuous_sqrt.measurable.comp hBm)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  change √(A x) * √(B x) ≤ |A x| + |B x|
  rw [abs_of_nonneg (hA0 x), abs_of_nonneg (hB0 x)]
  nlinarith [sq_nonneg (√(A x) - √(B x)), Real.sq_sqrt (hA0 x),
    Real.sq_sqrt (hB0 x)]

theorem capped_covariance {n : ℕ} (hn : 6 ≤ n) (c : Fin n → ℝ)
    {τ a d R S Lf Lz N C : ℝ} (hτ : 0 < τ) (hd : 0 < d) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hLf : 0 ≤ Lf) (hLz : 0 ≤ Lz) (f z : (Fin n → ℝ) → ℝ)
    (hf : EuLip f Lf) (hz : EuLip z Lz)
    (hfb : ∀ x, nrm x ≤ 1 → |f x| ≤ R)
    (hzb : ∀ x, nrm x ≤ 1 → |z x| ≤ S) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hA : ∫ ξ, projectedEnergy a d (sphereScalar c τ f) (sphereScalar c τ z) ξ
      ∂stdGauss (Fin n) ≤ N)
    (hB : ∫ ξ, capEnergy a d (sphereScalar c τ f) (sphereScalar c τ z) ξ
      ∂stdGauss (Fin n) ≤ C) :
    Integrable (fun ξ => (weight a d (sphereScalar c τ f ξ) * sphereScalar c τ z ξ -
      ∫ ξ', weight a d (sphereScalar c τ f ξ') * sphereScalar c τ z ξ'
        ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    (∫ ξ, (weight a d (sphereScalar c τ f ξ) * sphereScalar c τ z ξ -
      ∫ ξ', weight a d (sphereScalar c τ f ξ') * sphereScalar c τ z ξ'
        ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)) ≤ (√N + √C) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  let A := projectedEnergy a d (sphereScalar c τ f) (sphereScalar c τ z)
  let B := capEnergy a d (sphereScalar c τ f) (sphereScalar c τ z)
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun _ => normSq_nonneg _
  have hB0 : ∀ ξ, 0 ≤ B ξ := fun _ => normSq_nonneg _
  have hfm := sphereScalar_measurable c τ hLf hf
  have hzm := sphereScalar_measurable c τ hLz hz
  have hmA : Measurable A := BstLean.Part130.measurable_normSq.comp
    (((weight_continuous a hd).measurable.comp hfm).smul (gradientVector_measurable _))
  have hmB : Measurable B := BstLean.Part130.measurable_normSq.comp
    ((hzm.mul ((capSlope_measurable a d).comp hfm)).smul (gradientVector_measurable _))
  obtain ⟨hAi, hBi⟩ := capped_energies_integrable (by omega : 4 ≤ n) c
    hτ hd hR hS hLf hLz f z hf hz hfb hzb
  have hABi := sqrt_pair_integrable hmA hmB hA0 hB0 hAi hBi
  have he : (fun ξ => cappedExtension a d f z (sphPt (c + τ • ξ))) =
      fun ξ => weight a d (sphereScalar c τ f ξ) * sphereScalar c τ z ξ := by
    funext ξ
    exact cappedExtension_on_sphere a d f z (normSq_sphPt hn1 _)
  have hg := capped_sphere_ae_gradient (a := a) hn1 c hτ hd hR hLf hLz f z hf hz hfb
  have hp := weighted_covariance_of_gradient c hτ (cappedExtension a d f z)
    (extensionConstant_nonneg hd hR hS hLf hLz)
    (cappedExtension_lip hd hR hS hLf hLz f z hf hz hfb hzb)
    A B hA0 hB0 hAi hBi hABi
    (by rw [he]; exact hg) (invMoment_two_le hn c hτ).1 (ae_normSq_ne hn1 c hτ.ne')
    hN hC hA hB
  have he' := congrFun he
  simpa only [he'] using hp

end BstLean.Part229
