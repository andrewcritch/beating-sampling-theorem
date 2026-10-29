import BstLean.Part229Extension
import BstLean.Part229Deriv
import BstLean.Part229Sphere

/-! The actual derivative split includes the cap level set and excludes no extra event. -/
namespace BstLean.Part229
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part188
open BstLean.Part148 (EuLip)

noncomputable def sphereScalar {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (f : (Fin n → ℝ) → ℝ) (ξ : Fin n → ℝ) : ℝ := f (sphPt (c + τ • ξ))

theorem weight_sphere_ae_diff {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    {τ a d R Lf : ℝ} (hτ : 0 < τ) (hd : 0 < d) (hR : 0 ≤ R) (hLf : 0 ≤ Lf)
    (f : (Fin n → ℝ) → ℝ) (hf : EuLip f Lf)
    (hfb : ∀ x, nrm x ≤ 1 → |f x| ≤ R) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      DifferentiableAt ℝ (fun ξ => weight a d (sphereScalar c τ f ξ)) ξ := by
  have hl := cappedExtension_lip (a := a) hd hR zero_le_one hLf (le_refl (0 : ℝ))
    f (fun _ => 1) hf (by intro x y; simp) hfb (by intro x hx; norm_num)
  have ha := ae_diff_sphere hn c hτ
    (extensionConstant_nonneg hd hR zero_le_one hLf (le_refl (0 : ℝ))) hl
  have he : (fun ξ => cappedExtension a d f (fun _ => 1) (sphPt (c + τ • ξ))) =
      fun ξ => weight a d (sphereScalar c τ f ξ) := by
    funext ξ
    rw [cappedExtension_on_sphere a d f (fun _ => 1) (normSq_sphPt hn _)]
    simp [sphereScalar]
  rwa [he] at ha

theorem capped_sphere_ae_split {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    {τ a d R Lf Lz : ℝ} (hτ : 0 < τ) (hd : 0 < d) (hR : 0 ≤ R)
    (hLf : 0 ≤ Lf) (hLz : 0 ≤ Lz) (f z : (Fin n → ℝ) → ℝ)
    (hf : EuLip f Lf) (hz : EuLip z Lz)
    (hfb : ∀ x, nrm x ≤ 1 → |f x| ≤ R) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      fderiv ℝ (fun ξ => weight a d (sphereScalar c τ f ξ) * sphereScalar c τ z ξ) ξ =
        weight a d (sphereScalar c τ f ξ) • fderiv ℝ (sphereScalar c τ z) ξ +
          (sphereScalar c τ z ξ * capSlope a d (sphereScalar c τ f ξ)) •
            fderiv ℝ (sphereScalar c τ f) ξ := by
  filter_upwards [ae_diff_sphere hn c hτ hLf hf, ae_diff_sphere hn c hτ hLz hz,
    weight_sphere_ae_diff hn c hτ hd hR hLf f hf hfb] with ξ h1 h2 h3
  exact capped_test_fderiv hd h1 h2 h3

noncomputable def gradientVector {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ξ : Fin n → ℝ) : Fin n → ℝ := fun i => fderiv ℝ f ξ (Pi.single i 1)

lemma gradientVector_measurable {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Measurable (gradientVector f) := by
  exact measurable_pi_lambda fun i => measurable_fderiv_apply_const ℝ f (Pi.single i 1)

noncomputable def projectedEnergy {n : ℕ} (a d : ℝ) (f z : (Fin n → ℝ) → ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  normSq (weight a d (f ξ) • gradientVector z ξ)

noncomputable def capEnergy {n : ℕ} (a d : ℝ) (f z : (Fin n → ℝ) → ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  normSq ((z ξ * capSlope a d (f ξ)) • gradientVector f ξ)

lemma energy_formulas {n : ℕ} (a d : ℝ) (f z : (Fin n → ℝ) → ℝ) (ξ : Fin n → ℝ) :
    projectedEnergy a d f z ξ = weight a d (f ξ) ^ 2 * normSq (gradientVector z ξ) ∧
    capEnergy a d f z ξ = (z ξ * capSlope a d (f ξ)) ^ 2 * normSq (gradientVector f ξ) := by
  constructor <;> exact normSq_smul _ _

lemma normSq_add_bound {n : ℕ} (u v : Fin n → ℝ) :
    normSq (u + v) ≤ normSq u + 2 * (√(normSq u) * √(normSq v)) + normSq v := by
  have h := pow_le_pow_left₀ (nrm_nonneg _) (nrm_add_le u v) 2
  rw [nrm_sq, add_sq, nrm_sq, nrm_sq] at h
  simpa only [nrm, mul_assoc] using h

theorem capped_sphere_ae_gradient {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    {τ a d R Lf Lz : ℝ} (hτ : 0 < τ) (hd : 0 < d) (hR : 0 ≤ R)
    (hLf : 0 ≤ Lf) (hLz : 0 ≤ Lz) (f z : (Fin n → ℝ) → ℝ)
    (hf : EuLip f Lf) (hz : EuLip z Lz)
    (hfb : ∀ x, nrm x ≤ 1 → |f x| ≤ R) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      normSq (gradientVector (fun ξ => weight a d (sphereScalar c τ f ξ) *
        sphereScalar c τ z ξ) ξ) ≤
        projectedEnergy a d (sphereScalar c τ f) (sphereScalar c τ z) ξ +
        2 * (√(projectedEnergy a d (sphereScalar c τ f) (sphereScalar c τ z) ξ) *
          √(capEnergy a d (sphereScalar c τ f) (sphereScalar c τ z) ξ)) +
        capEnergy a d (sphereScalar c τ f) (sphereScalar c τ z) ξ := by
  filter_upwards [capped_sphere_ae_split (a := a) hn c hτ hd hR hLf hLz f z hf hz hfb]
    with ξ h
  have he : gradientVector (fun ξ => weight a d (sphereScalar c τ f ξ) *
      sphereScalar c τ z ξ) ξ =
      weight a d (sphereScalar c τ f ξ) • gradientVector (sphereScalar c τ z) ξ +
        (sphereScalar c τ z ξ * capSlope a d (sphereScalar c τ f ξ)) •
          gradientVector (sphereScalar c τ f) ξ := by
    funext i
    simp [gradientVector, h]
  rw [he]
  exact normSq_add_bound _ _

end BstLean.Part229
