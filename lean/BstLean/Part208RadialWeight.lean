import BstLean.Part208Latitude

/-! Part 208: bounded latitude coefficients need only the integrability of the weight. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53 measurable_radF)
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)

/-- Exact radial-weighted covariance, with no separate moment-integrability premises. -/
theorem radial_second_bounded {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℝ)
    (q a b : ℝ → ℝ) (hq : Measurable q) (ha : Measurable a) (hb : Measurable b)
    (hqi : Integrable (fun z : Fin d → ℝ => q (radF53 z)) (stdGauss (Fin d)))
    {A B : ℝ} (ha1 : ∀ r, |a r| ≤ A) (hb1 : ∀ r, |b r| ≤ B) :
    (∫ z, q (radF53 z) * (a (radF53 z) + b (radF53 z) *
      (v ⬝ᵥ unitF53 z)) ^ 2 ∂stdGauss (Fin d)) =
      (∫ z, q (radF53 z) * a (radF53 z) ^ 2 ∂stdGauss (Fin d)) +
      normSq v / d * ∫ z, q (radF53 z) * b (radF53 z) ^ 2 ∂stdGauss (Fin d) := by
  have ha2 : ∀ r, ‖a r ^ 2‖ ≤ A ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (ha1 r) 2
  have hb2 : ∀ r, ‖b r ^ 2‖ ≤ B ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb1 r) 2
  have hai := hqi.mul_bdd ((ha.comp measurable_radF).pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun z => ha2 (radF53 z))
  have hbi := hqi.mul_bdd ((hb.comp measurable_radF).pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun z => hb2 (radF53 z))
  have habi := (hqi.mul_bdd (ha.comp measurable_radF).aestronglyMeasurable
    (ae_of_all _ fun z => (show ‖a (radF53 z)‖ ≤ A from ha1 _))).mul_bdd
      (hb.comp measurable_radF).aestronglyMeasurable
      (ae_of_all _ fun z => (show ‖b (radF53 z)‖ ≤ B from hb1 _))
  have hdot : ∀ z : Fin d → ℝ, ‖v ⬝ᵥ unitF53 z‖ ≤ nrm v := by
    intro z
    rw [Real.norm_eq_abs]
    refine (abs_dot_le_nrm v (unitF53 z)).trans ?_
    have h := BstLean.Part162.radF_unitF_le z
    change nrm (unitF53 z) ≤ 1 at h
    nlinarith [nrm_nonneg v]
  have hdotsq : ∀ z : Fin d → ℝ, ‖(v ⬝ᵥ unitF53 z) ^ 2‖ ≤ normSq v := by
    intro z
    have h := pow_le_pow_left₀ (norm_nonneg _) (hdot z) 2
    simpa only [Real.norm_eq_abs, abs_pow, nrm_sq] using h
  have hcross : Integrable (fun z : Fin d → ℝ => (v ⬝ᵥ unitF53 z) *
      (2 * q (radF53 z) * a (radF53 z) * b (radF53 z))) (stdGauss (Fin d)) := by
    convert (habi.const_mul 2).bdd_mul (direction_dot_measurable v).aestronglyMeasurable
      (ae_of_all _ hdot) using 1
    ext z
    dsimp only [Function.comp_apply]
    ring
  have hsquare := hbi.bdd_mul ((direction_dot_measurable v).pow_const 2).aestronglyMeasurable
    (ae_of_all _ hdotsq)
  exact radial_affine_second hd v q a b hq ha hb hai hcross hsquare

end BstLean.Part208
