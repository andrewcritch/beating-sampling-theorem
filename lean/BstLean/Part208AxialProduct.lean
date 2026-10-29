import BstLean.Part208AxialMoment

/-! Part 208: integrate the longitudinal Gaussian coordinate after the transverse coordinates. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53 measurable_radF)
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)

/-- The complete shifted Gaussian second moment for an axially symmetric input weight.
The only integrability premise is for that weight. -/
theorem axial_product_second_le {d : ℕ} (hd : 1 ≤ d) (a τ p : ℝ) (v : Fin d → ℝ)
    (q : ℝ → ℝ → ℝ) (hq : Measurable (Function.uncurry q))
    (hqi : Integrable (fun y : ℝ × (Fin d → ℝ) => q y.1 (radF53 y.2))
      ((gaussianReal 0 1).prod (stdGauss (Fin d))))
    (hq0 : ∀ Z r, 0 ≤ q Z r) {sp : ℝ}
    (hsp : ∀ Z r, q Z r * axialLong (a + τ * Z) τ r ^ 2 ≤ sp * q Z r) :
    (∫ y : ℝ × (Fin d → ℝ), q y.1 (radF53 y.2) *
      (unitF53 (Fin.cons (a + τ * y.1) (τ • y.2)) ⬝ᵥ Fin.cons p v) ^ 2
      ∂((gaussianReal 0 1).prod (stdGauss (Fin d)))) ≤
      (sp * p ^ 2 + normSq v / d) * ∫ y : ℝ × (Fin d → ℝ), q y.1 (radF53 y.2)
        ∂((gaussianReal 0 1).prod (stdGauss (Fin d))) := by
  let F : (ℝ × (Fin d → ℝ)) → Fin (d + 1) → ℝ :=
    fun y => Fin.cons (a + τ * y.1) (τ • y.2)
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hdm : Measurable (fun y => unitF53 (F y) ⬝ᵥ Fin.cons p v) := by
    simp_rw [dotProduct_comm (unitF53 _) (Fin.cons p v)]
    exact (direction_dot_measurable (Fin.cons p v)).comp hFm
  have hdb : ∀ y, ‖(unitF53 (F y) ⬝ᵥ Fin.cons p v) ^ 2‖ ≤ normSq (Fin.cons p v) := by
    intro y
    have h := abs_dot_le_nrm (Fin.cons p v) (unitF53 (F y))
    have hr : nrm (unitF53 (F y)) ≤ 1 := BstLean.Part162.radF_unitF_le (F y)
    have h1 : |Fin.cons p v ⬝ᵥ unitF53 (F y)| ≤ nrm (Fin.cons p v) := by
      nlinarith [nrm_nonneg (Fin.cons p v)]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    simpa only [Real.norm_eq_abs, abs_pow, nrm_sq, dotProduct_comm] using h2
  have hmain := hqi.mul_bdd (hdm.pow_const 2).aestronglyMeasurable (ae_of_all _ hdb)
  change Integrable (fun y : ℝ × (Fin d → ℝ) => q y.1 (radF53 y.2) *
    (unitF53 (Fin.cons (a + τ * y.1) (τ • y.2)) ⬝ᵥ Fin.cons p v) ^ 2) _ at hmain
  rw [integral_prod _ hmain, integral_prod _ hqi, ← integral_const_mul]
  apply integral_mono_ae hmain.integral_prod_left (hqi.integral_prod_left.const_mul _)
  filter_upwards [hqi.prod_right_ae] with Z hZi
  exact axial_second_le hd (a + τ * Z) τ p v (q Z)
    (hq.comp (measurable_const.prodMk measurable_id)) hZi (hq0 Z) (hsp Z)

end BstLean.Part208
