import BstLean.Part208AxialProduct
import BstLean.Part161Lat

/-! Part 208: the axial covariance source on the original standard Gaussian space. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53 measurable_radF)

theorem gaussian_cons_map (d : ℕ) :
    ((gaussianReal 0 1).prod (stdGauss (Fin d))).map
      (fun y : ℝ × (Fin d → ℝ) => Fin.cons y.1 y.2) = stdGauss (Fin (d + 1)) := by
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => gaussianReal 0 1) 0).symm
  have he : (fun y : ℝ × (Fin d → ℝ) => Fin.cons y.1 y.2) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm := by
    funext y
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
  rw [he]
  exact hmp.map_eq

lemma shift_cons {d : ℕ} (a τ Z : ℝ) (G : Fin d → ℝ) :
    (Fin.cons a (0 : Fin d → ℝ)) + τ • Fin.cons Z G = Fin.cons (a + τ * Z) (τ • G) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The original standard Gaussian input gives the sharp transverse dimension factor.
The weight can contain an axial input-set restriction. -/
theorem gaussian_axial_second_le {d : ℕ} (hd : 1 ≤ d) (a τ : ℝ) (f : Fin (d + 1) → ℝ)
    (q : ℝ → ℝ → ℝ) (hq : Measurable (Function.uncurry q))
    (hqi : Integrable (fun ξ : Fin (d + 1) → ℝ => q (ξ 0) (radF53 (Fin.tail ξ)))
      (stdGauss (Fin (d + 1))))
    (hq0 : ∀ Z r, 0 ≤ q Z r) {sp : ℝ}
    (hsp : ∀ Z r, q Z r * axialLong (a + τ * Z) τ r ^ 2 ≤ sp * q Z r) :
    (∫ ξ, q (ξ 0) (radF53 (Fin.tail ξ)) *
      (unitF53 (Fin.cons a (0 : Fin d → ℝ) + τ • ξ) ⬝ᵥ f) ^ 2
      ∂stdGauss (Fin (d + 1))) ≤
      (sp * (f 0) ^ 2 + normSq (Fin.tail f) / d) *
        ∫ ξ : Fin (d + 1) → ℝ, q (ξ 0) (radF53 (Fin.tail ξ)) ∂stdGauss (Fin (d + 1)) := by
  let C : (ℝ × (Fin d → ℝ)) → Fin (d + 1) → ℝ := fun y => Fin.cons y.1 y.2
  have hCm : Measurable C := by dsimp [C]; fun_prop
  have hqm : Measurable (fun ξ : Fin (d + 1) → ℝ => q (ξ 0) (radF53 (Fin.tail ξ))) := by
    have htail : Measurable (fun ξ : Fin (d + 1) → ℝ => Fin.tail ξ) := by fun_prop
    exact hq.comp ((measurable_pi_apply 0).prodMk (measurable_radF.comp htail))
  have hqi' : Integrable (fun y : ℝ × (Fin d → ℝ) => q y.1 (radF53 y.2))
      ((gaussianReal 0 1).prod (stdGauss (Fin d))) := by
    rw [← gaussian_cons_map d] at hqi
    have h := (integrable_map_measure hqm.aestronglyMeasurable hCm.aemeasurable).mp hqi
    simpa only [Function.comp_def, C, Fin.cons_zero, Fin.tail_cons] using h
  have hmainm : Measurable (fun ξ : Fin (d + 1) → ℝ => q (ξ 0) (radF53 (Fin.tail ξ)) *
      (unitF53 (Fin.cons a (0 : Fin d → ℝ) + τ • ξ) ⬝ᵥ f) ^ 2) := by
    apply hqm.mul
    apply Measurable.pow_const
    simp_rw [dotProduct_comm (unitF53 _) f]
    exact (direction_dot_measurable f).comp (by fun_prop)
  have hmap1 := integral_map (μ := (gaussianReal 0 1).prod (stdGauss (Fin d)))
    hCm.aemeasurable hmainm.aestronglyMeasurable
  have hmap2 := integral_map (μ := (gaussianReal 0 1).prod (stdGauss (Fin d)))
    hCm.aemeasurable hqm.aestronglyMeasurable
  rw [gaussian_cons_map] at hmap1 hmap2
  rw [hmap1, hmap2]
  simp only [C, Fin.cons_zero, Fin.tail_cons, shift_cons]
  have h := axial_product_second_le hd a τ (f 0) (Fin.tail f) q hq hqi' hq0 hsp
  simpa only [Fin.cons_self_tail] using h

end BstLean.Part208
