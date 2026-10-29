import BstLean.Part208Reflection

/-! Part 208: the axial covariance source for any fixed unit centre direction. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53 measurable_radF)
open BstLean.Part161 (hhMat measurable_hh stdGauss_map_hh)

noncomputable def axialWeight {d : ℕ} (u : Fin (d + 1) → ℝ) (q : ℝ → ℝ → ℝ)
    (ξ : Fin (d + 1) → ℝ) : ℝ :=
  q ((hhMat u *ᵥ ξ) 0) (radF53 (Fin.tail (hhMat u *ᵥ ξ)))

lemma axialWeight_measurable {d : ℕ} (u : Fin (d + 1) → ℝ) (q : ℝ → ℝ → ℝ)
    (hq : Measurable (Function.uncurry q)) : Measurable (axialWeight u q) := by
  exact hq.comp (((measurable_pi_apply 0).comp (measurable_hh u)).prodMk
    (measurable_radF.comp
      ((by fun_prop : Measurable (fun ξ : Fin (d + 1) → ℝ => Fin.tail ξ)).comp
        (measurable_hh u))))

/-- For an axially symmetric input weight, the transverse covariance is bounded
by its mean weight divided by the transverse dimension. -/
theorem gaussian_rotated_second_le {d : ℕ} (hd : 1 ≤ d) (u : Fin (d + 1) → ℝ)
    (hu : normSq u = 1) (a τ : ℝ) (f : Fin (d + 1) → ℝ)
    (q : ℝ → ℝ → ℝ) (hq : Measurable (Function.uncurry q))
    (hqi : Integrable (axialWeight u q) (stdGauss (Fin (d + 1))))
    (hq0 : ∀ Z r, 0 ≤ q Z r) {sp : ℝ}
    (hsp : ∀ Z r, q Z r * axialLong (a + τ * Z) τ r ^ 2 ≤ sp * q Z r) :
    (∫ ξ, axialWeight u q ξ * (unitF53 (a • u + τ • ξ) ⬝ᵥ f) ^ 2
      ∂stdGauss (Fin (d + 1))) ≤
      (sp * (u ⬝ᵥ f) ^ 2 + normSq f / d) *
        ∫ ξ, axialWeight u q ξ ∂stdGauss (Fin (d + 1)) := by
  have hwm := axialWeight_measurable u q hq
  have hqi' : Integrable (fun ξ : Fin (d + 1) → ℝ => q (ξ 0) (radF53 (Fin.tail ξ)))
      (stdGauss (Fin (d + 1))) := by
    have hm : Integrable (axialWeight u q)
        ((stdGauss (Fin (d + 1))).map (fun ξ => hhMat u *ᵥ ξ)) := by
      rwa [stdGauss_map_hh]
    have h := (integrable_map_measure hwm.aestronglyMeasurable
      (measurable_hh u).aemeasurable).mp hm
    simpa only [Function.comp_def, axialWeight, hh_involutive] using h
  have hmainm : Measurable (fun ξ : Fin (d + 1) → ℝ =>
      axialWeight u q ξ * (unitF53 (a • u + τ • ξ) ⬝ᵥ f) ^ 2) := by
    apply hwm.mul
    apply Measurable.pow_const
    simp_rw [dotProduct_comm (unitF53 _) f]
    exact (direction_dot_measurable f).comp (by fun_prop)
  have hmap1 := integral_map (μ := stdGauss (Fin (d + 1)))
    (measurable_hh u).aemeasurable hmainm.aestronglyMeasurable
  have hmap2 := integral_map (μ := stdGauss (Fin (d + 1)))
    (measurable_hh u).aemeasurable hwm.aestronglyMeasurable
  rw [stdGauss_map_hh] at hmap1 hmap2
  have hpoint : ∀ ξ : Fin (d + 1) → ℝ,
      unitF53 (a • u + τ • (hhMat u *ᵥ ξ)) ⬝ᵥ f =
      unitF53 (Fin.cons a (0 : Fin d → ℝ) + τ • ξ) ⬝ᵥ (hhMat u *ᵥ f) := by
    intro ξ
    rw [← hh_shift hu, hh_unitF, hh_dot_right]
  rw [hmap1, hmap2]
  simp only [axialWeight, hh_involutive, hpoint]
  have h := gaussian_axial_second_le hd a τ (hhMat u *ᵥ f) q hq hqi' hq0 hsp
  rw [hh_zero_coordinate hu] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact add_le_add le_rfl
      (div_le_div_of_nonneg_right (hh_tail_normSq_le u f) (Nat.cast_nonneg d))
  · exact integral_nonneg fun ξ => hq0 _ _

end BstLean.Part208
