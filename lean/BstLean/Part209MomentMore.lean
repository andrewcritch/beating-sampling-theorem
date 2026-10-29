import BstLean.Part209MomentTools

namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real
open BstLean.Part152 BstLean.Part153
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem moment_mono {X Y : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXY : ∀ ω, X ω ≤ Y ω) {s : ℕ} {a : ℝ}
    (hi : Integrable (fun ω => Y ω ^ s) μ) (hb : (∫ ω, Y ω ^ s ∂μ) ≤ a ^ s) :
    Integrable (fun ω => X ω ^ s) μ ∧ (∫ ω, X ω ^ s ∂μ) ≤ a ^ s := by
  have hdom : ∀ ω, X ω ^ s ≤ Y ω ^ s := fun ω => pow_le_pow_left₀ (hX0 ω) (hXY ω) _
  have hI := hi.mono' (hX.pow_const s).aestronglyMeasurable (ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (pow_nonneg (hX0 ω) s)]
    exact hdom ω)
  exact ⟨hI, (integral_mono hI hi hdom).trans hb⟩

theorem moment_const_mul {X : Ω → ℝ} {c a : ℝ} (hc : 0 ≤ c) {s : ℕ}
    (hi : Integrable (fun ω => X ω ^ s) μ) (hb : (∫ ω, X ω ^ s ∂μ) ≤ a ^ s) :
    Integrable (fun ω => (c * X ω) ^ s) μ ∧
      (∫ ω, (c * X ω) ^ s ∂μ) ≤ (c * a) ^ s := by
  simp_rw [mul_pow]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hb (pow_nonneg hc _)

end BstLean.Part209
