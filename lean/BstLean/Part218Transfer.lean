import BstLean.Part218ScaledTrace

/-! Exact transfer under the actual He-scaled matrix distribution. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part133 BstLean.Part214

theorem gaussMat_transfer {N m : ℕ} (v : ℝ)
    {f g : Matrix (Fin m) (Fin N) ℝ → ℝ} (mf : Measurable f)
    (he : ∀ M, f (√v • M) = g M) :
    (Integrable f (gaussMat m N v) ↔ Integrable g (gaussMat m N 1)) ∧
    (∫ M, f M ∂gaussMat m N v) = ∫ M, g M ∂gaussMat m N 1 := by
  have mp := gaussMat_scale m N v
  constructor
  · rw [← mp.map_eq, integrable_map_measure mf.aestronglyMeasurable mp.measurable.aemeasurable]
    change Integrable (fun M => f (√v • M)) (gaussMat m N 1) ↔ _
    simp_rw [he]
  · rw [← mp.map_eq, integral_map mp.measurable.aemeasurable mf.aestronglyMeasurable]
    simp_rw [he]

end BstLean.Part218
#print axioms BstLean.Part218.gaussMat_transfer
