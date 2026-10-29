import BstLean.Part200Moments
import BstLean.Part132Upper

/-! A low-length complement uses its probability and a higher moment once. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part153

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- No independence premise connects the error to the bad set. -/
theorem restricted_moment_le {s : ℕ} {E : Ω → ℝ} (hE : Measurable E)
    (hE0 : ∀ ω, 0 ≤ E ω) (hi : Integrable (fun ω => E ω ^ (2 * s)) μ)
    {B : Set Ω} (hB : MeasurableSet B) :
    Integrable (B.indicator (fun ω => E ω ^ s)) μ ∧
    (∫ ω in B, E ω ^ s ∂μ) ≤
      √(∫ ω, E ω ^ (2 * s) ∂μ) * √(μ.real B) := by
  classical
  let I : Ω → ℝ := B.indicator (fun _ => 1)
  have hIm : Measurable I := measurable_const.indicator hB
  have hI2 : Integrable (fun ω => I ω ^ 2) μ := by
    have he : (fun ω => I ω ^ 2) = I := by
      funext ω; by_cases h : ω ∈ B <;> simp [I, h]
    rw [he]; exact (integrable_const (1 : ℝ)).indicator hB
  have heI : (∫ ω, I ω ^ 2 ∂μ) = μ.real B := by
    have he : (fun ω => I ω ^ 2) = I := by
      funext ω; by_cases h : ω ∈ B <;> simp [I, h]
    rw [he, integral_indicator hB]
    simp
  have he2 : (fun ω => (E ω ^ s) ^ 2) = fun ω => E ω ^ (2 * s) := by
    funext ω; rw [← pow_mul, Nat.mul_comm]
  obtain ⟨hIi, hIb⟩ := BstLean.Part132.integral_mul_le_sqrt
    (hE.pow_const s) hIm (he2.symm ▸ hi) hI2
  have he : (fun ω => |E ω ^ s| * |I ω|) = B.indicator (fun ω => E ω ^ s) := by
    funext ω
    by_cases h : ω ∈ B <;> simp [I, h, abs_of_nonneg (pow_nonneg (hE0 ω) s)]
  rw [he] at hIi hIb
  rw [integral_indicator hB, heI] at hIb
  simp_rw [he2] at hIb
  exact ⟨hIi, hIb⟩

/-- A supplied higher moment and one supplied probability give a bad-set payment. -/
theorem restricted_moment_bound {s : ℕ} {E : Ω → ℝ} (hE : Measurable E)
    (hE0 : ∀ ω, 0 ≤ E ω) (hi : Integrable (fun ω => E ω ^ (2 * s)) μ)
    {B : Set Ω} (hB : MeasurableSet B) {M P : ℝ}
    (hM : (∫ ω, E ω ^ (2 * s) ∂μ) ≤ M) (hP : μ.real B ≤ P) :
    (∫ ω in B, E ω ^ s ∂μ) ≤ √M * √P := by
  exact (restricted_moment_le hE hE0 hi hB).2.trans
    (mul_le_mul (sqrt_le_sqrt hM) (sqrt_le_sqrt hP) (sqrt_nonneg _) (sqrt_nonneg _))

/-- Combine the regular and low-length contributions without an event-union payment. -/
theorem moment_of_regular_and_complement {s : ℕ} {E : Ω → ℝ}
    (hE : Measurable E) (hE0 : ∀ ω, 0 ≤ E ω)
    (hi : Integrable (fun ω => E ω ^ s) μ)
    (hi2 : Integrable (fun ω => E ω ^ (2 * s)) μ)
    {B : Set Ω} (hB : MeasurableSet B) {R M P : ℝ}
    (hR : (∫ ω in Bᶜ, E ω ^ s ∂μ) ≤ R)
    (hM : (∫ ω, E ω ^ (2 * s) ∂μ) ≤ M) (hP : μ.real B ≤ P) :
    (∫ ω, E ω ^ s ∂μ) ≤ R + √M * √P := by
  have h := restricted_moment_bound hE hE0 hi2 hB hM hP
  have he := integral_add_compl hB hi
  linarith

end BstLean.Part200
