import BstLean.Part205Conditional
import BstLean.Part141Atom
import BstLean.Part153Op

/-! Cancellation in the actual World row distance. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part205
open BstLean.Part29 BstLean.Part105 BstLean.Part133
open BstLean.Part153 (nrm)

lemma relu_cancel (x : ℝ) : relu x = (x + |x|) / 2 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, relu_of_nonneg h]; ring
  · rw [abs_of_nonpos h, relu_of_nonpos h]; ring

/-- Equal means cancel the linear terms of two ReLU averages. -/
theorem integral_relu_cancellation {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → ℝ} {g : β → ℝ} (hf : Integrable f μ) (hg : Integrable g ν)
    (hmean : ∫ x, f x ∂μ = ∫ y, g y ∂ν) :
    (∫ x, relu (f x) ∂μ) - (∫ y, relu (g y) ∂ν) =
      ((∫ x, |f x| ∂μ) - (∫ y, |g y| ∂ν)) / 2 := by
  simp_rw [relu_cancel]
  rw [integral_div, integral_div, integral_add hf hf.abs, integral_add hg hg.abs,
    hmean]
  ring

/-- The smoothing Gaussian and the sphere average have exactly the same linear mean. -/
theorem world_row_cancellation {N m : ℕ} (hN : 1 ≤ N)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (σ : ℝ) (ξ : Fin m → ℝ) :
    rowMean (fun u => reluV (M₁.mulVec u)) ξ - rowSmooth (h1bar M₁) σ ξ =
      ((∫ u, |dotp ξ (reluV (M₁.mulVec u))| ∂uniformSphere N) -
        (∫ z, |dotp ξ (h1bar M₁) + σ * z| ∂gaussianReal 0 1)) / 2 := by
  have hf : Integrable (fun u => dotp ξ (reluV (M₁.mulVec u))) (uniformSphere N) :=
    sphere_cont_integrable hN
      (continuous_dotp.comp (continuous_const.prodMk (continuous_h1_u M₁)))
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    simpa using integrable_pow_gauss 1
  have hg := (integrable_const (dotp ξ (h1bar M₁))).add (hz.const_mul σ)
  apply integral_relu_cancellation hf hg
  change (∫ u, dotp ξ (reluV (M₁.mulVec u)) ∂uniformSphere N) =
    ∫ z, dotp ξ (h1bar M₁) + σ * z ∂gaussianReal 0 1
  rw [integral_add (integrable_const _) (hz.const_mul σ), integral_const_mul,
    integral_id_gaussianReal]
  simpa using (dotp_h1bar hN ξ M₁).symm

end BstLean.Part233
#print axioms BstLean.Part233.integral_relu_cancellation
#print axioms BstLean.Part233.world_row_cancellation
