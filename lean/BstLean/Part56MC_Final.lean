import BstLean.Part56MC_Operator
import Mathlib.Probability.Moments.Covariance

namespace BstLean.Part56

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (varU)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma preserving_mean {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    (G : β → ℝ) (hG : AEStronglyMeasurable G ν) :
    (∫ x, G (f x) ∂μ) = ∫ y, G y ∂ν := by
  have h := integral_map hf.aemeasurable (hf.map_eq.symm ▸ hG)
  rw [hf.map_eq] at h
  exact h.symm

private lemma toLp_norm (F : (ι → ℝ) → ℝ) (hF : MemLp F 2 (stdGauss ι)) :
    ‖hF.toLp F‖ = Real.sqrt (∫ x, F x ^ 2 ∂stdGauss ι) := by
  have hs : ‖hF.toLp F‖ ^ 2 = ∫ x, F x ^ 2 ∂stdGauss ι := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    simp [hx]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem mc56_full (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (ha : |a| ≤ 1)
    (Φ Ψ : (ι → ℝ) → ℝ) (hΦ : MemLp Φ 2 (stdGauss ι))
    (hΨ : MemLp Ψ 2 (stdGauss ι)) :
    |(∫ g, ∫ h, Φ g * Ψ (a • g + b • h) ∂stdGauss ι ∂stdGauss ι) -
      (∫ g, Φ g ∂stdGauss ι) * (∫ g, Ψ g ∂stdGauss ι)| ≤
      |a| * Real.sqrt (∫ g, (Φ g - ∫ x, Φ x ∂stdGauss ι) ^ 2 ∂stdGauss ι) *
        Real.sqrt (∫ g, (Ψ g - ∫ x, Ψ x ∂stdGauss ι) ^ 2 ∂stdGauss ι) := by
  let μ := stdGauss ι
  let mΦ := ∫ g, Φ g ∂μ
  let mΨ := ∫ g, Ψ g ∂μ
  let Fc : (ι → ℝ) → ℝ := fun g => Φ g - mΦ
  let Gc : (ι → ℝ) → ℝ := fun g => Ψ g - mΨ
  have hFc : MemLp Fc 2 μ := hΦ.sub (memLp_const _)
  have hGc : MemLp Gc 2 μ := hΨ.sub (memLp_const _)
  let F := hFc.toLp Fc
  let G := hGc.toLp Gc
  have hFm : (∫ g, F g ∂μ) = 0 := by
    rw [integral_congr_ae hFc.coeFn_toLp]
    change (∫ g, Φ g - mΦ ∂μ) = 0
    rw [integral_sub (hΦ.integrable (by simp)) (integrable_const _)]
    simp [mΦ, μ]
  have hGm : (∫ g, G g ∂μ) = 0 := by
    rw [integral_congr_ae hGc.coeFn_toLp]
    change (∫ g, Ψ g - mΨ ∂μ) = 0
    rw [integral_sub (hΨ.integrable (by simp)) (integrable_const _)]
    simp [mΨ, μ]
  have hfst := measurePreserving_fst (μ := μ) (ν := μ)
  have hmix := mc56_mix_preserving (ι := ι) a b hab
  have hU := hΦ.comp_measurePreserving hfst
  have hV := hΨ.comp_measurePreserving hmix
  have hmeanU := preserving_mean hfst Φ hΦ.aestronglyMeasurable
  have hmeanV := preserving_mean hmix Ψ hΨ.aestronglyMeasurable
  have hcov := ProbabilityTheory.covariance_eq_sub hU hV
  simp only [Pi.mul_apply, Function.comp_apply] at hcov
  rw [hmeanU, hmeanV] at hcov
  have hi : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => Φ p.1 * Ψ (a • p.1 + b • p.2))
      (μ.prod μ) := hU.integrable_mul hV
  rw [integral_prod _ hi] at hcov
  have hci := hFc.comp_measurePreserving hfst
  have hcj := hGc.comp_measurePreserving hmix
  have hcii : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => Fc p.1 * Gc (a • p.1 + b • p.2))
      (μ.prod μ) := hci.integrable_mul hcj
  have hcenter : inner ℝ F (mc56_centeredOperator a b hab G) =
      (∫ g, ∫ h, Φ g * Ψ (a • g + b • h) ∂μ ∂μ) - mΦ * mΨ := by
    rw [mc56_centeredOperator_inner, hFm, hGm, zero_mul, sub_zero]
    rw [← hcov]
    unfold ProbabilityTheory.covariance
    simp only [Function.comp_apply]
    rw [hmeanU, hmeanV, integral_prod _ hcii]
    apply integral_congr_ae
    have hFae := hfst.quasiMeasurePreserving.ae hFc.coeFn_toLp
    have hGae := hmix.quasiMeasurePreserving.ae hGc.coeFn_toLp
    filter_upwards [Measure.ae_ae_of_ae_prod hFae, Measure.ae_ae_of_ae_prod hGae] with g hg hj
    apply integral_congr_ae
    filter_upwards [hg, hj] with h hh hk
    exact congrArg₂ (· * ·) hh hk
  have hbound := (abs_real_inner_le_norm F (mc56_centeredOperator a b hab G)).trans
    (mul_le_mul_of_nonneg_left (mc56_centeredOperator_bound a b hab ha G) (norm_nonneg F))
  rw [hcenter] at hbound
  have hnF : ‖F‖ = Real.sqrt (∫ g, (Φ g - mΦ) ^ 2 ∂μ) := toLp_norm Fc hFc
  have hnG : ‖G‖ = Real.sqrt (∫ g, (Ψ g - mΨ) ^ 2 ∂μ) := toLp_norm Gc hGc
  rw [hnF, hnG] at hbound
  convert hbound using 1 <;> ring

end BstLean.Part56
