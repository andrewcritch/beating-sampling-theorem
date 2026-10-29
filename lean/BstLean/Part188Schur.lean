import BstLean.Part182Schur

/-! Schur with a bounded dependent density. No rotation invariance of the density is used. -/

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part182
open BstLean.Part153 (nrm nrm_nonneg)

variable {X : Type*} [MeasurableSpace X] {m k : ℕ}

/-- A bounded density can depend on the Jacobian, the radius, and the computed centre. -/
theorem dependent_weight_schur (μ : Measure X) [IsProbabilityMeasure μ]
    (B : X → Matrix (Fin m) (Fin k) ℝ) (hB : ∀ i j, Measurable (fun x => B x i j))
    (β : X → ℝ) (hβm : Measurable β) (hβ : ∀ x, opN (B x) ≤ β x) {CB : ℝ}
    (hCB : ∀ x, β x ≤ CB)
    (w q : X → ℝ) (hwm : Measurable w) (hqm : Measurable q)
    (hw0 : ∀ x, 0 ≤ w x) (hq0 : ∀ x, 0 ≤ q x)
    (hwi : Integrable w μ) (hw2 : Integrable (fun x => w x ^ 2) μ)
    {d : ℝ} (hd : 0 < d) (hqd : ∀ x, q x ≤ 1 / d)
    (S : Set X) (hS : MeasurableSet S) (hwS : ∀ x, x ∉ S → w x = 0)
    (κ : X → X → ℝ) (hκm : Measurable (Function.uncurry κ))
    (hκ0 : ∀ a b, 0 ≤ κ a b) (hκs : ∀ a b, κ a b = κ b a)
    {K : ℝ} (hκK : ∀ a b, κ a b ≤ K)
    (G : Set (X × X)) (hG : MeasurableSet G)
    (hGs : ∀ a b, (a, b) ∈ G → (b, a) ∈ G)
    (hpair : ∀ a b, (a, b) ∈ G → ∀ u u' : Fin k → ℝ,
      |(B a *ᵥ u) ⬝ᵥ (B b *ᵥ u')| ≤ κ a b * nrm u * nrm u')
    {R : ℝ} (hrow : ∀ x, ∫ y, G.indicator (Function.uncurry κ) (x, y) *
      (w y * q y) ∂μ ≤ R) (v : Fin m → ℝ) :
    ∫ x, w x * q x * normSq (vecMul v (B x)) ∂μ ≤
      (R + √(√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) *
        ∫ x, (w x * q x) ^ 2 * β x ^ 4 ∂μ)) * normSq v := by
  have hi : Integrable (fun x => w x * q x) μ := by
    refine Integrable.mono' (hwi.mul_const (1 / d)) (hwm.mul hqm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (hq0 x))]
    exact mul_le_mul_of_nonneg_left (hqd x) (hw0 x)
  have hi2 : Integrable (fun x => (w x * q x) ^ 2) μ := by
    refine Integrable.mono' (hw2.mul_const ((1 / d) ^ 2))
      ((hwm.mul hqm).pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hq0 x) (hqd x) 2) (sq_nonneg _)
  exact schur_abstract μ B hB β hβm hβ hCB (fun x => w x * q x) (hwm.mul hqm)
    (fun x => mul_nonneg (hw0 x) (hq0 x)) hi hi2 S hS
    (fun x hx => by rw [hwS x hx, zero_mul]) κ hκm hκ0 hκs hκK G hG hGs hpair hrow v

/-- The exceptional fourth-moment integral pays at most the inverse square of the cutoff. -/
theorem weighted_exceptional_moment (μ : Measure X) (w q β : X → ℝ)
    (hwm : Measurable w) (hqm : Measurable q) (hβm : Measurable β)
    {d : ℝ} (hd : 0 < d) (hq0 : ∀ x, 0 ≤ q x) (hqd : ∀ x, q x ≤ 1 / d)
    (hi : Integrable (fun x => w x ^ 2 * β x ^ 4) μ) :
    (∫ x, (w x * q x) ^ 2 * β x ^ 4 ∂μ) ≤
      (1 / d) ^ 2 * ∫ x, w x ^ 2 * β x ^ 4 ∂μ := by
  have hpt : ∀ x, (w x * q x) ^ 2 * β x ^ 4 ≤
      (1 / d) ^ 2 * (w x ^ 2 * β x ^ 4) := by
    intro x
    have hq2 := pow_le_pow_left₀ (hq0 x) (hqd x) 2
    have h := mul_le_mul_of_nonneg_left hq2 (by positivity : 0 ≤ w x ^ 2 * β x ^ 4)
    nlinarith only [h]
  have hqi : Integrable (fun x => (w x * q x) ^ 2 * β x ^ 4) μ := by
    refine Integrable.mono' (hi.const_mul ((1 / d) ^ 2))
      (((hwm.mul hqm).pow_const 2).mul (hβm.pow_const 4)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x
  have h := integral_mono hqi (hi.const_mul ((1 / d) ^ 2)) hpt
  rwa [integral_const_mul] at h

end BstLean.Part188
