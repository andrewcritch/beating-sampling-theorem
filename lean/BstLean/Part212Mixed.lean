import BstLean.Part212Event
import BstLean.Part153Lp

/-! A conservative mixed moment bound retains the same weights at all inputs. -/
namespace BstLean.Part212
open MeasureTheory
open scoped ENNReal

theorem field_score_le_moment80 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {g : Ω → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 12) ∂ν) ^ ((20 : ℝ) / 3) ≤
      ∫⁻ x, ENNReal.ofReal (g x ^ 80) ∂ν := by
  have he (p : ℕ) (hp : p ≠ 0) :
      (eLpNorm g (p : ℝ≥0∞) ν) ^ p = ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂ν := by
    simpa only [abs_of_nonneg (h0 _)] using
      BstLean.Part153.eLpNorm_nat_pow hp hg.aestronglyMeasurable
  rw [← he 12 (by norm_num), ← he 80 (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num only [Nat.cast_ofNat, show (12 : ℝ) * (20 / 3) = 80 by norm_num]
  change (eLpNorm g 12 ν) ^ ((80 : ℕ) : ℝ) ≤ (eLpNorm g 80 ν) ^ (80 : ℕ)
  rw [ENNReal.rpow_natCast]
  exact pow_le_pow_left' (eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) (f := g) (by norm_num :
    (12 : ℝ≥0∞) ≤ 80)) 80

/-- Integrate a single weight distribution. No independent weights are introduced at inputs. -/
theorem mixed_score80 {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (μ : Measure A) [SFinite μ] (ν : Measure X) [IsProbabilityMeasure ν]
    {Ψ : A → X → ℝ} (hΨ : Measurable (Function.uncurry Ψ))
    (h0 : ∀ a x, 0 ≤ Ψ a x) {B : ℝ}
    (hM : ∀ᵐ x ∂ν, ∫⁻ a, ENNReal.ofReal (Ψ a x ^ 80) ∂μ ≤ ENNReal.ofReal (B ^ 80)) :
    ∫⁻ a, (∫⁻ x, ENNReal.ofReal (Ψ a x ^ 12) ∂ν) ^ ((20 : ℝ) / 3) ∂μ ≤
      ENNReal.ofReal (B ^ 80) := by
  calc (∫⁻ a, (∫⁻ x, ENNReal.ofReal (Ψ a x ^ 12) ∂ν) ^ ((20 : ℝ) / 3) ∂μ)
      ≤ ∫⁻ a, ∫⁻ x, ENNReal.ofReal (Ψ a x ^ 80) ∂ν ∂μ := by
        apply lintegral_mono
        intro a
        exact field_score_le_moment80 ν
          (hΨ.comp (measurable_const.prodMk measurable_id)) (h0 a)
    _ = ∫⁻ x, ∫⁻ a, ENNReal.ofReal (Ψ a x ^ 80) ∂μ ∂ν :=
      lintegral_lintegral_swap (hΨ.pow_const 80).ennreal_ofReal.aemeasurable
    _ ≤ ∫⁻ _x, ENNReal.ofReal (B ^ 80) ∂ν := lintegral_mono_ae hM
    _ = ENNReal.ofReal (B ^ 80) := by simp
end BstLean.Part212
