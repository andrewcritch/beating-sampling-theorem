import BstLean.Part291Weighted
import BstLean.Part209MomentTools

namespace BstLean.BlueprintLow
open MeasureTheory Real BstLean.Part188
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157

/-- The actual order-32 energy-deviation interface supplies the order-16
energy moment used in GB. The measure is the original Gaussian measure. -/
theorem inputEnergy_moment16 {n : ℕ} (D : Design n) (c : Ret n) {H : ℝ}
    (hH : EnergyMoment D c H) :
    Integrable (fun ξ => inputEnergy D c ξ ^ 16) (stdGauss (Fin n)) ∧
    (∫ ξ, inputEnergy D c ξ ^ 16 ∂stdGauss (Fin n)) ≤ (1 + H) ^ 32 := by
  have hp : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hω := measurable_inputEnergy D c
  have hω0 : ∀ ξ, 0 ≤ inputEnergy D c ξ := inputEnergy_nonneg D c
  have he : ∀ x : ℝ, |x| ^ 32 = x ^ 32 := fun x => by
    rw [show (32 : ℕ) = 2 * 16 by norm_num, pow_mul, sq_abs, pow_mul]
  have hi : Integrable (fun ξ => |√(inputEnergy D c ξ) - 1| ^ 32) (stdGauss (Fin n)) := by
    simpa only [he] using hH.2.1
  have hb : (∫ ξ, |√(inputEnergy D c ξ) - 1| ^ 32 ∂stdGauss (Fin n)) ≤ H ^ 32 := by
    simpa only [he] using hH.2.2
  have hm := BstLean.Part209.moment_add (hω.sqrt.sub measurable_const).abs
    (measurable_const (a := (1 : ℝ))) (fun _ => abs_nonneg _) (fun _ => zero_le_one)
    (by norm_num : 1 ≤ (32 : ℕ)) hH.1 zero_le_one hi
    (by simpa only [one_pow] using (integrable_const (1 : ℝ))) hb (by simp)
  have hpt : ∀ ξ, inputEnergy D c ξ ^ 16 ≤ (|√(inputEnergy D c ξ) - 1| + 1) ^ 32 := by
    intro ξ
    have h : √(inputEnergy D c ξ) ≤ |√(inputEnergy D c ξ) - 1| + 1 := by
      linarith [le_abs_self (√(inputEnergy D c ξ) - 1)]
    have hh := pow_le_pow_left₀ (sqrt_nonneg _) h 32
    rw [show (32 : ℕ) = 2 * 16 by norm_num, pow_mul, sq_sqrt (hω0 ξ)] at hh
    exact hh
  have hiω : Integrable (fun ξ => inputEnergy D c ξ ^ 16) (stdGauss (Fin n)) := by
    apply hm.1.mono' (hω.pow_const 16).aestronglyMeasurable
    exact ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hω0 ξ) _)]
      exact hpt ξ
  exact ⟨hiω, (integral_mono hiω hm.1 hpt).trans (by simpa only [add_comm] using hm.2)⟩

end BstLean.BlueprintLow
