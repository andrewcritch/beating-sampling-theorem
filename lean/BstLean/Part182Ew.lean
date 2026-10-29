import BstLean.Part181W
import BstLean.Part181Jen

/-!
# Part 182 (file `Ew`): the noncentral inverse-radius mean `E w ≤ 1.0182·θ/n`

No proof is left open; no `native_decide` or `axiom` is used.

`w = τ²/|y|²`, `y = c + τξ`. From `W₂₀ ≤ (1.0182·θ/n)²⁰` (Part 181 `W20_le_22`, `n ≥ 22 000`,
`0.46 ≤ θ ≤ 0.528`) and the pointwise step `y ≤ y²⁰/20 + 19/20` (Part 181 `xq_pt` with `q = 1`),
`E w ≤ 1.0182·θ/n`. (The paper has `E w ≤ (θ/n)/(1 − 4θ/n)`.)
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part160 (WqN)

variable {n : ℕ}

/-- **`τ²·E|y|⁻² ≤ 1.0182·θ/n`** for `n ≥ 22 000` and `0.46 ≤ θ ≤ 0.528`. -/
theorem Ew_le_22 (hn : 22000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    τ ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n) ≤ 10182 / 10000 * (thetaC c τ / n) := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  set B := 10182 / 10000 * (thetaC c τ / n) with hB
  have hB0 : 0 < B := by
    rw [hB]; have : (0 : ℝ) < n := by linarith
    have : 0 < thetaC c τ := by linarith
    positivity
  have hW := BstLean.Part181.W20_le_22 hn c hτ hθ0 hθ1
  rw [← hB] at hW
  -- integrability
  obtain ⟨hi1, -⟩ := BstLean.Part153.invMoment_one_le (by omega) c hτ
  obtain ⟨hi20, -⟩ := BstLean.Part153.invMoment_le (p := 20) (by omega) c hτ
  have hf1 : Integrable (fun ξ : Fin n → ℝ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) :=
    hi1.const_mul _
  have hf20 : Integrable (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20)
      (stdGauss (Fin n)) := by
    have := hi20.const_mul ((τ ^ 2) ^ 20)
    refine this.congr (ae_of_all _ fun ξ => ?_)
    show (τ ^ 2) ^ 20 * (normSq (c + τ • ξ))⁻¹ ^ 20 = (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20
    rw [mul_pow]
  -- pointwise: w ≤ B·((w/B)²⁰/20 + 19/20)
  have hpt : ∀ ξ : Fin n → ℝ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤
      (1 / 20 / B ^ 19) * (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 + 19 / 20 * B := by
    intro ξ
    have hw0 : 0 ≤ τ ^ 2 * (normSq (c + τ • ξ))⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.2 (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have h := BstLean.Part181.xq_pt (q := 1) (by norm_num) (div_nonneg hw0 hB0.le)
    simp only [pow_one, Nat.cast_one] at h
    have e : (1 / 20 / B ^ 19) * (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 + 19 / 20 * B =
        B * (1 / 20 * ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) / B) ^ 20 + (1 - 1 / 20)) := by
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h hB0.le
    rwa [mul_div_cancel₀ _ hB0.ne'] at this
  have hint := integral_mono hf1 ((hf20.const_mul _).add (integrable_const _)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add (hf20.const_mul _) (integrable_const _), integral_const_mul, integral_const,
    probReal_univ, one_smul, integral_const_mul] at hint
  have hW' : ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 ∂stdGauss (Fin n) ≤ B ^ 20 := hW
  have h2 : (1 / 20 / B ^ 19) * ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 ∂stdGauss (Fin n) ≤
      B / 20 := by
    calc (1 / 20 / B ^ 19) * ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 ∂stdGauss (Fin n)
        ≤ (1 / 20 / B ^ 19) * B ^ 20 := mul_le_mul_of_nonneg_left hW' (by positivity)
      _ = B / 20 := by field_simp
  linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms Ew_le_22
