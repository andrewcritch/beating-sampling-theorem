import BstLean.Part153Bin
import BstLean.Part132Upper

/-! Moment addition and multiplication without an independence premise. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real
open BstLean.Part152 BstLean.Part153

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma moment_of_lintegral {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {s : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hb : (∫⁻ ω, ENNReal.ofReal (X ω) ^ s ∂μ) ≤ ENNReal.ofReal (a ^ s)) :
    Integrable (fun ω => X ω ^ s) μ ∧ (∫ ω, X ω ^ s ∂μ) ≤ a ^ s := by
  simp_rw [← ENNReal.ofReal_pow (hX0 _)] at hb
  have hi := (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const s).aestronglyMeasurable
    (ae_of_all _ fun ω => pow_nonneg (hX0 ω) _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => pow_nonneg (hX0 ω) _)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg ha _)).mp hb

lemma lintegral_of_moment {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {s : ℕ}
    (hi : Integrable (fun ω => X ω ^ s) μ) {a : ℝ}
    (hb : (∫ ω, X ω ^ s ∂μ) ≤ a ^ s) :
    (∫⁻ ω, ENNReal.ofReal (X ω) ^ s ∂μ) ≤ ENNReal.ofReal (a ^ s) := by
  simp_rw [← ENNReal.ofReal_pow (hX0 _)]
  exact lintegral_ofReal_le_of_integral_le (fun ω => pow_nonneg (hX0 ω) _) hi hb

theorem moment_add {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) {s : ℕ} (hs : 1 ≤ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hiX : Integrable (fun ω => X ω ^ s) μ) (hiY : Integrable (fun ω => Y ω ^ s) μ)
    (hMX : (∫ ω, X ω ^ s ∂μ) ≤ a ^ s) (hMY : (∫ ω, Y ω ^ s ∂μ) ≤ b ^ s) :
    Integrable (fun ω => (X ω + Y ω) ^ s) μ ∧
      (∫ ω, (X ω + Y ω) ^ s ∂μ) ≤ (a + b) ^ s := by
  have h := lintegral_pow_add_le hX.ennreal_ofReal.aemeasurable hY.ennreal_ofReal.aemeasurable
    ha hb hs (lintegral_of_moment hX0 hiX hMX) (lintegral_of_moment hY0 hiY hMY)
  simp_rw [← ENNReal.ofReal_add (hX0 _) (hY0 _)] at h
  exact moment_of_lintegral (hX.add hY) (fun ω => add_nonneg (hX0 ω) (hY0 ω)) (add_nonneg ha hb) h

theorem moment_mul [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) {s : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hiX : Integrable (fun ω => X ω ^ (2 * s)) μ)
    (hiY : Integrable (fun ω => Y ω ^ (2 * s)) μ)
    (hMX : (∫ ω, X ω ^ (2 * s) ∂μ) ≤ a ^ (2 * s))
    (hMY : (∫ ω, Y ω ^ (2 * s) ∂μ) ≤ b ^ (2 * s)) :
    Integrable (fun ω => (X ω * Y ω) ^ s) μ ∧
      (∫ ω, (X ω * Y ω) ^ s ∂μ) ≤ (a * b) ^ s := by
  have he : ∀ z : ℝ, (z ^ s) ^ 2 = z ^ (2 * s) := by
    intro z
    rw [← pow_mul, Nat.mul_comm]
  obtain ⟨hi, hm⟩ := BstLean.Part132.integral_mul_le_sqrt (hX.pow_const s) (hY.pow_const s)
    (by simpa only [he] using hiX) (by simpa only [he] using hiY)
  simp_rw [abs_of_nonneg (pow_nonneg (hX0 _) _), abs_of_nonneg (pow_nonneg (hY0 _) _),
    ← mul_pow] at hi hm
  refine ⟨hi, hm.trans ?_⟩
  simp_rw [he]
  have h := mul_le_mul (sqrt_le_sqrt hMX) (sqrt_le_sqrt hMY) (sqrt_nonneg _) (sqrt_nonneg _)
  rw [← he a, ← he b, sqrt_sq (pow_nonneg ha _), sqrt_sq (pow_nonneg hb _), ← mul_pow] at h
  exact h

end BstLean.Part209
