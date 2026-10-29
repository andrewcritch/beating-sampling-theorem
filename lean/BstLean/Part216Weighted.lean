import BstLean.Part216Location
import BstLean.Part213Norm
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Weighted node integration and the single moment payment.
The nodes and centre weights have no independence premise. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
variable {ν : Measure G} {σ : Measure Y}

/-- Location order24 uses exactly the weighted latitude order12 moment. -/
theorem weighted_location24 {q : G → ℝ} (hq0 : ∀ g, 0 ≤ q g)
    {H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (h12 : ∫⁻ g, ENNReal.ofReal (q g ^ 12) ∂ν ≤ ENNReal.ofReal (H ^ 12))
    {error : G → Y → ℝ}
    (hnode : ∀ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ 24) ∂σ ≤
      ENNReal.ofReal ((C * sqrt (q g)) ^ 24)) :
    ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ 24) ∂σ ∂ν ≤
      ENNReal.ofReal ((C * sqrt H) ^ 24) := by
  have he : ∀ x : ℝ, 0 ≤ x → (C * sqrt x) ^ 24 = C ^ 24 * x ^ 12 := by
    intro x hx
    simp only [mul_pow, show (24 : ℕ) = 2 * 12 by rfl, pow_mul, sq_sqrt hx]
  refine (lintegral_mono hnode).trans ?_
  simp_rw [he _ (hq0 _), ENNReal.ofReal_mul (pow_nonneg hC 24)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, he H hH,
    ENNReal.ofReal_mul (pow_nonneg hC 24)]
  exact mul_le_mul' le_rfl h12

/-- Energy order18 interpolates the weighted latitude order12 with the bulk cap. -/
theorem weighted_energy18 {q : G → ℝ} (hq0 : ∀ g, 0 ≤ q g)
    {H Q C : ℝ} (hH : 0 ≤ H) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hqQ : ∀ g, q g ≤ Q)
    (h12 : ∫⁻ g, ENNReal.ofReal (q g ^ 12) ∂ν ≤ ENNReal.ofReal (H ^ 12))
    {error : G → Y → ℝ}
    (hnode : ∀ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ 18) ∂σ ≤
      ENNReal.ofReal ((C * q g) ^ 18)) :
    ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ 18) ∂σ ∂ν ≤
      ENNReal.ofReal (C ^ 18 * H ^ 12 * Q ^ 6) := by
  have hq : ∀ g, (C * q g) ^ 18 ≤ (C ^ 18 * Q ^ 6) * q g ^ 12 := by
    intro g
    rw [mul_pow, show q g ^ 18 = q g ^ 12 * q g ^ 6 by rw [← pow_add]]
    have h := pow_le_pow_left₀ (hq0 g) (hqQ g) 6
    nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg (pow_nonneg hC 18)
      (pow_nonneg (hq0 g) 12))]
  refine (lintegral_mono hnode).trans ?_
  refine (lintegral_mono fun g => ENNReal.ofReal_le_ofReal (hq g)).trans ?_
  simp_rw [ENNReal.ofReal_mul (show 0 ≤ C ^ 18 * Q ^ 6 by positivity)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h12).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (show 0 ≤ C ^ 18 * Q ^ 6 by positivity)]
  congr 1
  ring

/-- Fubini uses one common row distribution for all nodes. -/
theorem weighted_moment_fubini {error : G → Y → ℝ}
    (hm : Measurable (Function.uncurry error)) (k : ℕ)
    [SFinite ν] [SFinite σ] :
    (∫⁻ y, ∫⁻ g, ENNReal.ofReal (|error g y| ^ k) ∂ν ∂σ) =
      ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ k) ∂σ ∂ν := by
  exact (lintegral_lintegral_swap ((hm.abs.pow_const k).ennreal_ofReal.aemeasurable)).symm

/-- Per-node distribution identities transfer the weighted moment to a shared network.
No joint independence between nodes enters this transfer. -/
theorem weighted_marginal_transfer {Z : Type*} [MeasurableSpace Z] {τ : Measure Z}
    {error : G → Y → ℝ} {actual : G → Z → ℝ}
    (he : ∀ g, Measurable (error g)) (ha : ∀ g, Measurable (actual g))
    (hmap : ∀ g, τ.map (actual g) = σ.map (error g)) (k : ℕ) :
    (∫⁻ g, ∫⁻ z, ENNReal.ofReal (|actual g z| ^ k) ∂τ ∂ν) =
      ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ k) ∂σ ∂ν := by
  apply lintegral_congr
  intro g
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ k)) :=
    (measurable_id.abs.pow_const k).ennreal_ofReal
  rw [← lintegral_map hf (ha g), hmap g, lintegral_map hf (he g)]

/-- One integrated moment pays one Markov complement, with no union over nodes. -/
theorem weighted_moment_charge {error : G → Y → ℝ}
    (hm : Measurable (Function.uncurry error)) [SFinite ν] [IsProbabilityMeasure σ]
    {k : ℕ} (hk : k ≠ 0) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 < A)
    (hM : ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ k) ∂σ ∂ν ≤ ENNReal.ofReal (B ^ k)) :
    σ {y | ENNReal.ofReal (A ^ k) < ∫⁻ g, ENNReal.ofReal (|error g y| ^ k) ∂ν} ≤
      ENNReal.ofReal ((B / A) ^ k) := by
  have hf : Measurable (fun y => ∫⁻ g, ENNReal.ofReal (|error g y| ^ k) ∂ν) :=
    ((hm.abs.pow_const k).ennreal_ofReal).lintegral_prod_left
  have hAp : 0 < A ^ k := pow_pos hA k
  have hmark := meas_ge_le_lintegral_div (μ := σ) hf.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr hAp)) ENNReal.ofReal_ne_top
  refine (measure_mono (fun y hy => ?_)).trans (hmark.trans ?_)
  · exact (show ENNReal.ofReal (A ^ k) <
      ∫⁻ g, ENNReal.ofReal (|error g y| ^ k) ∂ν from hy).le
  · rw [weighted_moment_fubini hm k]
    refine (ENNReal.div_le_div_right hM _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos hAp, div_pow]

/-- The same single payment is a real probability bound. -/
theorem weighted_moment_charge_real {error : G → Y → ℝ}
    (hm : Measurable (Function.uncurry error)) [SFinite ν] [IsProbabilityMeasure σ]
    {k : ℕ} (hk : k ≠ 0) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 < A)
    (hM : ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error g y| ^ k) ∂σ ∂ν ≤ ENNReal.ofReal (B ^ k)) :
    σ.real {y | ENNReal.ofReal (A ^ k) < ∫⁻ g, ENNReal.ofReal (|error g y| ^ k) ∂ν} ≤
      (B / A) ^ k := by
  have h := weighted_moment_charge hm hk hB hA hM
  rw [← ofReal_measureReal] at h
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (div_nonneg hB hA.le) k)).mp h

#print axioms weighted_location24
#print axioms weighted_energy18
#print axioms weighted_moment_fubini
#print axioms weighted_marginal_transfer
#print axioms weighted_moment_charge
#print axioms weighted_moment_charge_real
end BstLean.Part216
