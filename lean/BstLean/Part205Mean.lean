import BstLean.Part205Taylor
import BstLean.Part205Radial

/-! Scalar assembly of the deterministic mean estimate. The analytic error supplies are explicit. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real Set BstLean.Part130
open BstLean.Part133

noncomputable def meanBound (r T ν : ℝ) : ℝ :=
  endpointK r * (√T + √2 * ν) ^ 2 +
    (slopeK r + kappa r + 4) * ν ^ 2 + (√2 + 2) * ν * √T

lemma endpointK_nonneg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    0 ≤ endpointK r := by
  have h := remainder_nonneg (by linarith : -1 < r) (by linarith : r < 1)
    (by norm_num : (-1 : ℝ) ≤ 1) le_rfl
  unfold remainderK at h
  rw [kappa_one] at h
  exact div_nonneg h (sq_nonneg _)

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma kernel_integrable_of_range {f : Ω → ℝ} (hf : Measurable f)
    (hr : ∀ᵐ x ∂μ, f x ∈ Icc (-1 : ℝ) 1) : Integrable (fun x => kappa (f x)) μ := by
  refine Integrable.of_bound (continuous_kappa.measurable.comp hf).aestronglyMeasurable 1 ?_
  filter_upwards [hr] with x hx
  have h := kappa_mem hx.1 hx.2
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

lemma correlation_integrable_of_range {f : Ω → ℝ} (hf : Measurable f)
    (hr : ∀ᵐ x ∂μ, f x ∈ Icc (-1 : ℝ) 1) : Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1 ?_
  filter_upwards [hr] with x hx
  rw [Real.norm_eq_abs, abs_le]
  exact hx

/-- Restore normalized correlations by one radial error, with nonnegative norm bounds. -/
theorem correlation_normalization {a c : Ω → ℝ} {r A B : ℝ}
    (hc : Measurable c) (hc1 : ∀ x, |c x| ≤ 1)
    (hraw : L2le μ (fun x => a x * c x - r) A)
    (hrad : L2le μ (fun x => 1 - a x) B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    L2le μ (fun x => c x - r) (A + B) := by
  have herr : L2le μ (fun x => (1 - a x) * c x) B := by
    refine L2le.of_abs_le (hrad.aesm.mul hc.aestronglyMeasurable) hrad ?_
    intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hc1 x) (abs_nonneg _)).trans_eq (mul_one _)
  exact (hraw.add' herr hA hB).congr_fun fun x => by ring

/-- Integrate Taylor before radial weights are restored. Constant terms cancel exactly. -/
theorem unweighted_taylor_mean {c : Ω × Ω → ℝ} {d : Ω → ℝ} {r : ℝ}
    (hc : Measurable c) (hd : Measurable d)
    (hcr : ∀ᵐ p ∂μ.prod μ, c p ∈ Icc (-1 : ℝ) 1)
    (hdr : ∀ᵐ x ∂μ, d x ∈ Icc (-1 : ℝ) 1)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    (∫ p, kappa (c p) ∂μ.prod μ) - 2 * (∫ x, kappa (d x) ∂μ) + kappa r ≤
      slopeK r * ((∫ p, c p ∂μ.prod μ) - 2 * (∫ x, d x ∂μ) + r) +
        endpointK r * (∫ p, (c p - r) ^ 2 ∂μ.prod μ) := by
  have ic := correlation_integrable_of_range hc hcr
  have id := correlation_integrable_of_range hd hdr
  have ikc := kernel_integrable_of_range hc hcr
  have ikd := kernel_integrable_of_range hd hdr
  have ic2 : Integrable (fun p => (c p - r) ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound ((hc.sub_const r).pow_const 2).aestronglyMeasurable
      (9 / 4) ?_
    filter_upwards [hcr] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : -3 / 2 ≤ c p - r := by linarith [hp.1]
    have h2 : c p - r ≤ 3 / 2 := by linarith [hp.2]
    nlinarith
  have icterm : Integrable (fun p => slopeK r * (c p - r)) (μ.prod μ) :=
    (ic.sub (integrable_const r)).const_mul (slopeK r)
  have iclin : Integrable (fun p => kappa r + slopeK r * (c p - r)) (μ.prod μ) :=
    (integrable_const (kappa r)).add icterm
  have itc : Integrable (fun p => kappa r + slopeK r * (c p - r) +
      endpointK r * (c p - r) ^ 2) (μ.prod μ) := iclin.add (ic2.const_mul (endpointK r))
  have idterm : Integrable (fun x => slopeK r * (d x - r)) μ :=
    (id.sub (integrable_const r)).const_mul (slopeK r)
  have itd : Integrable (fun x => kappa r + slopeK r * (d x - r)) μ :=
    (integrable_const (kappa r)).add idterm
  have hupper : (∫ p, kappa (c p) ∂μ.prod μ) ≤
      ∫ p, kappa r + slopeK r * (c p - r) + endpointK r * (c p - r) ^ 2
        ∂μ.prod μ := by
    refine integral_mono_ae ikc itc ?_
    filter_upwards [hcr] with p hp
    have h := (global_taylor hr0 hr1 hp.1 hp.2).2
    unfold remainderK at h
    linarith
  have hlower : (∫ x, kappa r + slopeK r * (d x - r) ∂μ) ≤
      ∫ x, kappa (d x) ∂μ := by
    refine integral_mono_ae itd ikd ?_
    filter_upwards [hdr] with x hx
    have h := remainder_nonneg (by linarith : -1 < r) (by linarith : r < 1) hx.1 hx.2
    unfold remainderK at h
    linarith
  rw [integral_add iclin (ic2.const_mul (endpointK r)),
    integral_add (integrable_const (kappa r)) icterm,
    integral_const_mul, integral_const_mul,
    integral_sub ic (integrable_const r)] at hupper
  rw [integral_add (integrable_const (kappa r)) idterm, integral_const_mul,
    integral_sub id (integrable_const r)] at hlower
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hupper hlower
  linarith

end

/-- Assemble the unweighted Taylor term and the three retained radial-weight errors. -/
theorem mean_bound_of_error_bounds {r T ν Δ E₀ Ec Ep Es : ℝ}
    (hΔ : Δ ≤ E₀ + Ec + Ep + Es)
    (h₀ : E₀ ≤ endpointK r * (√T + √2 * ν) ^ 2 + slopeK r * ν ^ 2)
    (hc : Ec ≤ kappa r * ν ^ 2)
    (hp : Ep ≤ √2 * ν * (√T + √2 * ν))
    (hs : Es ≤ 2 * ν * (√T + ν)) : Δ ≤ meanBound r T ν := by
  have hsqrt : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : (endpointK r * (√T + √2 * ν) ^ 2 + slopeK r * ν ^ 2) +
      kappa r * ν ^ 2 + √2 * ν * (√T + √2 * ν) + 2 * ν * (√T + ν) =
      meanBound r T ν := by
    unfold meanBound
    ring_nf
    rw [hsqrt]
    ring
  rw [← he]
  linarith

end BstLean.Part205

#print axioms BstLean.Part205.mean_bound_of_error_bounds
#print axioms BstLean.Part205.endpointK_nonneg
#print axioms BstLean.Part205.unweighted_taylor_mean
