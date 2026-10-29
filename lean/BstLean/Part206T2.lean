import BstLean.Part206Energy

/-! Endpoint-local full-error transfer and uniform fallback. Endpoint bounds are
deterministic at fixed retained World data. No union over endpoint cells occurs. -/
namespace BstLean.Part206
open MeasureTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part153 (nrm)

/-- The four terms are the remainder, linear, bias and excluded-input allowances. -/
noncomputable def centreMoment (terms : Fin 4 → ℝ) : ℝ := ∑ i, terms i

noncomputable def centreFull (terms : Fin 4 → ℝ) (deviation radius finite : ℝ) : ℝ :=
  (√(centreMoment terms) + deviation + radius + finite) ^ 2

/-- A second-moment supply and the same mean-threshold event give MA's amplitude. -/
theorem MA_mean_threshold {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Ω → ℝ} {X deviation ξ : ℝ}
    (hX : 0 ≤ X) (hξ : 0 ≤ ξ) (hi : Integrable D μ)
    (hi2 : Integrable (fun x => D x ^ 2) μ)
    (hMoment : (∫ x, D x ^ 2 ∂μ) ≤ X ^ 2 * ξ)
    {x : Ω} (hEvent : D x ≤ (∫ x, D x ∂μ) + X * deviation) :
    D x ≤ X * (√ξ + deviation) := by
  have hj := (mean_sq_le_second hi hi2).trans hMoment
  have hm : (∫ x, D x ∂μ) ≤ X * √ξ := by
    have hs : (X * √ξ) ^ 2 = X ^ 2 * ξ := by rw [mul_pow, sq_sqrt hξ]
    have hnn : 0 ≤ X * √ξ := by positivity
    nlinarith
  linarith

/-- This conditional charge requires the sharp Lipschitz supply explicitly. -/
theorem MA_sharp_charge {m : ℕ} {D : Matrix (Fin m) (Fin m) ℝ → ℝ}
    {variance L level : ℝ} (hv : 0 < variance) (hL : 0 ≤ L) (hl : 0 ≤ level)
    (hLip : ∀ M M', |D M - D M'| ≤
      L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2)) :
    (gaussMat m m variance).real
      {M | (∫ M, D M ∂gaussMat m m variance) + √(2 * level * variance) * L < D M}
      ≤ exp (-level) :=
  BstLean.Part153.conc_upper_strict hL hLip hv hl

/-- The smaller deviation event implies the old event with the same mean. -/
theorem MA_event_inclusion {Ω : Type*} (D : Ω → ℝ) {mean sharp old : ℝ}
    (hdev : sharp ≤ old) :
    {x | D x ≤ mean + sharp} ⊆ {x | D x ≤ mean + old} := by
  intro x hx
  exact hx.trans (add_le_add le_rfl hdev)

/-- T2 combines four moment envelopes, the deviation, radius and finite errors. -/
theorem T2_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Ω → ℝ} {k : ℕ} (a h bo b : Fin k → ℝ)
    {x : Ω} {s X deviation radius finite : ℝ} (terms : Fin 4 → ℝ)
    (hs : 0 ≤ s) (hX : 0 ≤ X) (hdev : 0 ≤ deviation)
    (hrad : 0 ≤ radius) (hfin : 0 ≤ finite)
    (ht : ∀ i, 0 ≤ terms i) (hi : Integrable D μ)
    (hi2 : Integrable (fun x => D x ^ 2) μ)
    (hMoment : (∫ x, D x ^ 2 ∂μ) ≤ X ^ 2 * centreMoment terms)
    (hEvent : D x ≤ (∫ x, D x ∂μ) + X * deviation)
    (hD : s * nrm (h - bo) ≤ D x)
    (hR : s * nrm (a - h) ≤ X * radius)
    (hF : s * nrm (b - bo) ≤ X * finite) :
    s ^ 2 * normSq (a - b) ≤ X ^ 2 * centreFull terms deviation radius finite := by
  have ht0 : 0 ≤ centreMoment terms := Finset.sum_nonneg (fun i _ => ht i)
  have hd := hD.trans (MA_mean_threshold hX ht0 hi hi2 hMoment hEvent)
  have hf := full_centre_transfer a h bo b hs hd hR hF
  have hsq := pow_le_pow_left₀ (mul_nonneg hs (BstLean.Part153.nrm_nonneg _)) hf 2
  simpa only [mul_pow, BstLean.Part153.nrm_sq, fullAllowance, centreFull] using hsq

/-- The encoded endpoint covers the cell and stays inside the original window. -/
def EndpointGuard (θ cellHi encoded uniform : ℝ) (Valid : ℝ → Prop) : Prop :=
  θ ≤ cellHi ∧ cellHi ≤ encoded ∧ 46 / 100 ≤ encoded ∧ encoded ≤ uniform ∧ Valid encoded

/-- A failed endpoint guard uses the uniform bound. A valid guard uses the minimum. -/
noncomputable def guardedFull (θ cellHi encoded uniform : ℝ) (Valid : ℝ → Prop)
    (bound : ℝ → ℝ) : ℝ := by
  classical
  exact if EndpointGuard θ cellHi encoded uniform Valid then
    min (bound encoded) (bound uniform) else bound uniform

theorem T2_guarded {error θ cellHi encoded uniform : ℝ} {Valid : ℝ → Prop}
    {bound : ℝ → ℝ} (hUniform : error ≤ bound uniform)
    (hLocal : ∀ endpoint, 46 / 100 ≤ endpoint → θ ≤ endpoint →
      endpoint ≤ uniform → Valid endpoint → error ≤ bound endpoint) :
    error ≤ guardedFull θ cellHi encoded uniform Valid bound := by
  classical
  unfold guardedFull
  split_ifs with hg
  · exact le_min (hLocal encoded hg.2.2.1 (hg.1.trans hg.2.1) hg.2.2.2.1 hg.2.2.2.2)
      hUniform
  · exact hUniform

/-- Outward rounding above the original window selects the uniform fallback. -/
theorem T2_uniform_fallback {θ cellHi encoded uniform : ℝ} {Valid : ℝ → Prop}
    (bound : ℝ → ℝ) (hRound : uniform < encoded) :
    guardedFull θ cellHi encoded uniform Valid bound = bound uniform := by
  classical
  unfold guardedFull
  rw [if_neg]
  intro h
  exact (not_le.mpr hRound) h.2.2.2.1

/-- A deterministic cover preserves the supplied charge without a cell union. -/
theorem T2_same_charge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {E : Set Ω} {δ : ℝ} {error : Ω → ℝ}
    {θ cellHi encoded uniform : ℝ} {Valid : ℝ → Prop} {bound : ℝ → ℝ}
    (hCharge : μ.real Eᶜ ≤ δ)
    (hUniform : ∀ x ∈ E, error x ≤ bound uniform)
    (hLocal : ∀ endpoint, 46 / 100 ≤ endpoint → θ ≤ endpoint → endpoint ≤ uniform →
      Valid endpoint → ∀ x ∈ E, error x ≤ bound endpoint) :
    μ.real {x | guardedFull θ cellHi encoded uniform Valid bound < error x} ≤ δ := by
  apply (measureReal_mono (show {x | guardedFull θ cellHi encoded uniform Valid bound <
      error x} ⊆ Eᶜ from ?_)).trans hCharge
  intro x hx hxE
  exact (not_lt_of_ge (T2_guarded (hUniform x hxE)
    (fun endpoint hlo hθ hu hv => hLocal endpoint hlo hθ hu hv x hxE))) hx

#print axioms MA_mean_threshold
#print axioms MA_sharp_charge
#print axioms MA_event_inclusion
#print axioms T2_transfer
#print axioms T2_guarded
#print axioms T2_uniform_fallback
#print axioms T2_same_charge
end BstLean.Part206
