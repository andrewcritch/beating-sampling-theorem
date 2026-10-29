import BstLean.Part157Hell

/-! A positive mean reserve gives a direct distance charge. -/
namespace BstLean.Part214
open MeasureTheory Real Set

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A one-sided deviation uses the centred second moment at a positive reserve. -/
theorem upper_tail_of_mean_bound {f : Ω → ℝ} {c a X V : ℝ}
    (hi : Integrable (fun x => (f x - c) ^ 2) μ)
    (hv : (∫ x, (f x - c) ^ 2 ∂μ) ≤ V) (hc : c ≤ a) (hX : a < X) :
    μ.real {x | X < f x} ≤ V / (X - a) ^ 2 := by
  have hr : 0 < X - a := sub_pos.mpr hX
  have hs : {x | X < f x} ⊆ {x | (X - a) ^ 2 ≤ (f x - c) ^ 2} := by
    intro x hx
    exact pow_le_pow_left₀ hr.le (by dsimp at hx ⊢; linarith) 2
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x - c)) hi ((X - a) ^ 2)
  have hb := (mul_le_mul_of_nonneg_left (measureReal_mono hs) (sq_nonneg (X - a))).trans
    (hm.trans hv)
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hb)

end

section
variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable (μ : Measure Ω₁) (ν : Measure Ω₂) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Integrate complete conditional distributions and pay the first-layer complement once. -/
theorem conditional_distance_charge {E : Set Ω₁} (hE : MeasurableSet E)
    {f : Ω₁ × Ω₂ → ℝ} (hf : Measurable f) {c : Ω₁ → ℝ} {a X V δ : ℝ}
    (hX : a < X) (hV : 0 ≤ V) (hbad : μ.real Eᶜ ≤ δ)
    (hi : ∀ x ∈ E, Integrable (fun y => (f (x, y) - c x) ^ 2) ν)
    (hc : ∀ x ∈ E, c x ≤ a)
    (hv : ∀ x ∈ E, (∫ y, (f (x, y) - c x) ^ 2 ∂ν) ≤ V) :
    (μ.prod ν).real {p | X < f p} ≤ δ + V / (X - a) ^ 2 := by
  classical
  let B := V / (X - a) ^ 2
  have hB : 0 ≤ B := div_nonneg hV (sq_nonneg _)
  have mS : MeasurableSet {p | X < f p} := measurableSet_lt measurable_const hf
  have mR : Measurable (fun x => ν.real {y | X < f (x, y)}) := by
    exact (measurable_measure_prodMk_left mS).ennreal_toReal
  have iR : Integrable (fun x => ν.real {y | X < f (x, y)}) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) mR.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have iB : Integrable (Eᶜ.indicator fun _ : Ω₁ => (1 : ℝ)) μ :=
    (integrable_const _).indicator hE.compl
  have iC := iB.add (integrable_const B)
  rw [BstLean.Part157.real_prod_eq μ ν mS]
  change (∫ x, ν.real {y | X < f (x, y)} ∂μ) ≤ _
  calc
    _ ≤ ∫ x, (Eᶜ.indicator (fun _ : Ω₁ => (1 : ℝ)) x + B) ∂μ := by
      apply integral_mono iR iC
      intro x
      change ν.real {y | X < f (x, y)} ≤ Eᶜ.indicator (fun _ : Ω₁ => (1 : ℝ)) x + B
      by_cases hx : x ∈ E
      · simpa [hx, B] using
          upper_tail_of_mean_bound (hi x hx) (hv x hx) (hc x hx) hX
      · rw [Set.indicator_of_mem (show x ∈ Eᶜ from hx)]
        exact (measureReal_le_one (μ := ν)).trans (by linarith)
    _ = μ.real Eᶜ + B := by
      rw [integral_add iB (integrable_const B), integral_indicator_const _ hE.compl]
      simp
    _ ≤ δ + V / (X - a) ^ 2 := add_le_add hbad (le_refl B)

end
end BstLean.Part214

#print axioms BstLean.Part214.upper_tail_of_mean_bound
#print axioms BstLean.Part214.conditional_distance_charge
