import BstLean.Part48Rot

/-!
# Part 48, wave 1b: averaging over the rotation angle (omQ4 §4) — proved from `rot_preserving`

Specification: `delegations/answers/p48-spec-opus.md`, §3 and §5. Uses the statement of
`rot_preserving` (`Part48Rot`).

Claim. For a measurable set `A` of pairs, `2π (γ⊗γ)(A) = ∫ circ{s : (X_s, Y_s) ∈ A} d(γ⊗γ)`.

Route used. `circ univ = 2π` (`Real.volume_Ioc`). For each `s`, `rot_preserving s` gives
`(γ⊗γ){w : rot_s w ∈ A} = (γ⊗γ)(A)`, so `∫⁻ s ∂circ, (γ⊗γ)(rot_s⁻¹ A) = 2π (γ⊗γ)(A)`
(`lintegral_const`). Swap the two integrals (`lintegral_lintegral_swap`, or `lintegral_prod` and
`Measure.prod_swap`). The joint map `(s, w) ↦ rot_s w` is continuous, so the indicator of
`{(s, w) : rot_s w ∈ A}` is measurable (`measurable_measure_prodMk_left` and its relatives).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

/-- **Averaging over the angle**: `2π (γ⊗γ)(A) = ∫ circ{s : (X_s, Y_s) ∈ A} d(γ⊗γ)`. -/
theorem rot_avg {ι : Type} [Fintype ι] (A : Set ((ι → ℝ) × (ι → ℝ))) (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * Real.pi) * ((stdGauss ι).prod (stdGauss ι)) A =
      ∫⁻ w, circ {s | (rotX s w.1 w.2, rotY s w.1 w.2) ∈ A} ∂((stdGauss ι).prod (stdGauss ι)) := by
  have : SFinite circ := by unfold circ; infer_instance
  set μ2 := (stdGauss ι).prod (stdGauss ι)
  set Φ : ℝ × ((ι → ℝ) × (ι → ℝ)) → (ι → ℝ) × (ι → ℝ) :=
    fun p => (rotX p.1 p.2.1 p.2.2, rotY p.1 p.2.1 p.2.2) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ]; unfold rotX rotY; fun_prop
  have hB : MeasurableSet (Φ ⁻¹' A) := hΦc.measurable hA
  have h1 : ∫⁻ w, circ {s | (rotX s w.1 w.2, rotY s w.1 w.2) ∈ A} ∂μ2 = (circ.prod μ2) (Φ ⁻¹' A) := by
    rw [Measure.prod_apply_symm hB]
    rfl
  have h2 : (circ.prod μ2) (Φ ⁻¹' A) = ∫⁻ s, μ2 A ∂circ := by
    rw [Measure.prod_apply hB]
    refine lintegral_congr fun s => ?_
    exact (rot_preserving (ι := ι) s).measure_preimage hA.nullMeasurableSet
  rw [h1, h2, lintegral_const]
  have : circ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simp [circ, Real.volume_Ioc]
  rw [this, mul_comm]

end BstLean.Part48
