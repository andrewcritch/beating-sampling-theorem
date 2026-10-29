import BstLean.Part130Sym

/-!
# Part 131, a Fubini step: from a conditional probability bound to a joint bound

Role: `delegations/statements/p131-spec.md`, item 4. Five independent variables
`(x, y, z, w, t)` with the product measure `((a ⊗ (b ⊗ (c ⊗ g))) ⊗ d)`. If on the event `T` the
conditional probability over `w` of `S` (the other four variables fixed) is at least `κ`, then
`Pr(S) ≥ κ · Pr(T)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma lintegral_prod_mono' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] {f h : α × β → ℝ≥0∞}
    (hf : Measurable f) (hh : Measurable h)
    (H : ∀ x, ∫⁻ y, f (x, y) ∂ν ≤ ∫⁻ y, h (x, y) ∂ν) :
    ∫⁻ p, f p ∂μ.prod ν ≤ ∫⁻ p, h p ∂μ.prod ν := by
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hh.aemeasurable]
  exact lintegral_mono H

/-- **From conditional to joint.** `S`, `T` measurable events of `((x, y, z, w), t)`. If for
every point of `T` the probability over a fresh `w'` of `S` (with `x, y, z, t` fixed) is at least
`κ`, then `κ · Pr(T) ≤ Pr(S)`. In the application `T` does not depend on `w`; the statement does
not need that. -/
theorem prob_ge_of_cond {α β γ G δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace G] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (g : Measure G) (d : Measure δ)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c]
    [IsProbabilityMeasure g] [IsProbabilityMeasure d]
    (S T : Set ((α × β × γ × G) × δ)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hcond : ∀ x y z w t, ((x, y, z, w), t) ∈ T → κ ≤ g.real {w' | ((x, y, z, w'), t) ∈ S}) :
    κ * ((a.prod (b.prod (c.prod g))).prod d).real T ≤
      ((a.prod (b.prod (c.prod g))).prod d).real S := by
  set f : (α × β × γ × G) × δ → ℝ≥0∞ := fun p => ENNReal.ofReal κ * T.indicator 1 p with hf
  set h : (α × β × γ × G) × δ → ℝ≥0∞ := S.indicator 1 with hh
  have hfm : Measurable f := (measurable_const.indicator hT).const_mul _
  have hhm : Measurable h := measurable_const.indicator hS
  have key : ∫⁻ p, f p ∂((a.prod (b.prod (c.prod g))).prod d) ≤
      ∫⁻ p, h p ∂((a.prod (b.prod (c.prod g))).prod d) := by
    rw [lintegral_prod_symm _ hfm.aemeasurable, lintegral_prod_symm _ hhm.aemeasurable]
    refine lintegral_mono fun t => ?_
    have m0 : Measurable fun q : α × β × γ × G => (q, t) := measurable_id.prodMk measurable_const
    refine lintegral_prod_mono' _ _ (hfm.comp m0) (hhm.comp m0) fun x => ?_
    have m1 : Measurable fun r : β × γ × G => ((x, r), t) := m0.comp measurable_prodMk_left
    refine lintegral_prod_mono' _ _ (hfm.comp m1) (hhm.comp m1) fun y => ?_
    have m2 : Measurable fun r : γ × G => ((x, y, r), t) := m1.comp measurable_prodMk_left
    refine lintegral_prod_mono' _ _ (hfm.comp m2) (hhm.comp m2) fun z => ?_
    have m3 : Measurable fun w : G => ((x, y, z, w), t) := m2.comp measurable_prodMk_left
    have hSset : MeasurableSet {w' : G | ((x, y, z, w'), t) ∈ S} := m3 hS
    have hval : ∫⁻ w, h ((x, y, z, w), t) ∂g = g {w' : G | ((x, y, z, w'), t) ∈ S} := by
      have : (fun w : G => h ((x, y, z, w), t)) =
          ({w' : G | ((x, y, z, w'), t) ∈ S}).indicator 1 := by
        funext w
        simp only [hh, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
      rw [this, lintegral_indicator_one hSset]
    rw [hval]
    calc ∫⁻ w, f ((x, y, z, w), t) ∂g
        ≤ ∫⁻ _ : G, g {w' : G | ((x, y, z, w'), t) ∈ S} ∂g := by
          refine lintegral_mono fun w => ?_
          by_cases hw : ((x, y, z, w), t) ∈ T
          · simp only [hf, Set.indicator_of_mem hw, Pi.one_apply, mul_one]
            exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hcond x y z w t hw)
          · simp [hf, Set.indicator_of_notMem hw]
      _ = g {w' : G | ((x, y, z, w'), t) ∈ S} := by simp
  have e1 : ∫⁻ p, f p ∂((a.prod (b.prod (c.prod g))).prod d) =
      ENNReal.ofReal κ * ((a.prod (b.prod (c.prod g))).prod d) T := by
    simp only [hf]
    rw [lintegral_const_mul (f := T.indicator 1) _ (measurable_const.indicator hT),
      lintegral_indicator_one hT]
  have e2 : ∫⁻ p, h p ∂((a.prod (b.prod (c.prod g))).prod d) =
      ((a.prod (b.prod (c.prod g))).prod d) S := by
    rw [hh, lintegral_indicator_one hS]
  rw [e1, e2] at key
  have := ENNReal.toReal_mono (measure_ne_top _ _) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] at this

end BstLean.Part131

open BstLean.Part131 in
#print axioms prob_ge_of_cond
