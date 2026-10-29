import BstLean.Part221Gate
import Mathlib.MeasureTheory.Constructions.Pi

/-! Independence of the entire gate array from all even row observables. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

theorem halfGate_array_indep_even {m d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    {β : Type*} [MeasurableSpace β] {F : (Fin d → ℝ) → β}
    (hF : Measurable F) (hev : ∀ z, F (-z) = F z) :
    IndepFun (fun Z : Fin m → Fin d → ℝ => fun i => halfGate h (Z i))
      (fun Z : Fin m → Fin d → ℝ => fun i => F (Z i))
      (Measure.pi fun _ : Fin m => stdGauss (Fin d)) := by
  let μ := stdGauss (Fin d)
  let G := halfGate h
  have hG : Measurable G := measurable_halfGate h
  have hrow : μ.map (fun z => (G z, F z)) = (μ.map G).prod (μ.map F) :=
    (halfGate_indep_even hh hF hev).map_prod_eq_prod_map_map hG.aemeasurable hF.aemeasurable
  have hGa : Measurable (fun Z : Fin m → Fin d → ℝ => fun i => G (Z i)) :=
    measurable_pi_iff.mpr fun i => hG.comp (measurable_pi_apply i)
  have hFa : Measurable (fun Z : Fin m → Fin d → ℝ => fun i => F (Z i)) :=
    measurable_pi_iff.mpr fun i => hF.comp (measurable_pi_apply i)
  apply (indepFun_iff_map_prod_eq_prod_map_map hGa.aemeasurable hFa.aemeasurable).mpr
  change (Measure.pi fun _ : Fin m => μ).map
    (fun Z => ((fun i => G (Z i)), (fun i => F (Z i)))) = _
  have hpair : Measurable (fun Z : Fin m → Fin d → ℝ => fun i => (G (Z i), F (Z i))) :=
    measurable_pi_iff.mpr fun i => (hG.prodMk hF).comp (measurable_pi_apply i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Bool β (Fin m)
  have he : (fun Z : Fin m → Fin d → ℝ => ((fun i => G (Z i)), (fun i => F (Z i)))) =
      e ∘ (fun Z => fun i => (G (Z i), F (Z i))) := rfl
  rw [he, ← Measure.map_map e.measurable hpair,
    Measure.pi_map_pi (fun _ => (hG.prodMk hF).aemeasurable)]
  simp_rw [hrow]
  rw [(measurePreserving_arrowProdEquivProdArrow Bool β (Fin m)
    (fun _ => μ.map G) (fun _ => μ.map F)).map_eq]
  rw [Measure.pi_map_pi (fun _ => hG.aemeasurable),
    Measure.pi_map_pi (fun _ => hF.aemeasurable)]

theorem halfGate_array_indep_outerProduct {m d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0) :
    IndepFun (fun Z : Fin m → Fin d → ℝ => fun i => halfGate h (Z i))
      (fun Z : Fin m → Fin d → ℝ => fun i => outerProduct (Z i))
      (Measure.pi fun _ : Fin m => stdGauss (Fin d)) := by
  apply halfGate_array_indep_even hh
  · unfold outerProduct; fun_prop
  · intro z; funext i j; simp [outerProduct]

lemma halfGate_probability {d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0) (b : Bool) :
    stdGauss (Fin d) {z | halfGate h z = b} = (1 / 2 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
  change (stdGauss (Fin d)).real {z | halfGate h z = b} = _
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  cases b
  · simpa using halfGate_even_event_false hh MeasurableSet.univ (by simp)
  · simpa using halfGate_even_event hh MeasurableSet.univ (by simp)

lemma halfGate_array_probability {m d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    (b : Fin m → Bool) :
    (Measure.pi fun _ : Fin m => stdGauss (Fin d))
      {Z | (fun i => halfGate h (Z i)) = b} = (1 / 2 : ℝ≥0∞) ^ m := by
  have he : {Z : Fin m → Fin d → ℝ | (fun i => halfGate h (Z i)) = b} =
      Set.univ.pi (fun i => {z | halfGate h z = b i}) := by
    ext Z
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact funext_iff
  rw [he, Measure.pi_pi]
  simp_rw [halfGate_probability hh]
  simp

/-- The conditional distribution of all even row data is unchanged for each gate array. -/
theorem halfGate_array_even_event {m d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    {β : Type*} [MeasurableSpace β] {F : (Fin d → ℝ) → β}
    (hF : Measurable F) (hev : ∀ z, F (-z) = F z)
    (b : Fin m → Bool) {E : Set (Fin m → β)} (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin m => stdGauss (Fin d))
      ({Z | (fun i => halfGate h (Z i)) = b} ∩ {Z | (fun i => F (Z i)) ∈ E}) =
      (1 / 2 : ℝ≥0∞) ^ m * (Measure.pi fun _ : Fin m => stdGauss (Fin d))
        {Z | (fun i => F (Z i)) ∈ E} := by
  have hi := indepFun_iff_measure_inter_preimage_eq_mul.mp
    (halfGate_array_indep_even (m := m) hh hF hev) {b} E (measurableSet_singleton b) hE
  change _ = _ * _ at hi
  simpa only [Set.preimage, Set.mem_singleton_iff, halfGate_array_probability hh] using hi

/-- Fixing the gates leaves the selected Gaussian outer products unchanged. -/
theorem gated_outer_sum_event {m d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    (b : Fin m → Bool) {E : Set (Matrix (Fin d) (Fin d) ℝ)} (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin m => stdGauss (Fin d))
      {Z | (fun i => halfGate h (Z i)) = b ∧
        (∑ i, if halfGate h (Z i) then outerProduct (Z i) else 0) ∈ E} =
      (1 / 2 : ℝ≥0∞) ^ m * (Measure.pi fun _ : Fin m => stdGauss (Fin d))
        {Z | (∑ i, if b i then outerProduct (Z i) else 0) ∈ E} := by
  let H : (Fin m → Matrix (Fin d) (Fin d) ℝ) → Matrix (Fin d) (Fin d) ℝ :=
    fun Q => ∑ i, if b i then Q i else 0
  have hH : Measurable H := by
    apply Finset.measurable_sum
    intro i _
    cases b i
    · exact measurable_const
    · exact measurable_pi_apply i
  have he : {Z : Fin m → Fin d → ℝ | (fun i => halfGate h (Z i)) = b ∧
        (∑ i, if halfGate h (Z i) then outerProduct (Z i) else 0) ∈ E} =
      {Z | (fun i => halfGate h (Z i)) = b} ∩
        {Z | (fun i => outerProduct (Z i)) ∈ H ⁻¹' E} := by
    ext Z
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hg, hq⟩
      refine ⟨hg, ?_⟩
      change (∑ i, if b i then outerProduct (Z i) else 0) ∈ E
      simpa only [funext_iff.mp hg] using hq
    · rintro ⟨hg, hq⟩
      refine ⟨hg, ?_⟩
      change (∑ i, if b i then outerProduct (Z i) else 0) ∈ E at hq
      simpa only [funext_iff.mp hg] using hq
  rw [he]
  exact halfGate_array_even_event hh (by unfold outerProduct; fun_prop)
    (by intro z; funext i j; simp [outerProduct]) b (hH hE)

end BstLean.Part221
