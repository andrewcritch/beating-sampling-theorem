import BstLean.Part151J2
import Mathlib.Probability.Independence.Basic

/-! A Gaussian half-space gate is independent of every even observable. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)

noncomputable def halfGate {d : ℕ} (h z : Fin d → ℝ) : Bool :=
  if 0 < z ⬝ᵥ h then true else false

lemma measurable_halfGate {d : ℕ} (h : Fin d → ℝ) : Measurable (halfGate h) := by
  apply measurable_to_bool
  have he : halfGate h ⁻¹' {true} = {z | 0 < z ⬝ᵥ h} := by
    ext z; simp [halfGate]
  rw [he]
  exact measurableSet_lt measurable_const (by unfold dotProduct; fun_prop)

/-- Every measurable even event has half its mass in a nonzero half-space. -/
theorem halfGate_even_event {d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) (hev : ∀ z, -z ∈ E ↔ z ∈ E) :
    (stdGauss (Fin d)).real ({z | halfGate h z = true} ∩ E) =
      (stdGauss (Fin d)).real E / 2 := by
  have hid := BstLean.Part151.half_lint hh (by norm_num : (1 : ℝ) ≠ 0)
    (N := E.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hE)
    (fun z => by
      change E.indicator (fun _ => (1 : ℝ≥0∞)) (-z) = E.indicator (fun _ => (1 : ℝ≥0∞)) z
      by_cases hz : z ∈ E
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hev z).mpr hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (by simpa [hev] using hz)])
  have he : (fun z : Fin d → ℝ =>
      if 0 < z ⬝ᵥ h then E.indicator (fun _ => (1 : ℝ≥0∞)) z else 0) =
      ({z | halfGate h z = true} ∩ E).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    by_cases hz : 0 < z ⬝ᵥ h <;> by_cases hzE : z ∈ E <;>
      simp [halfGate, hz, hzE]
  simp only [one_smul] at hid
  have hgate : MeasurableSet {z | halfGate h z = true} :=
    measurableSet_eq_fun (measurable_halfGate h) measurable_const
  rw [he, lintegral_indicator_const (hgate.inter hE), lintegral_indicator_const hE] at hid
  simp only [one_mul] at hid
  · have ht := congrArg ENNReal.toReal hid
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at ht
    change 2 * (stdGauss (Fin d)).real ({z | halfGate h z = true} ∩ E) =
      (stdGauss (Fin d)).real E at ht
    linarith

theorem halfGate_even_event_false {d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) (hev : ∀ z, -z ∈ E ↔ z ∈ E) :
    (stdGauss (Fin d)).real ({z | halfGate h z = false} ∩ E) =
      (stdGauss (Fin d)).real E / 2 := by
  have htrue := halfGate_even_event hh hE hev
  have hsum := measureReal_inter_add_sdiff (μ := stdGauss (Fin d))
    ((measurable_halfGate h) (measurableSet_singleton true)) (s := E)
  change (stdGauss (Fin d)).real (E ∩ {z | halfGate h z = true}) +
    (stdGauss (Fin d)).real (E \ {z | halfGate h z = true}) =
    (stdGauss (Fin d)).real E at hsum
  have he : E \ {z | halfGate h z = true} = {z | halfGate h z = false} ∩ E := by
    ext z; cases hg : halfGate h z <;> simp [hg, and_comm]
  rw [he, inter_comm E] at hsum
  linarith

/-- The observable can be vector or matrix valued. -/
theorem halfGate_indep_even {d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    {β : Type*} [MeasurableSpace β] {F : (Fin d → ℝ) → β}
    (hF : Measurable F) (hev : ∀ z, F (-z) = F z) :
    IndepFun (halfGate h) F (stdGauss (Fin d)) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hhalf (b : Bool) :
      (stdGauss (Fin d)).real ({z | halfGate h z = b} ∩ (F ⁻¹' t)) =
        (stdGauss (Fin d)).real (F ⁻¹' t) / 2 := by
    cases b
    · exact halfGate_even_event_false hh (hF ht) (by intro z; simp [hev])
    · exact halfGate_even_event hh (hF ht) (by intro z; simp [hev])
  have hmass (b : Bool) : (stdGauss (Fin d)).real {z | halfGate h z = b} = 1 / 2 := by
    cases b
    · simpa using halfGate_even_event_false hh MeasurableSet.univ (by simp)
    · simpa using halfGate_even_event hh MeasurableSet.univ (by simp)
  by_cases hst : true ∈ s <;> by_cases hsf : false ∈ s
  · have he : s = univ := by ext b; cases b <;> simp_all
    rw [he, preimage_univ, univ_inter, measure_univ, one_mul]
  · have he : s = {true} := by ext b; cases b <;> simp_all
    rw [he]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul]
    change (stdGauss (Fin d)).real ({z | halfGate h z = true} ∩ (F ⁻¹' t)) =
      (stdGauss (Fin d)).real {z | halfGate h z = true} * (stdGauss (Fin d)).real (F ⁻¹' t)
    rw [hhalf, hmass]; ring
  · have he : s = {false} := by ext b; cases b <;> simp_all
    rw [he]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul]
    change (stdGauss (Fin d)).real ({z | halfGate h z = false} ∩ (F ⁻¹' t)) =
      (stdGauss (Fin d)).real {z | halfGate h z = false} * (stdGauss (Fin d)).real (F ⁻¹' t)
    rw [hhalf, hmass]; ring
  · have he : s = ∅ := by ext b; cases b <;> simp_all
    simp [he]

noncomputable def outerProduct {d : ℕ} (z : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => z i * z j

theorem halfGate_indep_outerProduct {d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0) :
    IndepFun (halfGate h) (outerProduct (d := d)) (stdGauss (Fin d)) := by
  apply halfGate_indep_even hh
  · unfold outerProduct; fun_prop
  · intro z; funext i j; simp [outerProduct]

end BstLean.Part221
