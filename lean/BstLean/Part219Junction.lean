import BstLean.Part219Events

/-! The remaining deterministic ideal estimate is explicit in this directional junction. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

noncomputable def directionalBudget (n : ℕ) (e ξhp I E O : ℝ) : ℝ :=
  ((√(n : ℝ) / √e) * I + (√(n : ℝ) / √e) * E +
    √(ξhp / ((n : ℝ) * e)) * O) ^ 2

/-- This identifies the three-term norm bound with the paper's squared formula. -/
theorem directionalBudget_eq_formula (n : ℕ) {e ξhp I E O : ℝ}
    (he : 0 < e) (hξ : 0 ≤ ξhp) (hO : 0 ≤ O) :
    directionalBudget n e ξhp I E O =
      directionFormula n ((√(n : ℝ) / √e) * I) (√(n : ℝ) * E) (O ^ 2) ξhp e := by
  have hs : √(O ^ 2 * ξhp / ((n : ℝ) * e)) =
      O * √(ξhp / ((n : ℝ) * e)) := by
    rw [mul_div_assoc, sqrt_mul (sq_nonneg O), sqrt_sq hO]
  unfold directionalBudget directionFormula
  rw [hs]
  congr 1
  ring

/-- The conclusion is the existing network interface, including integrability.
The deterministic ideal norm remains an explicit analytic premise. -/
theorem directionMoment_of_norms {n : ℕ} (hn : 1 ≤ n)
    (D : BstLean.Part157.Design n) (c : BstLean.Part157.Ret n)
    (hτ : 0 < D.tau0 c) {e ξhp I E O : ℝ}
    (he : 0 < e) (hξ : 0 ≤ ξhp) (hI : 0 ≤ I) (hE : 0 ≤ E) (hO : 0 ≤ O)
    (hb : (n : ℝ) * e ≤ normSq (D.bA c.1 c.2.1.1))
    (hfull : normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ ξhp)
    (hi : eLpNorm (idealSize c.1.2 (D.tau0 c)) 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal I)
    (herr : eLpNorm (errorSize c.1.2 (D.tau0 c) c.2.1.1) 24
      (stdGauss (Fin n)) ≤ ENNReal.ofReal E)
    (hop : eLpNorm (operatorSize c.1.2 (D.tau0 c) c.2.1.1) 24
      (stdGauss (Fin n)) ≤ ENNReal.ofReal O) :
    BstLean.Part188.DirectionMoment D c (directionalBudget n e ξhp I E O) := by
  have h := directional_norm_assembly hn c.1.2 hτ c.2.1.1 (D.bA c.1 c.2.1.1)
    he hξ hI hE hO hb hfull hi herr hop
  rw [computedCoordinate_eq_centreCoordinate D c] at h
  have hm := gradient_moment_of_norm hn (BstLean.Part188.centreCoordinate D c)
    (by positivity : 0 ≤ (√(n : ℝ) / √e) * I + (√(n : ℝ) / √e) * E +
      √(ξhp / ((n : ℝ) * e)) * O) h
  exact ⟨sq_nonneg _, hm⟩

/-- The error and operator bounds are supplied on their existing events.
No additional assumption on the actual gradient moment occurs here. -/
theorem directionMoment_on_events {n : ℕ} (hn : 1 ≤ n)
    (D : BstLean.Part157.Design n) (c : BstLean.Part157.Ret n)
    (hτ : 0 < D.tau0 c) {e ξhp I η : ℝ} {δ : ℝ≥0∞}
    (he : 0 < e) (hξ : 0 ≤ ξhp) (hI : 0 ≤ I) (hδ : δ ≠ 0)
    (hb : (n : ℝ) * e ≤ normSq (D.bA c.1 c.2.1.1))
    (hfull : normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ ξhp)
    (hi : eLpNorm (idealSize c.1.2 (D.tau0 c)) 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal I)
    (herr : c.2.1.1 ∈ sharpErrorEvent c.1.2 (D.tau0 c))
    (hop : c.2.1.1 ∈ operatorEvent c.1.2 (D.tau0 c) η δ) :
    BstLean.Part188.DirectionMoment D c
      (directionalBudget n e ξhp I (errorAllowance c.1.2 (D.tau0 c))
        (operatorAllowance c.1.2 (D.tau0 c) η δ)) := by
  exact directionMoment_of_norms hn D c hτ he hξ hI ENNReal.toReal_nonneg
    (mul_nonneg hτ.le ENNReal.toReal_nonneg) hb hfull hi
    (error_norm_on_event c.1.2 hτ.le herr)
    (operator_norm_on_event c.1.2 hτ.le η hδ hop)

/-- The intersection adds the two existing payments and uses no independence. -/
theorem directional_events_charge {n : ℕ} (hn : 322 ≤ n) (c : Fin n → ℝ)
    {τ η δ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hδ : 0 < δ) :
    (nuA n).real (sharpErrorEvent c τ ∩ operatorEvent c τ η (ENNReal.ofReal δ))ᶜ ≤
      7 / 25000 + δ := by
  have he := sharp_error_event_one_payment (by omega) c hτ
  have ho := operator_event_charge160 hn c hτ hη
    (ne_of_gt (ENNReal.ofReal_pos.mpr hδ)) ENNReal.ofReal_ne_top
  have hor : (nuA n).real (operatorEvent c τ η (ENNReal.ofReal δ))ᶜ ≤ δ := by
    simpa only [Measure.real, ENNReal.toReal_ofReal hδ.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top ho
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans (add_le_add he hor)

#print axioms directionalBudget_eq_formula
#print axioms directionMoment_of_norms
#print axioms directionMoment_on_events
#print axioms directional_events_charge
end BstLean.Part219
