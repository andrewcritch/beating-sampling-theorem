import BstLean.Part221Event

/-! A closed analytic calibration gives an actual event throughout the frontier interval. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 (mA)
open BstLean.Part157 BstLean.Part160
open BstLean.Part212

theorem factorialMoment_pos (ell : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < factorialMoment ell a t := by
  unfold factorialMoment
  apply Finset.sum_pos'
  · intro k hk; positivity
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simpa using pow_pos ha ell

noncomputable def automaticRadiusSquared160 (n : ℕ) : ℝ :=
  let a := automaticRadius (mA n) (n - 1 - 1)
  factorialMoment 160 a (a - ((n - 1 - 1 : ℕ) : ℝ) / a) ^ (1 / 80 : ℝ)

theorem automaticRadiusSquared160_properties {n : ℕ} (hn : 8000 ≤ n) :
    0 < automaticRadiusSquared160 n ∧
      let a := automaticRadius (mA n) (n - 1 - 1)
      factorialMoment 160 a (a - ((n - 1 - 1 : ℕ) : ℝ) / a) =
        automaticRadiusSquared160 n ^ 80 := by
  have hm : 0 < mA n := by
    unfold mA
    exact pow_pos (by omega : 0 < n) 2
  obtain ⟨ha, ha2, _⟩ := automaticRadius_guards hm (by omega : 1 ≤ n - 1 - 1)
  have ht := BstLean.Part217.radial_slope_pos ha ha2
  have hM := factorialMoment_pos 160 ha ht
  refine ⟨rpow_pos_of_pos hM _, ?_⟩
  dsimp [automaticRadiusSquared160]
  rw [← rpow_natCast, ← rpow_mul hM.le]
  norm_num

theorem automatic_latitudeMoment160 {n : ℕ} (hn : 8000 ≤ n) :
    LatitudeMoment160 n (activeJacobianSquared160 n (automaticRadiusSquared160 n)) := by
  have hm : 0 < mA n := by
    unfold mA
    exact pow_pos (by omega : 0 < n) 2
  obtain ⟨ha, ha2, hcal⟩ := automaticRadius_guards hm (by omega : 1 ≤ n - 1 - 1)
  obtain ⟨hR0, hR⟩ := automaticRadiusSquared160_properties hn
  exact activeLatitudeMoment160 hn hR0 (activeRadialMoment160_factorial (by omega) ha ha2 hcal hR.le)

/-- No radial calibration premise or moment premise remains in this event supply. -/
theorem automatic_retained_charge160 {n : ℕ} (hn : 8000 ≤ n)
    (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real
      (agentEv D (activeRetainedEvent160 n (automaticRadiusSquared160 n)))ᶜ ≤ 1 / 10000 := by
  have hm : 0 < mA n := by
    unfold mA
    exact pow_pos (by omega : 0 < n) 2
  obtain ⟨ha, ha2, hcal⟩ := automaticRadius_guards hm (by omega : 1 ≤ n - 1 - 1)
  obtain ⟨hR0, hR⟩ := automaticRadiusSquared160_properties hn
  exact active_retained_charge160 hn hR0 (activeRadialMoment160_factorial (by omega) ha ha2 hcal hR.le) D hτ

end BstLean.Part221
