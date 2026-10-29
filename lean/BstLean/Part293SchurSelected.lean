import BstLean.Part291SchurSelection
import BstLean.Part289Design

/-! Use Part 291's adaptive low-noise event as the Schur event throughout the
   Part 293 ledger. This keeps the event and the corrected TI payment aligned. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160
open BstLean.Part169 BstLean.Part289 BstLean.BlueprintLow

def selectedSchurEvent (n : ℕ) : Set (AgFam n) := lowSchurBandEvent n

theorem selectedSchurEvent_measurable (n : ℕ) : MeasurableSet (selectedSchurEvent n) :=
  lowSchurBandEvent_measurable n

theorem selectedSchurEvent_charge {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c, τ), a) ∉ selectedSchurEvent n} ≤ (0.00025 : ℝ) :=
  lowSchurBandEvent_charge hn c hτ

def selectedSchurRetained (n : ℕ) : Set (Ret n) := lowSchurRetained n

theorem selectedSchurRetained_measurable (n : ℕ) :
    MeasurableSet (selectedSchurRetained n) := lowSchurRetained_measurable n

theorem selectedSchurRetained_charge {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (BstLean.Part289.statedDesign2 n).toCentres).real
      (selectedSchurRetained n)ᶜ ≤ 0.00025 :=
  lowSchurRetained_charge hn

end BstLean.Part293
