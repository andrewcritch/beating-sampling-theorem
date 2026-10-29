import BstLean.Part293ActualEvents
import BstLean.Part293SchurCharge
import BstLean.Part134Var

/-! The exact node 40 interface supplies the last field of the paid band record. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part169 BstLean.Part188
open BstLean.Part289 BstLean.BlueprintLow

def BandFrameTests : Prop := ∀ {n : ℕ}, LowBand n → ∀ c : Ret n,
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528 →
    0 < normSq c.1.2 → 0 < (paperDesignP n).tau0 c →
    c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c) →
    ((c.1.2, (paperDesignP n).tau0 c), c.2.1.1) ∈ selectedSchurEvent n →
    ∀ v : Fin (mA n) → ℝ, normSq v = 1 →
    (n : ℝ) * ∫ ξ, (∑ j, eDir ((statedDesign2 n).bA c.1 c.2.1.1)
      (hStand (statedDesign2 n) c ξ) j * v j) ^ 2
      ∂stdGauss (Fin n) < weightedFrameCap

noncomputable def frameSupply_of_band_tests (tests : BandFrameTests) :
    RemainingFrameSupply where
  schur := fun _ hn => schurCharge_of_band hn.1
  frame := by
    intro n hn
    apply frameA_of_WF_tests (by have := hn.1; omega)
    intro c hc v hv
    have H := actualRetainedFields hn (schurCharge_of_band hn.1) hc
    have hschur : c ∈ selectedSchurRetained n := hc.1.1.2
    exact (tests hn c H.theta H.worldcentre_pos H.tau_pos
      H.source_agent (hschur H.tau_pos) v hv).le.trans
      (by norm_num [weightedFrameCap, agentFrame])

theorem classifier_stated2_8000_11882_of_frame_tests (tests : BandFrameTests) :
    ∀ n ∈ Icc (8000 : ℕ) 11882, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
        (10 ^ 12) z.1 z.2)} :=
  classifier_stated2_8000_11882_of_supplies (frameSupply_of_band_tests tests).toBandInputs

end BstLean.Part293

/-- info: 'BstLean.Part293.classifier_stated2_8000_11882_of_frame_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000_11882_of_frame_tests
