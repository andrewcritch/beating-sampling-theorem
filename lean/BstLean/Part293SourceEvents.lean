import BstLean.Part293Ledger
import BstLean.Part291SourceEvents
import BstLean.Part289Design

/-! Lift the actual source family to retained data with one source payment. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part252 BstLean.Part289

def sourceFamily (n : ℕ) : Set (AgFam n) :=
  (CentreSources n n ∩ (DirectionError n ∩ Operator160 n)) ∩ Energy32 n

theorem sourceFamily_measurable {n : ℕ} (hn : 1 ≤ n) :
    MeasurableSet (sourceFamily n) :=
  ((measurableSet_CentreSources hn n).inter
    ((measurableSet_DirectionError n).inter (measurableSet_Operator160 n))).inter
      (measurableSet_Energy32 n)

noncomputable def sourceCharge_of_band {n : ℕ} (hn : 8000 ≤ n) :
    NetworkCharge (retDist (statedDesign2 n).toCentres) sourceCharge where
  event := agentEv (statedDesign2 n) (sourceFamily n)
  measurable := measurableSet_agentEv _ (sourceFamily_measurable (by omega))
  nonneg := by norm_num [sourceCharge]
  complement := by
    rw [agentEv_compl]
    apply retDist_agent_charge (statedDesign2 n)
      (paperDesign_tauWorld passF passW measurable_passF measurable_passW)
      (sourceFamily_measurable (by omega))
      (by norm_num [sourceCharge])
    intro c tau htau
    exact (BstLean.BlueprintLow.agentCentreEvent_charge hn c htau).le.trans
      (by norm_num [sourceCharge])

theorem sourceFields_of_band {n : ℕ} (hn : 8000 ≤ n) {c : Ret n}
    (hc : c ∈ (sourceCharge_of_band hn).event) (htau : 0 < (paperDesignP n).tau0 c) :
    c.2.1.1 ∈ BstLean.BlueprintLow.agentCentreEvent c.1.2 ((paperDesignP n).tau0 c) :=
  hc htau

end BstLean.Part293
