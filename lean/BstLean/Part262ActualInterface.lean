import BstLean.Part262LowMass
import BstLean.Part262Sources

/-! The actual-table and HQ root interface consumes local source interfaces.
It has no pass-moment, table-payment, fluctuation or covariance premise. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188

structure ActualRootCertificate (n : ℕ) (root : ℝ) where
  dimension : 12225 ≤ n
  table_payment : (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ (9 / 10000 : ℝ)
  inputs : ∀ (t : ℝ) (c : Ret n), WINDOW (paperDesignP n) c → c ∈ sourceBase n →
    WFInterfaces (paperDesignP n) c (91 / 1000) ((2101 / 100) / n) (4 / 100) →
    centreEnergy (paperDesignP n) c ≤ 702 / 1000 →
    BstLean.Part243.RootInputs n t c root

structure LocalRootSupply (n : ℕ) (H : Set (Ret n)) : Prop where
  window : ∀ c ∈ H, c ∈ sourceBase n → WINDOW (paperDesignP n) c
  interfaces : ∀ c ∈ H, c ∈ sourceBase n →
    WFInterfaces (paperDesignP n) c (91 / 1000) ((2101 / 100) / n) (4 / 100)
  energy_cap : ∀ c ∈ H, c ∈ sourceBase n → centreEnergy (paperDesignP n) c ≤ 702 / 1000

noncomputable def actualBaseRootSupply {n : ℕ} {root : ℝ}
    (C : ActualRootCertificate n root) (H : Set (Ret n)) (L : LocalRootSupply n H) :
    BaseRootSupply n H root (1499145 / 10 ^ 9) where
  event := sourceBase n
  measurable := sourceBase_measurable (by have := C.dimension; omega)
  payment := (sourceBase_charge C.dimension C.table_payment H).trans (by norm_num)
  inputs := fun t c hw hc => C.inputs t c (L.window c hw hc) hc
    (L.interfaces c hw hc) (L.energy_cap c hw hc)

theorem actual_common_payment {n : ℕ} {root : ℝ}
    (C : ActualRootCertificate n root) {event : Set (BstLean.Part160.AgFam n)}
    (hCovariance : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (commonEvent n event)ᶜ) ≤
      (1799145 / 10 ^ 9 : ℝ) :=
  (commonEvent_charge C.dimension C.table_payment hCovariance H).trans (by norm_num)

end BstLean.Part262
