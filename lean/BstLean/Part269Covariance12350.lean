import BstLean.Part269Repair12350
import BstLean.Part264Covariance
import BstLean.Part269Supply12350Cells0
import BstLean.Part269Supply12350Cells1
import BstLean.Part269Supply12350Cells2
import BstLean.Part269Supply12350Cells3
import BstLean.Part269Supply12350Cells4
import BstLean.Part269Supply12350Cells5
import BstLean.Part269Supply12350Cells6
import BstLean.Part269Supply12350Cells7
import BstLean.Part269Supply12350Cells8
namespace BstLean.Part269.N12350
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem supplies12350 (j : Fin 43) : Supply 12350 (parameters j)
    (cellLower scalarRow12350.grid (sourceIndex j)) (cellUpper scalarRow12350.grid (sourceIndex j)) := by
  match j with
  | ⟨0,_⟩ => exact supply10
  | ⟨1,_⟩ => exact supply11
  | ⟨2,_⟩ => exact supply12
  | ⟨3,_⟩ => exact supply13
  | ⟨4,_⟩ => exact supply14
  | ⟨5,_⟩ => exact supply15
  | ⟨6,_⟩ => exact supply16
  | ⟨7,_⟩ => exact supply17
  | ⟨8,_⟩ => exact supply18
  | ⟨9,_⟩ => exact supply19
  | ⟨10,_⟩ => exact supply20
  | ⟨11,_⟩ => exact supply21
  | ⟨12,_⟩ => exact supply22
  | ⟨13,_⟩ => exact supply23
  | ⟨14,_⟩ => exact supply24
  | ⟨15,_⟩ => exact supply25
  | ⟨16,_⟩ => exact supply26
  | ⟨17,_⟩ => exact supply27
  | ⟨18,_⟩ => exact supply28
  | ⟨19,_⟩ => exact supply29
  | ⟨20,_⟩ => exact supply30
  | ⟨21,_⟩ => exact supply31
  | ⟨22,_⟩ => exact supply32
  | ⟨23,_⟩ => exact supply33
  | ⟨24,_⟩ => exact supply34
  | ⟨25,_⟩ => exact supply35
  | ⟨26,_⟩ => exact supply36
  | ⟨27,_⟩ => exact supply37
  | ⟨28,_⟩ => exact supply38
  | ⟨29,_⟩ => exact supply39
  | ⟨30,_⟩ => exact supply40
  | ⟨31,_⟩ => exact supply41
  | ⟨32,_⟩ => exact supply42
  | ⟨33,_⟩ => exact supply43
  | ⟨34,_⟩ => exact supply44
  | ⟨35,_⟩ => exact supply45
  | ⟨36,_⟩ => exact supply46
  | ⟨37,_⟩ => exact supply47
  | ⟨38,_⟩ => exact supply48
  | ⟨39,_⟩ => exact supply49
  | ⟨40,_⟩ => exact supply50
  | ⟨41,_⟩ => exact supply51
  | ⟨42,_⟩ => exact supply52
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem radii12350 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius := by
  match j with
  | ⟨0,_⟩ => exact (geometryCell10 hθ).2.2
  | ⟨1,_⟩ => exact (geometryCell11 hθ).2.2
  | ⟨2,_⟩ => exact (geometryCell12 hθ).2.2
  | ⟨3,_⟩ => exact (geometryCell13 hθ).2.2
  | ⟨4,_⟩ => exact (geometryCell14 hθ).2.2
  | ⟨5,_⟩ => exact (geometryCell15 hθ).2.2
  | ⟨6,_⟩ => exact (geometryCell16 hθ).2.2
  | ⟨7,_⟩ => exact (geometryCell17 hθ).2.2
  | ⟨8,_⟩ => exact (geometryCell18 hθ).2.2
  | ⟨9,_⟩ => exact (geometryCell19 hθ).2.2
  | ⟨10,_⟩ => exact (geometryCell20 hθ).2.2
  | ⟨11,_⟩ => exact (geometryCell21 hθ).2.2
  | ⟨12,_⟩ => exact (geometryCell22 hθ).2.2
  | ⟨13,_⟩ => exact (geometryCell23 hθ).2.2
  | ⟨14,_⟩ => exact (geometryCell24 hθ).2.2
  | ⟨15,_⟩ => exact (geometryCell25 hθ).2.2
  | ⟨16,_⟩ => exact (geometryCell26 hθ).2.2
  | ⟨17,_⟩ => exact (geometryCell27 hθ).2.2
  | ⟨18,_⟩ => exact (geometryCell28 hθ).2.2
  | ⟨19,_⟩ => exact (geometryCell29 hθ).2.2
  | ⟨20,_⟩ => exact (geometryCell30 hθ).2.2
  | ⟨21,_⟩ => exact (geometryCell31 hθ).2.2
  | ⟨22,_⟩ => exact (geometryCell32 hθ).2.2
  | ⟨23,_⟩ => exact (geometryCell33 hθ).2.2
  | ⟨24,_⟩ => exact (geometryCell34 hθ).2.2
  | ⟨25,_⟩ => exact (geometryCell35 hθ).2.2
  | ⟨26,_⟩ => exact (geometryCell36 hθ).2.2
  | ⟨27,_⟩ => exact (geometryCell37 hθ).2.2
  | ⟨28,_⟩ => exact (geometryCell38 hθ).2.2
  | ⟨29,_⟩ => exact (geometryCell39 hθ).2.2
  | ⟨30,_⟩ => exact (geometryCell40 hθ).2.2
  | ⟨31,_⟩ => exact (geometryCell41 hθ).2.2
  | ⟨32,_⟩ => exact (geometryCell42 hθ).2.2
  | ⟨33,_⟩ => exact (geometryCell43 hθ).2.2
  | ⟨34,_⟩ => exact (geometryCell44 hθ).2.2
  | ⟨35,_⟩ => exact (geometryCell45 hθ).2.2
  | ⟨36,_⟩ => exact (geometryCell46 hθ).2.2
  | ⟨37,_⟩ => exact (geometryCell47 hθ).2.2
  | ⟨38,_⟩ => exact (geometryCell48 hθ).2.2
  | ⟨39,_⟩ => exact (geometryCell49 hθ).2.2
  | ⟨40,_⟩ => exact (geometryCell50 hθ).2.2
  | ⟨41,_⟩ => exact (geometryCell51 hθ).2.2
  | ⟨42,_⟩ => exact (geometryCell52 hθ).2.2
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def covarianceInputs12350 :
    BstLean.Part263.CovarianceInputs 12350 scalarRow12350.grid parameters (caps repair12350) :=
  covarianceInputs_from_supplies (by norm_num) repair12350 supplies12350
    (fun j _ hθ => radii12350 j hθ)

noncomputable def covarianceEvent12350 : Set (AgFam 12350) :=
  BstLean.Part263.covarianceEvent 12350 scalarRow12350.grid parameters

theorem covarianceEvent12350_measurable : MeasurableSet covarianceEvent12350 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12350_payment :
    (retDist (paperDesignP 12350).toCentres).real
      (agentEv (paperDesignP 12350) covarianceEvent12350)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12350

theorem localCov12350 : BstLean.Part259.LocalCovarianceOn covarianceEvent12350
    (BstLean.Part263.cell scalarRow12350.grid) (caps repair12350) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12350

theorem covarianceGood12350_payment :
    (retDist (paperDesignP 12350).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12350)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12350_payment



end BstLean.Part269.N12350
