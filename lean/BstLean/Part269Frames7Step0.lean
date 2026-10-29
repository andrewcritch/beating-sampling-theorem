import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World7Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs7
import BstLean.Part269Rows7
import BstLean.Part269Sources7
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12525
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12525 : scalarRow12525.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12525, BstLean.Part268.grid12525, BstLean.Part263.worldGrid]

theorem supplies12525 (j : Fin 43) : Supply 12525 (parameters j)
    (cellLower scalarRow12525.grid (sourceIndex j))
    (cellUpper scalarRow12525.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12525.grid grid_top_bounds12525 j

theorem radii12525 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12525.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12525 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12525 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12525.grid grid_top_bounds12525 j hθ

noncomputable def covarianceInputs12525 :
    BstLean.Part263.CovarianceInputs 12525 scalarRow12525.grid parameters (caps repair12525) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12525 grid_top_bounds12525 repair12525

noncomputable def covarianceEvent12525 : Set (AgFam 12525) :=
  BstLean.Part263.covarianceEvent 12525 scalarRow12525.grid parameters

theorem covarianceEvent12525_measurable : MeasurableSet covarianceEvent12525 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12525_payment :
    (retDist (paperDesignP 12525).toCentres).real
      (agentEv (paperDesignP 12525) covarianceEvent12525)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12525

theorem localCov12525 : BstLean.Part259.LocalCovarianceOn covarianceEvent12525
    (BstLean.Part263.cell scalarRow12525.grid) (caps repair12525) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12525

theorem covarianceGood12525_payment :
    (retDist (paperDesignP 12525).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12525)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12525_payment



end BstLean.Part269.N12525

namespace BstLean.Part269.N12525
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12525}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12525.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12525) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12525).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12525 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12525) (by norm_num) BstLean.Part268.WorldRow12525.worldPackage rfl
    BstLean.Part268.WorldRow12525.product_lower (BstLean.Part268.WorldRow12525.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12525} (hw : c ∈ Hof BstLean.Part268.WorldRow12525.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12525) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12525) (by norm_num) BstLean.Part268.WorldRow12525.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12525} (hw : c ∈ Hof BstLean.Part268.WorldRow12525.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12525) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12525).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12525) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12525_eq : scalarRow12525.targetFrame = BstLean.Part268.agent12525.frame := by
  norm_num [scalarRow12525,BstLean.Part268.agent12525]

noncomputable def frameData12525 : BstLean.Part264b.FrameData 12525 :=
  BstLean.Part269.frameData_from_numerics (n := 12525) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12525.worldPackage rfl BstLean.Part268.WorldRow12525.product_lower (BstLean.Part268.WorldRow12525.producthi.2.trans (by norm_num))
    scalarRow12525 repair12525 covarianceInputs12525 (fun i hi => sourceNumerics12525 hi)
    BstLean.Part268.agent12525.frame targetFrame12525_eq


end BstLean.Part269.N12525

namespace BstLean.Part269.N12526
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12526 : scalarRow12526.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12526, BstLean.Part268.grid12526, BstLean.Part263.worldGrid]

theorem supplies12526 (j : Fin 43) : Supply 12526 (parameters j)
    (cellLower scalarRow12526.grid (sourceIndex j))
    (cellUpper scalarRow12526.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12526.grid grid_top_bounds12526 j

theorem radii12526 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12526.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12526 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12526 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12526.grid grid_top_bounds12526 j hθ

noncomputable def covarianceInputs12526 :
    BstLean.Part263.CovarianceInputs 12526 scalarRow12526.grid parameters (caps repair12526) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12526 grid_top_bounds12526 repair12526

noncomputable def covarianceEvent12526 : Set (AgFam 12526) :=
  BstLean.Part263.covarianceEvent 12526 scalarRow12526.grid parameters

theorem covarianceEvent12526_measurable : MeasurableSet covarianceEvent12526 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12526_payment :
    (retDist (paperDesignP 12526).toCentres).real
      (agentEv (paperDesignP 12526) covarianceEvent12526)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12526

theorem localCov12526 : BstLean.Part259.LocalCovarianceOn covarianceEvent12526
    (BstLean.Part263.cell scalarRow12526.grid) (caps repair12526) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12526

theorem covarianceGood12526_payment :
    (retDist (paperDesignP 12526).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12526)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12526_payment



end BstLean.Part269.N12526

namespace BstLean.Part269.N12526
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12526}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12526.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12526) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12526).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12526 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12526) (by norm_num) BstLean.Part268.WorldRow12526.worldPackage rfl
    BstLean.Part268.WorldRow12526.product_lower (BstLean.Part268.WorldRow12526.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12526} (hw : c ∈ Hof BstLean.Part268.WorldRow12526.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12526) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12526) (by norm_num) BstLean.Part268.WorldRow12526.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12526} (hw : c ∈ Hof BstLean.Part268.WorldRow12526.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12526) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12526).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12526) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12526_eq : scalarRow12526.targetFrame = BstLean.Part268.agent12526.frame := by
  norm_num [scalarRow12526,BstLean.Part268.agent12526]

noncomputable def frameData12526 : BstLean.Part264b.FrameData 12526 :=
  BstLean.Part269.frameData_from_numerics (n := 12526) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12526.worldPackage rfl BstLean.Part268.WorldRow12526.product_lower (BstLean.Part268.WorldRow12526.producthi.2.trans (by norm_num))
    scalarRow12526 repair12526 covarianceInputs12526 (fun i hi => sourceNumerics12526 hi)
    BstLean.Part268.agent12526.frame targetFrame12526_eq


end BstLean.Part269.N12526

namespace BstLean.Part269.N12527
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12527 : scalarRow12527.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12527, BstLean.Part268.grid12527, BstLean.Part263.worldGrid]

theorem supplies12527 (j : Fin 43) : Supply 12527 (parameters j)
    (cellLower scalarRow12527.grid (sourceIndex j))
    (cellUpper scalarRow12527.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12527.grid grid_top_bounds12527 j

theorem radii12527 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12527.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12527 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12527 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12527.grid grid_top_bounds12527 j hθ

noncomputable def covarianceInputs12527 :
    BstLean.Part263.CovarianceInputs 12527 scalarRow12527.grid parameters (caps repair12527) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12527 grid_top_bounds12527 repair12527

noncomputable def covarianceEvent12527 : Set (AgFam 12527) :=
  BstLean.Part263.covarianceEvent 12527 scalarRow12527.grid parameters

theorem covarianceEvent12527_measurable : MeasurableSet covarianceEvent12527 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12527_payment :
    (retDist (paperDesignP 12527).toCentres).real
      (agentEv (paperDesignP 12527) covarianceEvent12527)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12527

theorem localCov12527 : BstLean.Part259.LocalCovarianceOn covarianceEvent12527
    (BstLean.Part263.cell scalarRow12527.grid) (caps repair12527) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12527

theorem covarianceGood12527_payment :
    (retDist (paperDesignP 12527).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12527)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12527_payment



end BstLean.Part269.N12527

namespace BstLean.Part269.N12527
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12527}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12527.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12527) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12527).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12527 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12527) (by norm_num) BstLean.Part268.WorldRow12527.worldPackage rfl
    BstLean.Part268.WorldRow12527.product_lower (BstLean.Part268.WorldRow12527.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12527} (hw : c ∈ Hof BstLean.Part268.WorldRow12527.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12527) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12527) (by norm_num) BstLean.Part268.WorldRow12527.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12527} (hw : c ∈ Hof BstLean.Part268.WorldRow12527.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12527) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12527).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12527) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12527_eq : scalarRow12527.targetFrame = BstLean.Part268.agent12527.frame := by
  norm_num [scalarRow12527,BstLean.Part268.agent12527]

noncomputable def frameData12527 : BstLean.Part264b.FrameData 12527 :=
  BstLean.Part269.frameData_from_numerics (n := 12527) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12527.worldPackage rfl BstLean.Part268.WorldRow12527.product_lower (BstLean.Part268.WorldRow12527.producthi.2.trans (by norm_num))
    scalarRow12527 repair12527 covarianceInputs12527 (fun i hi => sourceNumerics12527 hi)
    BstLean.Part268.agent12527.frame targetFrame12527_eq


end BstLean.Part269.N12527

namespace BstLean.Part269.N12528
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12528 : scalarRow12528.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12528, BstLean.Part268.grid12528, BstLean.Part263.worldGrid]

theorem supplies12528 (j : Fin 43) : Supply 12528 (parameters j)
    (cellLower scalarRow12528.grid (sourceIndex j))
    (cellUpper scalarRow12528.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12528.grid grid_top_bounds12528 j

theorem radii12528 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12528.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12528 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12528 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12528.grid grid_top_bounds12528 j hθ

noncomputable def covarianceInputs12528 :
    BstLean.Part263.CovarianceInputs 12528 scalarRow12528.grid parameters (caps repair12528) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12528 grid_top_bounds12528 repair12528

noncomputable def covarianceEvent12528 : Set (AgFam 12528) :=
  BstLean.Part263.covarianceEvent 12528 scalarRow12528.grid parameters

theorem covarianceEvent12528_measurable : MeasurableSet covarianceEvent12528 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12528_payment :
    (retDist (paperDesignP 12528).toCentres).real
      (agentEv (paperDesignP 12528) covarianceEvent12528)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12528

theorem localCov12528 : BstLean.Part259.LocalCovarianceOn covarianceEvent12528
    (BstLean.Part263.cell scalarRow12528.grid) (caps repair12528) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12528

theorem covarianceGood12528_payment :
    (retDist (paperDesignP 12528).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12528)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12528_payment



end BstLean.Part269.N12528

namespace BstLean.Part269.N12528
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12528}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12528.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12528) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12528).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12528 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12528) (by norm_num) BstLean.Part268.WorldRow12528.worldPackage rfl
    BstLean.Part268.WorldRow12528.product_lower (BstLean.Part268.WorldRow12528.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12528} (hw : c ∈ Hof BstLean.Part268.WorldRow12528.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12528) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12528) (by norm_num) BstLean.Part268.WorldRow12528.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12528} (hw : c ∈ Hof BstLean.Part268.WorldRow12528.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12528) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12528).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12528) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12528_eq : scalarRow12528.targetFrame = BstLean.Part268.agent12528.frame := by
  norm_num [scalarRow12528,BstLean.Part268.agent12528]

noncomputable def frameData12528 : BstLean.Part264b.FrameData 12528 :=
  BstLean.Part269.frameData_from_numerics (n := 12528) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12528.worldPackage rfl BstLean.Part268.WorldRow12528.product_lower (BstLean.Part268.WorldRow12528.producthi.2.trans (by norm_num))
    scalarRow12528 repair12528 covarianceInputs12528 (fun i hi => sourceNumerics12528 hi)
    BstLean.Part268.agent12528.frame targetFrame12528_eq


end BstLean.Part269.N12528

namespace BstLean.Part269.N12529
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12529 : scalarRow12529.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12529, BstLean.Part268.grid12529, BstLean.Part263.worldGrid]

theorem supplies12529 (j : Fin 43) : Supply 12529 (parameters j)
    (cellLower scalarRow12529.grid (sourceIndex j))
    (cellUpper scalarRow12529.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12529.grid grid_top_bounds12529 j

theorem radii12529 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12529.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12529 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12529 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12529.grid grid_top_bounds12529 j hθ

noncomputable def covarianceInputs12529 :
    BstLean.Part263.CovarianceInputs 12529 scalarRow12529.grid parameters (caps repair12529) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12529 grid_top_bounds12529 repair12529

noncomputable def covarianceEvent12529 : Set (AgFam 12529) :=
  BstLean.Part263.covarianceEvent 12529 scalarRow12529.grid parameters

theorem covarianceEvent12529_measurable : MeasurableSet covarianceEvent12529 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12529_payment :
    (retDist (paperDesignP 12529).toCentres).real
      (agentEv (paperDesignP 12529) covarianceEvent12529)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12529

theorem localCov12529 : BstLean.Part259.LocalCovarianceOn covarianceEvent12529
    (BstLean.Part263.cell scalarRow12529.grid) (caps repair12529) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12529

theorem covarianceGood12529_payment :
    (retDist (paperDesignP 12529).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12529)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12529_payment



end BstLean.Part269.N12529

namespace BstLean.Part269.N12529
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12529}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12529.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12529) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12529).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12529 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12529) (by norm_num) BstLean.Part268.WorldRow12529.worldPackage rfl
    BstLean.Part268.WorldRow12529.product_lower (BstLean.Part268.WorldRow12529.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12529} (hw : c ∈ Hof BstLean.Part268.WorldRow12529.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12529) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12529) (by norm_num) BstLean.Part268.WorldRow12529.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12529} (hw : c ∈ Hof BstLean.Part268.WorldRow12529.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12529) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12529).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12529) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12529_eq : scalarRow12529.targetFrame = BstLean.Part268.agent12529.frame := by
  norm_num [scalarRow12529,BstLean.Part268.agent12529]

noncomputable def frameData12529 : BstLean.Part264b.FrameData 12529 :=
  BstLean.Part269.frameData_from_numerics (n := 12529) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12529.worldPackage rfl BstLean.Part268.WorldRow12529.product_lower (BstLean.Part268.WorldRow12529.producthi.2.trans (by norm_num))
    scalarRow12529 repair12529 covarianceInputs12529 (fun i hi => sourceNumerics12529 hi)
    BstLean.Part268.agent12529.frame targetFrame12529_eq


end BstLean.Part269.N12529
