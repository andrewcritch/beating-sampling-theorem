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

namespace BstLean.Part269.N12530
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12530 : scalarRow12530.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12530, BstLean.Part268.grid12530, BstLean.Part263.worldGrid]

theorem supplies12530 (j : Fin 43) : Supply 12530 (parameters j)
    (cellLower scalarRow12530.grid (sourceIndex j))
    (cellUpper scalarRow12530.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12530.grid grid_top_bounds12530 j

theorem radii12530 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12530.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12530 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12530 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12530.grid grid_top_bounds12530 j hθ

noncomputable def covarianceInputs12530 :
    BstLean.Part263.CovarianceInputs 12530 scalarRow12530.grid parameters (caps repair12530) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12530 grid_top_bounds12530 repair12530

noncomputable def covarianceEvent12530 : Set (AgFam 12530) :=
  BstLean.Part263.covarianceEvent 12530 scalarRow12530.grid parameters

theorem covarianceEvent12530_measurable : MeasurableSet covarianceEvent12530 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12530_payment :
    (retDist (paperDesignP 12530).toCentres).real
      (agentEv (paperDesignP 12530) covarianceEvent12530)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12530

theorem localCov12530 : BstLean.Part259.LocalCovarianceOn covarianceEvent12530
    (BstLean.Part263.cell scalarRow12530.grid) (caps repair12530) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12530

theorem covarianceGood12530_payment :
    (retDist (paperDesignP 12530).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12530)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12530_payment



end BstLean.Part269.N12530

namespace BstLean.Part269.N12530
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12530}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12530.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12530) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12530).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12530 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12530) (by norm_num) BstLean.Part268.WorldRow12530.worldPackage rfl
    BstLean.Part268.WorldRow12530.product_lower (BstLean.Part268.WorldRow12530.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12530} (hw : c ∈ Hof BstLean.Part268.WorldRow12530.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12530) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12530) (by norm_num) BstLean.Part268.WorldRow12530.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12530} (hw : c ∈ Hof BstLean.Part268.WorldRow12530.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12530) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12530).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12530) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12530_eq : scalarRow12530.targetFrame = BstLean.Part268.agent12530.frame := by
  norm_num [scalarRow12530,BstLean.Part268.agent12530]

noncomputable def frameData12530 : BstLean.Part264b.FrameData 12530 :=
  BstLean.Part269.frameData_from_numerics (n := 12530) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12530.worldPackage rfl BstLean.Part268.WorldRow12530.product_lower (BstLean.Part268.WorldRow12530.producthi.2.trans (by norm_num))
    scalarRow12530 repair12530 covarianceInputs12530 (fun i hi => sourceNumerics12530 hi)
    BstLean.Part268.agent12530.frame targetFrame12530_eq


end BstLean.Part269.N12530

namespace BstLean.Part269.N12531
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12531 : scalarRow12531.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12531, BstLean.Part268.grid12531, BstLean.Part263.worldGrid]

theorem supplies12531 (j : Fin 43) : Supply 12531 (parameters j)
    (cellLower scalarRow12531.grid (sourceIndex j))
    (cellUpper scalarRow12531.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12531.grid grid_top_bounds12531 j

theorem radii12531 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12531.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12531 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12531 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12531.grid grid_top_bounds12531 j hθ

noncomputable def covarianceInputs12531 :
    BstLean.Part263.CovarianceInputs 12531 scalarRow12531.grid parameters (caps repair12531) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12531 grid_top_bounds12531 repair12531

noncomputable def covarianceEvent12531 : Set (AgFam 12531) :=
  BstLean.Part263.covarianceEvent 12531 scalarRow12531.grid parameters

theorem covarianceEvent12531_measurable : MeasurableSet covarianceEvent12531 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12531_payment :
    (retDist (paperDesignP 12531).toCentres).real
      (agentEv (paperDesignP 12531) covarianceEvent12531)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12531

theorem localCov12531 : BstLean.Part259.LocalCovarianceOn covarianceEvent12531
    (BstLean.Part263.cell scalarRow12531.grid) (caps repair12531) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12531

theorem covarianceGood12531_payment :
    (retDist (paperDesignP 12531).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12531)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12531_payment



end BstLean.Part269.N12531

namespace BstLean.Part269.N12531
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12531}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12531.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12531) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12531).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12531 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12531) (by norm_num) BstLean.Part268.WorldRow12531.worldPackage rfl
    BstLean.Part268.WorldRow12531.product_lower (BstLean.Part268.WorldRow12531.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12531} (hw : c ∈ Hof BstLean.Part268.WorldRow12531.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12531) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12531) (by norm_num) BstLean.Part268.WorldRow12531.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12531} (hw : c ∈ Hof BstLean.Part268.WorldRow12531.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12531) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12531).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12531) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12531_eq : scalarRow12531.targetFrame = BstLean.Part268.agent12531.frame := by
  norm_num [scalarRow12531,BstLean.Part268.agent12531]

noncomputable def frameData12531 : BstLean.Part264b.FrameData 12531 :=
  BstLean.Part269.frameData_from_numerics (n := 12531) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12531.worldPackage rfl BstLean.Part268.WorldRow12531.product_lower (BstLean.Part268.WorldRow12531.producthi.2.trans (by norm_num))
    scalarRow12531 repair12531 covarianceInputs12531 (fun i hi => sourceNumerics12531 hi)
    BstLean.Part268.agent12531.frame targetFrame12531_eq


end BstLean.Part269.N12531

namespace BstLean.Part269.N12532
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12532 : scalarRow12532.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12532, BstLean.Part268.grid12532, BstLean.Part263.worldGrid]

theorem supplies12532 (j : Fin 43) : Supply 12532 (parameters j)
    (cellLower scalarRow12532.grid (sourceIndex j))
    (cellUpper scalarRow12532.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12532.grid grid_top_bounds12532 j

theorem radii12532 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12532.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12532 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12532 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12532.grid grid_top_bounds12532 j hθ

noncomputable def covarianceInputs12532 :
    BstLean.Part263.CovarianceInputs 12532 scalarRow12532.grid parameters (caps repair12532) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12532 grid_top_bounds12532 repair12532

noncomputable def covarianceEvent12532 : Set (AgFam 12532) :=
  BstLean.Part263.covarianceEvent 12532 scalarRow12532.grid parameters

theorem covarianceEvent12532_measurable : MeasurableSet covarianceEvent12532 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12532_payment :
    (retDist (paperDesignP 12532).toCentres).real
      (agentEv (paperDesignP 12532) covarianceEvent12532)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12532

theorem localCov12532 : BstLean.Part259.LocalCovarianceOn covarianceEvent12532
    (BstLean.Part263.cell scalarRow12532.grid) (caps repair12532) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12532

theorem covarianceGood12532_payment :
    (retDist (paperDesignP 12532).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12532)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12532_payment



end BstLean.Part269.N12532

namespace BstLean.Part269.N12532
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12532}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12532.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12532) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12532).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12532 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12532) (by norm_num) BstLean.Part268.WorldRow12532.worldPackage rfl
    BstLean.Part268.WorldRow12532.product_lower (BstLean.Part268.WorldRow12532.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12532} (hw : c ∈ Hof BstLean.Part268.WorldRow12532.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12532) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12532) (by norm_num) BstLean.Part268.WorldRow12532.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12532} (hw : c ∈ Hof BstLean.Part268.WorldRow12532.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12532) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12532).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12532) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12532_eq : scalarRow12532.targetFrame = BstLean.Part268.agent12532.frame := by
  norm_num [scalarRow12532,BstLean.Part268.agent12532]

noncomputable def frameData12532 : BstLean.Part264b.FrameData 12532 :=
  BstLean.Part269.frameData_from_numerics (n := 12532) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12532.worldPackage rfl BstLean.Part268.WorldRow12532.product_lower (BstLean.Part268.WorldRow12532.producthi.2.trans (by norm_num))
    scalarRow12532 repair12532 covarianceInputs12532 (fun i hi => sourceNumerics12532 hi)
    BstLean.Part268.agent12532.frame targetFrame12532_eq


end BstLean.Part269.N12532

namespace BstLean.Part269.N12533
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12533 : scalarRow12533.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12533, BstLean.Part268.grid12533, BstLean.Part263.worldGrid]

theorem supplies12533 (j : Fin 43) : Supply 12533 (parameters j)
    (cellLower scalarRow12533.grid (sourceIndex j))
    (cellUpper scalarRow12533.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12533.grid grid_top_bounds12533 j

theorem radii12533 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12533.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12533 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12533 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12533.grid grid_top_bounds12533 j hθ

noncomputable def covarianceInputs12533 :
    BstLean.Part263.CovarianceInputs 12533 scalarRow12533.grid parameters (caps repair12533) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12533 grid_top_bounds12533 repair12533

noncomputable def covarianceEvent12533 : Set (AgFam 12533) :=
  BstLean.Part263.covarianceEvent 12533 scalarRow12533.grid parameters

theorem covarianceEvent12533_measurable : MeasurableSet covarianceEvent12533 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12533_payment :
    (retDist (paperDesignP 12533).toCentres).real
      (agentEv (paperDesignP 12533) covarianceEvent12533)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12533

theorem localCov12533 : BstLean.Part259.LocalCovarianceOn covarianceEvent12533
    (BstLean.Part263.cell scalarRow12533.grid) (caps repair12533) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12533

theorem covarianceGood12533_payment :
    (retDist (paperDesignP 12533).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12533)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12533_payment



end BstLean.Part269.N12533

namespace BstLean.Part269.N12533
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12533}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12533.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12533) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12533).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12533 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12533) (by norm_num) BstLean.Part268.WorldRow12533.worldPackage rfl
    BstLean.Part268.WorldRow12533.product_lower (BstLean.Part268.WorldRow12533.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12533} (hw : c ∈ Hof BstLean.Part268.WorldRow12533.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12533) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12533) (by norm_num) BstLean.Part268.WorldRow12533.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12533} (hw : c ∈ Hof BstLean.Part268.WorldRow12533.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12533) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12533).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12533) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12533_eq : scalarRow12533.targetFrame = BstLean.Part268.agent12533.frame := by
  norm_num [scalarRow12533,BstLean.Part268.agent12533]

noncomputable def frameData12533 : BstLean.Part264b.FrameData 12533 :=
  BstLean.Part269.frameData_from_numerics (n := 12533) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12533.worldPackage rfl BstLean.Part268.WorldRow12533.product_lower (BstLean.Part268.WorldRow12533.producthi.2.trans (by norm_num))
    scalarRow12533 repair12533 covarianceInputs12533 (fun i hi => sourceNumerics12533 hi)
    BstLean.Part268.agent12533.frame targetFrame12533_eq


end BstLean.Part269.N12533

namespace BstLean.Part269.N12534
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12534 : scalarRow12534.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12534, BstLean.Part268.grid12534, BstLean.Part263.worldGrid]

theorem supplies12534 (j : Fin 43) : Supply 12534 (parameters j)
    (cellLower scalarRow12534.grid (sourceIndex j))
    (cellUpper scalarRow12534.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12534.grid grid_top_bounds12534 j

theorem radii12534 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12534.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12534 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12534 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12534.grid grid_top_bounds12534 j hθ

noncomputable def covarianceInputs12534 :
    BstLean.Part263.CovarianceInputs 12534 scalarRow12534.grid parameters (caps repair12534) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12534 grid_top_bounds12534 repair12534

noncomputable def covarianceEvent12534 : Set (AgFam 12534) :=
  BstLean.Part263.covarianceEvent 12534 scalarRow12534.grid parameters

theorem covarianceEvent12534_measurable : MeasurableSet covarianceEvent12534 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12534_payment :
    (retDist (paperDesignP 12534).toCentres).real
      (agentEv (paperDesignP 12534) covarianceEvent12534)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12534

theorem localCov12534 : BstLean.Part259.LocalCovarianceOn covarianceEvent12534
    (BstLean.Part263.cell scalarRow12534.grid) (caps repair12534) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12534

theorem covarianceGood12534_payment :
    (retDist (paperDesignP 12534).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12534)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12534_payment



end BstLean.Part269.N12534

namespace BstLean.Part269.N12534
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12534}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12534.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12534) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12534).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12534 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12534) (by norm_num) BstLean.Part268.WorldRow12534.worldPackage rfl
    BstLean.Part268.WorldRow12534.product_lower (BstLean.Part268.WorldRow12534.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12534} (hw : c ∈ Hof BstLean.Part268.WorldRow12534.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12534) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12534) (by norm_num) BstLean.Part268.WorldRow12534.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12534} (hw : c ∈ Hof BstLean.Part268.WorldRow12534.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12534) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12534).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12534) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12534_eq : scalarRow12534.targetFrame = BstLean.Part268.agent12534.frame := by
  norm_num [scalarRow12534,BstLean.Part268.agent12534]

noncomputable def frameData12534 : BstLean.Part264b.FrameData 12534 :=
  BstLean.Part269.frameData_from_numerics (n := 12534) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12534.worldPackage rfl BstLean.Part268.WorldRow12534.product_lower (BstLean.Part268.WorldRow12534.producthi.2.trans (by norm_num))
    scalarRow12534 repair12534 covarianceInputs12534 (fun i hi => sourceNumerics12534 hi)
    BstLean.Part268.agent12534.frame targetFrame12534_eq


end BstLean.Part269.N12534
