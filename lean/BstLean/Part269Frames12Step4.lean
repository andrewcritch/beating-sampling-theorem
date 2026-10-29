import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World12Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs12
import BstLean.Part269Rows12
import BstLean.Part269Sources12
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12670
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12670 : scalarRow12670.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12670, BstLean.Part268.grid12670, BstLean.Part263.worldGrid]

theorem supplies12670 (j : Fin 43) : Supply 12670 (parameters j)
    (cellLower scalarRow12670.grid (sourceIndex j))
    (cellUpper scalarRow12670.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12670.grid grid_top_bounds12670 j

theorem radii12670 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12670.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12670 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12670 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12670.grid grid_top_bounds12670 j hθ

noncomputable def covarianceInputs12670 :
    BstLean.Part263.CovarianceInputs 12670 scalarRow12670.grid parameters (caps repair12670) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12670 grid_top_bounds12670 repair12670

noncomputable def covarianceEvent12670 : Set (AgFam 12670) :=
  BstLean.Part263.covarianceEvent 12670 scalarRow12670.grid parameters

theorem covarianceEvent12670_measurable : MeasurableSet covarianceEvent12670 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12670_payment :
    (retDist (paperDesignP 12670).toCentres).real
      (agentEv (paperDesignP 12670) covarianceEvent12670)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12670

theorem localCov12670 : BstLean.Part259.LocalCovarianceOn covarianceEvent12670
    (BstLean.Part263.cell scalarRow12670.grid) (caps repair12670) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12670

theorem covarianceGood12670_payment :
    (retDist (paperDesignP 12670).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12670)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12670_payment



end BstLean.Part269.N12670

namespace BstLean.Part269.N12670
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12670}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12670.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12670) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12670).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12670 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12670) (by norm_num) BstLean.Part268.WorldRow12670.worldPackage rfl
    BstLean.Part268.WorldRow12670.product_lower (BstLean.Part268.WorldRow12670.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12670} (hw : c ∈ Hof BstLean.Part268.WorldRow12670.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12670) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12670) (by norm_num) BstLean.Part268.WorldRow12670.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12670} (hw : c ∈ Hof BstLean.Part268.WorldRow12670.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12670) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12670).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12670) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12670_eq : scalarRow12670.targetFrame = BstLean.Part268.agent12670.frame := by
  norm_num [scalarRow12670,BstLean.Part268.agent12670]

noncomputable def frameData12670 : BstLean.Part264b.FrameData 12670 :=
  BstLean.Part269.frameData_from_numerics (n := 12670) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12670.worldPackage rfl BstLean.Part268.WorldRow12670.product_lower (BstLean.Part268.WorldRow12670.producthi.2.trans (by norm_num))
    scalarRow12670 repair12670 covarianceInputs12670 (fun i hi => sourceNumerics12670 hi)
    BstLean.Part268.agent12670.frame targetFrame12670_eq


end BstLean.Part269.N12670

namespace BstLean.Part269.N12671
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12671 : scalarRow12671.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12671, BstLean.Part268.grid12671, BstLean.Part263.worldGrid]

theorem supplies12671 (j : Fin 43) : Supply 12671 (parameters j)
    (cellLower scalarRow12671.grid (sourceIndex j))
    (cellUpper scalarRow12671.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12671.grid grid_top_bounds12671 j

theorem radii12671 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12671.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12671 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12671 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12671.grid grid_top_bounds12671 j hθ

noncomputable def covarianceInputs12671 :
    BstLean.Part263.CovarianceInputs 12671 scalarRow12671.grid parameters (caps repair12671) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12671 grid_top_bounds12671 repair12671

noncomputable def covarianceEvent12671 : Set (AgFam 12671) :=
  BstLean.Part263.covarianceEvent 12671 scalarRow12671.grid parameters

theorem covarianceEvent12671_measurable : MeasurableSet covarianceEvent12671 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12671_payment :
    (retDist (paperDesignP 12671).toCentres).real
      (agentEv (paperDesignP 12671) covarianceEvent12671)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12671

theorem localCov12671 : BstLean.Part259.LocalCovarianceOn covarianceEvent12671
    (BstLean.Part263.cell scalarRow12671.grid) (caps repair12671) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12671

theorem covarianceGood12671_payment :
    (retDist (paperDesignP 12671).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12671)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12671_payment



end BstLean.Part269.N12671

namespace BstLean.Part269.N12671
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12671}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12671.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12671) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12671).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12671 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12671) (by norm_num) BstLean.Part268.WorldRow12671.worldPackage rfl
    BstLean.Part268.WorldRow12671.product_lower (BstLean.Part268.WorldRow12671.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12671} (hw : c ∈ Hof BstLean.Part268.WorldRow12671.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12671) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12671) (by norm_num) BstLean.Part268.WorldRow12671.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12671} (hw : c ∈ Hof BstLean.Part268.WorldRow12671.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12671) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12671).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12671) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12671_eq : scalarRow12671.targetFrame = BstLean.Part268.agent12671.frame := by
  norm_num [scalarRow12671,BstLean.Part268.agent12671]

noncomputable def frameData12671 : BstLean.Part264b.FrameData 12671 :=
  BstLean.Part269.frameData_from_numerics (n := 12671) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12671.worldPackage rfl BstLean.Part268.WorldRow12671.product_lower (BstLean.Part268.WorldRow12671.producthi.2.trans (by norm_num))
    scalarRow12671 repair12671 covarianceInputs12671 (fun i hi => sourceNumerics12671 hi)
    BstLean.Part268.agent12671.frame targetFrame12671_eq


end BstLean.Part269.N12671

namespace BstLean.Part269.N12672
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12672 : scalarRow12672.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12672, BstLean.Part268.grid12672, BstLean.Part263.worldGrid]

theorem supplies12672 (j : Fin 43) : Supply 12672 (parameters j)
    (cellLower scalarRow12672.grid (sourceIndex j))
    (cellUpper scalarRow12672.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12672.grid grid_top_bounds12672 j

theorem radii12672 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12672.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12672 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12672 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12672.grid grid_top_bounds12672 j hθ

noncomputable def covarianceInputs12672 :
    BstLean.Part263.CovarianceInputs 12672 scalarRow12672.grid parameters (caps repair12672) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12672 grid_top_bounds12672 repair12672

noncomputable def covarianceEvent12672 : Set (AgFam 12672) :=
  BstLean.Part263.covarianceEvent 12672 scalarRow12672.grid parameters

theorem covarianceEvent12672_measurable : MeasurableSet covarianceEvent12672 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12672_payment :
    (retDist (paperDesignP 12672).toCentres).real
      (agentEv (paperDesignP 12672) covarianceEvent12672)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12672

theorem localCov12672 : BstLean.Part259.LocalCovarianceOn covarianceEvent12672
    (BstLean.Part263.cell scalarRow12672.grid) (caps repair12672) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12672

theorem covarianceGood12672_payment :
    (retDist (paperDesignP 12672).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12672)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12672_payment



end BstLean.Part269.N12672

namespace BstLean.Part269.N12672
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12672}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12672.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12672) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12672).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12672 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12672) (by norm_num) BstLean.Part268.WorldRow12672.worldPackage rfl
    BstLean.Part268.WorldRow12672.product_lower (BstLean.Part268.WorldRow12672.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12672} (hw : c ∈ Hof BstLean.Part268.WorldRow12672.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12672) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12672) (by norm_num) BstLean.Part268.WorldRow12672.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12672} (hw : c ∈ Hof BstLean.Part268.WorldRow12672.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12672) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12672).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12672) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12672_eq : scalarRow12672.targetFrame = BstLean.Part268.agent12672.frame := by
  norm_num [scalarRow12672,BstLean.Part268.agent12672]

noncomputable def frameData12672 : BstLean.Part264b.FrameData 12672 :=
  BstLean.Part269.frameData_from_numerics (n := 12672) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12672.worldPackage rfl BstLean.Part268.WorldRow12672.product_lower (BstLean.Part268.WorldRow12672.producthi.2.trans (by norm_num))
    scalarRow12672 repair12672 covarianceInputs12672 (fun i hi => sourceNumerics12672 hi)
    BstLean.Part268.agent12672.frame targetFrame12672_eq


end BstLean.Part269.N12672

namespace BstLean.Part269.N12673
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12673 : scalarRow12673.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12673, BstLean.Part268.grid12673, BstLean.Part263.worldGrid]

theorem supplies12673 (j : Fin 43) : Supply 12673 (parameters j)
    (cellLower scalarRow12673.grid (sourceIndex j))
    (cellUpper scalarRow12673.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12673.grid grid_top_bounds12673 j

theorem radii12673 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12673.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12673 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12673 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12673.grid grid_top_bounds12673 j hθ

noncomputable def covarianceInputs12673 :
    BstLean.Part263.CovarianceInputs 12673 scalarRow12673.grid parameters (caps repair12673) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12673 grid_top_bounds12673 repair12673

noncomputable def covarianceEvent12673 : Set (AgFam 12673) :=
  BstLean.Part263.covarianceEvent 12673 scalarRow12673.grid parameters

theorem covarianceEvent12673_measurable : MeasurableSet covarianceEvent12673 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12673_payment :
    (retDist (paperDesignP 12673).toCentres).real
      (agentEv (paperDesignP 12673) covarianceEvent12673)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12673

theorem localCov12673 : BstLean.Part259.LocalCovarianceOn covarianceEvent12673
    (BstLean.Part263.cell scalarRow12673.grid) (caps repair12673) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12673

theorem covarianceGood12673_payment :
    (retDist (paperDesignP 12673).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12673)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12673_payment



end BstLean.Part269.N12673

namespace BstLean.Part269.N12673
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12673}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12673.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12673) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12673).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12673 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12673) (by norm_num) BstLean.Part268.WorldRow12673.worldPackage rfl
    BstLean.Part268.WorldRow12673.product_lower (BstLean.Part268.WorldRow12673.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12673} (hw : c ∈ Hof BstLean.Part268.WorldRow12673.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12673) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12673) (by norm_num) BstLean.Part268.WorldRow12673.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12673} (hw : c ∈ Hof BstLean.Part268.WorldRow12673.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12673) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12673).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12673) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12673_eq : scalarRow12673.targetFrame = BstLean.Part268.agent12673.frame := by
  norm_num [scalarRow12673,BstLean.Part268.agent12673]

noncomputable def frameData12673 : BstLean.Part264b.FrameData 12673 :=
  BstLean.Part269.frameData_from_numerics (n := 12673) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12673.worldPackage rfl BstLean.Part268.WorldRow12673.product_lower (BstLean.Part268.WorldRow12673.producthi.2.trans (by norm_num))
    scalarRow12673 repair12673 covarianceInputs12673 (fun i hi => sourceNumerics12673 hi)
    BstLean.Part268.agent12673.frame targetFrame12673_eq


end BstLean.Part269.N12673

namespace BstLean.Part269.N12674
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12674 : scalarRow12674.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12674, BstLean.Part268.grid12674, BstLean.Part263.worldGrid]

theorem supplies12674 (j : Fin 43) : Supply 12674 (parameters j)
    (cellLower scalarRow12674.grid (sourceIndex j))
    (cellUpper scalarRow12674.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12674.grid grid_top_bounds12674 j

theorem radii12674 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12674.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12674 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12674 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12674.grid grid_top_bounds12674 j hθ

noncomputable def covarianceInputs12674 :
    BstLean.Part263.CovarianceInputs 12674 scalarRow12674.grid parameters (caps repair12674) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12674 grid_top_bounds12674 repair12674

noncomputable def covarianceEvent12674 : Set (AgFam 12674) :=
  BstLean.Part263.covarianceEvent 12674 scalarRow12674.grid parameters

theorem covarianceEvent12674_measurable : MeasurableSet covarianceEvent12674 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12674_payment :
    (retDist (paperDesignP 12674).toCentres).real
      (agentEv (paperDesignP 12674) covarianceEvent12674)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12674

theorem localCov12674 : BstLean.Part259.LocalCovarianceOn covarianceEvent12674
    (BstLean.Part263.cell scalarRow12674.grid) (caps repair12674) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12674

theorem covarianceGood12674_payment :
    (retDist (paperDesignP 12674).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12674)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12674_payment



end BstLean.Part269.N12674

namespace BstLean.Part269.N12674
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12674}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12674.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12674) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12674).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12674 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12674) (by norm_num) BstLean.Part268.WorldRow12674.worldPackage rfl
    BstLean.Part268.WorldRow12674.product_lower (BstLean.Part268.WorldRow12674.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12674} (hw : c ∈ Hof BstLean.Part268.WorldRow12674.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12674) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12674) (by norm_num) BstLean.Part268.WorldRow12674.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12674} (hw : c ∈ Hof BstLean.Part268.WorldRow12674.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12674) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12674).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12674) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12674_eq : scalarRow12674.targetFrame = BstLean.Part268.agent12674.frame := by
  norm_num [scalarRow12674,BstLean.Part268.agent12674]

noncomputable def frameData12674 : BstLean.Part264b.FrameData 12674 :=
  BstLean.Part269.frameData_from_numerics (n := 12674) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12674.worldPackage rfl BstLean.Part268.WorldRow12674.product_lower (BstLean.Part268.WorldRow12674.producthi.2.trans (by norm_num))
    scalarRow12674 repair12674 covarianceInputs12674 (fun i hi => sourceNumerics12674 hi)
    BstLean.Part268.agent12674.frame targetFrame12674_eq


end BstLean.Part269.N12674
