import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World10Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs10
import BstLean.Part269Rows10
import BstLean.Part269Sources10
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12610
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12610 : scalarRow12610.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12610, BstLean.Part268.grid12610, BstLean.Part263.worldGrid]

theorem supplies12610 (j : Fin 43) : Supply 12610 (parameters j)
    (cellLower scalarRow12610.grid (sourceIndex j))
    (cellUpper scalarRow12610.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12610.grid grid_top_bounds12610 j

theorem radii12610 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12610.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12610 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12610 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12610.grid grid_top_bounds12610 j hθ

noncomputable def covarianceInputs12610 :
    BstLean.Part263.CovarianceInputs 12610 scalarRow12610.grid parameters (caps repair12610) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12610 grid_top_bounds12610 repair12610

noncomputable def covarianceEvent12610 : Set (AgFam 12610) :=
  BstLean.Part263.covarianceEvent 12610 scalarRow12610.grid parameters

theorem covarianceEvent12610_measurable : MeasurableSet covarianceEvent12610 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12610_payment :
    (retDist (paperDesignP 12610).toCentres).real
      (agentEv (paperDesignP 12610) covarianceEvent12610)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12610

theorem localCov12610 : BstLean.Part259.LocalCovarianceOn covarianceEvent12610
    (BstLean.Part263.cell scalarRow12610.grid) (caps repair12610) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12610

theorem covarianceGood12610_payment :
    (retDist (paperDesignP 12610).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12610)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12610_payment



end BstLean.Part269.N12610

namespace BstLean.Part269.N12610
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12610}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12610.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12610) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12610).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12610 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12610) (by norm_num) BstLean.Part268.WorldRow12610.worldPackage rfl
    BstLean.Part268.WorldRow12610.product_lower (BstLean.Part268.WorldRow12610.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12610} (hw : c ∈ Hof BstLean.Part268.WorldRow12610.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12610) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12610) (by norm_num) BstLean.Part268.WorldRow12610.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12610} (hw : c ∈ Hof BstLean.Part268.WorldRow12610.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12610) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12610).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12610) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12610_eq : scalarRow12610.targetFrame = BstLean.Part268.agent12610.frame := by
  norm_num [scalarRow12610,BstLean.Part268.agent12610]

noncomputable def frameData12610 : BstLean.Part264b.FrameData 12610 :=
  BstLean.Part269.frameData_from_numerics (n := 12610) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12610.worldPackage rfl BstLean.Part268.WorldRow12610.product_lower (BstLean.Part268.WorldRow12610.producthi.2.trans (by norm_num))
    scalarRow12610 repair12610 covarianceInputs12610 (fun i hi => sourceNumerics12610 hi)
    BstLean.Part268.agent12610.frame targetFrame12610_eq


end BstLean.Part269.N12610

namespace BstLean.Part269.N12611
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12611 : scalarRow12611.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12611, BstLean.Part268.grid12611, BstLean.Part263.worldGrid]

theorem supplies12611 (j : Fin 43) : Supply 12611 (parameters j)
    (cellLower scalarRow12611.grid (sourceIndex j))
    (cellUpper scalarRow12611.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12611.grid grid_top_bounds12611 j

theorem radii12611 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12611.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12611 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12611 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12611.grid grid_top_bounds12611 j hθ

noncomputable def covarianceInputs12611 :
    BstLean.Part263.CovarianceInputs 12611 scalarRow12611.grid parameters (caps repair12611) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12611 grid_top_bounds12611 repair12611

noncomputable def covarianceEvent12611 : Set (AgFam 12611) :=
  BstLean.Part263.covarianceEvent 12611 scalarRow12611.grid parameters

theorem covarianceEvent12611_measurable : MeasurableSet covarianceEvent12611 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12611_payment :
    (retDist (paperDesignP 12611).toCentres).real
      (agentEv (paperDesignP 12611) covarianceEvent12611)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12611

theorem localCov12611 : BstLean.Part259.LocalCovarianceOn covarianceEvent12611
    (BstLean.Part263.cell scalarRow12611.grid) (caps repair12611) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12611

theorem covarianceGood12611_payment :
    (retDist (paperDesignP 12611).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12611)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12611_payment



end BstLean.Part269.N12611

namespace BstLean.Part269.N12611
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12611}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12611.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12611) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12611).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12611 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12611) (by norm_num) BstLean.Part268.WorldRow12611.worldPackage rfl
    BstLean.Part268.WorldRow12611.product_lower (BstLean.Part268.WorldRow12611.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12611} (hw : c ∈ Hof BstLean.Part268.WorldRow12611.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12611) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12611) (by norm_num) BstLean.Part268.WorldRow12611.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12611} (hw : c ∈ Hof BstLean.Part268.WorldRow12611.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12611) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12611).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12611) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12611_eq : scalarRow12611.targetFrame = BstLean.Part268.agent12611.frame := by
  norm_num [scalarRow12611,BstLean.Part268.agent12611]

noncomputable def frameData12611 : BstLean.Part264b.FrameData 12611 :=
  BstLean.Part269.frameData_from_numerics (n := 12611) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12611.worldPackage rfl BstLean.Part268.WorldRow12611.product_lower (BstLean.Part268.WorldRow12611.producthi.2.trans (by norm_num))
    scalarRow12611 repair12611 covarianceInputs12611 (fun i hi => sourceNumerics12611 hi)
    BstLean.Part268.agent12611.frame targetFrame12611_eq


end BstLean.Part269.N12611

namespace BstLean.Part269.N12612
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12612 : scalarRow12612.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12612, BstLean.Part268.grid12612, BstLean.Part263.worldGrid]

theorem supplies12612 (j : Fin 43) : Supply 12612 (parameters j)
    (cellLower scalarRow12612.grid (sourceIndex j))
    (cellUpper scalarRow12612.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12612.grid grid_top_bounds12612 j

theorem radii12612 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12612.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12612 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12612 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12612.grid grid_top_bounds12612 j hθ

noncomputable def covarianceInputs12612 :
    BstLean.Part263.CovarianceInputs 12612 scalarRow12612.grid parameters (caps repair12612) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12612 grid_top_bounds12612 repair12612

noncomputable def covarianceEvent12612 : Set (AgFam 12612) :=
  BstLean.Part263.covarianceEvent 12612 scalarRow12612.grid parameters

theorem covarianceEvent12612_measurable : MeasurableSet covarianceEvent12612 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12612_payment :
    (retDist (paperDesignP 12612).toCentres).real
      (agentEv (paperDesignP 12612) covarianceEvent12612)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12612

theorem localCov12612 : BstLean.Part259.LocalCovarianceOn covarianceEvent12612
    (BstLean.Part263.cell scalarRow12612.grid) (caps repair12612) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12612

theorem covarianceGood12612_payment :
    (retDist (paperDesignP 12612).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12612)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12612_payment



end BstLean.Part269.N12612

namespace BstLean.Part269.N12612
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12612}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12612.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12612) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12612).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12612 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12612) (by norm_num) BstLean.Part268.WorldRow12612.worldPackage rfl
    BstLean.Part268.WorldRow12612.product_lower (BstLean.Part268.WorldRow12612.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12612} (hw : c ∈ Hof BstLean.Part268.WorldRow12612.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12612) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12612) (by norm_num) BstLean.Part268.WorldRow12612.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12612} (hw : c ∈ Hof BstLean.Part268.WorldRow12612.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12612) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12612).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12612) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12612_eq : scalarRow12612.targetFrame = BstLean.Part268.agent12612.frame := by
  norm_num [scalarRow12612,BstLean.Part268.agent12612]

noncomputable def frameData12612 : BstLean.Part264b.FrameData 12612 :=
  BstLean.Part269.frameData_from_numerics (n := 12612) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12612.worldPackage rfl BstLean.Part268.WorldRow12612.product_lower (BstLean.Part268.WorldRow12612.producthi.2.trans (by norm_num))
    scalarRow12612 repair12612 covarianceInputs12612 (fun i hi => sourceNumerics12612 hi)
    BstLean.Part268.agent12612.frame targetFrame12612_eq


end BstLean.Part269.N12612

namespace BstLean.Part269.N12613
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12613 : scalarRow12613.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12613, BstLean.Part268.grid12613, BstLean.Part263.worldGrid]

theorem supplies12613 (j : Fin 43) : Supply 12613 (parameters j)
    (cellLower scalarRow12613.grid (sourceIndex j))
    (cellUpper scalarRow12613.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12613.grid grid_top_bounds12613 j

theorem radii12613 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12613.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12613 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12613 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12613.grid grid_top_bounds12613 j hθ

noncomputable def covarianceInputs12613 :
    BstLean.Part263.CovarianceInputs 12613 scalarRow12613.grid parameters (caps repair12613) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12613 grid_top_bounds12613 repair12613

noncomputable def covarianceEvent12613 : Set (AgFam 12613) :=
  BstLean.Part263.covarianceEvent 12613 scalarRow12613.grid parameters

theorem covarianceEvent12613_measurable : MeasurableSet covarianceEvent12613 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12613_payment :
    (retDist (paperDesignP 12613).toCentres).real
      (agentEv (paperDesignP 12613) covarianceEvent12613)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12613

theorem localCov12613 : BstLean.Part259.LocalCovarianceOn covarianceEvent12613
    (BstLean.Part263.cell scalarRow12613.grid) (caps repair12613) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12613

theorem covarianceGood12613_payment :
    (retDist (paperDesignP 12613).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12613)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12613_payment



end BstLean.Part269.N12613

namespace BstLean.Part269.N12613
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12613}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12613.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12613) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12613).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12613 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12613) (by norm_num) BstLean.Part268.WorldRow12613.worldPackage rfl
    BstLean.Part268.WorldRow12613.product_lower (BstLean.Part268.WorldRow12613.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12613} (hw : c ∈ Hof BstLean.Part268.WorldRow12613.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12613) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12613) (by norm_num) BstLean.Part268.WorldRow12613.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12613} (hw : c ∈ Hof BstLean.Part268.WorldRow12613.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12613) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12613).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12613) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12613_eq : scalarRow12613.targetFrame = BstLean.Part268.agent12613.frame := by
  norm_num [scalarRow12613,BstLean.Part268.agent12613]

noncomputable def frameData12613 : BstLean.Part264b.FrameData 12613 :=
  BstLean.Part269.frameData_from_numerics (n := 12613) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12613.worldPackage rfl BstLean.Part268.WorldRow12613.product_lower (BstLean.Part268.WorldRow12613.producthi.2.trans (by norm_num))
    scalarRow12613 repair12613 covarianceInputs12613 (fun i hi => sourceNumerics12613 hi)
    BstLean.Part268.agent12613.frame targetFrame12613_eq


end BstLean.Part269.N12613

namespace BstLean.Part269.N12614
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12614 : scalarRow12614.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12614, BstLean.Part268.grid12614, BstLean.Part263.worldGrid]

theorem supplies12614 (j : Fin 43) : Supply 12614 (parameters j)
    (cellLower scalarRow12614.grid (sourceIndex j))
    (cellUpper scalarRow12614.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12614.grid grid_top_bounds12614 j

theorem radii12614 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12614.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12614 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12614 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12614.grid grid_top_bounds12614 j hθ

noncomputable def covarianceInputs12614 :
    BstLean.Part263.CovarianceInputs 12614 scalarRow12614.grid parameters (caps repair12614) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12614 grid_top_bounds12614 repair12614

noncomputable def covarianceEvent12614 : Set (AgFam 12614) :=
  BstLean.Part263.covarianceEvent 12614 scalarRow12614.grid parameters

theorem covarianceEvent12614_measurable : MeasurableSet covarianceEvent12614 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12614_payment :
    (retDist (paperDesignP 12614).toCentres).real
      (agentEv (paperDesignP 12614) covarianceEvent12614)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12614

theorem localCov12614 : BstLean.Part259.LocalCovarianceOn covarianceEvent12614
    (BstLean.Part263.cell scalarRow12614.grid) (caps repair12614) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12614

theorem covarianceGood12614_payment :
    (retDist (paperDesignP 12614).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12614)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12614_payment



end BstLean.Part269.N12614

namespace BstLean.Part269.N12614
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12614}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12614.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12614) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12614).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12614 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12614) (by norm_num) BstLean.Part268.WorldRow12614.worldPackage rfl
    BstLean.Part268.WorldRow12614.product_lower (BstLean.Part268.WorldRow12614.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12614} (hw : c ∈ Hof BstLean.Part268.WorldRow12614.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12614) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12614) (by norm_num) BstLean.Part268.WorldRow12614.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12614} (hw : c ∈ Hof BstLean.Part268.WorldRow12614.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12614) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12614).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12614) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12614_eq : scalarRow12614.targetFrame = BstLean.Part268.agent12614.frame := by
  norm_num [scalarRow12614,BstLean.Part268.agent12614]

noncomputable def frameData12614 : BstLean.Part264b.FrameData 12614 :=
  BstLean.Part269.frameData_from_numerics (n := 12614) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12614.worldPackage rfl BstLean.Part268.WorldRow12614.product_lower (BstLean.Part268.WorldRow12614.producthi.2.trans (by norm_num))
    scalarRow12614 repair12614 covarianceInputs12614 (fun i hi => sourceNumerics12614 hi)
    BstLean.Part268.agent12614.frame targetFrame12614_eq


end BstLean.Part269.N12614
