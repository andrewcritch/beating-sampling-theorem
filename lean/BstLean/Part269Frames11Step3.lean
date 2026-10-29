import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World11Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs11
import BstLean.Part269Rows11
import BstLean.Part269Sources11
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12640
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12640 : scalarRow12640.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12640, BstLean.Part268.grid12640, BstLean.Part263.worldGrid]

theorem supplies12640 (j : Fin 43) : Supply 12640 (parameters j)
    (cellLower scalarRow12640.grid (sourceIndex j))
    (cellUpper scalarRow12640.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12640.grid grid_top_bounds12640 j

theorem radii12640 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12640.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12640 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12640 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12640.grid grid_top_bounds12640 j hθ

noncomputable def covarianceInputs12640 :
    BstLean.Part263.CovarianceInputs 12640 scalarRow12640.grid parameters (caps repair12640) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12640 grid_top_bounds12640 repair12640

noncomputable def covarianceEvent12640 : Set (AgFam 12640) :=
  BstLean.Part263.covarianceEvent 12640 scalarRow12640.grid parameters

theorem covarianceEvent12640_measurable : MeasurableSet covarianceEvent12640 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12640_payment :
    (retDist (paperDesignP 12640).toCentres).real
      (agentEv (paperDesignP 12640) covarianceEvent12640)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12640

theorem localCov12640 : BstLean.Part259.LocalCovarianceOn covarianceEvent12640
    (BstLean.Part263.cell scalarRow12640.grid) (caps repair12640) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12640

theorem covarianceGood12640_payment :
    (retDist (paperDesignP 12640).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12640)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12640_payment



end BstLean.Part269.N12640

namespace BstLean.Part269.N12640
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12640}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12640.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12640) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12640).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12640 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12640) (by norm_num) BstLean.Part268.WorldRow12640.worldPackage rfl
    BstLean.Part268.WorldRow12640.product_lower (BstLean.Part268.WorldRow12640.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12640} (hw : c ∈ Hof BstLean.Part268.WorldRow12640.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12640) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12640) (by norm_num) BstLean.Part268.WorldRow12640.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12640} (hw : c ∈ Hof BstLean.Part268.WorldRow12640.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12640) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12640).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12640) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12640_eq : scalarRow12640.targetFrame = BstLean.Part268.agent12640.frame := by
  norm_num [scalarRow12640,BstLean.Part268.agent12640]

noncomputable def frameData12640 : BstLean.Part264b.FrameData 12640 :=
  BstLean.Part269.frameData_from_numerics (n := 12640) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12640.worldPackage rfl BstLean.Part268.WorldRow12640.product_lower (BstLean.Part268.WorldRow12640.producthi.2.trans (by norm_num))
    scalarRow12640 repair12640 covarianceInputs12640 (fun i hi => sourceNumerics12640 hi)
    BstLean.Part268.agent12640.frame targetFrame12640_eq


end BstLean.Part269.N12640

namespace BstLean.Part269.N12641
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12641 : scalarRow12641.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12641, BstLean.Part268.grid12641, BstLean.Part263.worldGrid]

theorem supplies12641 (j : Fin 43) : Supply 12641 (parameters j)
    (cellLower scalarRow12641.grid (sourceIndex j))
    (cellUpper scalarRow12641.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12641.grid grid_top_bounds12641 j

theorem radii12641 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12641.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12641 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12641 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12641.grid grid_top_bounds12641 j hθ

noncomputable def covarianceInputs12641 :
    BstLean.Part263.CovarianceInputs 12641 scalarRow12641.grid parameters (caps repair12641) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12641 grid_top_bounds12641 repair12641

noncomputable def covarianceEvent12641 : Set (AgFam 12641) :=
  BstLean.Part263.covarianceEvent 12641 scalarRow12641.grid parameters

theorem covarianceEvent12641_measurable : MeasurableSet covarianceEvent12641 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12641_payment :
    (retDist (paperDesignP 12641).toCentres).real
      (agentEv (paperDesignP 12641) covarianceEvent12641)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12641

theorem localCov12641 : BstLean.Part259.LocalCovarianceOn covarianceEvent12641
    (BstLean.Part263.cell scalarRow12641.grid) (caps repair12641) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12641

theorem covarianceGood12641_payment :
    (retDist (paperDesignP 12641).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12641)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12641_payment



end BstLean.Part269.N12641

namespace BstLean.Part269.N12641
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12641}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12641.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12641) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12641).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12641 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12641) (by norm_num) BstLean.Part268.WorldRow12641.worldPackage rfl
    BstLean.Part268.WorldRow12641.product_lower (BstLean.Part268.WorldRow12641.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12641} (hw : c ∈ Hof BstLean.Part268.WorldRow12641.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12641) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12641) (by norm_num) BstLean.Part268.WorldRow12641.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12641} (hw : c ∈ Hof BstLean.Part268.WorldRow12641.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12641) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12641).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12641) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12641_eq : scalarRow12641.targetFrame = BstLean.Part268.agent12641.frame := by
  norm_num [scalarRow12641,BstLean.Part268.agent12641]

noncomputable def frameData12641 : BstLean.Part264b.FrameData 12641 :=
  BstLean.Part269.frameData_from_numerics (n := 12641) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12641.worldPackage rfl BstLean.Part268.WorldRow12641.product_lower (BstLean.Part268.WorldRow12641.producthi.2.trans (by norm_num))
    scalarRow12641 repair12641 covarianceInputs12641 (fun i hi => sourceNumerics12641 hi)
    BstLean.Part268.agent12641.frame targetFrame12641_eq


end BstLean.Part269.N12641

namespace BstLean.Part269.N12642
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12642 : scalarRow12642.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12642, BstLean.Part268.grid12642, BstLean.Part263.worldGrid]

theorem supplies12642 (j : Fin 43) : Supply 12642 (parameters j)
    (cellLower scalarRow12642.grid (sourceIndex j))
    (cellUpper scalarRow12642.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12642.grid grid_top_bounds12642 j

theorem radii12642 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12642.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12642 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12642 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12642.grid grid_top_bounds12642 j hθ

noncomputable def covarianceInputs12642 :
    BstLean.Part263.CovarianceInputs 12642 scalarRow12642.grid parameters (caps repair12642) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12642 grid_top_bounds12642 repair12642

noncomputable def covarianceEvent12642 : Set (AgFam 12642) :=
  BstLean.Part263.covarianceEvent 12642 scalarRow12642.grid parameters

theorem covarianceEvent12642_measurable : MeasurableSet covarianceEvent12642 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12642_payment :
    (retDist (paperDesignP 12642).toCentres).real
      (agentEv (paperDesignP 12642) covarianceEvent12642)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12642

theorem localCov12642 : BstLean.Part259.LocalCovarianceOn covarianceEvent12642
    (BstLean.Part263.cell scalarRow12642.grid) (caps repair12642) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12642

theorem covarianceGood12642_payment :
    (retDist (paperDesignP 12642).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12642)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12642_payment



end BstLean.Part269.N12642

namespace BstLean.Part269.N12642
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12642}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12642.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12642) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12642).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12642 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12642) (by norm_num) BstLean.Part268.WorldRow12642.worldPackage rfl
    BstLean.Part268.WorldRow12642.product_lower (BstLean.Part268.WorldRow12642.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12642} (hw : c ∈ Hof BstLean.Part268.WorldRow12642.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12642) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12642) (by norm_num) BstLean.Part268.WorldRow12642.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12642} (hw : c ∈ Hof BstLean.Part268.WorldRow12642.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12642) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12642).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12642) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12642_eq : scalarRow12642.targetFrame = BstLean.Part268.agent12642.frame := by
  norm_num [scalarRow12642,BstLean.Part268.agent12642]

noncomputable def frameData12642 : BstLean.Part264b.FrameData 12642 :=
  BstLean.Part269.frameData_from_numerics (n := 12642) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12642.worldPackage rfl BstLean.Part268.WorldRow12642.product_lower (BstLean.Part268.WorldRow12642.producthi.2.trans (by norm_num))
    scalarRow12642 repair12642 covarianceInputs12642 (fun i hi => sourceNumerics12642 hi)
    BstLean.Part268.agent12642.frame targetFrame12642_eq


end BstLean.Part269.N12642

namespace BstLean.Part269.N12643
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12643 : scalarRow12643.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12643, BstLean.Part268.grid12643, BstLean.Part263.worldGrid]

theorem supplies12643 (j : Fin 43) : Supply 12643 (parameters j)
    (cellLower scalarRow12643.grid (sourceIndex j))
    (cellUpper scalarRow12643.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12643.grid grid_top_bounds12643 j

theorem radii12643 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12643.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12643 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12643 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12643.grid grid_top_bounds12643 j hθ

noncomputable def covarianceInputs12643 :
    BstLean.Part263.CovarianceInputs 12643 scalarRow12643.grid parameters (caps repair12643) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12643 grid_top_bounds12643 repair12643

noncomputable def covarianceEvent12643 : Set (AgFam 12643) :=
  BstLean.Part263.covarianceEvent 12643 scalarRow12643.grid parameters

theorem covarianceEvent12643_measurable : MeasurableSet covarianceEvent12643 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12643_payment :
    (retDist (paperDesignP 12643).toCentres).real
      (agentEv (paperDesignP 12643) covarianceEvent12643)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12643

theorem localCov12643 : BstLean.Part259.LocalCovarianceOn covarianceEvent12643
    (BstLean.Part263.cell scalarRow12643.grid) (caps repair12643) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12643

theorem covarianceGood12643_payment :
    (retDist (paperDesignP 12643).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12643)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12643_payment



end BstLean.Part269.N12643

namespace BstLean.Part269.N12643
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12643}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12643.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12643) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12643).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12643 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12643) (by norm_num) BstLean.Part268.WorldRow12643.worldPackage rfl
    BstLean.Part268.WorldRow12643.product_lower (BstLean.Part268.WorldRow12643.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12643} (hw : c ∈ Hof BstLean.Part268.WorldRow12643.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12643) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12643) (by norm_num) BstLean.Part268.WorldRow12643.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12643} (hw : c ∈ Hof BstLean.Part268.WorldRow12643.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12643) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12643).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12643) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12643_eq : scalarRow12643.targetFrame = BstLean.Part268.agent12643.frame := by
  norm_num [scalarRow12643,BstLean.Part268.agent12643]

noncomputable def frameData12643 : BstLean.Part264b.FrameData 12643 :=
  BstLean.Part269.frameData_from_numerics (n := 12643) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12643.worldPackage rfl BstLean.Part268.WorldRow12643.product_lower (BstLean.Part268.WorldRow12643.producthi.2.trans (by norm_num))
    scalarRow12643 repair12643 covarianceInputs12643 (fun i hi => sourceNumerics12643 hi)
    BstLean.Part268.agent12643.frame targetFrame12643_eq


end BstLean.Part269.N12643

namespace BstLean.Part269.N12644
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12644 : scalarRow12644.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12644, BstLean.Part268.grid12644, BstLean.Part263.worldGrid]

theorem supplies12644 (j : Fin 43) : Supply 12644 (parameters j)
    (cellLower scalarRow12644.grid (sourceIndex j))
    (cellUpper scalarRow12644.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12644.grid grid_top_bounds12644 j

theorem radii12644 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12644.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12644 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12644 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12644.grid grid_top_bounds12644 j hθ

noncomputable def covarianceInputs12644 :
    BstLean.Part263.CovarianceInputs 12644 scalarRow12644.grid parameters (caps repair12644) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12644 grid_top_bounds12644 repair12644

noncomputable def covarianceEvent12644 : Set (AgFam 12644) :=
  BstLean.Part263.covarianceEvent 12644 scalarRow12644.grid parameters

theorem covarianceEvent12644_measurable : MeasurableSet covarianceEvent12644 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12644_payment :
    (retDist (paperDesignP 12644).toCentres).real
      (agentEv (paperDesignP 12644) covarianceEvent12644)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12644

theorem localCov12644 : BstLean.Part259.LocalCovarianceOn covarianceEvent12644
    (BstLean.Part263.cell scalarRow12644.grid) (caps repair12644) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12644

theorem covarianceGood12644_payment :
    (retDist (paperDesignP 12644).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12644)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12644_payment



end BstLean.Part269.N12644

namespace BstLean.Part269.N12644
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12644}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12644.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12644) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12644).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12644 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12644) (by norm_num) BstLean.Part268.WorldRow12644.worldPackage rfl
    BstLean.Part268.WorldRow12644.product_lower (BstLean.Part268.WorldRow12644.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12644} (hw : c ∈ Hof BstLean.Part268.WorldRow12644.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12644) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12644) (by norm_num) BstLean.Part268.WorldRow12644.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12644} (hw : c ∈ Hof BstLean.Part268.WorldRow12644.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12644) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12644).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12644) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12644_eq : scalarRow12644.targetFrame = BstLean.Part268.agent12644.frame := by
  norm_num [scalarRow12644,BstLean.Part268.agent12644]

noncomputable def frameData12644 : BstLean.Part264b.FrameData 12644 :=
  BstLean.Part269.frameData_from_numerics (n := 12644) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12644.worldPackage rfl BstLean.Part268.WorldRow12644.product_lower (BstLean.Part268.WorldRow12644.producthi.2.trans (by norm_num))
    scalarRow12644 repair12644 covarianceInputs12644 (fun i hi => sourceNumerics12644 hi)
    BstLean.Part268.agent12644.frame targetFrame12644_eq


end BstLean.Part269.N12644
