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

namespace BstLean.Part269.N12605
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12605 : scalarRow12605.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12605, BstLean.Part268.grid12605, BstLean.Part263.worldGrid]

theorem supplies12605 (j : Fin 43) : Supply 12605 (parameters j)
    (cellLower scalarRow12605.grid (sourceIndex j))
    (cellUpper scalarRow12605.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12605.grid grid_top_bounds12605 j

theorem radii12605 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12605.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12605 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12605 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12605.grid grid_top_bounds12605 j hθ

noncomputable def covarianceInputs12605 :
    BstLean.Part263.CovarianceInputs 12605 scalarRow12605.grid parameters (caps repair12605) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12605 grid_top_bounds12605 repair12605

noncomputable def covarianceEvent12605 : Set (AgFam 12605) :=
  BstLean.Part263.covarianceEvent 12605 scalarRow12605.grid parameters

theorem covarianceEvent12605_measurable : MeasurableSet covarianceEvent12605 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12605_payment :
    (retDist (paperDesignP 12605).toCentres).real
      (agentEv (paperDesignP 12605) covarianceEvent12605)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12605

theorem localCov12605 : BstLean.Part259.LocalCovarianceOn covarianceEvent12605
    (BstLean.Part263.cell scalarRow12605.grid) (caps repair12605) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12605

theorem covarianceGood12605_payment :
    (retDist (paperDesignP 12605).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12605)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12605_payment



end BstLean.Part269.N12605

namespace BstLean.Part269.N12605
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12605}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12605.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12605) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12605).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12605 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12605) (by norm_num) BstLean.Part268.WorldRow12605.worldPackage rfl
    BstLean.Part268.WorldRow12605.product_lower (BstLean.Part268.WorldRow12605.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12605} (hw : c ∈ Hof BstLean.Part268.WorldRow12605.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12605) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12605) (by norm_num) BstLean.Part268.WorldRow12605.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12605} (hw : c ∈ Hof BstLean.Part268.WorldRow12605.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12605) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12605).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12605) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12605_eq : scalarRow12605.targetFrame = BstLean.Part268.agent12605.frame := by
  norm_num [scalarRow12605,BstLean.Part268.agent12605]

noncomputable def frameData12605 : BstLean.Part264b.FrameData 12605 :=
  BstLean.Part269.frameData_from_numerics (n := 12605) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12605.worldPackage rfl BstLean.Part268.WorldRow12605.product_lower (BstLean.Part268.WorldRow12605.producthi.2.trans (by norm_num))
    scalarRow12605 repair12605 covarianceInputs12605 (fun i hi => sourceNumerics12605 hi)
    BstLean.Part268.agent12605.frame targetFrame12605_eq


end BstLean.Part269.N12605

namespace BstLean.Part269.N12606
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12606 : scalarRow12606.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12606, BstLean.Part268.grid12606, BstLean.Part263.worldGrid]

theorem supplies12606 (j : Fin 43) : Supply 12606 (parameters j)
    (cellLower scalarRow12606.grid (sourceIndex j))
    (cellUpper scalarRow12606.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12606.grid grid_top_bounds12606 j

theorem radii12606 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12606.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12606 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12606 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12606.grid grid_top_bounds12606 j hθ

noncomputable def covarianceInputs12606 :
    BstLean.Part263.CovarianceInputs 12606 scalarRow12606.grid parameters (caps repair12606) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12606 grid_top_bounds12606 repair12606

noncomputable def covarianceEvent12606 : Set (AgFam 12606) :=
  BstLean.Part263.covarianceEvent 12606 scalarRow12606.grid parameters

theorem covarianceEvent12606_measurable : MeasurableSet covarianceEvent12606 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12606_payment :
    (retDist (paperDesignP 12606).toCentres).real
      (agentEv (paperDesignP 12606) covarianceEvent12606)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12606

theorem localCov12606 : BstLean.Part259.LocalCovarianceOn covarianceEvent12606
    (BstLean.Part263.cell scalarRow12606.grid) (caps repair12606) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12606

theorem covarianceGood12606_payment :
    (retDist (paperDesignP 12606).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12606)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12606_payment



end BstLean.Part269.N12606

namespace BstLean.Part269.N12606
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12606}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12606.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12606) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12606).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12606 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12606) (by norm_num) BstLean.Part268.WorldRow12606.worldPackage rfl
    BstLean.Part268.WorldRow12606.product_lower (BstLean.Part268.WorldRow12606.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12606} (hw : c ∈ Hof BstLean.Part268.WorldRow12606.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12606) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12606) (by norm_num) BstLean.Part268.WorldRow12606.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12606} (hw : c ∈ Hof BstLean.Part268.WorldRow12606.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12606) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12606).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12606) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12606_eq : scalarRow12606.targetFrame = BstLean.Part268.agent12606.frame := by
  norm_num [scalarRow12606,BstLean.Part268.agent12606]

noncomputable def frameData12606 : BstLean.Part264b.FrameData 12606 :=
  BstLean.Part269.frameData_from_numerics (n := 12606) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12606.worldPackage rfl BstLean.Part268.WorldRow12606.product_lower (BstLean.Part268.WorldRow12606.producthi.2.trans (by norm_num))
    scalarRow12606 repair12606 covarianceInputs12606 (fun i hi => sourceNumerics12606 hi)
    BstLean.Part268.agent12606.frame targetFrame12606_eq


end BstLean.Part269.N12606

namespace BstLean.Part269.N12607
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12607 : scalarRow12607.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12607, BstLean.Part268.grid12607, BstLean.Part263.worldGrid]

theorem supplies12607 (j : Fin 43) : Supply 12607 (parameters j)
    (cellLower scalarRow12607.grid (sourceIndex j))
    (cellUpper scalarRow12607.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12607.grid grid_top_bounds12607 j

theorem radii12607 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12607.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12607 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12607 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12607.grid grid_top_bounds12607 j hθ

noncomputable def covarianceInputs12607 :
    BstLean.Part263.CovarianceInputs 12607 scalarRow12607.grid parameters (caps repair12607) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12607 grid_top_bounds12607 repair12607

noncomputable def covarianceEvent12607 : Set (AgFam 12607) :=
  BstLean.Part263.covarianceEvent 12607 scalarRow12607.grid parameters

theorem covarianceEvent12607_measurable : MeasurableSet covarianceEvent12607 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12607_payment :
    (retDist (paperDesignP 12607).toCentres).real
      (agentEv (paperDesignP 12607) covarianceEvent12607)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12607

theorem localCov12607 : BstLean.Part259.LocalCovarianceOn covarianceEvent12607
    (BstLean.Part263.cell scalarRow12607.grid) (caps repair12607) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12607

theorem covarianceGood12607_payment :
    (retDist (paperDesignP 12607).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12607)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12607_payment



end BstLean.Part269.N12607

namespace BstLean.Part269.N12607
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12607}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12607.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12607) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12607).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12607 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12607) (by norm_num) BstLean.Part268.WorldRow12607.worldPackage rfl
    BstLean.Part268.WorldRow12607.product_lower (BstLean.Part268.WorldRow12607.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12607} (hw : c ∈ Hof BstLean.Part268.WorldRow12607.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12607) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12607) (by norm_num) BstLean.Part268.WorldRow12607.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12607} (hw : c ∈ Hof BstLean.Part268.WorldRow12607.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12607) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12607).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12607) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12607_eq : scalarRow12607.targetFrame = BstLean.Part268.agent12607.frame := by
  norm_num [scalarRow12607,BstLean.Part268.agent12607]

noncomputable def frameData12607 : BstLean.Part264b.FrameData 12607 :=
  BstLean.Part269.frameData_from_numerics (n := 12607) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12607.worldPackage rfl BstLean.Part268.WorldRow12607.product_lower (BstLean.Part268.WorldRow12607.producthi.2.trans (by norm_num))
    scalarRow12607 repair12607 covarianceInputs12607 (fun i hi => sourceNumerics12607 hi)
    BstLean.Part268.agent12607.frame targetFrame12607_eq


end BstLean.Part269.N12607

namespace BstLean.Part269.N12608
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12608 : scalarRow12608.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12608, BstLean.Part268.grid12608, BstLean.Part263.worldGrid]

theorem supplies12608 (j : Fin 43) : Supply 12608 (parameters j)
    (cellLower scalarRow12608.grid (sourceIndex j))
    (cellUpper scalarRow12608.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12608.grid grid_top_bounds12608 j

theorem radii12608 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12608.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12608 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12608 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12608.grid grid_top_bounds12608 j hθ

noncomputable def covarianceInputs12608 :
    BstLean.Part263.CovarianceInputs 12608 scalarRow12608.grid parameters (caps repair12608) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12608 grid_top_bounds12608 repair12608

noncomputable def covarianceEvent12608 : Set (AgFam 12608) :=
  BstLean.Part263.covarianceEvent 12608 scalarRow12608.grid parameters

theorem covarianceEvent12608_measurable : MeasurableSet covarianceEvent12608 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12608_payment :
    (retDist (paperDesignP 12608).toCentres).real
      (agentEv (paperDesignP 12608) covarianceEvent12608)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12608

theorem localCov12608 : BstLean.Part259.LocalCovarianceOn covarianceEvent12608
    (BstLean.Part263.cell scalarRow12608.grid) (caps repair12608) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12608

theorem covarianceGood12608_payment :
    (retDist (paperDesignP 12608).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12608)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12608_payment



end BstLean.Part269.N12608

namespace BstLean.Part269.N12608
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12608}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12608.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12608) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12608).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12608 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12608) (by norm_num) BstLean.Part268.WorldRow12608.worldPackage rfl
    BstLean.Part268.WorldRow12608.product_lower (BstLean.Part268.WorldRow12608.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12608} (hw : c ∈ Hof BstLean.Part268.WorldRow12608.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12608) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12608) (by norm_num) BstLean.Part268.WorldRow12608.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12608} (hw : c ∈ Hof BstLean.Part268.WorldRow12608.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12608) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12608).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12608) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12608_eq : scalarRow12608.targetFrame = BstLean.Part268.agent12608.frame := by
  norm_num [scalarRow12608,BstLean.Part268.agent12608]

noncomputable def frameData12608 : BstLean.Part264b.FrameData 12608 :=
  BstLean.Part269.frameData_from_numerics (n := 12608) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12608.worldPackage rfl BstLean.Part268.WorldRow12608.product_lower (BstLean.Part268.WorldRow12608.producthi.2.trans (by norm_num))
    scalarRow12608 repair12608 covarianceInputs12608 (fun i hi => sourceNumerics12608 hi)
    BstLean.Part268.agent12608.frame targetFrame12608_eq


end BstLean.Part269.N12608

namespace BstLean.Part269.N12609
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12609 : scalarRow12609.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12609, BstLean.Part268.grid12609, BstLean.Part263.worldGrid]

theorem supplies12609 (j : Fin 43) : Supply 12609 (parameters j)
    (cellLower scalarRow12609.grid (sourceIndex j))
    (cellUpper scalarRow12609.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12609.grid grid_top_bounds12609 j

theorem radii12609 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12609.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12609 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12609 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12609.grid grid_top_bounds12609 j hθ

noncomputable def covarianceInputs12609 :
    BstLean.Part263.CovarianceInputs 12609 scalarRow12609.grid parameters (caps repair12609) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12609 grid_top_bounds12609 repair12609

noncomputable def covarianceEvent12609 : Set (AgFam 12609) :=
  BstLean.Part263.covarianceEvent 12609 scalarRow12609.grid parameters

theorem covarianceEvent12609_measurable : MeasurableSet covarianceEvent12609 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12609_payment :
    (retDist (paperDesignP 12609).toCentres).real
      (agentEv (paperDesignP 12609) covarianceEvent12609)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12609

theorem localCov12609 : BstLean.Part259.LocalCovarianceOn covarianceEvent12609
    (BstLean.Part263.cell scalarRow12609.grid) (caps repair12609) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12609

theorem covarianceGood12609_payment :
    (retDist (paperDesignP 12609).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12609)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12609_payment



end BstLean.Part269.N12609

namespace BstLean.Part269.N12609
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12609}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12609.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12609) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12609).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12609 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12609) (by norm_num) BstLean.Part268.WorldRow12609.worldPackage rfl
    BstLean.Part268.WorldRow12609.product_lower (BstLean.Part268.WorldRow12609.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12609} (hw : c ∈ Hof BstLean.Part268.WorldRow12609.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12609) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12609) (by norm_num) BstLean.Part268.WorldRow12609.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12609} (hw : c ∈ Hof BstLean.Part268.WorldRow12609.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12609) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12609).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12609) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12609_eq : scalarRow12609.targetFrame = BstLean.Part268.agent12609.frame := by
  norm_num [scalarRow12609,BstLean.Part268.agent12609]

noncomputable def frameData12609 : BstLean.Part264b.FrameData 12609 :=
  BstLean.Part269.frameData_from_numerics (n := 12609) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12609.worldPackage rfl BstLean.Part268.WorldRow12609.product_lower (BstLean.Part268.WorldRow12609.producthi.2.trans (by norm_num))
    scalarRow12609 repair12609 covarianceInputs12609 (fun i hi => sourceNumerics12609 hi)
    BstLean.Part268.agent12609.frame targetFrame12609_eq


end BstLean.Part269.N12609
