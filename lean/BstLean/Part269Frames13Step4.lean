import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World13Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs13
import BstLean.Part269Rows13
import BstLean.Part269Sources13
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12695
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12695 : scalarRow12695.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12695, BstLean.Part268.grid12695, BstLean.Part263.worldGrid]

theorem supplies12695 (j : Fin 43) : Supply 12695 (parameters j)
    (cellLower scalarRow12695.grid (sourceIndex j))
    (cellUpper scalarRow12695.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12695.grid grid_top_bounds12695 j

theorem radii12695 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12695.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12695 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12695 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12695.grid grid_top_bounds12695 j hθ

noncomputable def covarianceInputs12695 :
    BstLean.Part263.CovarianceInputs 12695 scalarRow12695.grid parameters (caps repair12695) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12695 grid_top_bounds12695 repair12695

noncomputable def covarianceEvent12695 : Set (AgFam 12695) :=
  BstLean.Part263.covarianceEvent 12695 scalarRow12695.grid parameters

theorem covarianceEvent12695_measurable : MeasurableSet covarianceEvent12695 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12695_payment :
    (retDist (paperDesignP 12695).toCentres).real
      (agentEv (paperDesignP 12695) covarianceEvent12695)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12695

theorem localCov12695 : BstLean.Part259.LocalCovarianceOn covarianceEvent12695
    (BstLean.Part263.cell scalarRow12695.grid) (caps repair12695) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12695

theorem covarianceGood12695_payment :
    (retDist (paperDesignP 12695).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12695)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12695_payment



end BstLean.Part269.N12695

namespace BstLean.Part269.N12695
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12695}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12695.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12695) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12695).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12695 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12695) (by norm_num) BstLean.Part268.WorldRow12695.worldPackage rfl
    BstLean.Part268.WorldRow12695.product_lower (BstLean.Part268.WorldRow12695.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12695} (hw : c ∈ Hof BstLean.Part268.WorldRow12695.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12695) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12695) (by norm_num) BstLean.Part268.WorldRow12695.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12695} (hw : c ∈ Hof BstLean.Part268.WorldRow12695.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12695) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12695).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12695) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12695_eq : scalarRow12695.targetFrame = BstLean.Part268.agent12695.frame := by
  norm_num [scalarRow12695,BstLean.Part268.agent12695]

noncomputable def frameData12695 : BstLean.Part264b.FrameData 12695 :=
  BstLean.Part269.frameData_from_numerics (n := 12695) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12695.worldPackage rfl BstLean.Part268.WorldRow12695.product_lower (BstLean.Part268.WorldRow12695.producthi.2.trans (by norm_num))
    scalarRow12695 repair12695 covarianceInputs12695 (fun i hi => sourceNumerics12695 hi)
    BstLean.Part268.agent12695.frame targetFrame12695_eq


end BstLean.Part269.N12695

namespace BstLean.Part269.N12696
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12696 : scalarRow12696.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12696, BstLean.Part268.grid12696, BstLean.Part263.worldGrid]

theorem supplies12696 (j : Fin 43) : Supply 12696 (parameters j)
    (cellLower scalarRow12696.grid (sourceIndex j))
    (cellUpper scalarRow12696.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12696.grid grid_top_bounds12696 j

theorem radii12696 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12696.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12696 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12696 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12696.grid grid_top_bounds12696 j hθ

noncomputable def covarianceInputs12696 :
    BstLean.Part263.CovarianceInputs 12696 scalarRow12696.grid parameters (caps repair12696) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12696 grid_top_bounds12696 repair12696

noncomputable def covarianceEvent12696 : Set (AgFam 12696) :=
  BstLean.Part263.covarianceEvent 12696 scalarRow12696.grid parameters

theorem covarianceEvent12696_measurable : MeasurableSet covarianceEvent12696 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12696_payment :
    (retDist (paperDesignP 12696).toCentres).real
      (agentEv (paperDesignP 12696) covarianceEvent12696)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12696

theorem localCov12696 : BstLean.Part259.LocalCovarianceOn covarianceEvent12696
    (BstLean.Part263.cell scalarRow12696.grid) (caps repair12696) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12696

theorem covarianceGood12696_payment :
    (retDist (paperDesignP 12696).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12696)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12696_payment



end BstLean.Part269.N12696

namespace BstLean.Part269.N12696
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12696}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12696.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12696) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12696).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12696 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12696) (by norm_num) BstLean.Part268.WorldRow12696.worldPackage rfl
    BstLean.Part268.WorldRow12696.product_lower (BstLean.Part268.WorldRow12696.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12696} (hw : c ∈ Hof BstLean.Part268.WorldRow12696.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12696) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12696) (by norm_num) BstLean.Part268.WorldRow12696.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12696} (hw : c ∈ Hof BstLean.Part268.WorldRow12696.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12696) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12696).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12696) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12696_eq : scalarRow12696.targetFrame = BstLean.Part268.agent12696.frame := by
  norm_num [scalarRow12696,BstLean.Part268.agent12696]

noncomputable def frameData12696 : BstLean.Part264b.FrameData 12696 :=
  BstLean.Part269.frameData_from_numerics (n := 12696) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12696.worldPackage rfl BstLean.Part268.WorldRow12696.product_lower (BstLean.Part268.WorldRow12696.producthi.2.trans (by norm_num))
    scalarRow12696 repair12696 covarianceInputs12696 (fun i hi => sourceNumerics12696 hi)
    BstLean.Part268.agent12696.frame targetFrame12696_eq


end BstLean.Part269.N12696

namespace BstLean.Part269.N12697
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12697 : scalarRow12697.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12697, BstLean.Part268.grid12697, BstLean.Part263.worldGrid]

theorem supplies12697 (j : Fin 43) : Supply 12697 (parameters j)
    (cellLower scalarRow12697.grid (sourceIndex j))
    (cellUpper scalarRow12697.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12697.grid grid_top_bounds12697 j

theorem radii12697 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12697.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12697 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12697 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12697.grid grid_top_bounds12697 j hθ

noncomputable def covarianceInputs12697 :
    BstLean.Part263.CovarianceInputs 12697 scalarRow12697.grid parameters (caps repair12697) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12697 grid_top_bounds12697 repair12697

noncomputable def covarianceEvent12697 : Set (AgFam 12697) :=
  BstLean.Part263.covarianceEvent 12697 scalarRow12697.grid parameters

theorem covarianceEvent12697_measurable : MeasurableSet covarianceEvent12697 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12697_payment :
    (retDist (paperDesignP 12697).toCentres).real
      (agentEv (paperDesignP 12697) covarianceEvent12697)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12697

theorem localCov12697 : BstLean.Part259.LocalCovarianceOn covarianceEvent12697
    (BstLean.Part263.cell scalarRow12697.grid) (caps repair12697) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12697

theorem covarianceGood12697_payment :
    (retDist (paperDesignP 12697).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12697)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12697_payment



end BstLean.Part269.N12697

namespace BstLean.Part269.N12697
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12697}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12697.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12697) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12697).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12697 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12697) (by norm_num) BstLean.Part268.WorldRow12697.worldPackage rfl
    BstLean.Part268.WorldRow12697.product_lower (BstLean.Part268.WorldRow12697.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12697} (hw : c ∈ Hof BstLean.Part268.WorldRow12697.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12697) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12697) (by norm_num) BstLean.Part268.WorldRow12697.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12697} (hw : c ∈ Hof BstLean.Part268.WorldRow12697.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12697) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12697).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12697) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12697_eq : scalarRow12697.targetFrame = BstLean.Part268.agent12697.frame := by
  norm_num [scalarRow12697,BstLean.Part268.agent12697]

noncomputable def frameData12697 : BstLean.Part264b.FrameData 12697 :=
  BstLean.Part269.frameData_from_numerics (n := 12697) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12697.worldPackage rfl BstLean.Part268.WorldRow12697.product_lower (BstLean.Part268.WorldRow12697.producthi.2.trans (by norm_num))
    scalarRow12697 repair12697 covarianceInputs12697 (fun i hi => sourceNumerics12697 hi)
    BstLean.Part268.agent12697.frame targetFrame12697_eq


end BstLean.Part269.N12697

namespace BstLean.Part269.N12698
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12698 : scalarRow12698.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12698, BstLean.Part268.grid12698, BstLean.Part263.worldGrid]

theorem supplies12698 (j : Fin 43) : Supply 12698 (parameters j)
    (cellLower scalarRow12698.grid (sourceIndex j))
    (cellUpper scalarRow12698.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12698.grid grid_top_bounds12698 j

theorem radii12698 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12698.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12698 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12698 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12698.grid grid_top_bounds12698 j hθ

noncomputable def covarianceInputs12698 :
    BstLean.Part263.CovarianceInputs 12698 scalarRow12698.grid parameters (caps repair12698) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12698 grid_top_bounds12698 repair12698

noncomputable def covarianceEvent12698 : Set (AgFam 12698) :=
  BstLean.Part263.covarianceEvent 12698 scalarRow12698.grid parameters

theorem covarianceEvent12698_measurable : MeasurableSet covarianceEvent12698 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12698_payment :
    (retDist (paperDesignP 12698).toCentres).real
      (agentEv (paperDesignP 12698) covarianceEvent12698)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12698

theorem localCov12698 : BstLean.Part259.LocalCovarianceOn covarianceEvent12698
    (BstLean.Part263.cell scalarRow12698.grid) (caps repair12698) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12698

theorem covarianceGood12698_payment :
    (retDist (paperDesignP 12698).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12698)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12698_payment



end BstLean.Part269.N12698

namespace BstLean.Part269.N12698
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12698}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12698.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12698) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12698).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12698 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12698) (by norm_num) BstLean.Part268.WorldRow12698.worldPackage rfl
    BstLean.Part268.WorldRow12698.product_lower (BstLean.Part268.WorldRow12698.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12698} (hw : c ∈ Hof BstLean.Part268.WorldRow12698.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12698) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12698) (by norm_num) BstLean.Part268.WorldRow12698.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12698} (hw : c ∈ Hof BstLean.Part268.WorldRow12698.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12698) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12698).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12698) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12698_eq : scalarRow12698.targetFrame = BstLean.Part268.agent12698.frame := by
  norm_num [scalarRow12698,BstLean.Part268.agent12698]

noncomputable def frameData12698 : BstLean.Part264b.FrameData 12698 :=
  BstLean.Part269.frameData_from_numerics (n := 12698) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12698.worldPackage rfl BstLean.Part268.WorldRow12698.product_lower (BstLean.Part268.WorldRow12698.producthi.2.trans (by norm_num))
    scalarRow12698 repair12698 covarianceInputs12698 (fun i hi => sourceNumerics12698 hi)
    BstLean.Part268.agent12698.frame targetFrame12698_eq


end BstLean.Part269.N12698

namespace BstLean.Part269.N12699
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12699 : scalarRow12699.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12699, BstLean.Part268.grid12699, BstLean.Part263.worldGrid]

theorem supplies12699 (j : Fin 43) : Supply 12699 (parameters j)
    (cellLower scalarRow12699.grid (sourceIndex j))
    (cellUpper scalarRow12699.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12699.grid grid_top_bounds12699 j

theorem radii12699 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12699.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12699 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12699 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12699.grid grid_top_bounds12699 j hθ

noncomputable def covarianceInputs12699 :
    BstLean.Part263.CovarianceInputs 12699 scalarRow12699.grid parameters (caps repair12699) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12699 grid_top_bounds12699 repair12699

noncomputable def covarianceEvent12699 : Set (AgFam 12699) :=
  BstLean.Part263.covarianceEvent 12699 scalarRow12699.grid parameters

theorem covarianceEvent12699_measurable : MeasurableSet covarianceEvent12699 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12699_payment :
    (retDist (paperDesignP 12699).toCentres).real
      (agentEv (paperDesignP 12699) covarianceEvent12699)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12699

theorem localCov12699 : BstLean.Part259.LocalCovarianceOn covarianceEvent12699
    (BstLean.Part263.cell scalarRow12699.grid) (caps repair12699) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12699

theorem covarianceGood12699_payment :
    (retDist (paperDesignP 12699).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12699)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12699_payment



end BstLean.Part269.N12699

namespace BstLean.Part269.N12699
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12699}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12699.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12699) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12699).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12699 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12699) (by norm_num) BstLean.Part268.WorldRow12699.worldPackage rfl
    BstLean.Part268.WorldRow12699.product_lower (BstLean.Part268.WorldRow12699.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12699} (hw : c ∈ Hof BstLean.Part268.WorldRow12699.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12699) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12699) (by norm_num) BstLean.Part268.WorldRow12699.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12699} (hw : c ∈ Hof BstLean.Part268.WorldRow12699.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12699) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12699).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12699) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12699_eq : scalarRow12699.targetFrame = BstLean.Part268.agent12699.frame := by
  norm_num [scalarRow12699,BstLean.Part268.agent12699]

noncomputable def frameData12699 : BstLean.Part264b.FrameData 12699 :=
  BstLean.Part269.frameData_from_numerics (n := 12699) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12699.worldPackage rfl BstLean.Part268.WorldRow12699.product_lower (BstLean.Part268.WorldRow12699.producthi.2.trans (by norm_num))
    scalarRow12699 repair12699 covarianceInputs12699 (fun i hi => sourceNumerics12699 hi)
    BstLean.Part268.agent12699.frame targetFrame12699_eq


end BstLean.Part269.N12699
