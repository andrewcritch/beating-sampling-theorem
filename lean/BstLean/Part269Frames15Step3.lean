import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World15Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs15
import BstLean.Part269Rows15
import BstLean.Part269Sources15
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12740
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12740 : scalarRow12740.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12740, BstLean.Part268.grid12740, BstLean.Part263.worldGrid]

theorem supplies12740 (j : Fin 43) : Supply 12740 (parameters j)
    (cellLower scalarRow12740.grid (sourceIndex j))
    (cellUpper scalarRow12740.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12740.grid grid_top_bounds12740 j

theorem radii12740 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12740.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12740 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12740 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12740.grid grid_top_bounds12740 j hθ

noncomputable def covarianceInputs12740 :
    BstLean.Part263.CovarianceInputs 12740 scalarRow12740.grid parameters (caps repair12740) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12740 grid_top_bounds12740 repair12740

noncomputable def covarianceEvent12740 : Set (AgFam 12740) :=
  BstLean.Part263.covarianceEvent 12740 scalarRow12740.grid parameters

theorem covarianceEvent12740_measurable : MeasurableSet covarianceEvent12740 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12740_payment :
    (retDist (paperDesignP 12740).toCentres).real
      (agentEv (paperDesignP 12740) covarianceEvent12740)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12740

theorem localCov12740 : BstLean.Part259.LocalCovarianceOn covarianceEvent12740
    (BstLean.Part263.cell scalarRow12740.grid) (caps repair12740) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12740

theorem covarianceGood12740_payment :
    (retDist (paperDesignP 12740).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12740)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12740_payment



end BstLean.Part269.N12740

namespace BstLean.Part269.N12740
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12740}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12740.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12740) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12740).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12740 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12740) (by norm_num) BstLean.Part268.WorldRow12740.worldPackage rfl
    BstLean.Part268.WorldRow12740.product_lower (BstLean.Part268.WorldRow12740.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12740} (hw : c ∈ Hof BstLean.Part268.WorldRow12740.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12740) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12740) (by norm_num) BstLean.Part268.WorldRow12740.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12740} (hw : c ∈ Hof BstLean.Part268.WorldRow12740.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12740) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12740).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12740) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12740_eq : scalarRow12740.targetFrame = BstLean.Part268.agent12740.frame := by
  norm_num [scalarRow12740,BstLean.Part268.agent12740]

noncomputable def frameData12740 : BstLean.Part264b.FrameData 12740 :=
  BstLean.Part269.frameData_from_numerics (n := 12740) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12740.worldPackage rfl BstLean.Part268.WorldRow12740.product_lower (BstLean.Part268.WorldRow12740.producthi.2.trans (by norm_num))
    scalarRow12740 repair12740 covarianceInputs12740 (fun i hi => sourceNumerics12740 hi)
    BstLean.Part268.agent12740.frame targetFrame12740_eq


end BstLean.Part269.N12740

namespace BstLean.Part269.N12741
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12741 : scalarRow12741.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12741, BstLean.Part268.grid12741, BstLean.Part263.worldGrid]

theorem supplies12741 (j : Fin 43) : Supply 12741 (parameters j)
    (cellLower scalarRow12741.grid (sourceIndex j))
    (cellUpper scalarRow12741.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12741.grid grid_top_bounds12741 j

theorem radii12741 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12741.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12741 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12741 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12741.grid grid_top_bounds12741 j hθ

noncomputable def covarianceInputs12741 :
    BstLean.Part263.CovarianceInputs 12741 scalarRow12741.grid parameters (caps repair12741) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12741 grid_top_bounds12741 repair12741

noncomputable def covarianceEvent12741 : Set (AgFam 12741) :=
  BstLean.Part263.covarianceEvent 12741 scalarRow12741.grid parameters

theorem covarianceEvent12741_measurable : MeasurableSet covarianceEvent12741 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12741_payment :
    (retDist (paperDesignP 12741).toCentres).real
      (agentEv (paperDesignP 12741) covarianceEvent12741)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12741

theorem localCov12741 : BstLean.Part259.LocalCovarianceOn covarianceEvent12741
    (BstLean.Part263.cell scalarRow12741.grid) (caps repair12741) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12741

theorem covarianceGood12741_payment :
    (retDist (paperDesignP 12741).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12741)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12741_payment



end BstLean.Part269.N12741

namespace BstLean.Part269.N12741
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12741}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12741.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12741) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12741).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12741 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12741) (by norm_num) BstLean.Part268.WorldRow12741.worldPackage rfl
    BstLean.Part268.WorldRow12741.product_lower (BstLean.Part268.WorldRow12741.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12741} (hw : c ∈ Hof BstLean.Part268.WorldRow12741.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12741) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12741) (by norm_num) BstLean.Part268.WorldRow12741.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12741} (hw : c ∈ Hof BstLean.Part268.WorldRow12741.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12741) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12741).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12741) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12741_eq : scalarRow12741.targetFrame = BstLean.Part268.agent12741.frame := by
  norm_num [scalarRow12741,BstLean.Part268.agent12741]

noncomputable def frameData12741 : BstLean.Part264b.FrameData 12741 :=
  BstLean.Part269.frameData_from_numerics (n := 12741) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12741.worldPackage rfl BstLean.Part268.WorldRow12741.product_lower (BstLean.Part268.WorldRow12741.producthi.2.trans (by norm_num))
    scalarRow12741 repair12741 covarianceInputs12741 (fun i hi => sourceNumerics12741 hi)
    BstLean.Part268.agent12741.frame targetFrame12741_eq


end BstLean.Part269.N12741

namespace BstLean.Part269.N12742
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12742 : scalarRow12742.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12742, BstLean.Part268.grid12742, BstLean.Part263.worldGrid]

theorem supplies12742 (j : Fin 43) : Supply 12742 (parameters j)
    (cellLower scalarRow12742.grid (sourceIndex j))
    (cellUpper scalarRow12742.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12742.grid grid_top_bounds12742 j

theorem radii12742 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12742.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12742 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12742 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12742.grid grid_top_bounds12742 j hθ

noncomputable def covarianceInputs12742 :
    BstLean.Part263.CovarianceInputs 12742 scalarRow12742.grid parameters (caps repair12742) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12742 grid_top_bounds12742 repair12742

noncomputable def covarianceEvent12742 : Set (AgFam 12742) :=
  BstLean.Part263.covarianceEvent 12742 scalarRow12742.grid parameters

theorem covarianceEvent12742_measurable : MeasurableSet covarianceEvent12742 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12742_payment :
    (retDist (paperDesignP 12742).toCentres).real
      (agentEv (paperDesignP 12742) covarianceEvent12742)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12742

theorem localCov12742 : BstLean.Part259.LocalCovarianceOn covarianceEvent12742
    (BstLean.Part263.cell scalarRow12742.grid) (caps repair12742) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12742

theorem covarianceGood12742_payment :
    (retDist (paperDesignP 12742).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12742)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12742_payment



end BstLean.Part269.N12742

namespace BstLean.Part269.N12742
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12742}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12742.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12742) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12742).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12742 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12742) (by norm_num) BstLean.Part268.WorldRow12742.worldPackage rfl
    BstLean.Part268.WorldRow12742.product_lower (BstLean.Part268.WorldRow12742.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12742} (hw : c ∈ Hof BstLean.Part268.WorldRow12742.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12742) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12742) (by norm_num) BstLean.Part268.WorldRow12742.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12742} (hw : c ∈ Hof BstLean.Part268.WorldRow12742.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12742) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12742).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12742) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12742_eq : scalarRow12742.targetFrame = BstLean.Part268.agent12742.frame := by
  norm_num [scalarRow12742,BstLean.Part268.agent12742]

noncomputable def frameData12742 : BstLean.Part264b.FrameData 12742 :=
  BstLean.Part269.frameData_from_numerics (n := 12742) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12742.worldPackage rfl BstLean.Part268.WorldRow12742.product_lower (BstLean.Part268.WorldRow12742.producthi.2.trans (by norm_num))
    scalarRow12742 repair12742 covarianceInputs12742 (fun i hi => sourceNumerics12742 hi)
    BstLean.Part268.agent12742.frame targetFrame12742_eq


end BstLean.Part269.N12742

namespace BstLean.Part269.N12743
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12743 : scalarRow12743.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12743, BstLean.Part268.grid12743, BstLean.Part263.worldGrid]

theorem supplies12743 (j : Fin 43) : Supply 12743 (parameters j)
    (cellLower scalarRow12743.grid (sourceIndex j))
    (cellUpper scalarRow12743.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12743.grid grid_top_bounds12743 j

theorem radii12743 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12743.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12743 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12743 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12743.grid grid_top_bounds12743 j hθ

noncomputable def covarianceInputs12743 :
    BstLean.Part263.CovarianceInputs 12743 scalarRow12743.grid parameters (caps repair12743) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12743 grid_top_bounds12743 repair12743

noncomputable def covarianceEvent12743 : Set (AgFam 12743) :=
  BstLean.Part263.covarianceEvent 12743 scalarRow12743.grid parameters

theorem covarianceEvent12743_measurable : MeasurableSet covarianceEvent12743 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12743_payment :
    (retDist (paperDesignP 12743).toCentres).real
      (agentEv (paperDesignP 12743) covarianceEvent12743)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12743

theorem localCov12743 : BstLean.Part259.LocalCovarianceOn covarianceEvent12743
    (BstLean.Part263.cell scalarRow12743.grid) (caps repair12743) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12743

theorem covarianceGood12743_payment :
    (retDist (paperDesignP 12743).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12743)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12743_payment



end BstLean.Part269.N12743

namespace BstLean.Part269.N12743
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12743}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12743.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12743) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12743).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12743 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12743) (by norm_num) BstLean.Part268.WorldRow12743.worldPackage rfl
    BstLean.Part268.WorldRow12743.product_lower (BstLean.Part268.WorldRow12743.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12743} (hw : c ∈ Hof BstLean.Part268.WorldRow12743.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12743) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12743) (by norm_num) BstLean.Part268.WorldRow12743.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12743} (hw : c ∈ Hof BstLean.Part268.WorldRow12743.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12743) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12743).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12743) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12743_eq : scalarRow12743.targetFrame = BstLean.Part268.agent12743.frame := by
  norm_num [scalarRow12743,BstLean.Part268.agent12743]

noncomputable def frameData12743 : BstLean.Part264b.FrameData 12743 :=
  BstLean.Part269.frameData_from_numerics (n := 12743) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12743.worldPackage rfl BstLean.Part268.WorldRow12743.product_lower (BstLean.Part268.WorldRow12743.producthi.2.trans (by norm_num))
    scalarRow12743 repair12743 covarianceInputs12743 (fun i hi => sourceNumerics12743 hi)
    BstLean.Part268.agent12743.frame targetFrame12743_eq


end BstLean.Part269.N12743

namespace BstLean.Part269.N12744
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12744 : scalarRow12744.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12744, BstLean.Part268.grid12744, BstLean.Part263.worldGrid]

theorem supplies12744 (j : Fin 43) : Supply 12744 (parameters j)
    (cellLower scalarRow12744.grid (sourceIndex j))
    (cellUpper scalarRow12744.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12744.grid grid_top_bounds12744 j

theorem radii12744 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12744.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12744 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12744 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12744.grid grid_top_bounds12744 j hθ

noncomputable def covarianceInputs12744 :
    BstLean.Part263.CovarianceInputs 12744 scalarRow12744.grid parameters (caps repair12744) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12744 grid_top_bounds12744 repair12744

noncomputable def covarianceEvent12744 : Set (AgFam 12744) :=
  BstLean.Part263.covarianceEvent 12744 scalarRow12744.grid parameters

theorem covarianceEvent12744_measurable : MeasurableSet covarianceEvent12744 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12744_payment :
    (retDist (paperDesignP 12744).toCentres).real
      (agentEv (paperDesignP 12744) covarianceEvent12744)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12744

theorem localCov12744 : BstLean.Part259.LocalCovarianceOn covarianceEvent12744
    (BstLean.Part263.cell scalarRow12744.grid) (caps repair12744) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12744

theorem covarianceGood12744_payment :
    (retDist (paperDesignP 12744).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12744)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12744_payment



end BstLean.Part269.N12744

namespace BstLean.Part269.N12744
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12744}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12744.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12744) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12744).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12744 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12744) (by norm_num) BstLean.Part268.WorldRow12744.worldPackage rfl
    BstLean.Part268.WorldRow12744.product_lower (BstLean.Part268.WorldRow12744.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12744} (hw : c ∈ Hof BstLean.Part268.WorldRow12744.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12744) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12744) (by norm_num) BstLean.Part268.WorldRow12744.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12744} (hw : c ∈ Hof BstLean.Part268.WorldRow12744.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12744) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12744).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12744) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12744_eq : scalarRow12744.targetFrame = BstLean.Part268.agent12744.frame := by
  norm_num [scalarRow12744,BstLean.Part268.agent12744]

noncomputable def frameData12744 : BstLean.Part264b.FrameData 12744 :=
  BstLean.Part269.frameData_from_numerics (n := 12744) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12744.worldPackage rfl BstLean.Part268.WorldRow12744.product_lower (BstLean.Part268.WorldRow12744.producthi.2.trans (by norm_num))
    scalarRow12744 repair12744 covarianceInputs12744 (fun i hi => sourceNumerics12744 hi)
    BstLean.Part268.agent12744.frame targetFrame12744_eq


end BstLean.Part269.N12744
