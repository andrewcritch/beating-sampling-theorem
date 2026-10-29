import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World8Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs8
import BstLean.Part269Rows8
import BstLean.Part269Sources8
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12570
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12570 : scalarRow12570.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12570, BstLean.Part268.grid12570, BstLean.Part263.worldGrid]

theorem supplies12570 (j : Fin 43) : Supply 12570 (parameters j)
    (cellLower scalarRow12570.grid (sourceIndex j))
    (cellUpper scalarRow12570.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12570.grid grid_top_bounds12570 j

theorem radii12570 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12570.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12570 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12570 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12570.grid grid_top_bounds12570 j hθ

noncomputable def covarianceInputs12570 :
    BstLean.Part263.CovarianceInputs 12570 scalarRow12570.grid parameters (caps repair12570) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12570 grid_top_bounds12570 repair12570

noncomputable def covarianceEvent12570 : Set (AgFam 12570) :=
  BstLean.Part263.covarianceEvent 12570 scalarRow12570.grid parameters

theorem covarianceEvent12570_measurable : MeasurableSet covarianceEvent12570 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12570_payment :
    (retDist (paperDesignP 12570).toCentres).real
      (agentEv (paperDesignP 12570) covarianceEvent12570)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12570

theorem localCov12570 : BstLean.Part259.LocalCovarianceOn covarianceEvent12570
    (BstLean.Part263.cell scalarRow12570.grid) (caps repair12570) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12570

theorem covarianceGood12570_payment :
    (retDist (paperDesignP 12570).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12570)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12570_payment



end BstLean.Part269.N12570

namespace BstLean.Part269.N12570
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12570}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12570.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12570) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12570).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12570 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12570) (by norm_num) BstLean.Part268.WorldRow12570.worldPackage rfl
    BstLean.Part268.WorldRow12570.product_lower (BstLean.Part268.WorldRow12570.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12570} (hw : c ∈ Hof BstLean.Part268.WorldRow12570.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12570) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12570) (by norm_num) BstLean.Part268.WorldRow12570.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12570} (hw : c ∈ Hof BstLean.Part268.WorldRow12570.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12570) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12570).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12570) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12570_eq : scalarRow12570.targetFrame = BstLean.Part268.agent12570.frame := by
  norm_num [scalarRow12570,BstLean.Part268.agent12570]

noncomputable def frameData12570 : BstLean.Part264b.FrameData 12570 :=
  BstLean.Part269.frameData_from_numerics (n := 12570) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12570.worldPackage rfl BstLean.Part268.WorldRow12570.product_lower (BstLean.Part268.WorldRow12570.producthi.2.trans (by norm_num))
    scalarRow12570 repair12570 covarianceInputs12570 (fun i hi => sourceNumerics12570 hi)
    BstLean.Part268.agent12570.frame targetFrame12570_eq


end BstLean.Part269.N12570

namespace BstLean.Part269.N12571
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12571 : scalarRow12571.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12571, BstLean.Part268.grid12571, BstLean.Part263.worldGrid]

theorem supplies12571 (j : Fin 43) : Supply 12571 (parameters j)
    (cellLower scalarRow12571.grid (sourceIndex j))
    (cellUpper scalarRow12571.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12571.grid grid_top_bounds12571 j

theorem radii12571 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12571.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12571 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12571 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12571.grid grid_top_bounds12571 j hθ

noncomputable def covarianceInputs12571 :
    BstLean.Part263.CovarianceInputs 12571 scalarRow12571.grid parameters (caps repair12571) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12571 grid_top_bounds12571 repair12571

noncomputable def covarianceEvent12571 : Set (AgFam 12571) :=
  BstLean.Part263.covarianceEvent 12571 scalarRow12571.grid parameters

theorem covarianceEvent12571_measurable : MeasurableSet covarianceEvent12571 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12571_payment :
    (retDist (paperDesignP 12571).toCentres).real
      (agentEv (paperDesignP 12571) covarianceEvent12571)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12571

theorem localCov12571 : BstLean.Part259.LocalCovarianceOn covarianceEvent12571
    (BstLean.Part263.cell scalarRow12571.grid) (caps repair12571) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12571

theorem covarianceGood12571_payment :
    (retDist (paperDesignP 12571).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12571)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12571_payment



end BstLean.Part269.N12571

namespace BstLean.Part269.N12571
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12571}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12571.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12571) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12571).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12571 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12571) (by norm_num) BstLean.Part268.WorldRow12571.worldPackage rfl
    BstLean.Part268.WorldRow12571.product_lower (BstLean.Part268.WorldRow12571.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12571} (hw : c ∈ Hof BstLean.Part268.WorldRow12571.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12571) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12571) (by norm_num) BstLean.Part268.WorldRow12571.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12571} (hw : c ∈ Hof BstLean.Part268.WorldRow12571.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12571) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12571).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12571) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12571_eq : scalarRow12571.targetFrame = BstLean.Part268.agent12571.frame := by
  norm_num [scalarRow12571,BstLean.Part268.agent12571]

noncomputable def frameData12571 : BstLean.Part264b.FrameData 12571 :=
  BstLean.Part269.frameData_from_numerics (n := 12571) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12571.worldPackage rfl BstLean.Part268.WorldRow12571.product_lower (BstLean.Part268.WorldRow12571.producthi.2.trans (by norm_num))
    scalarRow12571 repair12571 covarianceInputs12571 (fun i hi => sourceNumerics12571 hi)
    BstLean.Part268.agent12571.frame targetFrame12571_eq


end BstLean.Part269.N12571

namespace BstLean.Part269.N12572
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12572 : scalarRow12572.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12572, BstLean.Part268.grid12572, BstLean.Part263.worldGrid]

theorem supplies12572 (j : Fin 43) : Supply 12572 (parameters j)
    (cellLower scalarRow12572.grid (sourceIndex j))
    (cellUpper scalarRow12572.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12572.grid grid_top_bounds12572 j

theorem radii12572 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12572.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12572 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12572 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12572.grid grid_top_bounds12572 j hθ

noncomputable def covarianceInputs12572 :
    BstLean.Part263.CovarianceInputs 12572 scalarRow12572.grid parameters (caps repair12572) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12572 grid_top_bounds12572 repair12572

noncomputable def covarianceEvent12572 : Set (AgFam 12572) :=
  BstLean.Part263.covarianceEvent 12572 scalarRow12572.grid parameters

theorem covarianceEvent12572_measurable : MeasurableSet covarianceEvent12572 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12572_payment :
    (retDist (paperDesignP 12572).toCentres).real
      (agentEv (paperDesignP 12572) covarianceEvent12572)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12572

theorem localCov12572 : BstLean.Part259.LocalCovarianceOn covarianceEvent12572
    (BstLean.Part263.cell scalarRow12572.grid) (caps repair12572) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12572

theorem covarianceGood12572_payment :
    (retDist (paperDesignP 12572).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12572)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12572_payment



end BstLean.Part269.N12572

namespace BstLean.Part269.N12572
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12572}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12572.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12572) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12572).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12572 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12572) (by norm_num) BstLean.Part268.WorldRow12572.worldPackage rfl
    BstLean.Part268.WorldRow12572.product_lower (BstLean.Part268.WorldRow12572.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12572} (hw : c ∈ Hof BstLean.Part268.WorldRow12572.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12572) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12572) (by norm_num) BstLean.Part268.WorldRow12572.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12572} (hw : c ∈ Hof BstLean.Part268.WorldRow12572.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12572) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12572).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12572) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12572_eq : scalarRow12572.targetFrame = BstLean.Part268.agent12572.frame := by
  norm_num [scalarRow12572,BstLean.Part268.agent12572]

noncomputable def frameData12572 : BstLean.Part264b.FrameData 12572 :=
  BstLean.Part269.frameData_from_numerics (n := 12572) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12572.worldPackage rfl BstLean.Part268.WorldRow12572.product_lower (BstLean.Part268.WorldRow12572.producthi.2.trans (by norm_num))
    scalarRow12572 repair12572 covarianceInputs12572 (fun i hi => sourceNumerics12572 hi)
    BstLean.Part268.agent12572.frame targetFrame12572_eq


end BstLean.Part269.N12572

namespace BstLean.Part269.N12573
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12573 : scalarRow12573.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12573, BstLean.Part268.grid12573, BstLean.Part263.worldGrid]

theorem supplies12573 (j : Fin 43) : Supply 12573 (parameters j)
    (cellLower scalarRow12573.grid (sourceIndex j))
    (cellUpper scalarRow12573.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12573.grid grid_top_bounds12573 j

theorem radii12573 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12573.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12573 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12573 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12573.grid grid_top_bounds12573 j hθ

noncomputable def covarianceInputs12573 :
    BstLean.Part263.CovarianceInputs 12573 scalarRow12573.grid parameters (caps repair12573) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12573 grid_top_bounds12573 repair12573

noncomputable def covarianceEvent12573 : Set (AgFam 12573) :=
  BstLean.Part263.covarianceEvent 12573 scalarRow12573.grid parameters

theorem covarianceEvent12573_measurable : MeasurableSet covarianceEvent12573 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12573_payment :
    (retDist (paperDesignP 12573).toCentres).real
      (agentEv (paperDesignP 12573) covarianceEvent12573)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12573

theorem localCov12573 : BstLean.Part259.LocalCovarianceOn covarianceEvent12573
    (BstLean.Part263.cell scalarRow12573.grid) (caps repair12573) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12573

theorem covarianceGood12573_payment :
    (retDist (paperDesignP 12573).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12573)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12573_payment



end BstLean.Part269.N12573

namespace BstLean.Part269.N12573
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12573}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12573.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12573) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12573).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12573 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12573) (by norm_num) BstLean.Part268.WorldRow12573.worldPackage rfl
    BstLean.Part268.WorldRow12573.product_lower (BstLean.Part268.WorldRow12573.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12573} (hw : c ∈ Hof BstLean.Part268.WorldRow12573.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12573) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12573) (by norm_num) BstLean.Part268.WorldRow12573.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12573} (hw : c ∈ Hof BstLean.Part268.WorldRow12573.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12573) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12573).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12573) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12573_eq : scalarRow12573.targetFrame = BstLean.Part268.agent12573.frame := by
  norm_num [scalarRow12573,BstLean.Part268.agent12573]

noncomputable def frameData12573 : BstLean.Part264b.FrameData 12573 :=
  BstLean.Part269.frameData_from_numerics (n := 12573) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12573.worldPackage rfl BstLean.Part268.WorldRow12573.product_lower (BstLean.Part268.WorldRow12573.producthi.2.trans (by norm_num))
    scalarRow12573 repair12573 covarianceInputs12573 (fun i hi => sourceNumerics12573 hi)
    BstLean.Part268.agent12573.frame targetFrame12573_eq


end BstLean.Part269.N12573

namespace BstLean.Part269.N12574
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12574 : scalarRow12574.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12574, BstLean.Part268.grid12574, BstLean.Part263.worldGrid]

theorem supplies12574 (j : Fin 43) : Supply 12574 (parameters j)
    (cellLower scalarRow12574.grid (sourceIndex j))
    (cellUpper scalarRow12574.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12574.grid grid_top_bounds12574 j

theorem radii12574 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12574.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12574 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12574 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12574.grid grid_top_bounds12574 j hθ

noncomputable def covarianceInputs12574 :
    BstLean.Part263.CovarianceInputs 12574 scalarRow12574.grid parameters (caps repair12574) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12574 grid_top_bounds12574 repair12574

noncomputable def covarianceEvent12574 : Set (AgFam 12574) :=
  BstLean.Part263.covarianceEvent 12574 scalarRow12574.grid parameters

theorem covarianceEvent12574_measurable : MeasurableSet covarianceEvent12574 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12574_payment :
    (retDist (paperDesignP 12574).toCentres).real
      (agentEv (paperDesignP 12574) covarianceEvent12574)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12574

theorem localCov12574 : BstLean.Part259.LocalCovarianceOn covarianceEvent12574
    (BstLean.Part263.cell scalarRow12574.grid) (caps repair12574) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12574

theorem covarianceGood12574_payment :
    (retDist (paperDesignP 12574).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12574)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12574_payment



end BstLean.Part269.N12574

namespace BstLean.Part269.N12574
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12574}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12574.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12574) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12574).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12574 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12574) (by norm_num) BstLean.Part268.WorldRow12574.worldPackage rfl
    BstLean.Part268.WorldRow12574.product_lower (BstLean.Part268.WorldRow12574.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12574} (hw : c ∈ Hof BstLean.Part268.WorldRow12574.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12574) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12574) (by norm_num) BstLean.Part268.WorldRow12574.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12574} (hw : c ∈ Hof BstLean.Part268.WorldRow12574.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12574) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12574).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12574) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12574_eq : scalarRow12574.targetFrame = BstLean.Part268.agent12574.frame := by
  norm_num [scalarRow12574,BstLean.Part268.agent12574]

noncomputable def frameData12574 : BstLean.Part264b.FrameData 12574 :=
  BstLean.Part269.frameData_from_numerics (n := 12574) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12574.worldPackage rfl BstLean.Part268.WorldRow12574.product_lower (BstLean.Part268.WorldRow12574.producthi.2.trans (by norm_num))
    scalarRow12574 repair12574 covarianceInputs12574 (fun i hi => sourceNumerics12574 hi)
    BstLean.Part268.agent12574.frame targetFrame12574_eq


end BstLean.Part269.N12574
