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

namespace BstLean.Part269.N12645
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12645 : scalarRow12645.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12645, BstLean.Part268.grid12645, BstLean.Part263.worldGrid]

theorem supplies12645 (j : Fin 43) : Supply 12645 (parameters j)
    (cellLower scalarRow12645.grid (sourceIndex j))
    (cellUpper scalarRow12645.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12645.grid grid_top_bounds12645 j

theorem radii12645 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12645.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12645 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12645 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12645.grid grid_top_bounds12645 j hθ

noncomputable def covarianceInputs12645 :
    BstLean.Part263.CovarianceInputs 12645 scalarRow12645.grid parameters (caps repair12645) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12645 grid_top_bounds12645 repair12645

noncomputable def covarianceEvent12645 : Set (AgFam 12645) :=
  BstLean.Part263.covarianceEvent 12645 scalarRow12645.grid parameters

theorem covarianceEvent12645_measurable : MeasurableSet covarianceEvent12645 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12645_payment :
    (retDist (paperDesignP 12645).toCentres).real
      (agentEv (paperDesignP 12645) covarianceEvent12645)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12645

theorem localCov12645 : BstLean.Part259.LocalCovarianceOn covarianceEvent12645
    (BstLean.Part263.cell scalarRow12645.grid) (caps repair12645) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12645

theorem covarianceGood12645_payment :
    (retDist (paperDesignP 12645).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12645)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12645_payment



end BstLean.Part269.N12645

namespace BstLean.Part269.N12645
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12645}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12645.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12645) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12645).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12645 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12645) (by norm_num) BstLean.Part268.WorldRow12645.worldPackage rfl
    BstLean.Part268.WorldRow12645.product_lower (BstLean.Part268.WorldRow12645.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12645} (hw : c ∈ Hof BstLean.Part268.WorldRow12645.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12645) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12645) (by norm_num) BstLean.Part268.WorldRow12645.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12645} (hw : c ∈ Hof BstLean.Part268.WorldRow12645.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12645) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12645).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12645) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12645_eq : scalarRow12645.targetFrame = BstLean.Part268.agent12645.frame := by
  norm_num [scalarRow12645,BstLean.Part268.agent12645]

noncomputable def frameData12645 : BstLean.Part264b.FrameData 12645 :=
  BstLean.Part269.frameData_from_numerics (n := 12645) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12645.worldPackage rfl BstLean.Part268.WorldRow12645.product_lower (BstLean.Part268.WorldRow12645.producthi.2.trans (by norm_num))
    scalarRow12645 repair12645 covarianceInputs12645 (fun i hi => sourceNumerics12645 hi)
    BstLean.Part268.agent12645.frame targetFrame12645_eq


end BstLean.Part269.N12645

namespace BstLean.Part269.N12646
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12646 : scalarRow12646.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12646, BstLean.Part268.grid12646, BstLean.Part263.worldGrid]

theorem supplies12646 (j : Fin 43) : Supply 12646 (parameters j)
    (cellLower scalarRow12646.grid (sourceIndex j))
    (cellUpper scalarRow12646.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12646.grid grid_top_bounds12646 j

theorem radii12646 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12646.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12646 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12646 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12646.grid grid_top_bounds12646 j hθ

noncomputable def covarianceInputs12646 :
    BstLean.Part263.CovarianceInputs 12646 scalarRow12646.grid parameters (caps repair12646) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12646 grid_top_bounds12646 repair12646

noncomputable def covarianceEvent12646 : Set (AgFam 12646) :=
  BstLean.Part263.covarianceEvent 12646 scalarRow12646.grid parameters

theorem covarianceEvent12646_measurable : MeasurableSet covarianceEvent12646 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12646_payment :
    (retDist (paperDesignP 12646).toCentres).real
      (agentEv (paperDesignP 12646) covarianceEvent12646)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12646

theorem localCov12646 : BstLean.Part259.LocalCovarianceOn covarianceEvent12646
    (BstLean.Part263.cell scalarRow12646.grid) (caps repair12646) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12646

theorem covarianceGood12646_payment :
    (retDist (paperDesignP 12646).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12646)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12646_payment



end BstLean.Part269.N12646

namespace BstLean.Part269.N12646
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12646}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12646.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12646) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12646).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12646 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12646) (by norm_num) BstLean.Part268.WorldRow12646.worldPackage rfl
    BstLean.Part268.WorldRow12646.product_lower (BstLean.Part268.WorldRow12646.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12646} (hw : c ∈ Hof BstLean.Part268.WorldRow12646.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12646) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12646) (by norm_num) BstLean.Part268.WorldRow12646.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12646} (hw : c ∈ Hof BstLean.Part268.WorldRow12646.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12646) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12646).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12646) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12646_eq : scalarRow12646.targetFrame = BstLean.Part268.agent12646.frame := by
  norm_num [scalarRow12646,BstLean.Part268.agent12646]

noncomputable def frameData12646 : BstLean.Part264b.FrameData 12646 :=
  BstLean.Part269.frameData_from_numerics (n := 12646) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12646.worldPackage rfl BstLean.Part268.WorldRow12646.product_lower (BstLean.Part268.WorldRow12646.producthi.2.trans (by norm_num))
    scalarRow12646 repair12646 covarianceInputs12646 (fun i hi => sourceNumerics12646 hi)
    BstLean.Part268.agent12646.frame targetFrame12646_eq


end BstLean.Part269.N12646

namespace BstLean.Part269.N12647
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12647 : scalarRow12647.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12647, BstLean.Part268.grid12647, BstLean.Part263.worldGrid]

theorem supplies12647 (j : Fin 43) : Supply 12647 (parameters j)
    (cellLower scalarRow12647.grid (sourceIndex j))
    (cellUpper scalarRow12647.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12647.grid grid_top_bounds12647 j

theorem radii12647 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12647.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12647 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12647 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12647.grid grid_top_bounds12647 j hθ

noncomputable def covarianceInputs12647 :
    BstLean.Part263.CovarianceInputs 12647 scalarRow12647.grid parameters (caps repair12647) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12647 grid_top_bounds12647 repair12647

noncomputable def covarianceEvent12647 : Set (AgFam 12647) :=
  BstLean.Part263.covarianceEvent 12647 scalarRow12647.grid parameters

theorem covarianceEvent12647_measurable : MeasurableSet covarianceEvent12647 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12647_payment :
    (retDist (paperDesignP 12647).toCentres).real
      (agentEv (paperDesignP 12647) covarianceEvent12647)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12647

theorem localCov12647 : BstLean.Part259.LocalCovarianceOn covarianceEvent12647
    (BstLean.Part263.cell scalarRow12647.grid) (caps repair12647) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12647

theorem covarianceGood12647_payment :
    (retDist (paperDesignP 12647).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12647)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12647_payment



end BstLean.Part269.N12647

namespace BstLean.Part269.N12647
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12647}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12647.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12647) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12647).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12647 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12647) (by norm_num) BstLean.Part268.WorldRow12647.worldPackage rfl
    BstLean.Part268.WorldRow12647.product_lower (BstLean.Part268.WorldRow12647.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12647} (hw : c ∈ Hof BstLean.Part268.WorldRow12647.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12647) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12647) (by norm_num) BstLean.Part268.WorldRow12647.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12647} (hw : c ∈ Hof BstLean.Part268.WorldRow12647.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12647) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12647).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12647) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12647_eq : scalarRow12647.targetFrame = BstLean.Part268.agent12647.frame := by
  norm_num [scalarRow12647,BstLean.Part268.agent12647]

noncomputable def frameData12647 : BstLean.Part264b.FrameData 12647 :=
  BstLean.Part269.frameData_from_numerics (n := 12647) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12647.worldPackage rfl BstLean.Part268.WorldRow12647.product_lower (BstLean.Part268.WorldRow12647.producthi.2.trans (by norm_num))
    scalarRow12647 repair12647 covarianceInputs12647 (fun i hi => sourceNumerics12647 hi)
    BstLean.Part268.agent12647.frame targetFrame12647_eq


end BstLean.Part269.N12647

namespace BstLean.Part269.N12648
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12648 : scalarRow12648.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12648, BstLean.Part268.grid12648, BstLean.Part263.worldGrid]

theorem supplies12648 (j : Fin 43) : Supply 12648 (parameters j)
    (cellLower scalarRow12648.grid (sourceIndex j))
    (cellUpper scalarRow12648.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12648.grid grid_top_bounds12648 j

theorem radii12648 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12648.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12648 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12648 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12648.grid grid_top_bounds12648 j hθ

noncomputable def covarianceInputs12648 :
    BstLean.Part263.CovarianceInputs 12648 scalarRow12648.grid parameters (caps repair12648) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12648 grid_top_bounds12648 repair12648

noncomputable def covarianceEvent12648 : Set (AgFam 12648) :=
  BstLean.Part263.covarianceEvent 12648 scalarRow12648.grid parameters

theorem covarianceEvent12648_measurable : MeasurableSet covarianceEvent12648 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12648_payment :
    (retDist (paperDesignP 12648).toCentres).real
      (agentEv (paperDesignP 12648) covarianceEvent12648)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12648

theorem localCov12648 : BstLean.Part259.LocalCovarianceOn covarianceEvent12648
    (BstLean.Part263.cell scalarRow12648.grid) (caps repair12648) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12648

theorem covarianceGood12648_payment :
    (retDist (paperDesignP 12648).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12648)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12648_payment



end BstLean.Part269.N12648

namespace BstLean.Part269.N12648
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12648}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12648.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12648) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12648).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12648 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12648) (by norm_num) BstLean.Part268.WorldRow12648.worldPackage rfl
    BstLean.Part268.WorldRow12648.product_lower (BstLean.Part268.WorldRow12648.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12648} (hw : c ∈ Hof BstLean.Part268.WorldRow12648.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12648) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12648) (by norm_num) BstLean.Part268.WorldRow12648.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12648} (hw : c ∈ Hof BstLean.Part268.WorldRow12648.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12648) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12648).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12648) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12648_eq : scalarRow12648.targetFrame = BstLean.Part268.agent12648.frame := by
  norm_num [scalarRow12648,BstLean.Part268.agent12648]

noncomputable def frameData12648 : BstLean.Part264b.FrameData 12648 :=
  BstLean.Part269.frameData_from_numerics (n := 12648) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12648.worldPackage rfl BstLean.Part268.WorldRow12648.product_lower (BstLean.Part268.WorldRow12648.producthi.2.trans (by norm_num))
    scalarRow12648 repair12648 covarianceInputs12648 (fun i hi => sourceNumerics12648 hi)
    BstLean.Part268.agent12648.frame targetFrame12648_eq


end BstLean.Part269.N12648

namespace BstLean.Part269.N12649
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12649 : scalarRow12649.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12649, BstLean.Part268.grid12649, BstLean.Part263.worldGrid]

theorem supplies12649 (j : Fin 43) : Supply 12649 (parameters j)
    (cellLower scalarRow12649.grid (sourceIndex j))
    (cellUpper scalarRow12649.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12649.grid grid_top_bounds12649 j

theorem radii12649 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12649.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12649 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12649 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12649.grid grid_top_bounds12649 j hθ

noncomputable def covarianceInputs12649 :
    BstLean.Part263.CovarianceInputs 12649 scalarRow12649.grid parameters (caps repair12649) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12649 grid_top_bounds12649 repair12649

noncomputable def covarianceEvent12649 : Set (AgFam 12649) :=
  BstLean.Part263.covarianceEvent 12649 scalarRow12649.grid parameters

theorem covarianceEvent12649_measurable : MeasurableSet covarianceEvent12649 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12649_payment :
    (retDist (paperDesignP 12649).toCentres).real
      (agentEv (paperDesignP 12649) covarianceEvent12649)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12649

theorem localCov12649 : BstLean.Part259.LocalCovarianceOn covarianceEvent12649
    (BstLean.Part263.cell scalarRow12649.grid) (caps repair12649) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12649

theorem covarianceGood12649_payment :
    (retDist (paperDesignP 12649).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12649)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12649_payment



end BstLean.Part269.N12649

namespace BstLean.Part269.N12649
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12649}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12649.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12649) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12649).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12649 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12649) (by norm_num) BstLean.Part268.WorldRow12649.worldPackage rfl
    BstLean.Part268.WorldRow12649.product_lower (BstLean.Part268.WorldRow12649.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12649} (hw : c ∈ Hof BstLean.Part268.WorldRow12649.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12649) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12649) (by norm_num) BstLean.Part268.WorldRow12649.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12649} (hw : c ∈ Hof BstLean.Part268.WorldRow12649.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12649) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12649).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12649) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12649_eq : scalarRow12649.targetFrame = BstLean.Part268.agent12649.frame := by
  norm_num [scalarRow12649,BstLean.Part268.agent12649]

noncomputable def frameData12649 : BstLean.Part264b.FrameData 12649 :=
  BstLean.Part269.frameData_from_numerics (n := 12649) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12649.worldPackage rfl BstLean.Part268.WorldRow12649.product_lower (BstLean.Part268.WorldRow12649.producthi.2.trans (by norm_num))
    scalarRow12649 repair12649 covarianceInputs12649 (fun i hi => sourceNumerics12649 hi)
    BstLean.Part268.agent12649.frame targetFrame12649_eq


end BstLean.Part269.N12649
