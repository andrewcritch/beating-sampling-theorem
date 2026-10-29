import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World18Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs18
import BstLean.Part269Rows18
import BstLean.Part269Sources18
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12810
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12810 : scalarRow12810.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12810, BstLean.Part268.grid12810, BstLean.Part263.worldGrid]

theorem supplies12810 (j : Fin 43) : Supply 12810 (parameters j)
    (cellLower scalarRow12810.grid (sourceIndex j))
    (cellUpper scalarRow12810.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12810.grid grid_top_bounds12810 j

theorem radii12810 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12810.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12810 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12810 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12810.grid grid_top_bounds12810 j hθ

noncomputable def covarianceInputs12810 :
    BstLean.Part263.CovarianceInputs 12810 scalarRow12810.grid parameters (caps repair12810) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12810 grid_top_bounds12810 repair12810

noncomputable def covarianceEvent12810 : Set (AgFam 12810) :=
  BstLean.Part263.covarianceEvent 12810 scalarRow12810.grid parameters

theorem covarianceEvent12810_measurable : MeasurableSet covarianceEvent12810 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12810_payment :
    (retDist (paperDesignP 12810).toCentres).real
      (agentEv (paperDesignP 12810) covarianceEvent12810)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12810

theorem localCov12810 : BstLean.Part259.LocalCovarianceOn covarianceEvent12810
    (BstLean.Part263.cell scalarRow12810.grid) (caps repair12810) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12810

theorem covarianceGood12810_payment :
    (retDist (paperDesignP 12810).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12810)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12810_payment



end BstLean.Part269.N12810

namespace BstLean.Part269.N12810
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12810}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12810.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12810) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12810).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12810 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12810) (by norm_num) BstLean.Part268.WorldRow12810.worldPackage rfl
    BstLean.Part268.WorldRow12810.product_lower (BstLean.Part268.WorldRow12810.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12810} (hw : c ∈ Hof BstLean.Part268.WorldRow12810.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12810) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12810) (by norm_num) BstLean.Part268.WorldRow12810.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12810} (hw : c ∈ Hof BstLean.Part268.WorldRow12810.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12810) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12810).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12810) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12810_eq : scalarRow12810.targetFrame = BstLean.Part268.agent12810.frame := by
  norm_num [scalarRow12810,BstLean.Part268.agent12810]

noncomputable def frameData12810 : BstLean.Part264b.FrameData 12810 :=
  BstLean.Part269.frameData_from_numerics (n := 12810) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12810.worldPackage rfl BstLean.Part268.WorldRow12810.product_lower (BstLean.Part268.WorldRow12810.producthi.2.trans (by norm_num))
    scalarRow12810 repair12810 covarianceInputs12810 (fun i hi => sourceNumerics12810 hi)
    BstLean.Part268.agent12810.frame targetFrame12810_eq


end BstLean.Part269.N12810

namespace BstLean.Part269.N12811
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12811 : scalarRow12811.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12811, BstLean.Part268.grid12811, BstLean.Part263.worldGrid]

theorem supplies12811 (j : Fin 43) : Supply 12811 (parameters j)
    (cellLower scalarRow12811.grid (sourceIndex j))
    (cellUpper scalarRow12811.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12811.grid grid_top_bounds12811 j

theorem radii12811 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12811.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12811 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12811 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12811.grid grid_top_bounds12811 j hθ

noncomputable def covarianceInputs12811 :
    BstLean.Part263.CovarianceInputs 12811 scalarRow12811.grid parameters (caps repair12811) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12811 grid_top_bounds12811 repair12811

noncomputable def covarianceEvent12811 : Set (AgFam 12811) :=
  BstLean.Part263.covarianceEvent 12811 scalarRow12811.grid parameters

theorem covarianceEvent12811_measurable : MeasurableSet covarianceEvent12811 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12811_payment :
    (retDist (paperDesignP 12811).toCentres).real
      (agentEv (paperDesignP 12811) covarianceEvent12811)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12811

theorem localCov12811 : BstLean.Part259.LocalCovarianceOn covarianceEvent12811
    (BstLean.Part263.cell scalarRow12811.grid) (caps repair12811) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12811

theorem covarianceGood12811_payment :
    (retDist (paperDesignP 12811).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12811)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12811_payment



end BstLean.Part269.N12811

namespace BstLean.Part269.N12811
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12811}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12811.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12811) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12811).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12811 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12811) (by norm_num) BstLean.Part268.WorldRow12811.worldPackage rfl
    BstLean.Part268.WorldRow12811.product_lower (BstLean.Part268.WorldRow12811.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12811} (hw : c ∈ Hof BstLean.Part268.WorldRow12811.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12811) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12811) (by norm_num) BstLean.Part268.WorldRow12811.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12811} (hw : c ∈ Hof BstLean.Part268.WorldRow12811.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12811) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12811).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12811) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12811_eq : scalarRow12811.targetFrame = BstLean.Part268.agent12811.frame := by
  norm_num [scalarRow12811,BstLean.Part268.agent12811]

noncomputable def frameData12811 : BstLean.Part264b.FrameData 12811 :=
  BstLean.Part269.frameData_from_numerics (n := 12811) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12811.worldPackage rfl BstLean.Part268.WorldRow12811.product_lower (BstLean.Part268.WorldRow12811.producthi.2.trans (by norm_num))
    scalarRow12811 repair12811 covarianceInputs12811 (fun i hi => sourceNumerics12811 hi)
    BstLean.Part268.agent12811.frame targetFrame12811_eq


end BstLean.Part269.N12811

namespace BstLean.Part269.N12812
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12812 : scalarRow12812.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12812, BstLean.Part268.grid12812, BstLean.Part263.worldGrid]

theorem supplies12812 (j : Fin 43) : Supply 12812 (parameters j)
    (cellLower scalarRow12812.grid (sourceIndex j))
    (cellUpper scalarRow12812.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12812.grid grid_top_bounds12812 j

theorem radii12812 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12812.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12812 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12812 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12812.grid grid_top_bounds12812 j hθ

noncomputable def covarianceInputs12812 :
    BstLean.Part263.CovarianceInputs 12812 scalarRow12812.grid parameters (caps repair12812) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12812 grid_top_bounds12812 repair12812

noncomputable def covarianceEvent12812 : Set (AgFam 12812) :=
  BstLean.Part263.covarianceEvent 12812 scalarRow12812.grid parameters

theorem covarianceEvent12812_measurable : MeasurableSet covarianceEvent12812 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12812_payment :
    (retDist (paperDesignP 12812).toCentres).real
      (agentEv (paperDesignP 12812) covarianceEvent12812)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12812

theorem localCov12812 : BstLean.Part259.LocalCovarianceOn covarianceEvent12812
    (BstLean.Part263.cell scalarRow12812.grid) (caps repair12812) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12812

theorem covarianceGood12812_payment :
    (retDist (paperDesignP 12812).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12812)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12812_payment



end BstLean.Part269.N12812

namespace BstLean.Part269.N12812
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12812}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12812.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12812) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12812).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12812 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12812) (by norm_num) BstLean.Part268.WorldRow12812.worldPackage rfl
    BstLean.Part268.WorldRow12812.product_lower (BstLean.Part268.WorldRow12812.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12812} (hw : c ∈ Hof BstLean.Part268.WorldRow12812.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12812) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12812) (by norm_num) BstLean.Part268.WorldRow12812.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12812} (hw : c ∈ Hof BstLean.Part268.WorldRow12812.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12812) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12812).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12812) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12812_eq : scalarRow12812.targetFrame = BstLean.Part268.agent12812.frame := by
  norm_num [scalarRow12812,BstLean.Part268.agent12812]

noncomputable def frameData12812 : BstLean.Part264b.FrameData 12812 :=
  BstLean.Part269.frameData_from_numerics (n := 12812) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12812.worldPackage rfl BstLean.Part268.WorldRow12812.product_lower (BstLean.Part268.WorldRow12812.producthi.2.trans (by norm_num))
    scalarRow12812 repair12812 covarianceInputs12812 (fun i hi => sourceNumerics12812 hi)
    BstLean.Part268.agent12812.frame targetFrame12812_eq


end BstLean.Part269.N12812

namespace BstLean.Part269.N12813
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12813 : scalarRow12813.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12813, BstLean.Part268.grid12813, BstLean.Part263.worldGrid]

theorem supplies12813 (j : Fin 43) : Supply 12813 (parameters j)
    (cellLower scalarRow12813.grid (sourceIndex j))
    (cellUpper scalarRow12813.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12813.grid grid_top_bounds12813 j

theorem radii12813 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12813.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12813 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12813 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12813.grid grid_top_bounds12813 j hθ

noncomputable def covarianceInputs12813 :
    BstLean.Part263.CovarianceInputs 12813 scalarRow12813.grid parameters (caps repair12813) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12813 grid_top_bounds12813 repair12813

noncomputable def covarianceEvent12813 : Set (AgFam 12813) :=
  BstLean.Part263.covarianceEvent 12813 scalarRow12813.grid parameters

theorem covarianceEvent12813_measurable : MeasurableSet covarianceEvent12813 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12813_payment :
    (retDist (paperDesignP 12813).toCentres).real
      (agentEv (paperDesignP 12813) covarianceEvent12813)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12813

theorem localCov12813 : BstLean.Part259.LocalCovarianceOn covarianceEvent12813
    (BstLean.Part263.cell scalarRow12813.grid) (caps repair12813) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12813

theorem covarianceGood12813_payment :
    (retDist (paperDesignP 12813).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12813)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12813_payment



end BstLean.Part269.N12813

namespace BstLean.Part269.N12813
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12813}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12813.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12813) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12813).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12813 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12813) (by norm_num) BstLean.Part268.WorldRow12813.worldPackage rfl
    BstLean.Part268.WorldRow12813.product_lower (BstLean.Part268.WorldRow12813.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12813} (hw : c ∈ Hof BstLean.Part268.WorldRow12813.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12813) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12813) (by norm_num) BstLean.Part268.WorldRow12813.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12813} (hw : c ∈ Hof BstLean.Part268.WorldRow12813.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12813) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12813).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12813) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12813_eq : scalarRow12813.targetFrame = BstLean.Part268.agent12813.frame := by
  norm_num [scalarRow12813,BstLean.Part268.agent12813]

noncomputable def frameData12813 : BstLean.Part264b.FrameData 12813 :=
  BstLean.Part269.frameData_from_numerics (n := 12813) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12813.worldPackage rfl BstLean.Part268.WorldRow12813.product_lower (BstLean.Part268.WorldRow12813.producthi.2.trans (by norm_num))
    scalarRow12813 repair12813 covarianceInputs12813 (fun i hi => sourceNumerics12813 hi)
    BstLean.Part268.agent12813.frame targetFrame12813_eq


end BstLean.Part269.N12813

namespace BstLean.Part269.N12814
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12814 : scalarRow12814.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12814, BstLean.Part268.grid12814, BstLean.Part263.worldGrid]

theorem supplies12814 (j : Fin 43) : Supply 12814 (parameters j)
    (cellLower scalarRow12814.grid (sourceIndex j))
    (cellUpper scalarRow12814.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12814.grid grid_top_bounds12814 j

theorem radii12814 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12814.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12814 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12814 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12814.grid grid_top_bounds12814 j hθ

noncomputable def covarianceInputs12814 :
    BstLean.Part263.CovarianceInputs 12814 scalarRow12814.grid parameters (caps repair12814) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12814 grid_top_bounds12814 repair12814

noncomputable def covarianceEvent12814 : Set (AgFam 12814) :=
  BstLean.Part263.covarianceEvent 12814 scalarRow12814.grid parameters

theorem covarianceEvent12814_measurable : MeasurableSet covarianceEvent12814 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12814_payment :
    (retDist (paperDesignP 12814).toCentres).real
      (agentEv (paperDesignP 12814) covarianceEvent12814)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12814

theorem localCov12814 : BstLean.Part259.LocalCovarianceOn covarianceEvent12814
    (BstLean.Part263.cell scalarRow12814.grid) (caps repair12814) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12814

theorem covarianceGood12814_payment :
    (retDist (paperDesignP 12814).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12814)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12814_payment



end BstLean.Part269.N12814

namespace BstLean.Part269.N12814
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12814}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12814.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12814) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12814).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12814 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12814) (by norm_num) BstLean.Part268.WorldRow12814.worldPackage rfl
    BstLean.Part268.WorldRow12814.product_lower (BstLean.Part268.WorldRow12814.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12814} (hw : c ∈ Hof BstLean.Part268.WorldRow12814.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12814) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12814) (by norm_num) BstLean.Part268.WorldRow12814.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12814} (hw : c ∈ Hof BstLean.Part268.WorldRow12814.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12814) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12814).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12814) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12814_eq : scalarRow12814.targetFrame = BstLean.Part268.agent12814.frame := by
  norm_num [scalarRow12814,BstLean.Part268.agent12814]

noncomputable def frameData12814 : BstLean.Part264b.FrameData 12814 :=
  BstLean.Part269.frameData_from_numerics (n := 12814) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12814.worldPackage rfl BstLean.Part268.WorldRow12814.product_lower (BstLean.Part268.WorldRow12814.producthi.2.trans (by norm_num))
    scalarRow12814 repair12814 covarianceInputs12814 (fun i hi => sourceNumerics12814 hi)
    BstLean.Part268.agent12814.frame targetFrame12814_eq


end BstLean.Part269.N12814
