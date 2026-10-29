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

namespace BstLean.Part269.N12800
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12800 : scalarRow12800.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12800, BstLean.Part268.grid12800, BstLean.Part263.worldGrid]

theorem supplies12800 (j : Fin 43) : Supply 12800 (parameters j)
    (cellLower scalarRow12800.grid (sourceIndex j))
    (cellUpper scalarRow12800.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12800.grid grid_top_bounds12800 j

theorem radii12800 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12800.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12800 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12800 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12800.grid grid_top_bounds12800 j hθ

noncomputable def covarianceInputs12800 :
    BstLean.Part263.CovarianceInputs 12800 scalarRow12800.grid parameters (caps repair12800) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12800 grid_top_bounds12800 repair12800

noncomputable def covarianceEvent12800 : Set (AgFam 12800) :=
  BstLean.Part263.covarianceEvent 12800 scalarRow12800.grid parameters

theorem covarianceEvent12800_measurable : MeasurableSet covarianceEvent12800 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12800_payment :
    (retDist (paperDesignP 12800).toCentres).real
      (agentEv (paperDesignP 12800) covarianceEvent12800)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12800

theorem localCov12800 : BstLean.Part259.LocalCovarianceOn covarianceEvent12800
    (BstLean.Part263.cell scalarRow12800.grid) (caps repair12800) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12800

theorem covarianceGood12800_payment :
    (retDist (paperDesignP 12800).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12800)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12800_payment



end BstLean.Part269.N12800

namespace BstLean.Part269.N12800
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12800}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12800.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12800) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12800).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12800 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12800) (by norm_num) BstLean.Part268.WorldRow12800.worldPackage rfl
    BstLean.Part268.WorldRow12800.product_lower (BstLean.Part268.WorldRow12800.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12800} (hw : c ∈ Hof BstLean.Part268.WorldRow12800.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12800) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12800) (by norm_num) BstLean.Part268.WorldRow12800.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12800} (hw : c ∈ Hof BstLean.Part268.WorldRow12800.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12800) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12800).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12800) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12800_eq : scalarRow12800.targetFrame = BstLean.Part268.agent12800.frame := by
  norm_num [scalarRow12800,BstLean.Part268.agent12800]

noncomputable def frameData12800 : BstLean.Part264b.FrameData 12800 :=
  BstLean.Part269.frameData_from_numerics (n := 12800) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12800.worldPackage rfl BstLean.Part268.WorldRow12800.product_lower (BstLean.Part268.WorldRow12800.producthi.2.trans (by norm_num))
    scalarRow12800 repair12800 covarianceInputs12800 (fun i hi => sourceNumerics12800 hi)
    BstLean.Part268.agent12800.frame targetFrame12800_eq


end BstLean.Part269.N12800

namespace BstLean.Part269.N12801
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12801 : scalarRow12801.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12801, BstLean.Part268.grid12801, BstLean.Part263.worldGrid]

theorem supplies12801 (j : Fin 43) : Supply 12801 (parameters j)
    (cellLower scalarRow12801.grid (sourceIndex j))
    (cellUpper scalarRow12801.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12801.grid grid_top_bounds12801 j

theorem radii12801 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12801.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12801 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12801 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12801.grid grid_top_bounds12801 j hθ

noncomputable def covarianceInputs12801 :
    BstLean.Part263.CovarianceInputs 12801 scalarRow12801.grid parameters (caps repair12801) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12801 grid_top_bounds12801 repair12801

noncomputable def covarianceEvent12801 : Set (AgFam 12801) :=
  BstLean.Part263.covarianceEvent 12801 scalarRow12801.grid parameters

theorem covarianceEvent12801_measurable : MeasurableSet covarianceEvent12801 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12801_payment :
    (retDist (paperDesignP 12801).toCentres).real
      (agentEv (paperDesignP 12801) covarianceEvent12801)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12801

theorem localCov12801 : BstLean.Part259.LocalCovarianceOn covarianceEvent12801
    (BstLean.Part263.cell scalarRow12801.grid) (caps repair12801) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12801

theorem covarianceGood12801_payment :
    (retDist (paperDesignP 12801).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12801)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12801_payment



end BstLean.Part269.N12801

namespace BstLean.Part269.N12801
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12801}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12801.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12801) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12801).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12801 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12801) (by norm_num) BstLean.Part268.WorldRow12801.worldPackage rfl
    BstLean.Part268.WorldRow12801.product_lower (BstLean.Part268.WorldRow12801.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12801} (hw : c ∈ Hof BstLean.Part268.WorldRow12801.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12801) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12801) (by norm_num) BstLean.Part268.WorldRow12801.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12801} (hw : c ∈ Hof BstLean.Part268.WorldRow12801.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12801) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12801).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12801) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12801_eq : scalarRow12801.targetFrame = BstLean.Part268.agent12801.frame := by
  norm_num [scalarRow12801,BstLean.Part268.agent12801]

noncomputable def frameData12801 : BstLean.Part264b.FrameData 12801 :=
  BstLean.Part269.frameData_from_numerics (n := 12801) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12801.worldPackage rfl BstLean.Part268.WorldRow12801.product_lower (BstLean.Part268.WorldRow12801.producthi.2.trans (by norm_num))
    scalarRow12801 repair12801 covarianceInputs12801 (fun i hi => sourceNumerics12801 hi)
    BstLean.Part268.agent12801.frame targetFrame12801_eq


end BstLean.Part269.N12801

namespace BstLean.Part269.N12802
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12802 : scalarRow12802.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12802, BstLean.Part268.grid12802, BstLean.Part263.worldGrid]

theorem supplies12802 (j : Fin 43) : Supply 12802 (parameters j)
    (cellLower scalarRow12802.grid (sourceIndex j))
    (cellUpper scalarRow12802.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12802.grid grid_top_bounds12802 j

theorem radii12802 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12802.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12802 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12802 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12802.grid grid_top_bounds12802 j hθ

noncomputable def covarianceInputs12802 :
    BstLean.Part263.CovarianceInputs 12802 scalarRow12802.grid parameters (caps repair12802) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12802 grid_top_bounds12802 repair12802

noncomputable def covarianceEvent12802 : Set (AgFam 12802) :=
  BstLean.Part263.covarianceEvent 12802 scalarRow12802.grid parameters

theorem covarianceEvent12802_measurable : MeasurableSet covarianceEvent12802 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12802_payment :
    (retDist (paperDesignP 12802).toCentres).real
      (agentEv (paperDesignP 12802) covarianceEvent12802)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12802

theorem localCov12802 : BstLean.Part259.LocalCovarianceOn covarianceEvent12802
    (BstLean.Part263.cell scalarRow12802.grid) (caps repair12802) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12802

theorem covarianceGood12802_payment :
    (retDist (paperDesignP 12802).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12802)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12802_payment



end BstLean.Part269.N12802

namespace BstLean.Part269.N12802
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12802}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12802.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12802) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12802).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12802 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12802) (by norm_num) BstLean.Part268.WorldRow12802.worldPackage rfl
    BstLean.Part268.WorldRow12802.product_lower (BstLean.Part268.WorldRow12802.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12802} (hw : c ∈ Hof BstLean.Part268.WorldRow12802.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12802) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12802) (by norm_num) BstLean.Part268.WorldRow12802.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12802} (hw : c ∈ Hof BstLean.Part268.WorldRow12802.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12802) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12802).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12802) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12802_eq : scalarRow12802.targetFrame = BstLean.Part268.agent12802.frame := by
  norm_num [scalarRow12802,BstLean.Part268.agent12802]

noncomputable def frameData12802 : BstLean.Part264b.FrameData 12802 :=
  BstLean.Part269.frameData_from_numerics (n := 12802) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12802.worldPackage rfl BstLean.Part268.WorldRow12802.product_lower (BstLean.Part268.WorldRow12802.producthi.2.trans (by norm_num))
    scalarRow12802 repair12802 covarianceInputs12802 (fun i hi => sourceNumerics12802 hi)
    BstLean.Part268.agent12802.frame targetFrame12802_eq


end BstLean.Part269.N12802

namespace BstLean.Part269.N12803
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12803 : scalarRow12803.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12803, BstLean.Part268.grid12803, BstLean.Part263.worldGrid]

theorem supplies12803 (j : Fin 43) : Supply 12803 (parameters j)
    (cellLower scalarRow12803.grid (sourceIndex j))
    (cellUpper scalarRow12803.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12803.grid grid_top_bounds12803 j

theorem radii12803 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12803.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12803 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12803 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12803.grid grid_top_bounds12803 j hθ

noncomputable def covarianceInputs12803 :
    BstLean.Part263.CovarianceInputs 12803 scalarRow12803.grid parameters (caps repair12803) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12803 grid_top_bounds12803 repair12803

noncomputable def covarianceEvent12803 : Set (AgFam 12803) :=
  BstLean.Part263.covarianceEvent 12803 scalarRow12803.grid parameters

theorem covarianceEvent12803_measurable : MeasurableSet covarianceEvent12803 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12803_payment :
    (retDist (paperDesignP 12803).toCentres).real
      (agentEv (paperDesignP 12803) covarianceEvent12803)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12803

theorem localCov12803 : BstLean.Part259.LocalCovarianceOn covarianceEvent12803
    (BstLean.Part263.cell scalarRow12803.grid) (caps repair12803) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12803

theorem covarianceGood12803_payment :
    (retDist (paperDesignP 12803).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12803)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12803_payment



end BstLean.Part269.N12803

namespace BstLean.Part269.N12803
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12803}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12803.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12803) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12803).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12803 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12803) (by norm_num) BstLean.Part268.WorldRow12803.worldPackage rfl
    BstLean.Part268.WorldRow12803.product_lower (BstLean.Part268.WorldRow12803.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12803} (hw : c ∈ Hof BstLean.Part268.WorldRow12803.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12803) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12803) (by norm_num) BstLean.Part268.WorldRow12803.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12803} (hw : c ∈ Hof BstLean.Part268.WorldRow12803.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12803) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12803).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12803) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12803_eq : scalarRow12803.targetFrame = BstLean.Part268.agent12803.frame := by
  norm_num [scalarRow12803,BstLean.Part268.agent12803]

noncomputable def frameData12803 : BstLean.Part264b.FrameData 12803 :=
  BstLean.Part269.frameData_from_numerics (n := 12803) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12803.worldPackage rfl BstLean.Part268.WorldRow12803.product_lower (BstLean.Part268.WorldRow12803.producthi.2.trans (by norm_num))
    scalarRow12803 repair12803 covarianceInputs12803 (fun i hi => sourceNumerics12803 hi)
    BstLean.Part268.agent12803.frame targetFrame12803_eq


end BstLean.Part269.N12803

namespace BstLean.Part269.N12804
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12804 : scalarRow12804.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12804, BstLean.Part268.grid12804, BstLean.Part263.worldGrid]

theorem supplies12804 (j : Fin 43) : Supply 12804 (parameters j)
    (cellLower scalarRow12804.grid (sourceIndex j))
    (cellUpper scalarRow12804.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12804.grid grid_top_bounds12804 j

theorem radii12804 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12804.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12804 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12804 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12804.grid grid_top_bounds12804 j hθ

noncomputable def covarianceInputs12804 :
    BstLean.Part263.CovarianceInputs 12804 scalarRow12804.grid parameters (caps repair12804) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12804 grid_top_bounds12804 repair12804

noncomputable def covarianceEvent12804 : Set (AgFam 12804) :=
  BstLean.Part263.covarianceEvent 12804 scalarRow12804.grid parameters

theorem covarianceEvent12804_measurable : MeasurableSet covarianceEvent12804 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12804_payment :
    (retDist (paperDesignP 12804).toCentres).real
      (agentEv (paperDesignP 12804) covarianceEvent12804)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12804

theorem localCov12804 : BstLean.Part259.LocalCovarianceOn covarianceEvent12804
    (BstLean.Part263.cell scalarRow12804.grid) (caps repair12804) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12804

theorem covarianceGood12804_payment :
    (retDist (paperDesignP 12804).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12804)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12804_payment



end BstLean.Part269.N12804

namespace BstLean.Part269.N12804
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12804}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12804.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12804) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12804).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12804 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12804) (by norm_num) BstLean.Part268.WorldRow12804.worldPackage rfl
    BstLean.Part268.WorldRow12804.product_lower (BstLean.Part268.WorldRow12804.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12804} (hw : c ∈ Hof BstLean.Part268.WorldRow12804.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12804) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12804) (by norm_num) BstLean.Part268.WorldRow12804.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12804} (hw : c ∈ Hof BstLean.Part268.WorldRow12804.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12804) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12804).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12804) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12804_eq : scalarRow12804.targetFrame = BstLean.Part268.agent12804.frame := by
  norm_num [scalarRow12804,BstLean.Part268.agent12804]

noncomputable def frameData12804 : BstLean.Part264b.FrameData 12804 :=
  BstLean.Part269.frameData_from_numerics (n := 12804) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12804.worldPackage rfl BstLean.Part268.WorldRow12804.product_lower (BstLean.Part268.WorldRow12804.producthi.2.trans (by norm_num))
    scalarRow12804 repair12804 covarianceInputs12804 (fun i hi => sourceNumerics12804 hi)
    BstLean.Part268.agent12804.frame targetFrame12804_eq


end BstLean.Part269.N12804
