import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World29Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs29
import BstLean.Part269Rows29
import BstLean.Part269Sources29
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13090
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13090 : scalarRow13090.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13090, BstLean.Part268.grid13090, BstLean.Part263.worldGrid]

theorem supplies13090 (j : Fin 43) : Supply 13090 (parameters j)
    (cellLower scalarRow13090.grid (sourceIndex j))
    (cellUpper scalarRow13090.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13090.grid grid_top_bounds13090 j

theorem radii13090 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13090.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13090 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13090 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13090.grid grid_top_bounds13090 j hθ

noncomputable def covarianceInputs13090 :
    BstLean.Part263.CovarianceInputs 13090 scalarRow13090.grid parameters (caps repair13090) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13090 grid_top_bounds13090 repair13090

noncomputable def covarianceEvent13090 : Set (AgFam 13090) :=
  BstLean.Part263.covarianceEvent 13090 scalarRow13090.grid parameters

theorem covarianceEvent13090_measurable : MeasurableSet covarianceEvent13090 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13090_payment :
    (retDist (paperDesignP 13090).toCentres).real
      (agentEv (paperDesignP 13090) covarianceEvent13090)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13090

theorem localCov13090 : BstLean.Part259.LocalCovarianceOn covarianceEvent13090
    (BstLean.Part263.cell scalarRow13090.grid) (caps repair13090) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13090

theorem covarianceGood13090_payment :
    (retDist (paperDesignP 13090).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13090)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13090_payment



end BstLean.Part269.N13090

namespace BstLean.Part269.N13090
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13090}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13090.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13090) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13090).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13090 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13090) (by norm_num) BstLean.Part268.WorldRow13090.worldPackage rfl
    BstLean.Part268.WorldRow13090.product_lower (BstLean.Part268.WorldRow13090.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13090} (hw : c ∈ Hof BstLean.Part268.WorldRow13090.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13090) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13090) (by norm_num) BstLean.Part268.WorldRow13090.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13090} (hw : c ∈ Hof BstLean.Part268.WorldRow13090.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13090) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13090).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13090) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13090_eq : scalarRow13090.targetFrame = BstLean.Part268.agent13090.frame := by
  norm_num [scalarRow13090,BstLean.Part268.agent13090]

noncomputable def frameData13090 : BstLean.Part264b.FrameData 13090 :=
  BstLean.Part269.frameData_from_numerics (n := 13090) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13090.worldPackage rfl BstLean.Part268.WorldRow13090.product_lower (BstLean.Part268.WorldRow13090.producthi.2.trans (by norm_num))
    scalarRow13090 repair13090 covarianceInputs13090 (fun i hi => sourceNumerics13090 hi)
    BstLean.Part268.agent13090.frame targetFrame13090_eq


end BstLean.Part269.N13090

namespace BstLean.Part269.N13091
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13091 : scalarRow13091.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13091, BstLean.Part268.grid13091, BstLean.Part263.worldGrid]

theorem supplies13091 (j : Fin 43) : Supply 13091 (parameters j)
    (cellLower scalarRow13091.grid (sourceIndex j))
    (cellUpper scalarRow13091.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13091.grid grid_top_bounds13091 j

theorem radii13091 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13091.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13091 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13091 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13091.grid grid_top_bounds13091 j hθ

noncomputable def covarianceInputs13091 :
    BstLean.Part263.CovarianceInputs 13091 scalarRow13091.grid parameters (caps repair13091) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13091 grid_top_bounds13091 repair13091

noncomputable def covarianceEvent13091 : Set (AgFam 13091) :=
  BstLean.Part263.covarianceEvent 13091 scalarRow13091.grid parameters

theorem covarianceEvent13091_measurable : MeasurableSet covarianceEvent13091 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13091_payment :
    (retDist (paperDesignP 13091).toCentres).real
      (agentEv (paperDesignP 13091) covarianceEvent13091)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13091

theorem localCov13091 : BstLean.Part259.LocalCovarianceOn covarianceEvent13091
    (BstLean.Part263.cell scalarRow13091.grid) (caps repair13091) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13091

theorem covarianceGood13091_payment :
    (retDist (paperDesignP 13091).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13091)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13091_payment



end BstLean.Part269.N13091

namespace BstLean.Part269.N13091
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13091}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13091.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13091) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13091).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13091 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13091) (by norm_num) BstLean.Part268.WorldRow13091.worldPackage rfl
    BstLean.Part268.WorldRow13091.product_lower (BstLean.Part268.WorldRow13091.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13091} (hw : c ∈ Hof BstLean.Part268.WorldRow13091.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13091) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13091) (by norm_num) BstLean.Part268.WorldRow13091.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13091} (hw : c ∈ Hof BstLean.Part268.WorldRow13091.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13091) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13091).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13091) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13091_eq : scalarRow13091.targetFrame = BstLean.Part268.agent13091.frame := by
  norm_num [scalarRow13091,BstLean.Part268.agent13091]

noncomputable def frameData13091 : BstLean.Part264b.FrameData 13091 :=
  BstLean.Part269.frameData_from_numerics (n := 13091) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13091.worldPackage rfl BstLean.Part268.WorldRow13091.product_lower (BstLean.Part268.WorldRow13091.producthi.2.trans (by norm_num))
    scalarRow13091 repair13091 covarianceInputs13091 (fun i hi => sourceNumerics13091 hi)
    BstLean.Part268.agent13091.frame targetFrame13091_eq


end BstLean.Part269.N13091

namespace BstLean.Part269.N13092
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13092 : scalarRow13092.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13092, BstLean.Part268.grid13092, BstLean.Part263.worldGrid]

theorem supplies13092 (j : Fin 43) : Supply 13092 (parameters j)
    (cellLower scalarRow13092.grid (sourceIndex j))
    (cellUpper scalarRow13092.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13092.grid grid_top_bounds13092 j

theorem radii13092 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13092.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13092 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13092 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13092.grid grid_top_bounds13092 j hθ

noncomputable def covarianceInputs13092 :
    BstLean.Part263.CovarianceInputs 13092 scalarRow13092.grid parameters (caps repair13092) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13092 grid_top_bounds13092 repair13092

noncomputable def covarianceEvent13092 : Set (AgFam 13092) :=
  BstLean.Part263.covarianceEvent 13092 scalarRow13092.grid parameters

theorem covarianceEvent13092_measurable : MeasurableSet covarianceEvent13092 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13092_payment :
    (retDist (paperDesignP 13092).toCentres).real
      (agentEv (paperDesignP 13092) covarianceEvent13092)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13092

theorem localCov13092 : BstLean.Part259.LocalCovarianceOn covarianceEvent13092
    (BstLean.Part263.cell scalarRow13092.grid) (caps repair13092) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13092

theorem covarianceGood13092_payment :
    (retDist (paperDesignP 13092).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13092)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13092_payment



end BstLean.Part269.N13092

namespace BstLean.Part269.N13092
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13092}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13092.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13092) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13092).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13092 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13092) (by norm_num) BstLean.Part268.WorldRow13092.worldPackage rfl
    BstLean.Part268.WorldRow13092.product_lower (BstLean.Part268.WorldRow13092.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13092} (hw : c ∈ Hof BstLean.Part268.WorldRow13092.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13092) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13092) (by norm_num) BstLean.Part268.WorldRow13092.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13092} (hw : c ∈ Hof BstLean.Part268.WorldRow13092.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13092) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13092).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13092) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13092_eq : scalarRow13092.targetFrame = BstLean.Part268.agent13092.frame := by
  norm_num [scalarRow13092,BstLean.Part268.agent13092]

noncomputable def frameData13092 : BstLean.Part264b.FrameData 13092 :=
  BstLean.Part269.frameData_from_numerics (n := 13092) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13092.worldPackage rfl BstLean.Part268.WorldRow13092.product_lower (BstLean.Part268.WorldRow13092.producthi.2.trans (by norm_num))
    scalarRow13092 repair13092 covarianceInputs13092 (fun i hi => sourceNumerics13092 hi)
    BstLean.Part268.agent13092.frame targetFrame13092_eq


end BstLean.Part269.N13092

namespace BstLean.Part269.N13093
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13093 : scalarRow13093.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13093, BstLean.Part268.grid13093, BstLean.Part263.worldGrid]

theorem supplies13093 (j : Fin 43) : Supply 13093 (parameters j)
    (cellLower scalarRow13093.grid (sourceIndex j))
    (cellUpper scalarRow13093.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13093.grid grid_top_bounds13093 j

theorem radii13093 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13093.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13093 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13093 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13093.grid grid_top_bounds13093 j hθ

noncomputable def covarianceInputs13093 :
    BstLean.Part263.CovarianceInputs 13093 scalarRow13093.grid parameters (caps repair13093) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13093 grid_top_bounds13093 repair13093

noncomputable def covarianceEvent13093 : Set (AgFam 13093) :=
  BstLean.Part263.covarianceEvent 13093 scalarRow13093.grid parameters

theorem covarianceEvent13093_measurable : MeasurableSet covarianceEvent13093 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13093_payment :
    (retDist (paperDesignP 13093).toCentres).real
      (agentEv (paperDesignP 13093) covarianceEvent13093)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13093

theorem localCov13093 : BstLean.Part259.LocalCovarianceOn covarianceEvent13093
    (BstLean.Part263.cell scalarRow13093.grid) (caps repair13093) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13093

theorem covarianceGood13093_payment :
    (retDist (paperDesignP 13093).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13093)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13093_payment



end BstLean.Part269.N13093

namespace BstLean.Part269.N13093
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13093}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13093.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13093) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13093).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13093 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13093) (by norm_num) BstLean.Part268.WorldRow13093.worldPackage rfl
    BstLean.Part268.WorldRow13093.product_lower (BstLean.Part268.WorldRow13093.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13093} (hw : c ∈ Hof BstLean.Part268.WorldRow13093.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13093) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13093) (by norm_num) BstLean.Part268.WorldRow13093.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13093} (hw : c ∈ Hof BstLean.Part268.WorldRow13093.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13093) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13093).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13093) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13093_eq : scalarRow13093.targetFrame = BstLean.Part268.agent13093.frame := by
  norm_num [scalarRow13093,BstLean.Part268.agent13093]

noncomputable def frameData13093 : BstLean.Part264b.FrameData 13093 :=
  BstLean.Part269.frameData_from_numerics (n := 13093) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13093.worldPackage rfl BstLean.Part268.WorldRow13093.product_lower (BstLean.Part268.WorldRow13093.producthi.2.trans (by norm_num))
    scalarRow13093 repair13093 covarianceInputs13093 (fun i hi => sourceNumerics13093 hi)
    BstLean.Part268.agent13093.frame targetFrame13093_eq


end BstLean.Part269.N13093

namespace BstLean.Part269.N13094
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13094 : scalarRow13094.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13094, BstLean.Part268.grid13094, BstLean.Part263.worldGrid]

theorem supplies13094 (j : Fin 43) : Supply 13094 (parameters j)
    (cellLower scalarRow13094.grid (sourceIndex j))
    (cellUpper scalarRow13094.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13094.grid grid_top_bounds13094 j

theorem radii13094 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13094.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13094 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13094 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13094.grid grid_top_bounds13094 j hθ

noncomputable def covarianceInputs13094 :
    BstLean.Part263.CovarianceInputs 13094 scalarRow13094.grid parameters (caps repair13094) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13094 grid_top_bounds13094 repair13094

noncomputable def covarianceEvent13094 : Set (AgFam 13094) :=
  BstLean.Part263.covarianceEvent 13094 scalarRow13094.grid parameters

theorem covarianceEvent13094_measurable : MeasurableSet covarianceEvent13094 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13094_payment :
    (retDist (paperDesignP 13094).toCentres).real
      (agentEv (paperDesignP 13094) covarianceEvent13094)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13094

theorem localCov13094 : BstLean.Part259.LocalCovarianceOn covarianceEvent13094
    (BstLean.Part263.cell scalarRow13094.grid) (caps repair13094) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13094

theorem covarianceGood13094_payment :
    (retDist (paperDesignP 13094).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13094)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13094_payment



end BstLean.Part269.N13094

namespace BstLean.Part269.N13094
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13094}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13094.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13094) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13094).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13094 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13094) (by norm_num) BstLean.Part268.WorldRow13094.worldPackage rfl
    BstLean.Part268.WorldRow13094.product_lower (BstLean.Part268.WorldRow13094.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13094} (hw : c ∈ Hof BstLean.Part268.WorldRow13094.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13094) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13094) (by norm_num) BstLean.Part268.WorldRow13094.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13094} (hw : c ∈ Hof BstLean.Part268.WorldRow13094.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13094) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13094).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13094) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13094_eq : scalarRow13094.targetFrame = BstLean.Part268.agent13094.frame := by
  norm_num [scalarRow13094,BstLean.Part268.agent13094]

noncomputable def frameData13094 : BstLean.Part264b.FrameData 13094 :=
  BstLean.Part269.frameData_from_numerics (n := 13094) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13094.worldPackage rfl BstLean.Part268.WorldRow13094.product_lower (BstLean.Part268.WorldRow13094.producthi.2.trans (by norm_num))
    scalarRow13094 repair13094 covarianceInputs13094 (fun i hi => sourceNumerics13094 hi)
    BstLean.Part268.agent13094.frame targetFrame13094_eq


end BstLean.Part269.N13094
