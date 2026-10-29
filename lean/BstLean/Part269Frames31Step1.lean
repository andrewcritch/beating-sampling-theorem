import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World31Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs31
import BstLean.Part269Rows31
import BstLean.Part269Sources31
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13130
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13130 : scalarRow13130.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13130, BstLean.Part268.grid13130, BstLean.Part263.worldGrid]

theorem supplies13130 (j : Fin 43) : Supply 13130 (parameters j)
    (cellLower scalarRow13130.grid (sourceIndex j))
    (cellUpper scalarRow13130.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13130.grid grid_top_bounds13130 j

theorem radii13130 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13130.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13130 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13130 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13130.grid grid_top_bounds13130 j hθ

noncomputable def covarianceInputs13130 :
    BstLean.Part263.CovarianceInputs 13130 scalarRow13130.grid parameters (caps repair13130) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13130 grid_top_bounds13130 repair13130

noncomputable def covarianceEvent13130 : Set (AgFam 13130) :=
  BstLean.Part263.covarianceEvent 13130 scalarRow13130.grid parameters

theorem covarianceEvent13130_measurable : MeasurableSet covarianceEvent13130 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13130_payment :
    (retDist (paperDesignP 13130).toCentres).real
      (agentEv (paperDesignP 13130) covarianceEvent13130)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13130

theorem localCov13130 : BstLean.Part259.LocalCovarianceOn covarianceEvent13130
    (BstLean.Part263.cell scalarRow13130.grid) (caps repair13130) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13130

theorem covarianceGood13130_payment :
    (retDist (paperDesignP 13130).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13130)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13130_payment



end BstLean.Part269.N13130

namespace BstLean.Part269.N13130
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13130}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13130.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13130) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13130).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13130 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13130) (by norm_num) BstLean.Part268.WorldRow13130.worldPackage rfl
    BstLean.Part268.WorldRow13130.product_lower (BstLean.Part268.WorldRow13130.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13130} (hw : c ∈ Hof BstLean.Part268.WorldRow13130.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13130) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13130) (by norm_num) BstLean.Part268.WorldRow13130.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13130} (hw : c ∈ Hof BstLean.Part268.WorldRow13130.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13130) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13130).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13130) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13130_eq : scalarRow13130.targetFrame = BstLean.Part268.agent13130.frame := by
  norm_num [scalarRow13130,BstLean.Part268.agent13130]

noncomputable def frameData13130 : BstLean.Part264b.FrameData 13130 :=
  BstLean.Part269.frameData_from_numerics (n := 13130) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13130.worldPackage rfl BstLean.Part268.WorldRow13130.product_lower (BstLean.Part268.WorldRow13130.producthi.2.trans (by norm_num))
    scalarRow13130 repair13130 covarianceInputs13130 (fun i hi => sourceNumerics13130 hi)
    BstLean.Part268.agent13130.frame targetFrame13130_eq


end BstLean.Part269.N13130

namespace BstLean.Part269.N13131
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13131 : scalarRow13131.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13131, BstLean.Part268.grid13131, BstLean.Part263.worldGrid]

theorem supplies13131 (j : Fin 43) : Supply 13131 (parameters j)
    (cellLower scalarRow13131.grid (sourceIndex j))
    (cellUpper scalarRow13131.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13131.grid grid_top_bounds13131 j

theorem radii13131 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13131.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13131 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13131 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13131.grid grid_top_bounds13131 j hθ

noncomputable def covarianceInputs13131 :
    BstLean.Part263.CovarianceInputs 13131 scalarRow13131.grid parameters (caps repair13131) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13131 grid_top_bounds13131 repair13131

noncomputable def covarianceEvent13131 : Set (AgFam 13131) :=
  BstLean.Part263.covarianceEvent 13131 scalarRow13131.grid parameters

theorem covarianceEvent13131_measurable : MeasurableSet covarianceEvent13131 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13131_payment :
    (retDist (paperDesignP 13131).toCentres).real
      (agentEv (paperDesignP 13131) covarianceEvent13131)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13131

theorem localCov13131 : BstLean.Part259.LocalCovarianceOn covarianceEvent13131
    (BstLean.Part263.cell scalarRow13131.grid) (caps repair13131) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13131

theorem covarianceGood13131_payment :
    (retDist (paperDesignP 13131).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13131)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13131_payment



end BstLean.Part269.N13131

namespace BstLean.Part269.N13131
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13131}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13131.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13131) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13131).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13131 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13131) (by norm_num) BstLean.Part268.WorldRow13131.worldPackage rfl
    BstLean.Part268.WorldRow13131.product_lower (BstLean.Part268.WorldRow13131.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13131} (hw : c ∈ Hof BstLean.Part268.WorldRow13131.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13131) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13131) (by norm_num) BstLean.Part268.WorldRow13131.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13131} (hw : c ∈ Hof BstLean.Part268.WorldRow13131.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13131) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13131).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13131) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13131_eq : scalarRow13131.targetFrame = BstLean.Part268.agent13131.frame := by
  norm_num [scalarRow13131,BstLean.Part268.agent13131]

noncomputable def frameData13131 : BstLean.Part264b.FrameData 13131 :=
  BstLean.Part269.frameData_from_numerics (n := 13131) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13131.worldPackage rfl BstLean.Part268.WorldRow13131.product_lower (BstLean.Part268.WorldRow13131.producthi.2.trans (by norm_num))
    scalarRow13131 repair13131 covarianceInputs13131 (fun i hi => sourceNumerics13131 hi)
    BstLean.Part268.agent13131.frame targetFrame13131_eq


end BstLean.Part269.N13131

namespace BstLean.Part269.N13132
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13132 : scalarRow13132.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13132, BstLean.Part268.grid13132, BstLean.Part263.worldGrid]

theorem supplies13132 (j : Fin 43) : Supply 13132 (parameters j)
    (cellLower scalarRow13132.grid (sourceIndex j))
    (cellUpper scalarRow13132.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13132.grid grid_top_bounds13132 j

theorem radii13132 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13132.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13132 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13132 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13132.grid grid_top_bounds13132 j hθ

noncomputable def covarianceInputs13132 :
    BstLean.Part263.CovarianceInputs 13132 scalarRow13132.grid parameters (caps repair13132) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13132 grid_top_bounds13132 repair13132

noncomputable def covarianceEvent13132 : Set (AgFam 13132) :=
  BstLean.Part263.covarianceEvent 13132 scalarRow13132.grid parameters

theorem covarianceEvent13132_measurable : MeasurableSet covarianceEvent13132 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13132_payment :
    (retDist (paperDesignP 13132).toCentres).real
      (agentEv (paperDesignP 13132) covarianceEvent13132)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13132

theorem localCov13132 : BstLean.Part259.LocalCovarianceOn covarianceEvent13132
    (BstLean.Part263.cell scalarRow13132.grid) (caps repair13132) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13132

theorem covarianceGood13132_payment :
    (retDist (paperDesignP 13132).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13132)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13132_payment



end BstLean.Part269.N13132

namespace BstLean.Part269.N13132
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13132}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13132.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13132) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13132).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13132 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13132) (by norm_num) BstLean.Part268.WorldRow13132.worldPackage rfl
    BstLean.Part268.WorldRow13132.product_lower (BstLean.Part268.WorldRow13132.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13132} (hw : c ∈ Hof BstLean.Part268.WorldRow13132.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13132) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13132) (by norm_num) BstLean.Part268.WorldRow13132.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13132} (hw : c ∈ Hof BstLean.Part268.WorldRow13132.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13132) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13132).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13132) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13132_eq : scalarRow13132.targetFrame = BstLean.Part268.agent13132.frame := by
  norm_num [scalarRow13132,BstLean.Part268.agent13132]

noncomputable def frameData13132 : BstLean.Part264b.FrameData 13132 :=
  BstLean.Part269.frameData_from_numerics (n := 13132) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13132.worldPackage rfl BstLean.Part268.WorldRow13132.product_lower (BstLean.Part268.WorldRow13132.producthi.2.trans (by norm_num))
    scalarRow13132 repair13132 covarianceInputs13132 (fun i hi => sourceNumerics13132 hi)
    BstLean.Part268.agent13132.frame targetFrame13132_eq


end BstLean.Part269.N13132

namespace BstLean.Part269.N13133
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13133 : scalarRow13133.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13133, BstLean.Part268.grid13133, BstLean.Part263.worldGrid]

theorem supplies13133 (j : Fin 43) : Supply 13133 (parameters j)
    (cellLower scalarRow13133.grid (sourceIndex j))
    (cellUpper scalarRow13133.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13133.grid grid_top_bounds13133 j

theorem radii13133 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13133.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13133 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13133 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13133.grid grid_top_bounds13133 j hθ

noncomputable def covarianceInputs13133 :
    BstLean.Part263.CovarianceInputs 13133 scalarRow13133.grid parameters (caps repair13133) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13133 grid_top_bounds13133 repair13133

noncomputable def covarianceEvent13133 : Set (AgFam 13133) :=
  BstLean.Part263.covarianceEvent 13133 scalarRow13133.grid parameters

theorem covarianceEvent13133_measurable : MeasurableSet covarianceEvent13133 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13133_payment :
    (retDist (paperDesignP 13133).toCentres).real
      (agentEv (paperDesignP 13133) covarianceEvent13133)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13133

theorem localCov13133 : BstLean.Part259.LocalCovarianceOn covarianceEvent13133
    (BstLean.Part263.cell scalarRow13133.grid) (caps repair13133) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13133

theorem covarianceGood13133_payment :
    (retDist (paperDesignP 13133).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13133)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13133_payment



end BstLean.Part269.N13133

namespace BstLean.Part269.N13133
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13133}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13133.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13133) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13133).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13133 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13133) (by norm_num) BstLean.Part268.WorldRow13133.worldPackage rfl
    BstLean.Part268.WorldRow13133.product_lower (BstLean.Part268.WorldRow13133.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13133} (hw : c ∈ Hof BstLean.Part268.WorldRow13133.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13133) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13133) (by norm_num) BstLean.Part268.WorldRow13133.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13133} (hw : c ∈ Hof BstLean.Part268.WorldRow13133.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13133) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13133).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13133) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13133_eq : scalarRow13133.targetFrame = BstLean.Part268.agent13133.frame := by
  norm_num [scalarRow13133,BstLean.Part268.agent13133]

noncomputable def frameData13133 : BstLean.Part264b.FrameData 13133 :=
  BstLean.Part269.frameData_from_numerics (n := 13133) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13133.worldPackage rfl BstLean.Part268.WorldRow13133.product_lower (BstLean.Part268.WorldRow13133.producthi.2.trans (by norm_num))
    scalarRow13133 repair13133 covarianceInputs13133 (fun i hi => sourceNumerics13133 hi)
    BstLean.Part268.agent13133.frame targetFrame13133_eq


end BstLean.Part269.N13133

namespace BstLean.Part269.N13134
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13134 : scalarRow13134.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13134, BstLean.Part268.grid13134, BstLean.Part263.worldGrid]

theorem supplies13134 (j : Fin 43) : Supply 13134 (parameters j)
    (cellLower scalarRow13134.grid (sourceIndex j))
    (cellUpper scalarRow13134.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13134.grid grid_top_bounds13134 j

theorem radii13134 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13134.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13134 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13134 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13134.grid grid_top_bounds13134 j hθ

noncomputable def covarianceInputs13134 :
    BstLean.Part263.CovarianceInputs 13134 scalarRow13134.grid parameters (caps repair13134) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13134 grid_top_bounds13134 repair13134

noncomputable def covarianceEvent13134 : Set (AgFam 13134) :=
  BstLean.Part263.covarianceEvent 13134 scalarRow13134.grid parameters

theorem covarianceEvent13134_measurable : MeasurableSet covarianceEvent13134 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13134_payment :
    (retDist (paperDesignP 13134).toCentres).real
      (agentEv (paperDesignP 13134) covarianceEvent13134)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13134

theorem localCov13134 : BstLean.Part259.LocalCovarianceOn covarianceEvent13134
    (BstLean.Part263.cell scalarRow13134.grid) (caps repair13134) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13134

theorem covarianceGood13134_payment :
    (retDist (paperDesignP 13134).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13134)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13134_payment



end BstLean.Part269.N13134

namespace BstLean.Part269.N13134
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13134}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13134.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13134) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13134).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13134 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13134) (by norm_num) BstLean.Part268.WorldRow13134.worldPackage rfl
    BstLean.Part268.WorldRow13134.product_lower (BstLean.Part268.WorldRow13134.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13134} (hw : c ∈ Hof BstLean.Part268.WorldRow13134.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13134) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13134) (by norm_num) BstLean.Part268.WorldRow13134.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13134} (hw : c ∈ Hof BstLean.Part268.WorldRow13134.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13134) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13134).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13134) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13134_eq : scalarRow13134.targetFrame = BstLean.Part268.agent13134.frame := by
  norm_num [scalarRow13134,BstLean.Part268.agent13134]

noncomputable def frameData13134 : BstLean.Part264b.FrameData 13134 :=
  BstLean.Part269.frameData_from_numerics (n := 13134) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13134.worldPackage rfl BstLean.Part268.WorldRow13134.product_lower (BstLean.Part268.WorldRow13134.producthi.2.trans (by norm_num))
    scalarRow13134 repair13134 covarianceInputs13134 (fun i hi => sourceNumerics13134 hi)
    BstLean.Part268.agent13134.frame targetFrame13134_eq


end BstLean.Part269.N13134
