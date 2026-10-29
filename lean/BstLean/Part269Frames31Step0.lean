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

namespace BstLean.Part269.N13125
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13125 : scalarRow13125.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13125, BstLean.Part268.grid13125, BstLean.Part263.worldGrid]

theorem supplies13125 (j : Fin 43) : Supply 13125 (parameters j)
    (cellLower scalarRow13125.grid (sourceIndex j))
    (cellUpper scalarRow13125.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13125.grid grid_top_bounds13125 j

theorem radii13125 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13125.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13125 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13125 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13125.grid grid_top_bounds13125 j hθ

noncomputable def covarianceInputs13125 :
    BstLean.Part263.CovarianceInputs 13125 scalarRow13125.grid parameters (caps repair13125) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13125 grid_top_bounds13125 repair13125

noncomputable def covarianceEvent13125 : Set (AgFam 13125) :=
  BstLean.Part263.covarianceEvent 13125 scalarRow13125.grid parameters

theorem covarianceEvent13125_measurable : MeasurableSet covarianceEvent13125 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13125_payment :
    (retDist (paperDesignP 13125).toCentres).real
      (agentEv (paperDesignP 13125) covarianceEvent13125)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13125

theorem localCov13125 : BstLean.Part259.LocalCovarianceOn covarianceEvent13125
    (BstLean.Part263.cell scalarRow13125.grid) (caps repair13125) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13125

theorem covarianceGood13125_payment :
    (retDist (paperDesignP 13125).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13125)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13125_payment



end BstLean.Part269.N13125

namespace BstLean.Part269.N13125
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13125}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13125.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13125) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13125).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13125 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13125) (by norm_num) BstLean.Part268.WorldRow13125.worldPackage rfl
    BstLean.Part268.WorldRow13125.product_lower (BstLean.Part268.WorldRow13125.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13125} (hw : c ∈ Hof BstLean.Part268.WorldRow13125.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13125) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13125) (by norm_num) BstLean.Part268.WorldRow13125.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13125} (hw : c ∈ Hof BstLean.Part268.WorldRow13125.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13125) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13125).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13125) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13125_eq : scalarRow13125.targetFrame = BstLean.Part268.agent13125.frame := by
  norm_num [scalarRow13125,BstLean.Part268.agent13125]

noncomputable def frameData13125 : BstLean.Part264b.FrameData 13125 :=
  BstLean.Part269.frameData_from_numerics (n := 13125) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13125.worldPackage rfl BstLean.Part268.WorldRow13125.product_lower (BstLean.Part268.WorldRow13125.producthi.2.trans (by norm_num))
    scalarRow13125 repair13125 covarianceInputs13125 (fun i hi => sourceNumerics13125 hi)
    BstLean.Part268.agent13125.frame targetFrame13125_eq


end BstLean.Part269.N13125

namespace BstLean.Part269.N13126
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13126 : scalarRow13126.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13126, BstLean.Part268.grid13126, BstLean.Part263.worldGrid]

theorem supplies13126 (j : Fin 43) : Supply 13126 (parameters j)
    (cellLower scalarRow13126.grid (sourceIndex j))
    (cellUpper scalarRow13126.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13126.grid grid_top_bounds13126 j

theorem radii13126 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13126.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13126 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13126 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13126.grid grid_top_bounds13126 j hθ

noncomputable def covarianceInputs13126 :
    BstLean.Part263.CovarianceInputs 13126 scalarRow13126.grid parameters (caps repair13126) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13126 grid_top_bounds13126 repair13126

noncomputable def covarianceEvent13126 : Set (AgFam 13126) :=
  BstLean.Part263.covarianceEvent 13126 scalarRow13126.grid parameters

theorem covarianceEvent13126_measurable : MeasurableSet covarianceEvent13126 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13126_payment :
    (retDist (paperDesignP 13126).toCentres).real
      (agentEv (paperDesignP 13126) covarianceEvent13126)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13126

theorem localCov13126 : BstLean.Part259.LocalCovarianceOn covarianceEvent13126
    (BstLean.Part263.cell scalarRow13126.grid) (caps repair13126) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13126

theorem covarianceGood13126_payment :
    (retDist (paperDesignP 13126).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13126)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13126_payment



end BstLean.Part269.N13126

namespace BstLean.Part269.N13126
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13126}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13126.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13126) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13126).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13126 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13126) (by norm_num) BstLean.Part268.WorldRow13126.worldPackage rfl
    BstLean.Part268.WorldRow13126.product_lower (BstLean.Part268.WorldRow13126.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13126} (hw : c ∈ Hof BstLean.Part268.WorldRow13126.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13126) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13126) (by norm_num) BstLean.Part268.WorldRow13126.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13126} (hw : c ∈ Hof BstLean.Part268.WorldRow13126.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13126) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13126).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13126) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13126_eq : scalarRow13126.targetFrame = BstLean.Part268.agent13126.frame := by
  norm_num [scalarRow13126,BstLean.Part268.agent13126]

noncomputable def frameData13126 : BstLean.Part264b.FrameData 13126 :=
  BstLean.Part269.frameData_from_numerics (n := 13126) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13126.worldPackage rfl BstLean.Part268.WorldRow13126.product_lower (BstLean.Part268.WorldRow13126.producthi.2.trans (by norm_num))
    scalarRow13126 repair13126 covarianceInputs13126 (fun i hi => sourceNumerics13126 hi)
    BstLean.Part268.agent13126.frame targetFrame13126_eq


end BstLean.Part269.N13126

namespace BstLean.Part269.N13127
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13127 : scalarRow13127.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13127, BstLean.Part268.grid13127, BstLean.Part263.worldGrid]

theorem supplies13127 (j : Fin 43) : Supply 13127 (parameters j)
    (cellLower scalarRow13127.grid (sourceIndex j))
    (cellUpper scalarRow13127.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13127.grid grid_top_bounds13127 j

theorem radii13127 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13127.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13127 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13127 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13127.grid grid_top_bounds13127 j hθ

noncomputable def covarianceInputs13127 :
    BstLean.Part263.CovarianceInputs 13127 scalarRow13127.grid parameters (caps repair13127) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13127 grid_top_bounds13127 repair13127

noncomputable def covarianceEvent13127 : Set (AgFam 13127) :=
  BstLean.Part263.covarianceEvent 13127 scalarRow13127.grid parameters

theorem covarianceEvent13127_measurable : MeasurableSet covarianceEvent13127 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13127_payment :
    (retDist (paperDesignP 13127).toCentres).real
      (agentEv (paperDesignP 13127) covarianceEvent13127)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13127

theorem localCov13127 : BstLean.Part259.LocalCovarianceOn covarianceEvent13127
    (BstLean.Part263.cell scalarRow13127.grid) (caps repair13127) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13127

theorem covarianceGood13127_payment :
    (retDist (paperDesignP 13127).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13127)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13127_payment



end BstLean.Part269.N13127

namespace BstLean.Part269.N13127
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13127}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13127.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13127) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13127).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13127 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13127) (by norm_num) BstLean.Part268.WorldRow13127.worldPackage rfl
    BstLean.Part268.WorldRow13127.product_lower (BstLean.Part268.WorldRow13127.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13127} (hw : c ∈ Hof BstLean.Part268.WorldRow13127.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13127) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13127) (by norm_num) BstLean.Part268.WorldRow13127.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13127} (hw : c ∈ Hof BstLean.Part268.WorldRow13127.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13127) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13127).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13127) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13127_eq : scalarRow13127.targetFrame = BstLean.Part268.agent13127.frame := by
  norm_num [scalarRow13127,BstLean.Part268.agent13127]

noncomputable def frameData13127 : BstLean.Part264b.FrameData 13127 :=
  BstLean.Part269.frameData_from_numerics (n := 13127) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13127.worldPackage rfl BstLean.Part268.WorldRow13127.product_lower (BstLean.Part268.WorldRow13127.producthi.2.trans (by norm_num))
    scalarRow13127 repair13127 covarianceInputs13127 (fun i hi => sourceNumerics13127 hi)
    BstLean.Part268.agent13127.frame targetFrame13127_eq


end BstLean.Part269.N13127

namespace BstLean.Part269.N13128
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13128 : scalarRow13128.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13128, BstLean.Part268.grid13128, BstLean.Part263.worldGrid]

theorem supplies13128 (j : Fin 43) : Supply 13128 (parameters j)
    (cellLower scalarRow13128.grid (sourceIndex j))
    (cellUpper scalarRow13128.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13128.grid grid_top_bounds13128 j

theorem radii13128 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13128.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13128 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13128 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13128.grid grid_top_bounds13128 j hθ

noncomputable def covarianceInputs13128 :
    BstLean.Part263.CovarianceInputs 13128 scalarRow13128.grid parameters (caps repair13128) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13128 grid_top_bounds13128 repair13128

noncomputable def covarianceEvent13128 : Set (AgFam 13128) :=
  BstLean.Part263.covarianceEvent 13128 scalarRow13128.grid parameters

theorem covarianceEvent13128_measurable : MeasurableSet covarianceEvent13128 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13128_payment :
    (retDist (paperDesignP 13128).toCentres).real
      (agentEv (paperDesignP 13128) covarianceEvent13128)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13128

theorem localCov13128 : BstLean.Part259.LocalCovarianceOn covarianceEvent13128
    (BstLean.Part263.cell scalarRow13128.grid) (caps repair13128) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13128

theorem covarianceGood13128_payment :
    (retDist (paperDesignP 13128).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13128)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13128_payment



end BstLean.Part269.N13128

namespace BstLean.Part269.N13128
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13128}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13128.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13128) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13128).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13128 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13128) (by norm_num) BstLean.Part268.WorldRow13128.worldPackage rfl
    BstLean.Part268.WorldRow13128.product_lower (BstLean.Part268.WorldRow13128.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13128} (hw : c ∈ Hof BstLean.Part268.WorldRow13128.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13128) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13128) (by norm_num) BstLean.Part268.WorldRow13128.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13128} (hw : c ∈ Hof BstLean.Part268.WorldRow13128.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13128) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13128).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13128) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13128_eq : scalarRow13128.targetFrame = BstLean.Part268.agent13128.frame := by
  norm_num [scalarRow13128,BstLean.Part268.agent13128]

noncomputable def frameData13128 : BstLean.Part264b.FrameData 13128 :=
  BstLean.Part269.frameData_from_numerics (n := 13128) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13128.worldPackage rfl BstLean.Part268.WorldRow13128.product_lower (BstLean.Part268.WorldRow13128.producthi.2.trans (by norm_num))
    scalarRow13128 repair13128 covarianceInputs13128 (fun i hi => sourceNumerics13128 hi)
    BstLean.Part268.agent13128.frame targetFrame13128_eq


end BstLean.Part269.N13128

namespace BstLean.Part269.N13129
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13129 : scalarRow13129.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13129, BstLean.Part268.grid13129, BstLean.Part263.worldGrid]

theorem supplies13129 (j : Fin 43) : Supply 13129 (parameters j)
    (cellLower scalarRow13129.grid (sourceIndex j))
    (cellUpper scalarRow13129.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13129.grid grid_top_bounds13129 j

theorem radii13129 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13129.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13129 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13129 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13129.grid grid_top_bounds13129 j hθ

noncomputable def covarianceInputs13129 :
    BstLean.Part263.CovarianceInputs 13129 scalarRow13129.grid parameters (caps repair13129) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13129 grid_top_bounds13129 repair13129

noncomputable def covarianceEvent13129 : Set (AgFam 13129) :=
  BstLean.Part263.covarianceEvent 13129 scalarRow13129.grid parameters

theorem covarianceEvent13129_measurable : MeasurableSet covarianceEvent13129 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13129_payment :
    (retDist (paperDesignP 13129).toCentres).real
      (agentEv (paperDesignP 13129) covarianceEvent13129)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13129

theorem localCov13129 : BstLean.Part259.LocalCovarianceOn covarianceEvent13129
    (BstLean.Part263.cell scalarRow13129.grid) (caps repair13129) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13129

theorem covarianceGood13129_payment :
    (retDist (paperDesignP 13129).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13129)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13129_payment



end BstLean.Part269.N13129

namespace BstLean.Part269.N13129
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13129}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13129.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13129) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13129).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13129 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13129) (by norm_num) BstLean.Part268.WorldRow13129.worldPackage rfl
    BstLean.Part268.WorldRow13129.product_lower (BstLean.Part268.WorldRow13129.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13129} (hw : c ∈ Hof BstLean.Part268.WorldRow13129.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13129) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13129) (by norm_num) BstLean.Part268.WorldRow13129.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13129} (hw : c ∈ Hof BstLean.Part268.WorldRow13129.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13129) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13129).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13129) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13129_eq : scalarRow13129.targetFrame = BstLean.Part268.agent13129.frame := by
  norm_num [scalarRow13129,BstLean.Part268.agent13129]

noncomputable def frameData13129 : BstLean.Part264b.FrameData 13129 :=
  BstLean.Part269.frameData_from_numerics (n := 13129) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13129.worldPackage rfl BstLean.Part268.WorldRow13129.product_lower (BstLean.Part268.WorldRow13129.producthi.2.trans (by norm_num))
    scalarRow13129 repair13129 covarianceInputs13129 (fun i hi => sourceNumerics13129 hi)
    BstLean.Part268.agent13129.frame targetFrame13129_eq


end BstLean.Part269.N13129
