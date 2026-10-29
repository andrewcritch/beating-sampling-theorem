import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World34Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269Frame13224
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs34
import BstLean.Part269Rows34
import BstLean.Part269Sources34
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13215
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13215 : scalarRow13215.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13215, BstLean.Part268.grid13215, BstLean.Part263.worldGrid]

theorem supplies13215 (j : Fin 43) : Supply 13215 (parameters j)
    (cellLower scalarRow13215.grid (sourceIndex j))
    (cellUpper scalarRow13215.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13215.grid grid_top_bounds13215 j

theorem radii13215 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13215.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13215 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13215 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13215.grid grid_top_bounds13215 j hθ

noncomputable def covarianceInputs13215 :
    BstLean.Part263.CovarianceInputs 13215 scalarRow13215.grid parameters (caps repair13215) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13215 grid_top_bounds13215 repair13215

noncomputable def covarianceEvent13215 : Set (AgFam 13215) :=
  BstLean.Part263.covarianceEvent 13215 scalarRow13215.grid parameters

theorem covarianceEvent13215_measurable : MeasurableSet covarianceEvent13215 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13215_payment :
    (retDist (paperDesignP 13215).toCentres).real
      (agentEv (paperDesignP 13215) covarianceEvent13215)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13215

theorem localCov13215 : BstLean.Part259.LocalCovarianceOn covarianceEvent13215
    (BstLean.Part263.cell scalarRow13215.grid) (caps repair13215) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13215

theorem covarianceGood13215_payment :
    (retDist (paperDesignP 13215).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13215)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13215_payment



end BstLean.Part269.N13215

namespace BstLean.Part269.N13215
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13215}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13215.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13215) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13215).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13215 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13215) (by norm_num) BstLean.Part268.WorldRow13215.worldPackage rfl
    BstLean.Part268.WorldRow13215.product_lower (BstLean.Part268.WorldRow13215.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13215} (hw : c ∈ Hof BstLean.Part268.WorldRow13215.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13215) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13215) (by norm_num) BstLean.Part268.WorldRow13215.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13215} (hw : c ∈ Hof BstLean.Part268.WorldRow13215.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13215) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13215).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13215) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13215_eq : scalarRow13215.targetFrame = BstLean.Part268.agent13215.frame := by
  norm_num [scalarRow13215,BstLean.Part268.agent13215]

noncomputable def frameData13215 : BstLean.Part264b.FrameData 13215 :=
  BstLean.Part269.frameData_from_numerics (n := 13215) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13215.worldPackage rfl BstLean.Part268.WorldRow13215.product_lower (BstLean.Part268.WorldRow13215.producthi.2.trans (by norm_num))
    scalarRow13215 repair13215 covarianceInputs13215 (fun i hi => sourceNumerics13215 hi)
    BstLean.Part268.agent13215.frame targetFrame13215_eq


end BstLean.Part269.N13215

namespace BstLean.Part269.N13216
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13216 : scalarRow13216.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13216, BstLean.Part268.grid13216, BstLean.Part263.worldGrid]

theorem supplies13216 (j : Fin 43) : Supply 13216 (parameters j)
    (cellLower scalarRow13216.grid (sourceIndex j))
    (cellUpper scalarRow13216.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13216.grid grid_top_bounds13216 j

theorem radii13216 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13216.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13216 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13216 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13216.grid grid_top_bounds13216 j hθ

noncomputable def covarianceInputs13216 :
    BstLean.Part263.CovarianceInputs 13216 scalarRow13216.grid parameters (caps repair13216) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13216 grid_top_bounds13216 repair13216

noncomputable def covarianceEvent13216 : Set (AgFam 13216) :=
  BstLean.Part263.covarianceEvent 13216 scalarRow13216.grid parameters

theorem covarianceEvent13216_measurable : MeasurableSet covarianceEvent13216 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13216_payment :
    (retDist (paperDesignP 13216).toCentres).real
      (agentEv (paperDesignP 13216) covarianceEvent13216)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13216

theorem localCov13216 : BstLean.Part259.LocalCovarianceOn covarianceEvent13216
    (BstLean.Part263.cell scalarRow13216.grid) (caps repair13216) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13216

theorem covarianceGood13216_payment :
    (retDist (paperDesignP 13216).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13216)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13216_payment



end BstLean.Part269.N13216

namespace BstLean.Part269.N13216
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13216}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13216.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13216) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13216).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13216 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13216) (by norm_num) BstLean.Part268.WorldRow13216.worldPackage rfl
    BstLean.Part268.WorldRow13216.product_lower (BstLean.Part268.WorldRow13216.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13216} (hw : c ∈ Hof BstLean.Part268.WorldRow13216.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13216) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13216) (by norm_num) BstLean.Part268.WorldRow13216.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13216} (hw : c ∈ Hof BstLean.Part268.WorldRow13216.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13216) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13216).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13216) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13216_eq : scalarRow13216.targetFrame = BstLean.Part268.agent13216.frame := by
  norm_num [scalarRow13216,BstLean.Part268.agent13216]

noncomputable def frameData13216 : BstLean.Part264b.FrameData 13216 :=
  BstLean.Part269.frameData_from_numerics (n := 13216) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13216.worldPackage rfl BstLean.Part268.WorldRow13216.product_lower (BstLean.Part268.WorldRow13216.producthi.2.trans (by norm_num))
    scalarRow13216 repair13216 covarianceInputs13216 (fun i hi => sourceNumerics13216 hi)
    BstLean.Part268.agent13216.frame targetFrame13216_eq


end BstLean.Part269.N13216

namespace BstLean.Part269.N13217
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13217 : scalarRow13217.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13217, BstLean.Part268.grid13217, BstLean.Part263.worldGrid]

theorem supplies13217 (j : Fin 43) : Supply 13217 (parameters j)
    (cellLower scalarRow13217.grid (sourceIndex j))
    (cellUpper scalarRow13217.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13217.grid grid_top_bounds13217 j

theorem radii13217 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13217.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13217 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13217 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13217.grid grid_top_bounds13217 j hθ

noncomputable def covarianceInputs13217 :
    BstLean.Part263.CovarianceInputs 13217 scalarRow13217.grid parameters (caps repair13217) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13217 grid_top_bounds13217 repair13217

noncomputable def covarianceEvent13217 : Set (AgFam 13217) :=
  BstLean.Part263.covarianceEvent 13217 scalarRow13217.grid parameters

theorem covarianceEvent13217_measurable : MeasurableSet covarianceEvent13217 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13217_payment :
    (retDist (paperDesignP 13217).toCentres).real
      (agentEv (paperDesignP 13217) covarianceEvent13217)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13217

theorem localCov13217 : BstLean.Part259.LocalCovarianceOn covarianceEvent13217
    (BstLean.Part263.cell scalarRow13217.grid) (caps repair13217) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13217

theorem covarianceGood13217_payment :
    (retDist (paperDesignP 13217).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13217)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13217_payment



end BstLean.Part269.N13217

namespace BstLean.Part269.N13217
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13217}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13217.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13217) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13217).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13217 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13217) (by norm_num) BstLean.Part268.WorldRow13217.worldPackage rfl
    BstLean.Part268.WorldRow13217.product_lower (BstLean.Part268.WorldRow13217.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13217} (hw : c ∈ Hof BstLean.Part268.WorldRow13217.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13217) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13217) (by norm_num) BstLean.Part268.WorldRow13217.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13217} (hw : c ∈ Hof BstLean.Part268.WorldRow13217.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13217) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13217).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13217) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13217_eq : scalarRow13217.targetFrame = BstLean.Part268.agent13217.frame := by
  norm_num [scalarRow13217,BstLean.Part268.agent13217]

noncomputable def frameData13217 : BstLean.Part264b.FrameData 13217 :=
  BstLean.Part269.frameData_from_numerics (n := 13217) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13217.worldPackage rfl BstLean.Part268.WorldRow13217.product_lower (BstLean.Part268.WorldRow13217.producthi.2.trans (by norm_num))
    scalarRow13217 repair13217 covarianceInputs13217 (fun i hi => sourceNumerics13217 hi)
    BstLean.Part268.agent13217.frame targetFrame13217_eq


end BstLean.Part269.N13217

namespace BstLean.Part269.N13218
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13218 : scalarRow13218.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13218, BstLean.Part268.grid13218, BstLean.Part263.worldGrid]

theorem supplies13218 (j : Fin 43) : Supply 13218 (parameters j)
    (cellLower scalarRow13218.grid (sourceIndex j))
    (cellUpper scalarRow13218.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13218.grid grid_top_bounds13218 j

theorem radii13218 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13218.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13218 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13218 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13218.grid grid_top_bounds13218 j hθ

noncomputable def covarianceInputs13218 :
    BstLean.Part263.CovarianceInputs 13218 scalarRow13218.grid parameters (caps repair13218) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13218 grid_top_bounds13218 repair13218

noncomputable def covarianceEvent13218 : Set (AgFam 13218) :=
  BstLean.Part263.covarianceEvent 13218 scalarRow13218.grid parameters

theorem covarianceEvent13218_measurable : MeasurableSet covarianceEvent13218 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13218_payment :
    (retDist (paperDesignP 13218).toCentres).real
      (agentEv (paperDesignP 13218) covarianceEvent13218)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13218

theorem localCov13218 : BstLean.Part259.LocalCovarianceOn covarianceEvent13218
    (BstLean.Part263.cell scalarRow13218.grid) (caps repair13218) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13218

theorem covarianceGood13218_payment :
    (retDist (paperDesignP 13218).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13218)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13218_payment



end BstLean.Part269.N13218

namespace BstLean.Part269.N13218
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13218}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13218.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13218) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13218).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13218 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13218) (by norm_num) BstLean.Part268.WorldRow13218.worldPackage rfl
    BstLean.Part268.WorldRow13218.product_lower (BstLean.Part268.WorldRow13218.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13218} (hw : c ∈ Hof BstLean.Part268.WorldRow13218.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13218) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13218) (by norm_num) BstLean.Part268.WorldRow13218.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13218} (hw : c ∈ Hof BstLean.Part268.WorldRow13218.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13218) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13218).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13218) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13218_eq : scalarRow13218.targetFrame = BstLean.Part268.agent13218.frame := by
  norm_num [scalarRow13218,BstLean.Part268.agent13218]

noncomputable def frameData13218 : BstLean.Part264b.FrameData 13218 :=
  BstLean.Part269.frameData_from_numerics (n := 13218) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13218.worldPackage rfl BstLean.Part268.WorldRow13218.product_lower (BstLean.Part268.WorldRow13218.producthi.2.trans (by norm_num))
    scalarRow13218 repair13218 covarianceInputs13218 (fun i hi => sourceNumerics13218 hi)
    BstLean.Part268.agent13218.frame targetFrame13218_eq


end BstLean.Part269.N13218

namespace BstLean.Part269.N13219
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13219 : scalarRow13219.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13219, BstLean.Part268.grid13219, BstLean.Part263.worldGrid]

theorem supplies13219 (j : Fin 43) : Supply 13219 (parameters j)
    (cellLower scalarRow13219.grid (sourceIndex j))
    (cellUpper scalarRow13219.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13219.grid grid_top_bounds13219 j

theorem radii13219 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13219.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13219 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13219 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13219.grid grid_top_bounds13219 j hθ

noncomputable def covarianceInputs13219 :
    BstLean.Part263.CovarianceInputs 13219 scalarRow13219.grid parameters (caps repair13219) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13219 grid_top_bounds13219 repair13219

noncomputable def covarianceEvent13219 : Set (AgFam 13219) :=
  BstLean.Part263.covarianceEvent 13219 scalarRow13219.grid parameters

theorem covarianceEvent13219_measurable : MeasurableSet covarianceEvent13219 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13219_payment :
    (retDist (paperDesignP 13219).toCentres).real
      (agentEv (paperDesignP 13219) covarianceEvent13219)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13219

theorem localCov13219 : BstLean.Part259.LocalCovarianceOn covarianceEvent13219
    (BstLean.Part263.cell scalarRow13219.grid) (caps repair13219) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13219

theorem covarianceGood13219_payment :
    (retDist (paperDesignP 13219).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13219)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13219_payment



end BstLean.Part269.N13219

namespace BstLean.Part269.N13219
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13219}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13219.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13219) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13219).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13219 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13219) (by norm_num) BstLean.Part268.WorldRow13219.worldPackage rfl
    BstLean.Part268.WorldRow13219.product_lower (BstLean.Part268.WorldRow13219.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13219} (hw : c ∈ Hof BstLean.Part268.WorldRow13219.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13219) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13219) (by norm_num) BstLean.Part268.WorldRow13219.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13219} (hw : c ∈ Hof BstLean.Part268.WorldRow13219.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13219) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13219).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13219) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13219_eq : scalarRow13219.targetFrame = BstLean.Part268.agent13219.frame := by
  norm_num [scalarRow13219,BstLean.Part268.agent13219]

noncomputable def frameData13219 : BstLean.Part264b.FrameData 13219 :=
  BstLean.Part269.frameData_from_numerics (n := 13219) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13219.worldPackage rfl BstLean.Part268.WorldRow13219.product_lower (BstLean.Part268.WorldRow13219.producthi.2.trans (by norm_num))
    scalarRow13219 repair13219 covarianceInputs13219 (fun i hi => sourceNumerics13219 hi)
    BstLean.Part268.agent13219.frame targetFrame13219_eq


end BstLean.Part269.N13219
