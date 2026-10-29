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

namespace BstLean.Part269.N13075
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13075 : scalarRow13075.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13075, BstLean.Part268.grid13075, BstLean.Part263.worldGrid]

theorem supplies13075 (j : Fin 43) : Supply 13075 (parameters j)
    (cellLower scalarRow13075.grid (sourceIndex j))
    (cellUpper scalarRow13075.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13075.grid grid_top_bounds13075 j

theorem radii13075 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13075.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13075 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13075 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13075.grid grid_top_bounds13075 j hθ

noncomputable def covarianceInputs13075 :
    BstLean.Part263.CovarianceInputs 13075 scalarRow13075.grid parameters (caps repair13075) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13075 grid_top_bounds13075 repair13075

noncomputable def covarianceEvent13075 : Set (AgFam 13075) :=
  BstLean.Part263.covarianceEvent 13075 scalarRow13075.grid parameters

theorem covarianceEvent13075_measurable : MeasurableSet covarianceEvent13075 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13075_payment :
    (retDist (paperDesignP 13075).toCentres).real
      (agentEv (paperDesignP 13075) covarianceEvent13075)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13075

theorem localCov13075 : BstLean.Part259.LocalCovarianceOn covarianceEvent13075
    (BstLean.Part263.cell scalarRow13075.grid) (caps repair13075) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13075

theorem covarianceGood13075_payment :
    (retDist (paperDesignP 13075).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13075)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13075_payment



end BstLean.Part269.N13075

namespace BstLean.Part269.N13075
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13075}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13075.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13075) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13075).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13075 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13075) (by norm_num) BstLean.Part268.WorldRow13075.worldPackage rfl
    BstLean.Part268.WorldRow13075.product_lower (BstLean.Part268.WorldRow13075.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13075} (hw : c ∈ Hof BstLean.Part268.WorldRow13075.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13075) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13075) (by norm_num) BstLean.Part268.WorldRow13075.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13075} (hw : c ∈ Hof BstLean.Part268.WorldRow13075.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13075) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13075).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13075) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13075_eq : scalarRow13075.targetFrame = BstLean.Part268.agent13075.frame := by
  norm_num [scalarRow13075,BstLean.Part268.agent13075]

noncomputable def frameData13075 : BstLean.Part264b.FrameData 13075 :=
  BstLean.Part269.frameData_from_numerics (n := 13075) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13075.worldPackage rfl BstLean.Part268.WorldRow13075.product_lower (BstLean.Part268.WorldRow13075.producthi.2.trans (by norm_num))
    scalarRow13075 repair13075 covarianceInputs13075 (fun i hi => sourceNumerics13075 hi)
    BstLean.Part268.agent13075.frame targetFrame13075_eq


end BstLean.Part269.N13075

namespace BstLean.Part269.N13076
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13076 : scalarRow13076.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13076, BstLean.Part268.grid13076, BstLean.Part263.worldGrid]

theorem supplies13076 (j : Fin 43) : Supply 13076 (parameters j)
    (cellLower scalarRow13076.grid (sourceIndex j))
    (cellUpper scalarRow13076.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13076.grid grid_top_bounds13076 j

theorem radii13076 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13076.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13076 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13076 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13076.grid grid_top_bounds13076 j hθ

noncomputable def covarianceInputs13076 :
    BstLean.Part263.CovarianceInputs 13076 scalarRow13076.grid parameters (caps repair13076) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13076 grid_top_bounds13076 repair13076

noncomputable def covarianceEvent13076 : Set (AgFam 13076) :=
  BstLean.Part263.covarianceEvent 13076 scalarRow13076.grid parameters

theorem covarianceEvent13076_measurable : MeasurableSet covarianceEvent13076 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13076_payment :
    (retDist (paperDesignP 13076).toCentres).real
      (agentEv (paperDesignP 13076) covarianceEvent13076)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13076

theorem localCov13076 : BstLean.Part259.LocalCovarianceOn covarianceEvent13076
    (BstLean.Part263.cell scalarRow13076.grid) (caps repair13076) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13076

theorem covarianceGood13076_payment :
    (retDist (paperDesignP 13076).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13076)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13076_payment



end BstLean.Part269.N13076

namespace BstLean.Part269.N13076
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13076}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13076.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13076) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13076).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13076 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13076) (by norm_num) BstLean.Part268.WorldRow13076.worldPackage rfl
    BstLean.Part268.WorldRow13076.product_lower (BstLean.Part268.WorldRow13076.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13076} (hw : c ∈ Hof BstLean.Part268.WorldRow13076.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13076) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13076) (by norm_num) BstLean.Part268.WorldRow13076.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13076} (hw : c ∈ Hof BstLean.Part268.WorldRow13076.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13076) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13076).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13076) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13076_eq : scalarRow13076.targetFrame = BstLean.Part268.agent13076.frame := by
  norm_num [scalarRow13076,BstLean.Part268.agent13076]

noncomputable def frameData13076 : BstLean.Part264b.FrameData 13076 :=
  BstLean.Part269.frameData_from_numerics (n := 13076) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13076.worldPackage rfl BstLean.Part268.WorldRow13076.product_lower (BstLean.Part268.WorldRow13076.producthi.2.trans (by norm_num))
    scalarRow13076 repair13076 covarianceInputs13076 (fun i hi => sourceNumerics13076 hi)
    BstLean.Part268.agent13076.frame targetFrame13076_eq


end BstLean.Part269.N13076

namespace BstLean.Part269.N13077
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13077 : scalarRow13077.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13077, BstLean.Part268.grid13077, BstLean.Part263.worldGrid]

theorem supplies13077 (j : Fin 43) : Supply 13077 (parameters j)
    (cellLower scalarRow13077.grid (sourceIndex j))
    (cellUpper scalarRow13077.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13077.grid grid_top_bounds13077 j

theorem radii13077 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13077.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13077 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13077 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13077.grid grid_top_bounds13077 j hθ

noncomputable def covarianceInputs13077 :
    BstLean.Part263.CovarianceInputs 13077 scalarRow13077.grid parameters (caps repair13077) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13077 grid_top_bounds13077 repair13077

noncomputable def covarianceEvent13077 : Set (AgFam 13077) :=
  BstLean.Part263.covarianceEvent 13077 scalarRow13077.grid parameters

theorem covarianceEvent13077_measurable : MeasurableSet covarianceEvent13077 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13077_payment :
    (retDist (paperDesignP 13077).toCentres).real
      (agentEv (paperDesignP 13077) covarianceEvent13077)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13077

theorem localCov13077 : BstLean.Part259.LocalCovarianceOn covarianceEvent13077
    (BstLean.Part263.cell scalarRow13077.grid) (caps repair13077) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13077

theorem covarianceGood13077_payment :
    (retDist (paperDesignP 13077).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13077)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13077_payment



end BstLean.Part269.N13077

namespace BstLean.Part269.N13077
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13077}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13077.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13077) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13077).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13077 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13077) (by norm_num) BstLean.Part268.WorldRow13077.worldPackage rfl
    BstLean.Part268.WorldRow13077.product_lower (BstLean.Part268.WorldRow13077.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13077} (hw : c ∈ Hof BstLean.Part268.WorldRow13077.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13077) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13077) (by norm_num) BstLean.Part268.WorldRow13077.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13077} (hw : c ∈ Hof BstLean.Part268.WorldRow13077.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13077) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13077).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13077) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13077_eq : scalarRow13077.targetFrame = BstLean.Part268.agent13077.frame := by
  norm_num [scalarRow13077,BstLean.Part268.agent13077]

noncomputable def frameData13077 : BstLean.Part264b.FrameData 13077 :=
  BstLean.Part269.frameData_from_numerics (n := 13077) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13077.worldPackage rfl BstLean.Part268.WorldRow13077.product_lower (BstLean.Part268.WorldRow13077.producthi.2.trans (by norm_num))
    scalarRow13077 repair13077 covarianceInputs13077 (fun i hi => sourceNumerics13077 hi)
    BstLean.Part268.agent13077.frame targetFrame13077_eq


end BstLean.Part269.N13077

namespace BstLean.Part269.N13078
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13078 : scalarRow13078.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13078, BstLean.Part268.grid13078, BstLean.Part263.worldGrid]

theorem supplies13078 (j : Fin 43) : Supply 13078 (parameters j)
    (cellLower scalarRow13078.grid (sourceIndex j))
    (cellUpper scalarRow13078.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13078.grid grid_top_bounds13078 j

theorem radii13078 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13078.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13078 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13078 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13078.grid grid_top_bounds13078 j hθ

noncomputable def covarianceInputs13078 :
    BstLean.Part263.CovarianceInputs 13078 scalarRow13078.grid parameters (caps repair13078) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13078 grid_top_bounds13078 repair13078

noncomputable def covarianceEvent13078 : Set (AgFam 13078) :=
  BstLean.Part263.covarianceEvent 13078 scalarRow13078.grid parameters

theorem covarianceEvent13078_measurable : MeasurableSet covarianceEvent13078 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13078_payment :
    (retDist (paperDesignP 13078).toCentres).real
      (agentEv (paperDesignP 13078) covarianceEvent13078)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13078

theorem localCov13078 : BstLean.Part259.LocalCovarianceOn covarianceEvent13078
    (BstLean.Part263.cell scalarRow13078.grid) (caps repair13078) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13078

theorem covarianceGood13078_payment :
    (retDist (paperDesignP 13078).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13078)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13078_payment



end BstLean.Part269.N13078

namespace BstLean.Part269.N13078
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13078}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13078.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13078) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13078).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13078 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13078) (by norm_num) BstLean.Part268.WorldRow13078.worldPackage rfl
    BstLean.Part268.WorldRow13078.product_lower (BstLean.Part268.WorldRow13078.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13078} (hw : c ∈ Hof BstLean.Part268.WorldRow13078.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13078) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13078) (by norm_num) BstLean.Part268.WorldRow13078.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13078} (hw : c ∈ Hof BstLean.Part268.WorldRow13078.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13078) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13078).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13078) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13078_eq : scalarRow13078.targetFrame = BstLean.Part268.agent13078.frame := by
  norm_num [scalarRow13078,BstLean.Part268.agent13078]

noncomputable def frameData13078 : BstLean.Part264b.FrameData 13078 :=
  BstLean.Part269.frameData_from_numerics (n := 13078) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13078.worldPackage rfl BstLean.Part268.WorldRow13078.product_lower (BstLean.Part268.WorldRow13078.producthi.2.trans (by norm_num))
    scalarRow13078 repair13078 covarianceInputs13078 (fun i hi => sourceNumerics13078 hi)
    BstLean.Part268.agent13078.frame targetFrame13078_eq


end BstLean.Part269.N13078

namespace BstLean.Part269.N13079
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13079 : scalarRow13079.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13079, BstLean.Part268.grid13079, BstLean.Part263.worldGrid]

theorem supplies13079 (j : Fin 43) : Supply 13079 (parameters j)
    (cellLower scalarRow13079.grid (sourceIndex j))
    (cellUpper scalarRow13079.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13079.grid grid_top_bounds13079 j

theorem radii13079 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13079.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13079 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13079 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13079.grid grid_top_bounds13079 j hθ

noncomputable def covarianceInputs13079 :
    BstLean.Part263.CovarianceInputs 13079 scalarRow13079.grid parameters (caps repair13079) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13079 grid_top_bounds13079 repair13079

noncomputable def covarianceEvent13079 : Set (AgFam 13079) :=
  BstLean.Part263.covarianceEvent 13079 scalarRow13079.grid parameters

theorem covarianceEvent13079_measurable : MeasurableSet covarianceEvent13079 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13079_payment :
    (retDist (paperDesignP 13079).toCentres).real
      (agentEv (paperDesignP 13079) covarianceEvent13079)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13079

theorem localCov13079 : BstLean.Part259.LocalCovarianceOn covarianceEvent13079
    (BstLean.Part263.cell scalarRow13079.grid) (caps repair13079) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13079

theorem covarianceGood13079_payment :
    (retDist (paperDesignP 13079).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13079)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13079_payment



end BstLean.Part269.N13079

namespace BstLean.Part269.N13079
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13079}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13079.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13079) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13079).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13079 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13079) (by norm_num) BstLean.Part268.WorldRow13079.worldPackage rfl
    BstLean.Part268.WorldRow13079.product_lower (BstLean.Part268.WorldRow13079.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13079} (hw : c ∈ Hof BstLean.Part268.WorldRow13079.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13079) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13079) (by norm_num) BstLean.Part268.WorldRow13079.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13079} (hw : c ∈ Hof BstLean.Part268.WorldRow13079.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13079) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13079).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13079) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13079_eq : scalarRow13079.targetFrame = BstLean.Part268.agent13079.frame := by
  norm_num [scalarRow13079,BstLean.Part268.agent13079]

noncomputable def frameData13079 : BstLean.Part264b.FrameData 13079 :=
  BstLean.Part269.frameData_from_numerics (n := 13079) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13079.worldPackage rfl BstLean.Part268.WorldRow13079.product_lower (BstLean.Part268.WorldRow13079.producthi.2.trans (by norm_num))
    scalarRow13079 repair13079 covarianceInputs13079 (fun i hi => sourceNumerics13079 hi)
    BstLean.Part268.agent13079.frame targetFrame13079_eq


end BstLean.Part269.N13079
