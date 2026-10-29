import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World28Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs28
import BstLean.Part269Rows28
import BstLean.Part269Sources28
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13055
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13055 : scalarRow13055.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13055, BstLean.Part268.grid13055, BstLean.Part263.worldGrid]

theorem supplies13055 (j : Fin 43) : Supply 13055 (parameters j)
    (cellLower scalarRow13055.grid (sourceIndex j))
    (cellUpper scalarRow13055.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13055.grid grid_top_bounds13055 j

theorem radii13055 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13055.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13055 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13055 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13055.grid grid_top_bounds13055 j hθ

noncomputable def covarianceInputs13055 :
    BstLean.Part263.CovarianceInputs 13055 scalarRow13055.grid parameters (caps repair13055) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13055 grid_top_bounds13055 repair13055

noncomputable def covarianceEvent13055 : Set (AgFam 13055) :=
  BstLean.Part263.covarianceEvent 13055 scalarRow13055.grid parameters

theorem covarianceEvent13055_measurable : MeasurableSet covarianceEvent13055 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13055_payment :
    (retDist (paperDesignP 13055).toCentres).real
      (agentEv (paperDesignP 13055) covarianceEvent13055)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13055

theorem localCov13055 : BstLean.Part259.LocalCovarianceOn covarianceEvent13055
    (BstLean.Part263.cell scalarRow13055.grid) (caps repair13055) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13055

theorem covarianceGood13055_payment :
    (retDist (paperDesignP 13055).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13055)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13055_payment



end BstLean.Part269.N13055

namespace BstLean.Part269.N13055
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13055}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13055.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13055) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13055).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13055 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13055) (by norm_num) BstLean.Part268.WorldRow13055.worldPackage rfl
    BstLean.Part268.WorldRow13055.product_lower (BstLean.Part268.WorldRow13055.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13055} (hw : c ∈ Hof BstLean.Part268.WorldRow13055.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13055) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13055) (by norm_num) BstLean.Part268.WorldRow13055.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13055} (hw : c ∈ Hof BstLean.Part268.WorldRow13055.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13055) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13055).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13055) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13055_eq : scalarRow13055.targetFrame = BstLean.Part268.agent13055.frame := by
  norm_num [scalarRow13055,BstLean.Part268.agent13055]

noncomputable def frameData13055 : BstLean.Part264b.FrameData 13055 :=
  BstLean.Part269.frameData_from_numerics (n := 13055) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13055.worldPackage rfl BstLean.Part268.WorldRow13055.product_lower (BstLean.Part268.WorldRow13055.producthi.2.trans (by norm_num))
    scalarRow13055 repair13055 covarianceInputs13055 (fun i hi => sourceNumerics13055 hi)
    BstLean.Part268.agent13055.frame targetFrame13055_eq


end BstLean.Part269.N13055

namespace BstLean.Part269.N13056
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13056 : scalarRow13056.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13056, BstLean.Part268.grid13056, BstLean.Part263.worldGrid]

theorem supplies13056 (j : Fin 43) : Supply 13056 (parameters j)
    (cellLower scalarRow13056.grid (sourceIndex j))
    (cellUpper scalarRow13056.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13056.grid grid_top_bounds13056 j

theorem radii13056 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13056.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13056 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13056 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13056.grid grid_top_bounds13056 j hθ

noncomputable def covarianceInputs13056 :
    BstLean.Part263.CovarianceInputs 13056 scalarRow13056.grid parameters (caps repair13056) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13056 grid_top_bounds13056 repair13056

noncomputable def covarianceEvent13056 : Set (AgFam 13056) :=
  BstLean.Part263.covarianceEvent 13056 scalarRow13056.grid parameters

theorem covarianceEvent13056_measurable : MeasurableSet covarianceEvent13056 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13056_payment :
    (retDist (paperDesignP 13056).toCentres).real
      (agentEv (paperDesignP 13056) covarianceEvent13056)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13056

theorem localCov13056 : BstLean.Part259.LocalCovarianceOn covarianceEvent13056
    (BstLean.Part263.cell scalarRow13056.grid) (caps repair13056) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13056

theorem covarianceGood13056_payment :
    (retDist (paperDesignP 13056).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13056)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13056_payment



end BstLean.Part269.N13056

namespace BstLean.Part269.N13056
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13056}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13056.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13056) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13056).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13056 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13056) (by norm_num) BstLean.Part268.WorldRow13056.worldPackage rfl
    BstLean.Part268.WorldRow13056.product_lower (BstLean.Part268.WorldRow13056.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13056} (hw : c ∈ Hof BstLean.Part268.WorldRow13056.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13056) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13056) (by norm_num) BstLean.Part268.WorldRow13056.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13056} (hw : c ∈ Hof BstLean.Part268.WorldRow13056.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13056) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13056).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13056) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13056_eq : scalarRow13056.targetFrame = BstLean.Part268.agent13056.frame := by
  norm_num [scalarRow13056,BstLean.Part268.agent13056]

noncomputable def frameData13056 : BstLean.Part264b.FrameData 13056 :=
  BstLean.Part269.frameData_from_numerics (n := 13056) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13056.worldPackage rfl BstLean.Part268.WorldRow13056.product_lower (BstLean.Part268.WorldRow13056.producthi.2.trans (by norm_num))
    scalarRow13056 repair13056 covarianceInputs13056 (fun i hi => sourceNumerics13056 hi)
    BstLean.Part268.agent13056.frame targetFrame13056_eq


end BstLean.Part269.N13056

namespace BstLean.Part269.N13057
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13057 : scalarRow13057.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13057, BstLean.Part268.grid13057, BstLean.Part263.worldGrid]

theorem supplies13057 (j : Fin 43) : Supply 13057 (parameters j)
    (cellLower scalarRow13057.grid (sourceIndex j))
    (cellUpper scalarRow13057.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13057.grid grid_top_bounds13057 j

theorem radii13057 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13057.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13057 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13057 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13057.grid grid_top_bounds13057 j hθ

noncomputable def covarianceInputs13057 :
    BstLean.Part263.CovarianceInputs 13057 scalarRow13057.grid parameters (caps repair13057) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13057 grid_top_bounds13057 repair13057

noncomputable def covarianceEvent13057 : Set (AgFam 13057) :=
  BstLean.Part263.covarianceEvent 13057 scalarRow13057.grid parameters

theorem covarianceEvent13057_measurable : MeasurableSet covarianceEvent13057 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13057_payment :
    (retDist (paperDesignP 13057).toCentres).real
      (agentEv (paperDesignP 13057) covarianceEvent13057)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13057

theorem localCov13057 : BstLean.Part259.LocalCovarianceOn covarianceEvent13057
    (BstLean.Part263.cell scalarRow13057.grid) (caps repair13057) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13057

theorem covarianceGood13057_payment :
    (retDist (paperDesignP 13057).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13057)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13057_payment



end BstLean.Part269.N13057

namespace BstLean.Part269.N13057
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13057}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13057.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13057) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13057).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13057 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13057) (by norm_num) BstLean.Part268.WorldRow13057.worldPackage rfl
    BstLean.Part268.WorldRow13057.product_lower (BstLean.Part268.WorldRow13057.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13057} (hw : c ∈ Hof BstLean.Part268.WorldRow13057.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13057) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13057) (by norm_num) BstLean.Part268.WorldRow13057.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13057} (hw : c ∈ Hof BstLean.Part268.WorldRow13057.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13057) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13057).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13057) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13057_eq : scalarRow13057.targetFrame = BstLean.Part268.agent13057.frame := by
  norm_num [scalarRow13057,BstLean.Part268.agent13057]

noncomputable def frameData13057 : BstLean.Part264b.FrameData 13057 :=
  BstLean.Part269.frameData_from_numerics (n := 13057) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13057.worldPackage rfl BstLean.Part268.WorldRow13057.product_lower (BstLean.Part268.WorldRow13057.producthi.2.trans (by norm_num))
    scalarRow13057 repair13057 covarianceInputs13057 (fun i hi => sourceNumerics13057 hi)
    BstLean.Part268.agent13057.frame targetFrame13057_eq


end BstLean.Part269.N13057

namespace BstLean.Part269.N13058
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13058 : scalarRow13058.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13058, BstLean.Part268.grid13058, BstLean.Part263.worldGrid]

theorem supplies13058 (j : Fin 43) : Supply 13058 (parameters j)
    (cellLower scalarRow13058.grid (sourceIndex j))
    (cellUpper scalarRow13058.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13058.grid grid_top_bounds13058 j

theorem radii13058 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13058.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13058 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13058 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13058.grid grid_top_bounds13058 j hθ

noncomputable def covarianceInputs13058 :
    BstLean.Part263.CovarianceInputs 13058 scalarRow13058.grid parameters (caps repair13058) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13058 grid_top_bounds13058 repair13058

noncomputable def covarianceEvent13058 : Set (AgFam 13058) :=
  BstLean.Part263.covarianceEvent 13058 scalarRow13058.grid parameters

theorem covarianceEvent13058_measurable : MeasurableSet covarianceEvent13058 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13058_payment :
    (retDist (paperDesignP 13058).toCentres).real
      (agentEv (paperDesignP 13058) covarianceEvent13058)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13058

theorem localCov13058 : BstLean.Part259.LocalCovarianceOn covarianceEvent13058
    (BstLean.Part263.cell scalarRow13058.grid) (caps repair13058) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13058

theorem covarianceGood13058_payment :
    (retDist (paperDesignP 13058).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13058)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13058_payment



end BstLean.Part269.N13058

namespace BstLean.Part269.N13058
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13058}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13058.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13058) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13058).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13058 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13058) (by norm_num) BstLean.Part268.WorldRow13058.worldPackage rfl
    BstLean.Part268.WorldRow13058.product_lower (BstLean.Part268.WorldRow13058.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13058} (hw : c ∈ Hof BstLean.Part268.WorldRow13058.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13058) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13058) (by norm_num) BstLean.Part268.WorldRow13058.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13058} (hw : c ∈ Hof BstLean.Part268.WorldRow13058.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13058) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13058).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13058) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13058_eq : scalarRow13058.targetFrame = BstLean.Part268.agent13058.frame := by
  norm_num [scalarRow13058,BstLean.Part268.agent13058]

noncomputable def frameData13058 : BstLean.Part264b.FrameData 13058 :=
  BstLean.Part269.frameData_from_numerics (n := 13058) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13058.worldPackage rfl BstLean.Part268.WorldRow13058.product_lower (BstLean.Part268.WorldRow13058.producthi.2.trans (by norm_num))
    scalarRow13058 repair13058 covarianceInputs13058 (fun i hi => sourceNumerics13058 hi)
    BstLean.Part268.agent13058.frame targetFrame13058_eq


end BstLean.Part269.N13058

namespace BstLean.Part269.N13059
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13059 : scalarRow13059.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13059, BstLean.Part268.grid13059, BstLean.Part263.worldGrid]

theorem supplies13059 (j : Fin 43) : Supply 13059 (parameters j)
    (cellLower scalarRow13059.grid (sourceIndex j))
    (cellUpper scalarRow13059.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13059.grid grid_top_bounds13059 j

theorem radii13059 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13059.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13059 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13059 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13059.grid grid_top_bounds13059 j hθ

noncomputable def covarianceInputs13059 :
    BstLean.Part263.CovarianceInputs 13059 scalarRow13059.grid parameters (caps repair13059) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13059 grid_top_bounds13059 repair13059

noncomputable def covarianceEvent13059 : Set (AgFam 13059) :=
  BstLean.Part263.covarianceEvent 13059 scalarRow13059.grid parameters

theorem covarianceEvent13059_measurable : MeasurableSet covarianceEvent13059 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13059_payment :
    (retDist (paperDesignP 13059).toCentres).real
      (agentEv (paperDesignP 13059) covarianceEvent13059)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13059

theorem localCov13059 : BstLean.Part259.LocalCovarianceOn covarianceEvent13059
    (BstLean.Part263.cell scalarRow13059.grid) (caps repair13059) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13059

theorem covarianceGood13059_payment :
    (retDist (paperDesignP 13059).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13059)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13059_payment



end BstLean.Part269.N13059

namespace BstLean.Part269.N13059
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13059}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13059.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13059) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13059).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13059 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13059) (by norm_num) BstLean.Part268.WorldRow13059.worldPackage rfl
    BstLean.Part268.WorldRow13059.product_lower (BstLean.Part268.WorldRow13059.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13059} (hw : c ∈ Hof BstLean.Part268.WorldRow13059.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13059) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13059) (by norm_num) BstLean.Part268.WorldRow13059.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13059} (hw : c ∈ Hof BstLean.Part268.WorldRow13059.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13059) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13059).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13059) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13059_eq : scalarRow13059.targetFrame = BstLean.Part268.agent13059.frame := by
  norm_num [scalarRow13059,BstLean.Part268.agent13059]

noncomputable def frameData13059 : BstLean.Part264b.FrameData 13059 :=
  BstLean.Part269.frameData_from_numerics (n := 13059) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13059.worldPackage rfl BstLean.Part268.WorldRow13059.product_lower (BstLean.Part268.WorldRow13059.producthi.2.trans (by norm_num))
    scalarRow13059 repair13059 covarianceInputs13059 (fun i hi => sourceNumerics13059 hi)
    BstLean.Part268.agent13059.frame targetFrame13059_eq


end BstLean.Part269.N13059
