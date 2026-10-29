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

namespace BstLean.Part269.N13095
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13095 : scalarRow13095.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13095, BstLean.Part268.grid13095, BstLean.Part263.worldGrid]

theorem supplies13095 (j : Fin 43) : Supply 13095 (parameters j)
    (cellLower scalarRow13095.grid (sourceIndex j))
    (cellUpper scalarRow13095.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13095.grid grid_top_bounds13095 j

theorem radii13095 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13095.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13095 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13095 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13095.grid grid_top_bounds13095 j hθ

noncomputable def covarianceInputs13095 :
    BstLean.Part263.CovarianceInputs 13095 scalarRow13095.grid parameters (caps repair13095) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13095 grid_top_bounds13095 repair13095

noncomputable def covarianceEvent13095 : Set (AgFam 13095) :=
  BstLean.Part263.covarianceEvent 13095 scalarRow13095.grid parameters

theorem covarianceEvent13095_measurable : MeasurableSet covarianceEvent13095 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13095_payment :
    (retDist (paperDesignP 13095).toCentres).real
      (agentEv (paperDesignP 13095) covarianceEvent13095)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13095

theorem localCov13095 : BstLean.Part259.LocalCovarianceOn covarianceEvent13095
    (BstLean.Part263.cell scalarRow13095.grid) (caps repair13095) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13095

theorem covarianceGood13095_payment :
    (retDist (paperDesignP 13095).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13095)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13095_payment



end BstLean.Part269.N13095

namespace BstLean.Part269.N13095
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13095}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13095.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13095) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13095).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13095 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13095) (by norm_num) BstLean.Part268.WorldRow13095.worldPackage rfl
    BstLean.Part268.WorldRow13095.product_lower (BstLean.Part268.WorldRow13095.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13095} (hw : c ∈ Hof BstLean.Part268.WorldRow13095.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13095) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13095) (by norm_num) BstLean.Part268.WorldRow13095.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13095} (hw : c ∈ Hof BstLean.Part268.WorldRow13095.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13095) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13095).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13095) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13095_eq : scalarRow13095.targetFrame = BstLean.Part268.agent13095.frame := by
  norm_num [scalarRow13095,BstLean.Part268.agent13095]

noncomputable def frameData13095 : BstLean.Part264b.FrameData 13095 :=
  BstLean.Part269.frameData_from_numerics (n := 13095) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13095.worldPackage rfl BstLean.Part268.WorldRow13095.product_lower (BstLean.Part268.WorldRow13095.producthi.2.trans (by norm_num))
    scalarRow13095 repair13095 covarianceInputs13095 (fun i hi => sourceNumerics13095 hi)
    BstLean.Part268.agent13095.frame targetFrame13095_eq


end BstLean.Part269.N13095

namespace BstLean.Part269.N13096
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13096 : scalarRow13096.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13096, BstLean.Part268.grid13096, BstLean.Part263.worldGrid]

theorem supplies13096 (j : Fin 43) : Supply 13096 (parameters j)
    (cellLower scalarRow13096.grid (sourceIndex j))
    (cellUpper scalarRow13096.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13096.grid grid_top_bounds13096 j

theorem radii13096 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13096.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13096 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13096 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13096.grid grid_top_bounds13096 j hθ

noncomputable def covarianceInputs13096 :
    BstLean.Part263.CovarianceInputs 13096 scalarRow13096.grid parameters (caps repair13096) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13096 grid_top_bounds13096 repair13096

noncomputable def covarianceEvent13096 : Set (AgFam 13096) :=
  BstLean.Part263.covarianceEvent 13096 scalarRow13096.grid parameters

theorem covarianceEvent13096_measurable : MeasurableSet covarianceEvent13096 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13096_payment :
    (retDist (paperDesignP 13096).toCentres).real
      (agentEv (paperDesignP 13096) covarianceEvent13096)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13096

theorem localCov13096 : BstLean.Part259.LocalCovarianceOn covarianceEvent13096
    (BstLean.Part263.cell scalarRow13096.grid) (caps repair13096) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13096

theorem covarianceGood13096_payment :
    (retDist (paperDesignP 13096).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13096)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13096_payment



end BstLean.Part269.N13096

namespace BstLean.Part269.N13096
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13096}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13096.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13096) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13096).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13096 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13096) (by norm_num) BstLean.Part268.WorldRow13096.worldPackage rfl
    BstLean.Part268.WorldRow13096.product_lower (BstLean.Part268.WorldRow13096.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13096} (hw : c ∈ Hof BstLean.Part268.WorldRow13096.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13096) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13096) (by norm_num) BstLean.Part268.WorldRow13096.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13096} (hw : c ∈ Hof BstLean.Part268.WorldRow13096.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13096) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13096).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13096) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13096_eq : scalarRow13096.targetFrame = BstLean.Part268.agent13096.frame := by
  norm_num [scalarRow13096,BstLean.Part268.agent13096]

noncomputable def frameData13096 : BstLean.Part264b.FrameData 13096 :=
  BstLean.Part269.frameData_from_numerics (n := 13096) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13096.worldPackage rfl BstLean.Part268.WorldRow13096.product_lower (BstLean.Part268.WorldRow13096.producthi.2.trans (by norm_num))
    scalarRow13096 repair13096 covarianceInputs13096 (fun i hi => sourceNumerics13096 hi)
    BstLean.Part268.agent13096.frame targetFrame13096_eq


end BstLean.Part269.N13096

namespace BstLean.Part269.N13097
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13097 : scalarRow13097.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13097, BstLean.Part268.grid13097, BstLean.Part263.worldGrid]

theorem supplies13097 (j : Fin 43) : Supply 13097 (parameters j)
    (cellLower scalarRow13097.grid (sourceIndex j))
    (cellUpper scalarRow13097.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13097.grid grid_top_bounds13097 j

theorem radii13097 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13097.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13097 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13097 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13097.grid grid_top_bounds13097 j hθ

noncomputable def covarianceInputs13097 :
    BstLean.Part263.CovarianceInputs 13097 scalarRow13097.grid parameters (caps repair13097) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13097 grid_top_bounds13097 repair13097

noncomputable def covarianceEvent13097 : Set (AgFam 13097) :=
  BstLean.Part263.covarianceEvent 13097 scalarRow13097.grid parameters

theorem covarianceEvent13097_measurable : MeasurableSet covarianceEvent13097 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13097_payment :
    (retDist (paperDesignP 13097).toCentres).real
      (agentEv (paperDesignP 13097) covarianceEvent13097)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13097

theorem localCov13097 : BstLean.Part259.LocalCovarianceOn covarianceEvent13097
    (BstLean.Part263.cell scalarRow13097.grid) (caps repair13097) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13097

theorem covarianceGood13097_payment :
    (retDist (paperDesignP 13097).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13097)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13097_payment



end BstLean.Part269.N13097

namespace BstLean.Part269.N13097
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13097}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13097.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13097) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13097).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13097 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13097) (by norm_num) BstLean.Part268.WorldRow13097.worldPackage rfl
    BstLean.Part268.WorldRow13097.product_lower (BstLean.Part268.WorldRow13097.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13097} (hw : c ∈ Hof BstLean.Part268.WorldRow13097.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13097) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13097) (by norm_num) BstLean.Part268.WorldRow13097.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13097} (hw : c ∈ Hof BstLean.Part268.WorldRow13097.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13097) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13097).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13097) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13097_eq : scalarRow13097.targetFrame = BstLean.Part268.agent13097.frame := by
  norm_num [scalarRow13097,BstLean.Part268.agent13097]

noncomputable def frameData13097 : BstLean.Part264b.FrameData 13097 :=
  BstLean.Part269.frameData_from_numerics (n := 13097) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13097.worldPackage rfl BstLean.Part268.WorldRow13097.product_lower (BstLean.Part268.WorldRow13097.producthi.2.trans (by norm_num))
    scalarRow13097 repair13097 covarianceInputs13097 (fun i hi => sourceNumerics13097 hi)
    BstLean.Part268.agent13097.frame targetFrame13097_eq


end BstLean.Part269.N13097

namespace BstLean.Part269.N13098
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13098 : scalarRow13098.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13098, BstLean.Part268.grid13098, BstLean.Part263.worldGrid]

theorem supplies13098 (j : Fin 43) : Supply 13098 (parameters j)
    (cellLower scalarRow13098.grid (sourceIndex j))
    (cellUpper scalarRow13098.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13098.grid grid_top_bounds13098 j

theorem radii13098 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13098.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13098 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13098 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13098.grid grid_top_bounds13098 j hθ

noncomputable def covarianceInputs13098 :
    BstLean.Part263.CovarianceInputs 13098 scalarRow13098.grid parameters (caps repair13098) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13098 grid_top_bounds13098 repair13098

noncomputable def covarianceEvent13098 : Set (AgFam 13098) :=
  BstLean.Part263.covarianceEvent 13098 scalarRow13098.grid parameters

theorem covarianceEvent13098_measurable : MeasurableSet covarianceEvent13098 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13098_payment :
    (retDist (paperDesignP 13098).toCentres).real
      (agentEv (paperDesignP 13098) covarianceEvent13098)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13098

theorem localCov13098 : BstLean.Part259.LocalCovarianceOn covarianceEvent13098
    (BstLean.Part263.cell scalarRow13098.grid) (caps repair13098) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13098

theorem covarianceGood13098_payment :
    (retDist (paperDesignP 13098).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13098)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13098_payment



end BstLean.Part269.N13098

namespace BstLean.Part269.N13098
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13098}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13098.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13098) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13098).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13098 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13098) (by norm_num) BstLean.Part268.WorldRow13098.worldPackage rfl
    BstLean.Part268.WorldRow13098.product_lower (BstLean.Part268.WorldRow13098.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13098} (hw : c ∈ Hof BstLean.Part268.WorldRow13098.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13098) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13098) (by norm_num) BstLean.Part268.WorldRow13098.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13098} (hw : c ∈ Hof BstLean.Part268.WorldRow13098.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13098) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13098).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13098) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13098_eq : scalarRow13098.targetFrame = BstLean.Part268.agent13098.frame := by
  norm_num [scalarRow13098,BstLean.Part268.agent13098]

noncomputable def frameData13098 : BstLean.Part264b.FrameData 13098 :=
  BstLean.Part269.frameData_from_numerics (n := 13098) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13098.worldPackage rfl BstLean.Part268.WorldRow13098.product_lower (BstLean.Part268.WorldRow13098.producthi.2.trans (by norm_num))
    scalarRow13098 repair13098 covarianceInputs13098 (fun i hi => sourceNumerics13098 hi)
    BstLean.Part268.agent13098.frame targetFrame13098_eq


end BstLean.Part269.N13098

namespace BstLean.Part269.N13099
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13099 : scalarRow13099.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13099, BstLean.Part268.grid13099, BstLean.Part263.worldGrid]

theorem supplies13099 (j : Fin 43) : Supply 13099 (parameters j)
    (cellLower scalarRow13099.grid (sourceIndex j))
    (cellUpper scalarRow13099.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13099.grid grid_top_bounds13099 j

theorem radii13099 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13099.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13099 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13099 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13099.grid grid_top_bounds13099 j hθ

noncomputable def covarianceInputs13099 :
    BstLean.Part263.CovarianceInputs 13099 scalarRow13099.grid parameters (caps repair13099) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13099 grid_top_bounds13099 repair13099

noncomputable def covarianceEvent13099 : Set (AgFam 13099) :=
  BstLean.Part263.covarianceEvent 13099 scalarRow13099.grid parameters

theorem covarianceEvent13099_measurable : MeasurableSet covarianceEvent13099 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13099_payment :
    (retDist (paperDesignP 13099).toCentres).real
      (agentEv (paperDesignP 13099) covarianceEvent13099)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13099

theorem localCov13099 : BstLean.Part259.LocalCovarianceOn covarianceEvent13099
    (BstLean.Part263.cell scalarRow13099.grid) (caps repair13099) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13099

theorem covarianceGood13099_payment :
    (retDist (paperDesignP 13099).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13099)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13099_payment



end BstLean.Part269.N13099

namespace BstLean.Part269.N13099
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13099}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13099.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13099) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13099).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13099 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13099) (by norm_num) BstLean.Part268.WorldRow13099.worldPackage rfl
    BstLean.Part268.WorldRow13099.product_lower (BstLean.Part268.WorldRow13099.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13099} (hw : c ∈ Hof BstLean.Part268.WorldRow13099.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13099) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13099) (by norm_num) BstLean.Part268.WorldRow13099.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13099} (hw : c ∈ Hof BstLean.Part268.WorldRow13099.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13099) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13099).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13099) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13099_eq : scalarRow13099.targetFrame = BstLean.Part268.agent13099.frame := by
  norm_num [scalarRow13099,BstLean.Part268.agent13099]

noncomputable def frameData13099 : BstLean.Part264b.FrameData 13099 :=
  BstLean.Part269.frameData_from_numerics (n := 13099) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13099.worldPackage rfl BstLean.Part268.WorldRow13099.product_lower (BstLean.Part268.WorldRow13099.producthi.2.trans (by norm_num))
    scalarRow13099 repair13099 covarianceInputs13099 (fun i hi => sourceNumerics13099 hi)
    BstLean.Part268.agent13099.frame targetFrame13099_eq


end BstLean.Part269.N13099
