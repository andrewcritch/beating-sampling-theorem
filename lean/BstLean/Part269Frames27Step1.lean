import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World27Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs27
import BstLean.Part269Rows27
import BstLean.Part269Sources27
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13030
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13030 : scalarRow13030.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13030, BstLean.Part268.grid13030, BstLean.Part263.worldGrid]

theorem supplies13030 (j : Fin 43) : Supply 13030 (parameters j)
    (cellLower scalarRow13030.grid (sourceIndex j))
    (cellUpper scalarRow13030.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13030.grid grid_top_bounds13030 j

theorem radii13030 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13030.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13030 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13030 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13030.grid grid_top_bounds13030 j hθ

noncomputable def covarianceInputs13030 :
    BstLean.Part263.CovarianceInputs 13030 scalarRow13030.grid parameters (caps repair13030) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13030 grid_top_bounds13030 repair13030

noncomputable def covarianceEvent13030 : Set (AgFam 13030) :=
  BstLean.Part263.covarianceEvent 13030 scalarRow13030.grid parameters

theorem covarianceEvent13030_measurable : MeasurableSet covarianceEvent13030 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13030_payment :
    (retDist (paperDesignP 13030).toCentres).real
      (agentEv (paperDesignP 13030) covarianceEvent13030)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13030

theorem localCov13030 : BstLean.Part259.LocalCovarianceOn covarianceEvent13030
    (BstLean.Part263.cell scalarRow13030.grid) (caps repair13030) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13030

theorem covarianceGood13030_payment :
    (retDist (paperDesignP 13030).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13030)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13030_payment



end BstLean.Part269.N13030

namespace BstLean.Part269.N13030
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13030}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13030.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13030) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13030).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13030 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13030) (by norm_num) BstLean.Part268.WorldRow13030.worldPackage rfl
    BstLean.Part268.WorldRow13030.product_lower (BstLean.Part268.WorldRow13030.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13030} (hw : c ∈ Hof BstLean.Part268.WorldRow13030.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13030) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13030) (by norm_num) BstLean.Part268.WorldRow13030.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13030} (hw : c ∈ Hof BstLean.Part268.WorldRow13030.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13030) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13030).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13030) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13030_eq : scalarRow13030.targetFrame = BstLean.Part268.agent13030.frame := by
  norm_num [scalarRow13030,BstLean.Part268.agent13030]

noncomputable def frameData13030 : BstLean.Part264b.FrameData 13030 :=
  BstLean.Part269.frameData_from_numerics (n := 13030) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13030.worldPackage rfl BstLean.Part268.WorldRow13030.product_lower (BstLean.Part268.WorldRow13030.producthi.2.trans (by norm_num))
    scalarRow13030 repair13030 covarianceInputs13030 (fun i hi => sourceNumerics13030 hi)
    BstLean.Part268.agent13030.frame targetFrame13030_eq


end BstLean.Part269.N13030

namespace BstLean.Part269.N13031
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13031 : scalarRow13031.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13031, BstLean.Part268.grid13031, BstLean.Part263.worldGrid]

theorem supplies13031 (j : Fin 43) : Supply 13031 (parameters j)
    (cellLower scalarRow13031.grid (sourceIndex j))
    (cellUpper scalarRow13031.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13031.grid grid_top_bounds13031 j

theorem radii13031 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13031.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13031 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13031 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13031.grid grid_top_bounds13031 j hθ

noncomputable def covarianceInputs13031 :
    BstLean.Part263.CovarianceInputs 13031 scalarRow13031.grid parameters (caps repair13031) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13031 grid_top_bounds13031 repair13031

noncomputable def covarianceEvent13031 : Set (AgFam 13031) :=
  BstLean.Part263.covarianceEvent 13031 scalarRow13031.grid parameters

theorem covarianceEvent13031_measurable : MeasurableSet covarianceEvent13031 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13031_payment :
    (retDist (paperDesignP 13031).toCentres).real
      (agentEv (paperDesignP 13031) covarianceEvent13031)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13031

theorem localCov13031 : BstLean.Part259.LocalCovarianceOn covarianceEvent13031
    (BstLean.Part263.cell scalarRow13031.grid) (caps repair13031) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13031

theorem covarianceGood13031_payment :
    (retDist (paperDesignP 13031).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13031)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13031_payment



end BstLean.Part269.N13031

namespace BstLean.Part269.N13031
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13031}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13031.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13031) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13031).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13031 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13031) (by norm_num) BstLean.Part268.WorldRow13031.worldPackage rfl
    BstLean.Part268.WorldRow13031.product_lower (BstLean.Part268.WorldRow13031.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13031} (hw : c ∈ Hof BstLean.Part268.WorldRow13031.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13031) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13031) (by norm_num) BstLean.Part268.WorldRow13031.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13031} (hw : c ∈ Hof BstLean.Part268.WorldRow13031.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13031) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13031).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13031) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13031_eq : scalarRow13031.targetFrame = BstLean.Part268.agent13031.frame := by
  norm_num [scalarRow13031,BstLean.Part268.agent13031]

noncomputable def frameData13031 : BstLean.Part264b.FrameData 13031 :=
  BstLean.Part269.frameData_from_numerics (n := 13031) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13031.worldPackage rfl BstLean.Part268.WorldRow13031.product_lower (BstLean.Part268.WorldRow13031.producthi.2.trans (by norm_num))
    scalarRow13031 repair13031 covarianceInputs13031 (fun i hi => sourceNumerics13031 hi)
    BstLean.Part268.agent13031.frame targetFrame13031_eq


end BstLean.Part269.N13031

namespace BstLean.Part269.N13032
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13032 : scalarRow13032.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13032, BstLean.Part268.grid13032, BstLean.Part263.worldGrid]

theorem supplies13032 (j : Fin 43) : Supply 13032 (parameters j)
    (cellLower scalarRow13032.grid (sourceIndex j))
    (cellUpper scalarRow13032.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13032.grid grid_top_bounds13032 j

theorem radii13032 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13032.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13032 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13032 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13032.grid grid_top_bounds13032 j hθ

noncomputable def covarianceInputs13032 :
    BstLean.Part263.CovarianceInputs 13032 scalarRow13032.grid parameters (caps repair13032) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13032 grid_top_bounds13032 repair13032

noncomputable def covarianceEvent13032 : Set (AgFam 13032) :=
  BstLean.Part263.covarianceEvent 13032 scalarRow13032.grid parameters

theorem covarianceEvent13032_measurable : MeasurableSet covarianceEvent13032 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13032_payment :
    (retDist (paperDesignP 13032).toCentres).real
      (agentEv (paperDesignP 13032) covarianceEvent13032)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13032

theorem localCov13032 : BstLean.Part259.LocalCovarianceOn covarianceEvent13032
    (BstLean.Part263.cell scalarRow13032.grid) (caps repair13032) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13032

theorem covarianceGood13032_payment :
    (retDist (paperDesignP 13032).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13032)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13032_payment



end BstLean.Part269.N13032

namespace BstLean.Part269.N13032
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13032}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13032.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13032) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13032).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13032 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13032) (by norm_num) BstLean.Part268.WorldRow13032.worldPackage rfl
    BstLean.Part268.WorldRow13032.product_lower (BstLean.Part268.WorldRow13032.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13032} (hw : c ∈ Hof BstLean.Part268.WorldRow13032.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13032) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13032) (by norm_num) BstLean.Part268.WorldRow13032.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13032} (hw : c ∈ Hof BstLean.Part268.WorldRow13032.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13032) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13032).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13032) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13032_eq : scalarRow13032.targetFrame = BstLean.Part268.agent13032.frame := by
  norm_num [scalarRow13032,BstLean.Part268.agent13032]

noncomputable def frameData13032 : BstLean.Part264b.FrameData 13032 :=
  BstLean.Part269.frameData_from_numerics (n := 13032) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13032.worldPackage rfl BstLean.Part268.WorldRow13032.product_lower (BstLean.Part268.WorldRow13032.producthi.2.trans (by norm_num))
    scalarRow13032 repair13032 covarianceInputs13032 (fun i hi => sourceNumerics13032 hi)
    BstLean.Part268.agent13032.frame targetFrame13032_eq


end BstLean.Part269.N13032

namespace BstLean.Part269.N13033
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13033 : scalarRow13033.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13033, BstLean.Part268.grid13033, BstLean.Part263.worldGrid]

theorem supplies13033 (j : Fin 43) : Supply 13033 (parameters j)
    (cellLower scalarRow13033.grid (sourceIndex j))
    (cellUpper scalarRow13033.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13033.grid grid_top_bounds13033 j

theorem radii13033 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13033.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13033 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13033 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13033.grid grid_top_bounds13033 j hθ

noncomputable def covarianceInputs13033 :
    BstLean.Part263.CovarianceInputs 13033 scalarRow13033.grid parameters (caps repair13033) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13033 grid_top_bounds13033 repair13033

noncomputable def covarianceEvent13033 : Set (AgFam 13033) :=
  BstLean.Part263.covarianceEvent 13033 scalarRow13033.grid parameters

theorem covarianceEvent13033_measurable : MeasurableSet covarianceEvent13033 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13033_payment :
    (retDist (paperDesignP 13033).toCentres).real
      (agentEv (paperDesignP 13033) covarianceEvent13033)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13033

theorem localCov13033 : BstLean.Part259.LocalCovarianceOn covarianceEvent13033
    (BstLean.Part263.cell scalarRow13033.grid) (caps repair13033) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13033

theorem covarianceGood13033_payment :
    (retDist (paperDesignP 13033).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13033)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13033_payment



end BstLean.Part269.N13033

namespace BstLean.Part269.N13033
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13033}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13033.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13033) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13033).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13033 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13033) (by norm_num) BstLean.Part268.WorldRow13033.worldPackage rfl
    BstLean.Part268.WorldRow13033.product_lower (BstLean.Part268.WorldRow13033.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13033} (hw : c ∈ Hof BstLean.Part268.WorldRow13033.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13033) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13033) (by norm_num) BstLean.Part268.WorldRow13033.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13033} (hw : c ∈ Hof BstLean.Part268.WorldRow13033.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13033) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13033).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13033) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13033_eq : scalarRow13033.targetFrame = BstLean.Part268.agent13033.frame := by
  norm_num [scalarRow13033,BstLean.Part268.agent13033]

noncomputable def frameData13033 : BstLean.Part264b.FrameData 13033 :=
  BstLean.Part269.frameData_from_numerics (n := 13033) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13033.worldPackage rfl BstLean.Part268.WorldRow13033.product_lower (BstLean.Part268.WorldRow13033.producthi.2.trans (by norm_num))
    scalarRow13033 repair13033 covarianceInputs13033 (fun i hi => sourceNumerics13033 hi)
    BstLean.Part268.agent13033.frame targetFrame13033_eq


end BstLean.Part269.N13033

namespace BstLean.Part269.N13034
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13034 : scalarRow13034.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13034, BstLean.Part268.grid13034, BstLean.Part263.worldGrid]

theorem supplies13034 (j : Fin 43) : Supply 13034 (parameters j)
    (cellLower scalarRow13034.grid (sourceIndex j))
    (cellUpper scalarRow13034.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13034.grid grid_top_bounds13034 j

theorem radii13034 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13034.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13034 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13034 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13034.grid grid_top_bounds13034 j hθ

noncomputable def covarianceInputs13034 :
    BstLean.Part263.CovarianceInputs 13034 scalarRow13034.grid parameters (caps repair13034) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13034 grid_top_bounds13034 repair13034

noncomputable def covarianceEvent13034 : Set (AgFam 13034) :=
  BstLean.Part263.covarianceEvent 13034 scalarRow13034.grid parameters

theorem covarianceEvent13034_measurable : MeasurableSet covarianceEvent13034 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13034_payment :
    (retDist (paperDesignP 13034).toCentres).real
      (agentEv (paperDesignP 13034) covarianceEvent13034)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13034

theorem localCov13034 : BstLean.Part259.LocalCovarianceOn covarianceEvent13034
    (BstLean.Part263.cell scalarRow13034.grid) (caps repair13034) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13034

theorem covarianceGood13034_payment :
    (retDist (paperDesignP 13034).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13034)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13034_payment



end BstLean.Part269.N13034

namespace BstLean.Part269.N13034
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13034}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13034.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13034) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13034).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13034 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13034) (by norm_num) BstLean.Part268.WorldRow13034.worldPackage rfl
    BstLean.Part268.WorldRow13034.product_lower (BstLean.Part268.WorldRow13034.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13034} (hw : c ∈ Hof BstLean.Part268.WorldRow13034.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13034) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13034) (by norm_num) BstLean.Part268.WorldRow13034.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13034} (hw : c ∈ Hof BstLean.Part268.WorldRow13034.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13034) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13034).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13034) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13034_eq : scalarRow13034.targetFrame = BstLean.Part268.agent13034.frame := by
  norm_num [scalarRow13034,BstLean.Part268.agent13034]

noncomputable def frameData13034 : BstLean.Part264b.FrameData 13034 :=
  BstLean.Part269.frameData_from_numerics (n := 13034) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13034.worldPackage rfl BstLean.Part268.WorldRow13034.product_lower (BstLean.Part268.WorldRow13034.producthi.2.trans (by norm_num))
    scalarRow13034 repair13034 covarianceInputs13034 (fun i hi => sourceNumerics13034 hi)
    BstLean.Part268.agent13034.frame targetFrame13034_eq


end BstLean.Part269.N13034
