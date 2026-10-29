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

namespace BstLean.Part269.N13025
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13025 : scalarRow13025.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13025, BstLean.Part268.grid13025, BstLean.Part263.worldGrid]

theorem supplies13025 (j : Fin 43) : Supply 13025 (parameters j)
    (cellLower scalarRow13025.grid (sourceIndex j))
    (cellUpper scalarRow13025.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13025.grid grid_top_bounds13025 j

theorem radii13025 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13025.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13025 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13025 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13025.grid grid_top_bounds13025 j hθ

noncomputable def covarianceInputs13025 :
    BstLean.Part263.CovarianceInputs 13025 scalarRow13025.grid parameters (caps repair13025) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13025 grid_top_bounds13025 repair13025

noncomputable def covarianceEvent13025 : Set (AgFam 13025) :=
  BstLean.Part263.covarianceEvent 13025 scalarRow13025.grid parameters

theorem covarianceEvent13025_measurable : MeasurableSet covarianceEvent13025 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13025_payment :
    (retDist (paperDesignP 13025).toCentres).real
      (agentEv (paperDesignP 13025) covarianceEvent13025)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13025

theorem localCov13025 : BstLean.Part259.LocalCovarianceOn covarianceEvent13025
    (BstLean.Part263.cell scalarRow13025.grid) (caps repair13025) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13025

theorem covarianceGood13025_payment :
    (retDist (paperDesignP 13025).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13025)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13025_payment



end BstLean.Part269.N13025

namespace BstLean.Part269.N13025
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13025}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13025.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13025) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13025).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13025 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13025) (by norm_num) BstLean.Part268.WorldRow13025.worldPackage rfl
    BstLean.Part268.WorldRow13025.product_lower (BstLean.Part268.WorldRow13025.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13025} (hw : c ∈ Hof BstLean.Part268.WorldRow13025.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13025) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13025) (by norm_num) BstLean.Part268.WorldRow13025.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13025} (hw : c ∈ Hof BstLean.Part268.WorldRow13025.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13025) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13025).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13025) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13025_eq : scalarRow13025.targetFrame = BstLean.Part268.agent13025.frame := by
  norm_num [scalarRow13025,BstLean.Part268.agent13025]

noncomputable def frameData13025 : BstLean.Part264b.FrameData 13025 :=
  BstLean.Part269.frameData_from_numerics (n := 13025) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13025.worldPackage rfl BstLean.Part268.WorldRow13025.product_lower (BstLean.Part268.WorldRow13025.producthi.2.trans (by norm_num))
    scalarRow13025 repair13025 covarianceInputs13025 (fun i hi => sourceNumerics13025 hi)
    BstLean.Part268.agent13025.frame targetFrame13025_eq


end BstLean.Part269.N13025

namespace BstLean.Part269.N13026
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13026 : scalarRow13026.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13026, BstLean.Part268.grid13026, BstLean.Part263.worldGrid]

theorem supplies13026 (j : Fin 43) : Supply 13026 (parameters j)
    (cellLower scalarRow13026.grid (sourceIndex j))
    (cellUpper scalarRow13026.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13026.grid grid_top_bounds13026 j

theorem radii13026 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13026.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13026 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13026 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13026.grid grid_top_bounds13026 j hθ

noncomputable def covarianceInputs13026 :
    BstLean.Part263.CovarianceInputs 13026 scalarRow13026.grid parameters (caps repair13026) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13026 grid_top_bounds13026 repair13026

noncomputable def covarianceEvent13026 : Set (AgFam 13026) :=
  BstLean.Part263.covarianceEvent 13026 scalarRow13026.grid parameters

theorem covarianceEvent13026_measurable : MeasurableSet covarianceEvent13026 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13026_payment :
    (retDist (paperDesignP 13026).toCentres).real
      (agentEv (paperDesignP 13026) covarianceEvent13026)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13026

theorem localCov13026 : BstLean.Part259.LocalCovarianceOn covarianceEvent13026
    (BstLean.Part263.cell scalarRow13026.grid) (caps repair13026) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13026

theorem covarianceGood13026_payment :
    (retDist (paperDesignP 13026).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13026)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13026_payment



end BstLean.Part269.N13026

namespace BstLean.Part269.N13026
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13026}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13026.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13026) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13026).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13026 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13026) (by norm_num) BstLean.Part268.WorldRow13026.worldPackage rfl
    BstLean.Part268.WorldRow13026.product_lower (BstLean.Part268.WorldRow13026.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13026} (hw : c ∈ Hof BstLean.Part268.WorldRow13026.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13026) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13026) (by norm_num) BstLean.Part268.WorldRow13026.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13026} (hw : c ∈ Hof BstLean.Part268.WorldRow13026.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13026) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13026).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13026) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13026_eq : scalarRow13026.targetFrame = BstLean.Part268.agent13026.frame := by
  norm_num [scalarRow13026,BstLean.Part268.agent13026]

noncomputable def frameData13026 : BstLean.Part264b.FrameData 13026 :=
  BstLean.Part269.frameData_from_numerics (n := 13026) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13026.worldPackage rfl BstLean.Part268.WorldRow13026.product_lower (BstLean.Part268.WorldRow13026.producthi.2.trans (by norm_num))
    scalarRow13026 repair13026 covarianceInputs13026 (fun i hi => sourceNumerics13026 hi)
    BstLean.Part268.agent13026.frame targetFrame13026_eq


end BstLean.Part269.N13026

namespace BstLean.Part269.N13027
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13027 : scalarRow13027.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13027, BstLean.Part268.grid13027, BstLean.Part263.worldGrid]

theorem supplies13027 (j : Fin 43) : Supply 13027 (parameters j)
    (cellLower scalarRow13027.grid (sourceIndex j))
    (cellUpper scalarRow13027.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13027.grid grid_top_bounds13027 j

theorem radii13027 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13027.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13027 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13027 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13027.grid grid_top_bounds13027 j hθ

noncomputable def covarianceInputs13027 :
    BstLean.Part263.CovarianceInputs 13027 scalarRow13027.grid parameters (caps repair13027) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13027 grid_top_bounds13027 repair13027

noncomputable def covarianceEvent13027 : Set (AgFam 13027) :=
  BstLean.Part263.covarianceEvent 13027 scalarRow13027.grid parameters

theorem covarianceEvent13027_measurable : MeasurableSet covarianceEvent13027 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13027_payment :
    (retDist (paperDesignP 13027).toCentres).real
      (agentEv (paperDesignP 13027) covarianceEvent13027)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13027

theorem localCov13027 : BstLean.Part259.LocalCovarianceOn covarianceEvent13027
    (BstLean.Part263.cell scalarRow13027.grid) (caps repair13027) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13027

theorem covarianceGood13027_payment :
    (retDist (paperDesignP 13027).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13027)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13027_payment



end BstLean.Part269.N13027

namespace BstLean.Part269.N13027
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13027}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13027.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13027) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13027).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13027 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13027) (by norm_num) BstLean.Part268.WorldRow13027.worldPackage rfl
    BstLean.Part268.WorldRow13027.product_lower (BstLean.Part268.WorldRow13027.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13027} (hw : c ∈ Hof BstLean.Part268.WorldRow13027.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13027) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13027) (by norm_num) BstLean.Part268.WorldRow13027.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13027} (hw : c ∈ Hof BstLean.Part268.WorldRow13027.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13027) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13027).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13027) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13027_eq : scalarRow13027.targetFrame = BstLean.Part268.agent13027.frame := by
  norm_num [scalarRow13027,BstLean.Part268.agent13027]

noncomputable def frameData13027 : BstLean.Part264b.FrameData 13027 :=
  BstLean.Part269.frameData_from_numerics (n := 13027) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13027.worldPackage rfl BstLean.Part268.WorldRow13027.product_lower (BstLean.Part268.WorldRow13027.producthi.2.trans (by norm_num))
    scalarRow13027 repair13027 covarianceInputs13027 (fun i hi => sourceNumerics13027 hi)
    BstLean.Part268.agent13027.frame targetFrame13027_eq


end BstLean.Part269.N13027

namespace BstLean.Part269.N13028
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13028 : scalarRow13028.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13028, BstLean.Part268.grid13028, BstLean.Part263.worldGrid]

theorem supplies13028 (j : Fin 43) : Supply 13028 (parameters j)
    (cellLower scalarRow13028.grid (sourceIndex j))
    (cellUpper scalarRow13028.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13028.grid grid_top_bounds13028 j

theorem radii13028 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13028.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13028 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13028 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13028.grid grid_top_bounds13028 j hθ

noncomputable def covarianceInputs13028 :
    BstLean.Part263.CovarianceInputs 13028 scalarRow13028.grid parameters (caps repair13028) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13028 grid_top_bounds13028 repair13028

noncomputable def covarianceEvent13028 : Set (AgFam 13028) :=
  BstLean.Part263.covarianceEvent 13028 scalarRow13028.grid parameters

theorem covarianceEvent13028_measurable : MeasurableSet covarianceEvent13028 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13028_payment :
    (retDist (paperDesignP 13028).toCentres).real
      (agentEv (paperDesignP 13028) covarianceEvent13028)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13028

theorem localCov13028 : BstLean.Part259.LocalCovarianceOn covarianceEvent13028
    (BstLean.Part263.cell scalarRow13028.grid) (caps repair13028) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13028

theorem covarianceGood13028_payment :
    (retDist (paperDesignP 13028).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13028)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13028_payment



end BstLean.Part269.N13028

namespace BstLean.Part269.N13028
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13028}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13028.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13028) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13028).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13028 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13028) (by norm_num) BstLean.Part268.WorldRow13028.worldPackage rfl
    BstLean.Part268.WorldRow13028.product_lower (BstLean.Part268.WorldRow13028.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13028} (hw : c ∈ Hof BstLean.Part268.WorldRow13028.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13028) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13028) (by norm_num) BstLean.Part268.WorldRow13028.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13028} (hw : c ∈ Hof BstLean.Part268.WorldRow13028.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13028) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13028).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13028) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13028_eq : scalarRow13028.targetFrame = BstLean.Part268.agent13028.frame := by
  norm_num [scalarRow13028,BstLean.Part268.agent13028]

noncomputable def frameData13028 : BstLean.Part264b.FrameData 13028 :=
  BstLean.Part269.frameData_from_numerics (n := 13028) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13028.worldPackage rfl BstLean.Part268.WorldRow13028.product_lower (BstLean.Part268.WorldRow13028.producthi.2.trans (by norm_num))
    scalarRow13028 repair13028 covarianceInputs13028 (fun i hi => sourceNumerics13028 hi)
    BstLean.Part268.agent13028.frame targetFrame13028_eq


end BstLean.Part269.N13028

namespace BstLean.Part269.N13029
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13029 : scalarRow13029.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13029, BstLean.Part268.grid13029, BstLean.Part263.worldGrid]

theorem supplies13029 (j : Fin 43) : Supply 13029 (parameters j)
    (cellLower scalarRow13029.grid (sourceIndex j))
    (cellUpper scalarRow13029.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13029.grid grid_top_bounds13029 j

theorem radii13029 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13029.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13029 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13029 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13029.grid grid_top_bounds13029 j hθ

noncomputable def covarianceInputs13029 :
    BstLean.Part263.CovarianceInputs 13029 scalarRow13029.grid parameters (caps repair13029) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13029 grid_top_bounds13029 repair13029

noncomputable def covarianceEvent13029 : Set (AgFam 13029) :=
  BstLean.Part263.covarianceEvent 13029 scalarRow13029.grid parameters

theorem covarianceEvent13029_measurable : MeasurableSet covarianceEvent13029 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13029_payment :
    (retDist (paperDesignP 13029).toCentres).real
      (agentEv (paperDesignP 13029) covarianceEvent13029)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13029

theorem localCov13029 : BstLean.Part259.LocalCovarianceOn covarianceEvent13029
    (BstLean.Part263.cell scalarRow13029.grid) (caps repair13029) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13029

theorem covarianceGood13029_payment :
    (retDist (paperDesignP 13029).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13029)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13029_payment



end BstLean.Part269.N13029

namespace BstLean.Part269.N13029
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13029}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13029.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13029) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13029).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13029 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13029) (by norm_num) BstLean.Part268.WorldRow13029.worldPackage rfl
    BstLean.Part268.WorldRow13029.product_lower (BstLean.Part268.WorldRow13029.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13029} (hw : c ∈ Hof BstLean.Part268.WorldRow13029.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13029) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13029) (by norm_num) BstLean.Part268.WorldRow13029.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13029} (hw : c ∈ Hof BstLean.Part268.WorldRow13029.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13029) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13029).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13029) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13029_eq : scalarRow13029.targetFrame = BstLean.Part268.agent13029.frame := by
  norm_num [scalarRow13029,BstLean.Part268.agent13029]

noncomputable def frameData13029 : BstLean.Part264b.FrameData 13029 :=
  BstLean.Part269.frameData_from_numerics (n := 13029) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13029.worldPackage rfl BstLean.Part268.WorldRow13029.product_lower (BstLean.Part268.WorldRow13029.producthi.2.trans (by norm_num))
    scalarRow13029 repair13029 covarianceInputs13029 (fun i hi => sourceNumerics13029 hi)
    BstLean.Part268.agent13029.frame targetFrame13029_eq


end BstLean.Part269.N13029
