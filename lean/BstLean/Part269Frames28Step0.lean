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

namespace BstLean.Part269.N13050
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13050 : scalarRow13050.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13050, BstLean.Part268.grid13050, BstLean.Part263.worldGrid]

theorem supplies13050 (j : Fin 43) : Supply 13050 (parameters j)
    (cellLower scalarRow13050.grid (sourceIndex j))
    (cellUpper scalarRow13050.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13050.grid grid_top_bounds13050 j

theorem radii13050 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13050.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13050 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13050 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13050.grid grid_top_bounds13050 j hθ

noncomputable def covarianceInputs13050 :
    BstLean.Part263.CovarianceInputs 13050 scalarRow13050.grid parameters (caps repair13050) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13050 grid_top_bounds13050 repair13050

noncomputable def covarianceEvent13050 : Set (AgFam 13050) :=
  BstLean.Part263.covarianceEvent 13050 scalarRow13050.grid parameters

theorem covarianceEvent13050_measurable : MeasurableSet covarianceEvent13050 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13050_payment :
    (retDist (paperDesignP 13050).toCentres).real
      (agentEv (paperDesignP 13050) covarianceEvent13050)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13050

theorem localCov13050 : BstLean.Part259.LocalCovarianceOn covarianceEvent13050
    (BstLean.Part263.cell scalarRow13050.grid) (caps repair13050) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13050

theorem covarianceGood13050_payment :
    (retDist (paperDesignP 13050).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13050)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13050_payment



end BstLean.Part269.N13050

namespace BstLean.Part269.N13050
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13050}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13050.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13050) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13050).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13050 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13050) (by norm_num) BstLean.Part268.WorldRow13050.worldPackage rfl
    BstLean.Part268.WorldRow13050.product_lower (BstLean.Part268.WorldRow13050.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13050} (hw : c ∈ Hof BstLean.Part268.WorldRow13050.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13050) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13050) (by norm_num) BstLean.Part268.WorldRow13050.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13050} (hw : c ∈ Hof BstLean.Part268.WorldRow13050.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13050) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13050).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13050) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13050_eq : scalarRow13050.targetFrame = BstLean.Part268.agent13050.frame := by
  norm_num [scalarRow13050,BstLean.Part268.agent13050]

noncomputable def frameData13050 : BstLean.Part264b.FrameData 13050 :=
  BstLean.Part269.frameData_from_numerics (n := 13050) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13050.worldPackage rfl BstLean.Part268.WorldRow13050.product_lower (BstLean.Part268.WorldRow13050.producthi.2.trans (by norm_num))
    scalarRow13050 repair13050 covarianceInputs13050 (fun i hi => sourceNumerics13050 hi)
    BstLean.Part268.agent13050.frame targetFrame13050_eq


end BstLean.Part269.N13050

namespace BstLean.Part269.N13051
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13051 : scalarRow13051.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13051, BstLean.Part268.grid13051, BstLean.Part263.worldGrid]

theorem supplies13051 (j : Fin 43) : Supply 13051 (parameters j)
    (cellLower scalarRow13051.grid (sourceIndex j))
    (cellUpper scalarRow13051.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13051.grid grid_top_bounds13051 j

theorem radii13051 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13051.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13051 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13051 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13051.grid grid_top_bounds13051 j hθ

noncomputable def covarianceInputs13051 :
    BstLean.Part263.CovarianceInputs 13051 scalarRow13051.grid parameters (caps repair13051) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13051 grid_top_bounds13051 repair13051

noncomputable def covarianceEvent13051 : Set (AgFam 13051) :=
  BstLean.Part263.covarianceEvent 13051 scalarRow13051.grid parameters

theorem covarianceEvent13051_measurable : MeasurableSet covarianceEvent13051 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13051_payment :
    (retDist (paperDesignP 13051).toCentres).real
      (agentEv (paperDesignP 13051) covarianceEvent13051)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13051

theorem localCov13051 : BstLean.Part259.LocalCovarianceOn covarianceEvent13051
    (BstLean.Part263.cell scalarRow13051.grid) (caps repair13051) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13051

theorem covarianceGood13051_payment :
    (retDist (paperDesignP 13051).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13051)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13051_payment



end BstLean.Part269.N13051

namespace BstLean.Part269.N13051
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13051}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13051.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13051) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13051).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13051 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13051) (by norm_num) BstLean.Part268.WorldRow13051.worldPackage rfl
    BstLean.Part268.WorldRow13051.product_lower (BstLean.Part268.WorldRow13051.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13051} (hw : c ∈ Hof BstLean.Part268.WorldRow13051.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13051) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13051) (by norm_num) BstLean.Part268.WorldRow13051.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13051} (hw : c ∈ Hof BstLean.Part268.WorldRow13051.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13051) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13051).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13051) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13051_eq : scalarRow13051.targetFrame = BstLean.Part268.agent13051.frame := by
  norm_num [scalarRow13051,BstLean.Part268.agent13051]

noncomputable def frameData13051 : BstLean.Part264b.FrameData 13051 :=
  BstLean.Part269.frameData_from_numerics (n := 13051) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13051.worldPackage rfl BstLean.Part268.WorldRow13051.product_lower (BstLean.Part268.WorldRow13051.producthi.2.trans (by norm_num))
    scalarRow13051 repair13051 covarianceInputs13051 (fun i hi => sourceNumerics13051 hi)
    BstLean.Part268.agent13051.frame targetFrame13051_eq


end BstLean.Part269.N13051

namespace BstLean.Part269.N13052
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13052 : scalarRow13052.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13052, BstLean.Part268.grid13052, BstLean.Part263.worldGrid]

theorem supplies13052 (j : Fin 43) : Supply 13052 (parameters j)
    (cellLower scalarRow13052.grid (sourceIndex j))
    (cellUpper scalarRow13052.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13052.grid grid_top_bounds13052 j

theorem radii13052 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13052.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13052 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13052 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13052.grid grid_top_bounds13052 j hθ

noncomputable def covarianceInputs13052 :
    BstLean.Part263.CovarianceInputs 13052 scalarRow13052.grid parameters (caps repair13052) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13052 grid_top_bounds13052 repair13052

noncomputable def covarianceEvent13052 : Set (AgFam 13052) :=
  BstLean.Part263.covarianceEvent 13052 scalarRow13052.grid parameters

theorem covarianceEvent13052_measurable : MeasurableSet covarianceEvent13052 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13052_payment :
    (retDist (paperDesignP 13052).toCentres).real
      (agentEv (paperDesignP 13052) covarianceEvent13052)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13052

theorem localCov13052 : BstLean.Part259.LocalCovarianceOn covarianceEvent13052
    (BstLean.Part263.cell scalarRow13052.grid) (caps repair13052) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13052

theorem covarianceGood13052_payment :
    (retDist (paperDesignP 13052).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13052)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13052_payment



end BstLean.Part269.N13052

namespace BstLean.Part269.N13052
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13052}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13052.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13052) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13052).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13052 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13052) (by norm_num) BstLean.Part268.WorldRow13052.worldPackage rfl
    BstLean.Part268.WorldRow13052.product_lower (BstLean.Part268.WorldRow13052.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13052} (hw : c ∈ Hof BstLean.Part268.WorldRow13052.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13052) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13052) (by norm_num) BstLean.Part268.WorldRow13052.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13052} (hw : c ∈ Hof BstLean.Part268.WorldRow13052.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13052) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13052).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13052) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13052_eq : scalarRow13052.targetFrame = BstLean.Part268.agent13052.frame := by
  norm_num [scalarRow13052,BstLean.Part268.agent13052]

noncomputable def frameData13052 : BstLean.Part264b.FrameData 13052 :=
  BstLean.Part269.frameData_from_numerics (n := 13052) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13052.worldPackage rfl BstLean.Part268.WorldRow13052.product_lower (BstLean.Part268.WorldRow13052.producthi.2.trans (by norm_num))
    scalarRow13052 repair13052 covarianceInputs13052 (fun i hi => sourceNumerics13052 hi)
    BstLean.Part268.agent13052.frame targetFrame13052_eq


end BstLean.Part269.N13052

namespace BstLean.Part269.N13053
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13053 : scalarRow13053.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13053, BstLean.Part268.grid13053, BstLean.Part263.worldGrid]

theorem supplies13053 (j : Fin 43) : Supply 13053 (parameters j)
    (cellLower scalarRow13053.grid (sourceIndex j))
    (cellUpper scalarRow13053.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13053.grid grid_top_bounds13053 j

theorem radii13053 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13053.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13053 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13053 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13053.grid grid_top_bounds13053 j hθ

noncomputable def covarianceInputs13053 :
    BstLean.Part263.CovarianceInputs 13053 scalarRow13053.grid parameters (caps repair13053) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13053 grid_top_bounds13053 repair13053

noncomputable def covarianceEvent13053 : Set (AgFam 13053) :=
  BstLean.Part263.covarianceEvent 13053 scalarRow13053.grid parameters

theorem covarianceEvent13053_measurable : MeasurableSet covarianceEvent13053 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13053_payment :
    (retDist (paperDesignP 13053).toCentres).real
      (agentEv (paperDesignP 13053) covarianceEvent13053)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13053

theorem localCov13053 : BstLean.Part259.LocalCovarianceOn covarianceEvent13053
    (BstLean.Part263.cell scalarRow13053.grid) (caps repair13053) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13053

theorem covarianceGood13053_payment :
    (retDist (paperDesignP 13053).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13053)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13053_payment



end BstLean.Part269.N13053

namespace BstLean.Part269.N13053
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13053}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13053.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13053) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13053).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13053 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13053) (by norm_num) BstLean.Part268.WorldRow13053.worldPackage rfl
    BstLean.Part268.WorldRow13053.product_lower (BstLean.Part268.WorldRow13053.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13053} (hw : c ∈ Hof BstLean.Part268.WorldRow13053.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13053) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13053) (by norm_num) BstLean.Part268.WorldRow13053.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13053} (hw : c ∈ Hof BstLean.Part268.WorldRow13053.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13053) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13053).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13053) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13053_eq : scalarRow13053.targetFrame = BstLean.Part268.agent13053.frame := by
  norm_num [scalarRow13053,BstLean.Part268.agent13053]

noncomputable def frameData13053 : BstLean.Part264b.FrameData 13053 :=
  BstLean.Part269.frameData_from_numerics (n := 13053) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13053.worldPackage rfl BstLean.Part268.WorldRow13053.product_lower (BstLean.Part268.WorldRow13053.producthi.2.trans (by norm_num))
    scalarRow13053 repair13053 covarianceInputs13053 (fun i hi => sourceNumerics13053 hi)
    BstLean.Part268.agent13053.frame targetFrame13053_eq


end BstLean.Part269.N13053

namespace BstLean.Part269.N13054
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13054 : scalarRow13054.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13054, BstLean.Part268.grid13054, BstLean.Part263.worldGrid]

theorem supplies13054 (j : Fin 43) : Supply 13054 (parameters j)
    (cellLower scalarRow13054.grid (sourceIndex j))
    (cellUpper scalarRow13054.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13054.grid grid_top_bounds13054 j

theorem radii13054 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13054.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13054 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13054 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13054.grid grid_top_bounds13054 j hθ

noncomputable def covarianceInputs13054 :
    BstLean.Part263.CovarianceInputs 13054 scalarRow13054.grid parameters (caps repair13054) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13054 grid_top_bounds13054 repair13054

noncomputable def covarianceEvent13054 : Set (AgFam 13054) :=
  BstLean.Part263.covarianceEvent 13054 scalarRow13054.grid parameters

theorem covarianceEvent13054_measurable : MeasurableSet covarianceEvent13054 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13054_payment :
    (retDist (paperDesignP 13054).toCentres).real
      (agentEv (paperDesignP 13054) covarianceEvent13054)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13054

theorem localCov13054 : BstLean.Part259.LocalCovarianceOn covarianceEvent13054
    (BstLean.Part263.cell scalarRow13054.grid) (caps repair13054) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13054

theorem covarianceGood13054_payment :
    (retDist (paperDesignP 13054).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13054)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13054_payment



end BstLean.Part269.N13054

namespace BstLean.Part269.N13054
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13054}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13054.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13054) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13054).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13054 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13054) (by norm_num) BstLean.Part268.WorldRow13054.worldPackage rfl
    BstLean.Part268.WorldRow13054.product_lower (BstLean.Part268.WorldRow13054.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13054} (hw : c ∈ Hof BstLean.Part268.WorldRow13054.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13054) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13054) (by norm_num) BstLean.Part268.WorldRow13054.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13054} (hw : c ∈ Hof BstLean.Part268.WorldRow13054.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13054) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13054).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13054) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13054_eq : scalarRow13054.targetFrame = BstLean.Part268.agent13054.frame := by
  norm_num [scalarRow13054,BstLean.Part268.agent13054]

noncomputable def frameData13054 : BstLean.Part264b.FrameData 13054 :=
  BstLean.Part269.frameData_from_numerics (n := 13054) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13054.worldPackage rfl BstLean.Part268.WorldRow13054.product_lower (BstLean.Part268.WorldRow13054.producthi.2.trans (by norm_num))
    scalarRow13054 repair13054 covarianceInputs13054 (fun i hi => sourceNumerics13054 hi)
    BstLean.Part268.agent13054.frame targetFrame13054_eq


end BstLean.Part269.N13054
