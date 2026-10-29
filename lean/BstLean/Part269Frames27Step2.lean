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

namespace BstLean.Part269.N13035
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13035 : scalarRow13035.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13035, BstLean.Part268.grid13035, BstLean.Part263.worldGrid]

theorem supplies13035 (j : Fin 43) : Supply 13035 (parameters j)
    (cellLower scalarRow13035.grid (sourceIndex j))
    (cellUpper scalarRow13035.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13035.grid grid_top_bounds13035 j

theorem radii13035 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13035.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13035 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13035 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13035.grid grid_top_bounds13035 j hθ

noncomputable def covarianceInputs13035 :
    BstLean.Part263.CovarianceInputs 13035 scalarRow13035.grid parameters (caps repair13035) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13035 grid_top_bounds13035 repair13035

noncomputable def covarianceEvent13035 : Set (AgFam 13035) :=
  BstLean.Part263.covarianceEvent 13035 scalarRow13035.grid parameters

theorem covarianceEvent13035_measurable : MeasurableSet covarianceEvent13035 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13035_payment :
    (retDist (paperDesignP 13035).toCentres).real
      (agentEv (paperDesignP 13035) covarianceEvent13035)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13035

theorem localCov13035 : BstLean.Part259.LocalCovarianceOn covarianceEvent13035
    (BstLean.Part263.cell scalarRow13035.grid) (caps repair13035) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13035

theorem covarianceGood13035_payment :
    (retDist (paperDesignP 13035).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13035)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13035_payment



end BstLean.Part269.N13035

namespace BstLean.Part269.N13035
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13035}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13035.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13035) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13035).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13035 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13035) (by norm_num) BstLean.Part268.WorldRow13035.worldPackage rfl
    BstLean.Part268.WorldRow13035.product_lower (BstLean.Part268.WorldRow13035.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13035} (hw : c ∈ Hof BstLean.Part268.WorldRow13035.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13035) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13035) (by norm_num) BstLean.Part268.WorldRow13035.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13035} (hw : c ∈ Hof BstLean.Part268.WorldRow13035.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13035) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13035).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13035) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13035_eq : scalarRow13035.targetFrame = BstLean.Part268.agent13035.frame := by
  norm_num [scalarRow13035,BstLean.Part268.agent13035]

noncomputable def frameData13035 : BstLean.Part264b.FrameData 13035 :=
  BstLean.Part269.frameData_from_numerics (n := 13035) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13035.worldPackage rfl BstLean.Part268.WorldRow13035.product_lower (BstLean.Part268.WorldRow13035.producthi.2.trans (by norm_num))
    scalarRow13035 repair13035 covarianceInputs13035 (fun i hi => sourceNumerics13035 hi)
    BstLean.Part268.agent13035.frame targetFrame13035_eq


end BstLean.Part269.N13035

namespace BstLean.Part269.N13036
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13036 : scalarRow13036.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13036, BstLean.Part268.grid13036, BstLean.Part263.worldGrid]

theorem supplies13036 (j : Fin 43) : Supply 13036 (parameters j)
    (cellLower scalarRow13036.grid (sourceIndex j))
    (cellUpper scalarRow13036.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13036.grid grid_top_bounds13036 j

theorem radii13036 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13036.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13036 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13036 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13036.grid grid_top_bounds13036 j hθ

noncomputable def covarianceInputs13036 :
    BstLean.Part263.CovarianceInputs 13036 scalarRow13036.grid parameters (caps repair13036) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13036 grid_top_bounds13036 repair13036

noncomputable def covarianceEvent13036 : Set (AgFam 13036) :=
  BstLean.Part263.covarianceEvent 13036 scalarRow13036.grid parameters

theorem covarianceEvent13036_measurable : MeasurableSet covarianceEvent13036 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13036_payment :
    (retDist (paperDesignP 13036).toCentres).real
      (agentEv (paperDesignP 13036) covarianceEvent13036)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13036

theorem localCov13036 : BstLean.Part259.LocalCovarianceOn covarianceEvent13036
    (BstLean.Part263.cell scalarRow13036.grid) (caps repair13036) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13036

theorem covarianceGood13036_payment :
    (retDist (paperDesignP 13036).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13036)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13036_payment



end BstLean.Part269.N13036

namespace BstLean.Part269.N13036
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13036}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13036.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13036) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13036).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13036 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13036) (by norm_num) BstLean.Part268.WorldRow13036.worldPackage rfl
    BstLean.Part268.WorldRow13036.product_lower (BstLean.Part268.WorldRow13036.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13036} (hw : c ∈ Hof BstLean.Part268.WorldRow13036.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13036) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13036) (by norm_num) BstLean.Part268.WorldRow13036.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13036} (hw : c ∈ Hof BstLean.Part268.WorldRow13036.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13036) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13036).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13036) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13036_eq : scalarRow13036.targetFrame = BstLean.Part268.agent13036.frame := by
  norm_num [scalarRow13036,BstLean.Part268.agent13036]

noncomputable def frameData13036 : BstLean.Part264b.FrameData 13036 :=
  BstLean.Part269.frameData_from_numerics (n := 13036) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13036.worldPackage rfl BstLean.Part268.WorldRow13036.product_lower (BstLean.Part268.WorldRow13036.producthi.2.trans (by norm_num))
    scalarRow13036 repair13036 covarianceInputs13036 (fun i hi => sourceNumerics13036 hi)
    BstLean.Part268.agent13036.frame targetFrame13036_eq


end BstLean.Part269.N13036

namespace BstLean.Part269.N13037
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13037 : scalarRow13037.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13037, BstLean.Part268.grid13037, BstLean.Part263.worldGrid]

theorem supplies13037 (j : Fin 43) : Supply 13037 (parameters j)
    (cellLower scalarRow13037.grid (sourceIndex j))
    (cellUpper scalarRow13037.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13037.grid grid_top_bounds13037 j

theorem radii13037 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13037.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13037 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13037 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13037.grid grid_top_bounds13037 j hθ

noncomputable def covarianceInputs13037 :
    BstLean.Part263.CovarianceInputs 13037 scalarRow13037.grid parameters (caps repair13037) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13037 grid_top_bounds13037 repair13037

noncomputable def covarianceEvent13037 : Set (AgFam 13037) :=
  BstLean.Part263.covarianceEvent 13037 scalarRow13037.grid parameters

theorem covarianceEvent13037_measurable : MeasurableSet covarianceEvent13037 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13037_payment :
    (retDist (paperDesignP 13037).toCentres).real
      (agentEv (paperDesignP 13037) covarianceEvent13037)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13037

theorem localCov13037 : BstLean.Part259.LocalCovarianceOn covarianceEvent13037
    (BstLean.Part263.cell scalarRow13037.grid) (caps repair13037) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13037

theorem covarianceGood13037_payment :
    (retDist (paperDesignP 13037).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13037)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13037_payment



end BstLean.Part269.N13037

namespace BstLean.Part269.N13037
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13037}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13037.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13037) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13037).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13037 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13037) (by norm_num) BstLean.Part268.WorldRow13037.worldPackage rfl
    BstLean.Part268.WorldRow13037.product_lower (BstLean.Part268.WorldRow13037.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13037} (hw : c ∈ Hof BstLean.Part268.WorldRow13037.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13037) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13037) (by norm_num) BstLean.Part268.WorldRow13037.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13037} (hw : c ∈ Hof BstLean.Part268.WorldRow13037.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13037) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13037).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13037) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13037_eq : scalarRow13037.targetFrame = BstLean.Part268.agent13037.frame := by
  norm_num [scalarRow13037,BstLean.Part268.agent13037]

noncomputable def frameData13037 : BstLean.Part264b.FrameData 13037 :=
  BstLean.Part269.frameData_from_numerics (n := 13037) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13037.worldPackage rfl BstLean.Part268.WorldRow13037.product_lower (BstLean.Part268.WorldRow13037.producthi.2.trans (by norm_num))
    scalarRow13037 repair13037 covarianceInputs13037 (fun i hi => sourceNumerics13037 hi)
    BstLean.Part268.agent13037.frame targetFrame13037_eq


end BstLean.Part269.N13037

namespace BstLean.Part269.N13038
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13038 : scalarRow13038.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13038, BstLean.Part268.grid13038, BstLean.Part263.worldGrid]

theorem supplies13038 (j : Fin 43) : Supply 13038 (parameters j)
    (cellLower scalarRow13038.grid (sourceIndex j))
    (cellUpper scalarRow13038.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13038.grid grid_top_bounds13038 j

theorem radii13038 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13038.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13038 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13038 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13038.grid grid_top_bounds13038 j hθ

noncomputable def covarianceInputs13038 :
    BstLean.Part263.CovarianceInputs 13038 scalarRow13038.grid parameters (caps repair13038) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13038 grid_top_bounds13038 repair13038

noncomputable def covarianceEvent13038 : Set (AgFam 13038) :=
  BstLean.Part263.covarianceEvent 13038 scalarRow13038.grid parameters

theorem covarianceEvent13038_measurable : MeasurableSet covarianceEvent13038 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13038_payment :
    (retDist (paperDesignP 13038).toCentres).real
      (agentEv (paperDesignP 13038) covarianceEvent13038)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13038

theorem localCov13038 : BstLean.Part259.LocalCovarianceOn covarianceEvent13038
    (BstLean.Part263.cell scalarRow13038.grid) (caps repair13038) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13038

theorem covarianceGood13038_payment :
    (retDist (paperDesignP 13038).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13038)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13038_payment



end BstLean.Part269.N13038

namespace BstLean.Part269.N13038
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13038}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13038.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13038) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13038).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13038 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13038) (by norm_num) BstLean.Part268.WorldRow13038.worldPackage rfl
    BstLean.Part268.WorldRow13038.product_lower (BstLean.Part268.WorldRow13038.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13038} (hw : c ∈ Hof BstLean.Part268.WorldRow13038.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13038) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13038) (by norm_num) BstLean.Part268.WorldRow13038.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13038} (hw : c ∈ Hof BstLean.Part268.WorldRow13038.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13038) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13038).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13038) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13038_eq : scalarRow13038.targetFrame = BstLean.Part268.agent13038.frame := by
  norm_num [scalarRow13038,BstLean.Part268.agent13038]

noncomputable def frameData13038 : BstLean.Part264b.FrameData 13038 :=
  BstLean.Part269.frameData_from_numerics (n := 13038) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13038.worldPackage rfl BstLean.Part268.WorldRow13038.product_lower (BstLean.Part268.WorldRow13038.producthi.2.trans (by norm_num))
    scalarRow13038 repair13038 covarianceInputs13038 (fun i hi => sourceNumerics13038 hi)
    BstLean.Part268.agent13038.frame targetFrame13038_eq


end BstLean.Part269.N13038

namespace BstLean.Part269.N13039
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13039 : scalarRow13039.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13039, BstLean.Part268.grid13039, BstLean.Part263.worldGrid]

theorem supplies13039 (j : Fin 43) : Supply 13039 (parameters j)
    (cellLower scalarRow13039.grid (sourceIndex j))
    (cellUpper scalarRow13039.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13039.grid grid_top_bounds13039 j

theorem radii13039 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13039.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13039 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13039 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13039.grid grid_top_bounds13039 j hθ

noncomputable def covarianceInputs13039 :
    BstLean.Part263.CovarianceInputs 13039 scalarRow13039.grid parameters (caps repair13039) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13039 grid_top_bounds13039 repair13039

noncomputable def covarianceEvent13039 : Set (AgFam 13039) :=
  BstLean.Part263.covarianceEvent 13039 scalarRow13039.grid parameters

theorem covarianceEvent13039_measurable : MeasurableSet covarianceEvent13039 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13039_payment :
    (retDist (paperDesignP 13039).toCentres).real
      (agentEv (paperDesignP 13039) covarianceEvent13039)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13039

theorem localCov13039 : BstLean.Part259.LocalCovarianceOn covarianceEvent13039
    (BstLean.Part263.cell scalarRow13039.grid) (caps repair13039) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13039

theorem covarianceGood13039_payment :
    (retDist (paperDesignP 13039).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13039)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13039_payment



end BstLean.Part269.N13039

namespace BstLean.Part269.N13039
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13039}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13039.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13039) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13039).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13039 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13039) (by norm_num) BstLean.Part268.WorldRow13039.worldPackage rfl
    BstLean.Part268.WorldRow13039.product_lower (BstLean.Part268.WorldRow13039.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13039} (hw : c ∈ Hof BstLean.Part268.WorldRow13039.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13039) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13039) (by norm_num) BstLean.Part268.WorldRow13039.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13039} (hw : c ∈ Hof BstLean.Part268.WorldRow13039.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13039) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13039).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13039) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13039_eq : scalarRow13039.targetFrame = BstLean.Part268.agent13039.frame := by
  norm_num [scalarRow13039,BstLean.Part268.agent13039]

noncomputable def frameData13039 : BstLean.Part264b.FrameData 13039 :=
  BstLean.Part269.frameData_from_numerics (n := 13039) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13039.worldPackage rfl BstLean.Part268.WorldRow13039.product_lower (BstLean.Part268.WorldRow13039.producthi.2.trans (by norm_num))
    scalarRow13039 repair13039 covarianceInputs13039 (fun i hi => sourceNumerics13039 hi)
    BstLean.Part268.agent13039.frame targetFrame13039_eq


end BstLean.Part269.N13039
