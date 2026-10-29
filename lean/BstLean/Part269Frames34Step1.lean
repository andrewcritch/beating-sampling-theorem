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

namespace BstLean.Part269.N13205
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13205 : scalarRow13205.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13205, BstLean.Part268.grid13205, BstLean.Part263.worldGrid]

theorem supplies13205 (j : Fin 43) : Supply 13205 (parameters j)
    (cellLower scalarRow13205.grid (sourceIndex j))
    (cellUpper scalarRow13205.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13205.grid grid_top_bounds13205 j

theorem radii13205 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13205.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13205 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13205 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13205.grid grid_top_bounds13205 j hθ

noncomputable def covarianceInputs13205 :
    BstLean.Part263.CovarianceInputs 13205 scalarRow13205.grid parameters (caps repair13205) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13205 grid_top_bounds13205 repair13205

noncomputable def covarianceEvent13205 : Set (AgFam 13205) :=
  BstLean.Part263.covarianceEvent 13205 scalarRow13205.grid parameters

theorem covarianceEvent13205_measurable : MeasurableSet covarianceEvent13205 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13205_payment :
    (retDist (paperDesignP 13205).toCentres).real
      (agentEv (paperDesignP 13205) covarianceEvent13205)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13205

theorem localCov13205 : BstLean.Part259.LocalCovarianceOn covarianceEvent13205
    (BstLean.Part263.cell scalarRow13205.grid) (caps repair13205) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13205

theorem covarianceGood13205_payment :
    (retDist (paperDesignP 13205).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13205)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13205_payment



end BstLean.Part269.N13205

namespace BstLean.Part269.N13205
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13205}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13205.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13205) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13205).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13205 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13205) (by norm_num) BstLean.Part268.WorldRow13205.worldPackage rfl
    BstLean.Part268.WorldRow13205.product_lower (BstLean.Part268.WorldRow13205.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13205} (hw : c ∈ Hof BstLean.Part268.WorldRow13205.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13205) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13205) (by norm_num) BstLean.Part268.WorldRow13205.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13205} (hw : c ∈ Hof BstLean.Part268.WorldRow13205.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13205) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13205).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13205) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13205_eq : scalarRow13205.targetFrame = BstLean.Part268.agent13205.frame := by
  norm_num [scalarRow13205,BstLean.Part268.agent13205]

noncomputable def frameData13205 : BstLean.Part264b.FrameData 13205 :=
  BstLean.Part269.frameData_from_numerics (n := 13205) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13205.worldPackage rfl BstLean.Part268.WorldRow13205.product_lower (BstLean.Part268.WorldRow13205.producthi.2.trans (by norm_num))
    scalarRow13205 repair13205 covarianceInputs13205 (fun i hi => sourceNumerics13205 hi)
    BstLean.Part268.agent13205.frame targetFrame13205_eq


end BstLean.Part269.N13205

namespace BstLean.Part269.N13206
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13206 : scalarRow13206.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13206, BstLean.Part268.grid13206, BstLean.Part263.worldGrid]

theorem supplies13206 (j : Fin 43) : Supply 13206 (parameters j)
    (cellLower scalarRow13206.grid (sourceIndex j))
    (cellUpper scalarRow13206.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13206.grid grid_top_bounds13206 j

theorem radii13206 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13206.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13206 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13206 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13206.grid grid_top_bounds13206 j hθ

noncomputable def covarianceInputs13206 :
    BstLean.Part263.CovarianceInputs 13206 scalarRow13206.grid parameters (caps repair13206) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13206 grid_top_bounds13206 repair13206

noncomputable def covarianceEvent13206 : Set (AgFam 13206) :=
  BstLean.Part263.covarianceEvent 13206 scalarRow13206.grid parameters

theorem covarianceEvent13206_measurable : MeasurableSet covarianceEvent13206 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13206_payment :
    (retDist (paperDesignP 13206).toCentres).real
      (agentEv (paperDesignP 13206) covarianceEvent13206)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13206

theorem localCov13206 : BstLean.Part259.LocalCovarianceOn covarianceEvent13206
    (BstLean.Part263.cell scalarRow13206.grid) (caps repair13206) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13206

theorem covarianceGood13206_payment :
    (retDist (paperDesignP 13206).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13206)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13206_payment



end BstLean.Part269.N13206

namespace BstLean.Part269.N13206
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13206}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13206.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13206) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13206).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13206 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13206) (by norm_num) BstLean.Part268.WorldRow13206.worldPackage rfl
    BstLean.Part268.WorldRow13206.product_lower (BstLean.Part268.WorldRow13206.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13206} (hw : c ∈ Hof BstLean.Part268.WorldRow13206.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13206) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13206) (by norm_num) BstLean.Part268.WorldRow13206.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13206} (hw : c ∈ Hof BstLean.Part268.WorldRow13206.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13206) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13206).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13206) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13206_eq : scalarRow13206.targetFrame = BstLean.Part268.agent13206.frame := by
  norm_num [scalarRow13206,BstLean.Part268.agent13206]

noncomputable def frameData13206 : BstLean.Part264b.FrameData 13206 :=
  BstLean.Part269.frameData_from_numerics (n := 13206) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13206.worldPackage rfl BstLean.Part268.WorldRow13206.product_lower (BstLean.Part268.WorldRow13206.producthi.2.trans (by norm_num))
    scalarRow13206 repair13206 covarianceInputs13206 (fun i hi => sourceNumerics13206 hi)
    BstLean.Part268.agent13206.frame targetFrame13206_eq


end BstLean.Part269.N13206

namespace BstLean.Part269.N13207
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13207 : scalarRow13207.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13207, BstLean.Part268.grid13207, BstLean.Part263.worldGrid]

theorem supplies13207 (j : Fin 43) : Supply 13207 (parameters j)
    (cellLower scalarRow13207.grid (sourceIndex j))
    (cellUpper scalarRow13207.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13207.grid grid_top_bounds13207 j

theorem radii13207 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13207.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13207 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13207 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13207.grid grid_top_bounds13207 j hθ

noncomputable def covarianceInputs13207 :
    BstLean.Part263.CovarianceInputs 13207 scalarRow13207.grid parameters (caps repair13207) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13207 grid_top_bounds13207 repair13207

noncomputable def covarianceEvent13207 : Set (AgFam 13207) :=
  BstLean.Part263.covarianceEvent 13207 scalarRow13207.grid parameters

theorem covarianceEvent13207_measurable : MeasurableSet covarianceEvent13207 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13207_payment :
    (retDist (paperDesignP 13207).toCentres).real
      (agentEv (paperDesignP 13207) covarianceEvent13207)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13207

theorem localCov13207 : BstLean.Part259.LocalCovarianceOn covarianceEvent13207
    (BstLean.Part263.cell scalarRow13207.grid) (caps repair13207) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13207

theorem covarianceGood13207_payment :
    (retDist (paperDesignP 13207).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13207)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13207_payment



end BstLean.Part269.N13207

namespace BstLean.Part269.N13207
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13207}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13207.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13207) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13207).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13207 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13207) (by norm_num) BstLean.Part268.WorldRow13207.worldPackage rfl
    BstLean.Part268.WorldRow13207.product_lower (BstLean.Part268.WorldRow13207.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13207} (hw : c ∈ Hof BstLean.Part268.WorldRow13207.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13207) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13207) (by norm_num) BstLean.Part268.WorldRow13207.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13207} (hw : c ∈ Hof BstLean.Part268.WorldRow13207.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13207) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13207).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13207) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13207_eq : scalarRow13207.targetFrame = BstLean.Part268.agent13207.frame := by
  norm_num [scalarRow13207,BstLean.Part268.agent13207]

noncomputable def frameData13207 : BstLean.Part264b.FrameData 13207 :=
  BstLean.Part269.frameData_from_numerics (n := 13207) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13207.worldPackage rfl BstLean.Part268.WorldRow13207.product_lower (BstLean.Part268.WorldRow13207.producthi.2.trans (by norm_num))
    scalarRow13207 repair13207 covarianceInputs13207 (fun i hi => sourceNumerics13207 hi)
    BstLean.Part268.agent13207.frame targetFrame13207_eq


end BstLean.Part269.N13207

namespace BstLean.Part269.N13208
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13208 : scalarRow13208.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13208, BstLean.Part268.grid13208, BstLean.Part263.worldGrid]

theorem supplies13208 (j : Fin 43) : Supply 13208 (parameters j)
    (cellLower scalarRow13208.grid (sourceIndex j))
    (cellUpper scalarRow13208.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13208.grid grid_top_bounds13208 j

theorem radii13208 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13208.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13208 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13208 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13208.grid grid_top_bounds13208 j hθ

noncomputable def covarianceInputs13208 :
    BstLean.Part263.CovarianceInputs 13208 scalarRow13208.grid parameters (caps repair13208) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13208 grid_top_bounds13208 repair13208

noncomputable def covarianceEvent13208 : Set (AgFam 13208) :=
  BstLean.Part263.covarianceEvent 13208 scalarRow13208.grid parameters

theorem covarianceEvent13208_measurable : MeasurableSet covarianceEvent13208 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13208_payment :
    (retDist (paperDesignP 13208).toCentres).real
      (agentEv (paperDesignP 13208) covarianceEvent13208)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13208

theorem localCov13208 : BstLean.Part259.LocalCovarianceOn covarianceEvent13208
    (BstLean.Part263.cell scalarRow13208.grid) (caps repair13208) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13208

theorem covarianceGood13208_payment :
    (retDist (paperDesignP 13208).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13208)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13208_payment



end BstLean.Part269.N13208

namespace BstLean.Part269.N13208
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13208}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13208.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13208) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13208).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13208 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13208) (by norm_num) BstLean.Part268.WorldRow13208.worldPackage rfl
    BstLean.Part268.WorldRow13208.product_lower (BstLean.Part268.WorldRow13208.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13208} (hw : c ∈ Hof BstLean.Part268.WorldRow13208.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13208) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13208) (by norm_num) BstLean.Part268.WorldRow13208.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13208} (hw : c ∈ Hof BstLean.Part268.WorldRow13208.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13208) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13208).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13208) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13208_eq : scalarRow13208.targetFrame = BstLean.Part268.agent13208.frame := by
  norm_num [scalarRow13208,BstLean.Part268.agent13208]

noncomputable def frameData13208 : BstLean.Part264b.FrameData 13208 :=
  BstLean.Part269.frameData_from_numerics (n := 13208) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13208.worldPackage rfl BstLean.Part268.WorldRow13208.product_lower (BstLean.Part268.WorldRow13208.producthi.2.trans (by norm_num))
    scalarRow13208 repair13208 covarianceInputs13208 (fun i hi => sourceNumerics13208 hi)
    BstLean.Part268.agent13208.frame targetFrame13208_eq


end BstLean.Part269.N13208

namespace BstLean.Part269.N13209
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13209 : scalarRow13209.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13209, BstLean.Part268.grid13209, BstLean.Part263.worldGrid]

theorem supplies13209 (j : Fin 43) : Supply 13209 (parameters j)
    (cellLower scalarRow13209.grid (sourceIndex j))
    (cellUpper scalarRow13209.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13209.grid grid_top_bounds13209 j

theorem radii13209 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13209.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13209 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13209 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13209.grid grid_top_bounds13209 j hθ

noncomputable def covarianceInputs13209 :
    BstLean.Part263.CovarianceInputs 13209 scalarRow13209.grid parameters (caps repair13209) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13209 grid_top_bounds13209 repair13209

noncomputable def covarianceEvent13209 : Set (AgFam 13209) :=
  BstLean.Part263.covarianceEvent 13209 scalarRow13209.grid parameters

theorem covarianceEvent13209_measurable : MeasurableSet covarianceEvent13209 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13209_payment :
    (retDist (paperDesignP 13209).toCentres).real
      (agentEv (paperDesignP 13209) covarianceEvent13209)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13209

theorem localCov13209 : BstLean.Part259.LocalCovarianceOn covarianceEvent13209
    (BstLean.Part263.cell scalarRow13209.grid) (caps repair13209) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13209

theorem covarianceGood13209_payment :
    (retDist (paperDesignP 13209).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13209)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13209_payment



end BstLean.Part269.N13209

namespace BstLean.Part269.N13209
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13209}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13209.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13209) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13209).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13209 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13209) (by norm_num) BstLean.Part268.WorldRow13209.worldPackage rfl
    BstLean.Part268.WorldRow13209.product_lower (BstLean.Part268.WorldRow13209.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13209} (hw : c ∈ Hof BstLean.Part268.WorldRow13209.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13209) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13209) (by norm_num) BstLean.Part268.WorldRow13209.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13209} (hw : c ∈ Hof BstLean.Part268.WorldRow13209.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13209) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13209).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13209) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13209_eq : scalarRow13209.targetFrame = BstLean.Part268.agent13209.frame := by
  norm_num [scalarRow13209,BstLean.Part268.agent13209]

noncomputable def frameData13209 : BstLean.Part264b.FrameData 13209 :=
  BstLean.Part269.frameData_from_numerics (n := 13209) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13209.worldPackage rfl BstLean.Part268.WorldRow13209.product_lower (BstLean.Part268.WorldRow13209.producthi.2.trans (by norm_num))
    scalarRow13209 repair13209 covarianceInputs13209 (fun i hi => sourceNumerics13209 hi)
    BstLean.Part268.agent13209.frame targetFrame13209_eq


end BstLean.Part269.N13209
