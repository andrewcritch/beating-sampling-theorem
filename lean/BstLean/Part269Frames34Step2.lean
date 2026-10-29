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

namespace BstLean.Part269.N13210
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13210 : scalarRow13210.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13210, BstLean.Part268.grid13210, BstLean.Part263.worldGrid]

theorem supplies13210 (j : Fin 43) : Supply 13210 (parameters j)
    (cellLower scalarRow13210.grid (sourceIndex j))
    (cellUpper scalarRow13210.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13210.grid grid_top_bounds13210 j

theorem radii13210 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13210.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13210 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13210 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13210.grid grid_top_bounds13210 j hθ

noncomputable def covarianceInputs13210 :
    BstLean.Part263.CovarianceInputs 13210 scalarRow13210.grid parameters (caps repair13210) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13210 grid_top_bounds13210 repair13210

noncomputable def covarianceEvent13210 : Set (AgFam 13210) :=
  BstLean.Part263.covarianceEvent 13210 scalarRow13210.grid parameters

theorem covarianceEvent13210_measurable : MeasurableSet covarianceEvent13210 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13210_payment :
    (retDist (paperDesignP 13210).toCentres).real
      (agentEv (paperDesignP 13210) covarianceEvent13210)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13210

theorem localCov13210 : BstLean.Part259.LocalCovarianceOn covarianceEvent13210
    (BstLean.Part263.cell scalarRow13210.grid) (caps repair13210) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13210

theorem covarianceGood13210_payment :
    (retDist (paperDesignP 13210).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13210)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13210_payment



end BstLean.Part269.N13210

namespace BstLean.Part269.N13210
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13210}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13210.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13210) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13210).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13210 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13210) (by norm_num) BstLean.Part268.WorldRow13210.worldPackage rfl
    BstLean.Part268.WorldRow13210.product_lower (BstLean.Part268.WorldRow13210.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13210} (hw : c ∈ Hof BstLean.Part268.WorldRow13210.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13210) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13210) (by norm_num) BstLean.Part268.WorldRow13210.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13210} (hw : c ∈ Hof BstLean.Part268.WorldRow13210.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13210) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13210).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13210) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13210_eq : scalarRow13210.targetFrame = BstLean.Part268.agent13210.frame := by
  norm_num [scalarRow13210,BstLean.Part268.agent13210]

noncomputable def frameData13210 : BstLean.Part264b.FrameData 13210 :=
  BstLean.Part269.frameData_from_numerics (n := 13210) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13210.worldPackage rfl BstLean.Part268.WorldRow13210.product_lower (BstLean.Part268.WorldRow13210.producthi.2.trans (by norm_num))
    scalarRow13210 repair13210 covarianceInputs13210 (fun i hi => sourceNumerics13210 hi)
    BstLean.Part268.agent13210.frame targetFrame13210_eq


end BstLean.Part269.N13210

namespace BstLean.Part269.N13211
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13211 : scalarRow13211.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13211, BstLean.Part268.grid13211, BstLean.Part263.worldGrid]

theorem supplies13211 (j : Fin 43) : Supply 13211 (parameters j)
    (cellLower scalarRow13211.grid (sourceIndex j))
    (cellUpper scalarRow13211.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13211.grid grid_top_bounds13211 j

theorem radii13211 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13211.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13211 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13211 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13211.grid grid_top_bounds13211 j hθ

noncomputable def covarianceInputs13211 :
    BstLean.Part263.CovarianceInputs 13211 scalarRow13211.grid parameters (caps repair13211) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13211 grid_top_bounds13211 repair13211

noncomputable def covarianceEvent13211 : Set (AgFam 13211) :=
  BstLean.Part263.covarianceEvent 13211 scalarRow13211.grid parameters

theorem covarianceEvent13211_measurable : MeasurableSet covarianceEvent13211 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13211_payment :
    (retDist (paperDesignP 13211).toCentres).real
      (agentEv (paperDesignP 13211) covarianceEvent13211)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13211

theorem localCov13211 : BstLean.Part259.LocalCovarianceOn covarianceEvent13211
    (BstLean.Part263.cell scalarRow13211.grid) (caps repair13211) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13211

theorem covarianceGood13211_payment :
    (retDist (paperDesignP 13211).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13211)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13211_payment



end BstLean.Part269.N13211

namespace BstLean.Part269.N13211
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13211}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13211.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13211) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13211).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13211 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13211) (by norm_num) BstLean.Part268.WorldRow13211.worldPackage rfl
    BstLean.Part268.WorldRow13211.product_lower (BstLean.Part268.WorldRow13211.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13211} (hw : c ∈ Hof BstLean.Part268.WorldRow13211.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13211) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13211) (by norm_num) BstLean.Part268.WorldRow13211.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13211} (hw : c ∈ Hof BstLean.Part268.WorldRow13211.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13211) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13211).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13211) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13211_eq : scalarRow13211.targetFrame = BstLean.Part268.agent13211.frame := by
  norm_num [scalarRow13211,BstLean.Part268.agent13211]

noncomputable def frameData13211 : BstLean.Part264b.FrameData 13211 :=
  BstLean.Part269.frameData_from_numerics (n := 13211) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13211.worldPackage rfl BstLean.Part268.WorldRow13211.product_lower (BstLean.Part268.WorldRow13211.producthi.2.trans (by norm_num))
    scalarRow13211 repair13211 covarianceInputs13211 (fun i hi => sourceNumerics13211 hi)
    BstLean.Part268.agent13211.frame targetFrame13211_eq


end BstLean.Part269.N13211

namespace BstLean.Part269.N13212
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13212 : scalarRow13212.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13212, BstLean.Part268.grid13212, BstLean.Part263.worldGrid]

theorem supplies13212 (j : Fin 43) : Supply 13212 (parameters j)
    (cellLower scalarRow13212.grid (sourceIndex j))
    (cellUpper scalarRow13212.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13212.grid grid_top_bounds13212 j

theorem radii13212 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13212.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13212 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13212 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13212.grid grid_top_bounds13212 j hθ

noncomputable def covarianceInputs13212 :
    BstLean.Part263.CovarianceInputs 13212 scalarRow13212.grid parameters (caps repair13212) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13212 grid_top_bounds13212 repair13212

noncomputable def covarianceEvent13212 : Set (AgFam 13212) :=
  BstLean.Part263.covarianceEvent 13212 scalarRow13212.grid parameters

theorem covarianceEvent13212_measurable : MeasurableSet covarianceEvent13212 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13212_payment :
    (retDist (paperDesignP 13212).toCentres).real
      (agentEv (paperDesignP 13212) covarianceEvent13212)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13212

theorem localCov13212 : BstLean.Part259.LocalCovarianceOn covarianceEvent13212
    (BstLean.Part263.cell scalarRow13212.grid) (caps repair13212) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13212

theorem covarianceGood13212_payment :
    (retDist (paperDesignP 13212).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13212)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13212_payment



end BstLean.Part269.N13212

namespace BstLean.Part269.N13212
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13212}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13212.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13212) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13212).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13212 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13212) (by norm_num) BstLean.Part268.WorldRow13212.worldPackage rfl
    BstLean.Part268.WorldRow13212.product_lower (BstLean.Part268.WorldRow13212.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13212} (hw : c ∈ Hof BstLean.Part268.WorldRow13212.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13212) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13212) (by norm_num) BstLean.Part268.WorldRow13212.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13212} (hw : c ∈ Hof BstLean.Part268.WorldRow13212.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13212) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13212).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13212) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13212_eq : scalarRow13212.targetFrame = BstLean.Part268.agent13212.frame := by
  norm_num [scalarRow13212,BstLean.Part268.agent13212]

noncomputable def frameData13212 : BstLean.Part264b.FrameData 13212 :=
  BstLean.Part269.frameData_from_numerics (n := 13212) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13212.worldPackage rfl BstLean.Part268.WorldRow13212.product_lower (BstLean.Part268.WorldRow13212.producthi.2.trans (by norm_num))
    scalarRow13212 repair13212 covarianceInputs13212 (fun i hi => sourceNumerics13212 hi)
    BstLean.Part268.agent13212.frame targetFrame13212_eq


end BstLean.Part269.N13212

namespace BstLean.Part269.N13213
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13213 : scalarRow13213.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13213, BstLean.Part268.grid13213, BstLean.Part263.worldGrid]

theorem supplies13213 (j : Fin 43) : Supply 13213 (parameters j)
    (cellLower scalarRow13213.grid (sourceIndex j))
    (cellUpper scalarRow13213.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13213.grid grid_top_bounds13213 j

theorem radii13213 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13213.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13213 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13213 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13213.grid grid_top_bounds13213 j hθ

noncomputable def covarianceInputs13213 :
    BstLean.Part263.CovarianceInputs 13213 scalarRow13213.grid parameters (caps repair13213) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13213 grid_top_bounds13213 repair13213

noncomputable def covarianceEvent13213 : Set (AgFam 13213) :=
  BstLean.Part263.covarianceEvent 13213 scalarRow13213.grid parameters

theorem covarianceEvent13213_measurable : MeasurableSet covarianceEvent13213 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13213_payment :
    (retDist (paperDesignP 13213).toCentres).real
      (agentEv (paperDesignP 13213) covarianceEvent13213)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13213

theorem localCov13213 : BstLean.Part259.LocalCovarianceOn covarianceEvent13213
    (BstLean.Part263.cell scalarRow13213.grid) (caps repair13213) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13213

theorem covarianceGood13213_payment :
    (retDist (paperDesignP 13213).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13213)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13213_payment



end BstLean.Part269.N13213

namespace BstLean.Part269.N13213
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13213}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13213.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13213) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13213).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13213 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13213) (by norm_num) BstLean.Part268.WorldRow13213.worldPackage rfl
    BstLean.Part268.WorldRow13213.product_lower (BstLean.Part268.WorldRow13213.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13213} (hw : c ∈ Hof BstLean.Part268.WorldRow13213.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13213) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13213) (by norm_num) BstLean.Part268.WorldRow13213.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13213} (hw : c ∈ Hof BstLean.Part268.WorldRow13213.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13213) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13213).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13213) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13213_eq : scalarRow13213.targetFrame = BstLean.Part268.agent13213.frame := by
  norm_num [scalarRow13213,BstLean.Part268.agent13213]

noncomputable def frameData13213 : BstLean.Part264b.FrameData 13213 :=
  BstLean.Part269.frameData_from_numerics (n := 13213) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13213.worldPackage rfl BstLean.Part268.WorldRow13213.product_lower (BstLean.Part268.WorldRow13213.producthi.2.trans (by norm_num))
    scalarRow13213 repair13213 covarianceInputs13213 (fun i hi => sourceNumerics13213 hi)
    BstLean.Part268.agent13213.frame targetFrame13213_eq


end BstLean.Part269.N13213

namespace BstLean.Part269.N13214
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13214 : scalarRow13214.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13214, BstLean.Part268.grid13214, BstLean.Part263.worldGrid]

theorem supplies13214 (j : Fin 43) : Supply 13214 (parameters j)
    (cellLower scalarRow13214.grid (sourceIndex j))
    (cellUpper scalarRow13214.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13214.grid grid_top_bounds13214 j

theorem radii13214 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13214.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13214 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13214 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13214.grid grid_top_bounds13214 j hθ

noncomputable def covarianceInputs13214 :
    BstLean.Part263.CovarianceInputs 13214 scalarRow13214.grid parameters (caps repair13214) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13214 grid_top_bounds13214 repair13214

noncomputable def covarianceEvent13214 : Set (AgFam 13214) :=
  BstLean.Part263.covarianceEvent 13214 scalarRow13214.grid parameters

theorem covarianceEvent13214_measurable : MeasurableSet covarianceEvent13214 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13214_payment :
    (retDist (paperDesignP 13214).toCentres).real
      (agentEv (paperDesignP 13214) covarianceEvent13214)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13214

theorem localCov13214 : BstLean.Part259.LocalCovarianceOn covarianceEvent13214
    (BstLean.Part263.cell scalarRow13214.grid) (caps repair13214) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13214

theorem covarianceGood13214_payment :
    (retDist (paperDesignP 13214).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13214)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13214_payment



end BstLean.Part269.N13214

namespace BstLean.Part269.N13214
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13214}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13214.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13214) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13214).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13214 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13214) (by norm_num) BstLean.Part268.WorldRow13214.worldPackage rfl
    BstLean.Part268.WorldRow13214.product_lower (BstLean.Part268.WorldRow13214.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13214} (hw : c ∈ Hof BstLean.Part268.WorldRow13214.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13214) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13214) (by norm_num) BstLean.Part268.WorldRow13214.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13214} (hw : c ∈ Hof BstLean.Part268.WorldRow13214.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13214) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13214).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13214) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13214_eq : scalarRow13214.targetFrame = BstLean.Part268.agent13214.frame := by
  norm_num [scalarRow13214,BstLean.Part268.agent13214]

noncomputable def frameData13214 : BstLean.Part264b.FrameData 13214 :=
  BstLean.Part269.frameData_from_numerics (n := 13214) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13214.worldPackage rfl BstLean.Part268.WorldRow13214.product_lower (BstLean.Part268.WorldRow13214.producthi.2.trans (by norm_num))
    scalarRow13214 repair13214 covarianceInputs13214 (fun i hi => sourceNumerics13214 hi)
    BstLean.Part268.agent13214.frame targetFrame13214_eq


end BstLean.Part269.N13214
