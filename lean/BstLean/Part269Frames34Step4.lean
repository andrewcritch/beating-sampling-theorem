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

namespace BstLean.Part269.N13220
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13220 : scalarRow13220.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13220, BstLean.Part268.grid13220, BstLean.Part263.worldGrid]

theorem supplies13220 (j : Fin 43) : Supply 13220 (parameters j)
    (cellLower scalarRow13220.grid (sourceIndex j))
    (cellUpper scalarRow13220.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13220.grid grid_top_bounds13220 j

theorem radii13220 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13220.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13220 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13220 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13220.grid grid_top_bounds13220 j hθ

noncomputable def covarianceInputs13220 :
    BstLean.Part263.CovarianceInputs 13220 scalarRow13220.grid parameters (caps repair13220) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13220 grid_top_bounds13220 repair13220

noncomputable def covarianceEvent13220 : Set (AgFam 13220) :=
  BstLean.Part263.covarianceEvent 13220 scalarRow13220.grid parameters

theorem covarianceEvent13220_measurable : MeasurableSet covarianceEvent13220 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13220_payment :
    (retDist (paperDesignP 13220).toCentres).real
      (agentEv (paperDesignP 13220) covarianceEvent13220)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13220

theorem localCov13220 : BstLean.Part259.LocalCovarianceOn covarianceEvent13220
    (BstLean.Part263.cell scalarRow13220.grid) (caps repair13220) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13220

theorem covarianceGood13220_payment :
    (retDist (paperDesignP 13220).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13220)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13220_payment



end BstLean.Part269.N13220

namespace BstLean.Part269.N13220
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13220}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13220.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13220) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13220).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13220 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13220) (by norm_num) BstLean.Part268.WorldRow13220.worldPackage rfl
    BstLean.Part268.WorldRow13220.product_lower (BstLean.Part268.WorldRow13220.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13220} (hw : c ∈ Hof BstLean.Part268.WorldRow13220.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13220) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13220) (by norm_num) BstLean.Part268.WorldRow13220.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13220} (hw : c ∈ Hof BstLean.Part268.WorldRow13220.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13220) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13220).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13220) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13220_eq : scalarRow13220.targetFrame = BstLean.Part268.agent13220.frame := by
  norm_num [scalarRow13220,BstLean.Part268.agent13220]

noncomputable def frameData13220 : BstLean.Part264b.FrameData 13220 :=
  BstLean.Part269.frameData_from_numerics (n := 13220) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13220.worldPackage rfl BstLean.Part268.WorldRow13220.product_lower (BstLean.Part268.WorldRow13220.producthi.2.trans (by norm_num))
    scalarRow13220 repair13220 covarianceInputs13220 (fun i hi => sourceNumerics13220 hi)
    BstLean.Part268.agent13220.frame targetFrame13220_eq


end BstLean.Part269.N13220

namespace BstLean.Part269.N13221
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13221 : scalarRow13221.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13221, BstLean.Part268.grid13221, BstLean.Part263.worldGrid]

theorem supplies13221 (j : Fin 43) : Supply 13221 (parameters j)
    (cellLower scalarRow13221.grid (sourceIndex j))
    (cellUpper scalarRow13221.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13221.grid grid_top_bounds13221 j

theorem radii13221 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13221.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13221 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13221 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13221.grid grid_top_bounds13221 j hθ

noncomputable def covarianceInputs13221 :
    BstLean.Part263.CovarianceInputs 13221 scalarRow13221.grid parameters (caps repair13221) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13221 grid_top_bounds13221 repair13221

noncomputable def covarianceEvent13221 : Set (AgFam 13221) :=
  BstLean.Part263.covarianceEvent 13221 scalarRow13221.grid parameters

theorem covarianceEvent13221_measurable : MeasurableSet covarianceEvent13221 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13221_payment :
    (retDist (paperDesignP 13221).toCentres).real
      (agentEv (paperDesignP 13221) covarianceEvent13221)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13221

theorem localCov13221 : BstLean.Part259.LocalCovarianceOn covarianceEvent13221
    (BstLean.Part263.cell scalarRow13221.grid) (caps repair13221) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13221

theorem covarianceGood13221_payment :
    (retDist (paperDesignP 13221).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13221)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13221_payment



end BstLean.Part269.N13221

namespace BstLean.Part269.N13221
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13221}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13221.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13221) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13221).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13221 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13221) (by norm_num) BstLean.Part268.WorldRow13221.worldPackage rfl
    BstLean.Part268.WorldRow13221.product_lower (BstLean.Part268.WorldRow13221.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13221} (hw : c ∈ Hof BstLean.Part268.WorldRow13221.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13221) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13221) (by norm_num) BstLean.Part268.WorldRow13221.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13221} (hw : c ∈ Hof BstLean.Part268.WorldRow13221.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13221) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13221).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13221) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13221_eq : scalarRow13221.targetFrame = BstLean.Part268.agent13221.frame := by
  norm_num [scalarRow13221,BstLean.Part268.agent13221]

noncomputable def frameData13221 : BstLean.Part264b.FrameData 13221 :=
  BstLean.Part269.frameData_from_numerics (n := 13221) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13221.worldPackage rfl BstLean.Part268.WorldRow13221.product_lower (BstLean.Part268.WorldRow13221.producthi.2.trans (by norm_num))
    scalarRow13221 repair13221 covarianceInputs13221 (fun i hi => sourceNumerics13221 hi)
    BstLean.Part268.agent13221.frame targetFrame13221_eq


end BstLean.Part269.N13221

namespace BstLean.Part269.N13222
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13222 : scalarRow13222.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13222, BstLean.Part268.grid13222, BstLean.Part263.worldGrid]

theorem supplies13222 (j : Fin 43) : Supply 13222 (parameters j)
    (cellLower scalarRow13222.grid (sourceIndex j))
    (cellUpper scalarRow13222.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13222.grid grid_top_bounds13222 j

theorem radii13222 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13222.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13222 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13222 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13222.grid grid_top_bounds13222 j hθ

noncomputable def covarianceInputs13222 :
    BstLean.Part263.CovarianceInputs 13222 scalarRow13222.grid parameters (caps repair13222) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13222 grid_top_bounds13222 repair13222

noncomputable def covarianceEvent13222 : Set (AgFam 13222) :=
  BstLean.Part263.covarianceEvent 13222 scalarRow13222.grid parameters

theorem covarianceEvent13222_measurable : MeasurableSet covarianceEvent13222 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13222_payment :
    (retDist (paperDesignP 13222).toCentres).real
      (agentEv (paperDesignP 13222) covarianceEvent13222)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13222

theorem localCov13222 : BstLean.Part259.LocalCovarianceOn covarianceEvent13222
    (BstLean.Part263.cell scalarRow13222.grid) (caps repair13222) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13222

theorem covarianceGood13222_payment :
    (retDist (paperDesignP 13222).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13222)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13222_payment



end BstLean.Part269.N13222

namespace BstLean.Part269.N13222
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13222}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13222.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13222) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13222).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13222 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13222) (by norm_num) BstLean.Part268.WorldRow13222.worldPackage rfl
    BstLean.Part268.WorldRow13222.product_lower (BstLean.Part268.WorldRow13222.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13222} (hw : c ∈ Hof BstLean.Part268.WorldRow13222.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13222) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13222) (by norm_num) BstLean.Part268.WorldRow13222.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13222} (hw : c ∈ Hof BstLean.Part268.WorldRow13222.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13222) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13222).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13222) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13222_eq : scalarRow13222.targetFrame = BstLean.Part268.agent13222.frame := by
  norm_num [scalarRow13222,BstLean.Part268.agent13222]

noncomputable def frameData13222 : BstLean.Part264b.FrameData 13222 :=
  BstLean.Part269.frameData_from_numerics (n := 13222) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13222.worldPackage rfl BstLean.Part268.WorldRow13222.product_lower (BstLean.Part268.WorldRow13222.producthi.2.trans (by norm_num))
    scalarRow13222 repair13222 covarianceInputs13222 (fun i hi => sourceNumerics13222 hi)
    BstLean.Part268.agent13222.frame targetFrame13222_eq


end BstLean.Part269.N13222

namespace BstLean.Part269.N13223
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13223 : scalarRow13223.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13223, BstLean.Part268.grid13223, BstLean.Part263.worldGrid]

theorem supplies13223 (j : Fin 43) : Supply 13223 (parameters j)
    (cellLower scalarRow13223.grid (sourceIndex j))
    (cellUpper scalarRow13223.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13223.grid grid_top_bounds13223 j

theorem radii13223 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13223.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13223 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13223 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13223.grid grid_top_bounds13223 j hθ

noncomputable def covarianceInputs13223 :
    BstLean.Part263.CovarianceInputs 13223 scalarRow13223.grid parameters (caps repair13223) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13223 grid_top_bounds13223 repair13223

noncomputable def covarianceEvent13223 : Set (AgFam 13223) :=
  BstLean.Part263.covarianceEvent 13223 scalarRow13223.grid parameters

theorem covarianceEvent13223_measurable : MeasurableSet covarianceEvent13223 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13223_payment :
    (retDist (paperDesignP 13223).toCentres).real
      (agentEv (paperDesignP 13223) covarianceEvent13223)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13223

theorem localCov13223 : BstLean.Part259.LocalCovarianceOn covarianceEvent13223
    (BstLean.Part263.cell scalarRow13223.grid) (caps repair13223) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13223

theorem covarianceGood13223_payment :
    (retDist (paperDesignP 13223).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13223)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13223_payment



end BstLean.Part269.N13223

namespace BstLean.Part269.N13223
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13223}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13223.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13223) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13223).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13223 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13223) (by norm_num) BstLean.Part268.WorldRow13223.worldPackage rfl
    BstLean.Part268.WorldRow13223.product_lower (BstLean.Part268.WorldRow13223.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13223} (hw : c ∈ Hof BstLean.Part268.WorldRow13223.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13223) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13223) (by norm_num) BstLean.Part268.WorldRow13223.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13223} (hw : c ∈ Hof BstLean.Part268.WorldRow13223.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13223) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13223).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13223) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13223_eq : scalarRow13223.targetFrame = BstLean.Part268.agent13223.frame := by
  norm_num [scalarRow13223,BstLean.Part268.agent13223]

noncomputable def frameData13223 : BstLean.Part264b.FrameData 13223 :=
  BstLean.Part269.frameData_from_numerics (n := 13223) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13223.worldPackage rfl BstLean.Part268.WorldRow13223.product_lower (BstLean.Part268.WorldRow13223.producthi.2.trans (by norm_num))
    scalarRow13223 repair13223 covarianceInputs13223 (fun i hi => sourceNumerics13223 hi)
    BstLean.Part268.agent13223.frame targetFrame13223_eq


end BstLean.Part269.N13223
