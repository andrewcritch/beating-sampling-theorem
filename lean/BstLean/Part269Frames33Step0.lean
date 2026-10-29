import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World33Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs33
import BstLean.Part269Rows33
import BstLean.Part269Sources33
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13175
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13175 : scalarRow13175.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13175, BstLean.Part268.grid13175, BstLean.Part263.worldGrid]

theorem supplies13175 (j : Fin 43) : Supply 13175 (parameters j)
    (cellLower scalarRow13175.grid (sourceIndex j))
    (cellUpper scalarRow13175.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13175.grid grid_top_bounds13175 j

theorem radii13175 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13175.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13175 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13175 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13175.grid grid_top_bounds13175 j hθ

noncomputable def covarianceInputs13175 :
    BstLean.Part263.CovarianceInputs 13175 scalarRow13175.grid parameters (caps repair13175) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13175 grid_top_bounds13175 repair13175

noncomputable def covarianceEvent13175 : Set (AgFam 13175) :=
  BstLean.Part263.covarianceEvent 13175 scalarRow13175.grid parameters

theorem covarianceEvent13175_measurable : MeasurableSet covarianceEvent13175 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13175_payment :
    (retDist (paperDesignP 13175).toCentres).real
      (agentEv (paperDesignP 13175) covarianceEvent13175)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13175

theorem localCov13175 : BstLean.Part259.LocalCovarianceOn covarianceEvent13175
    (BstLean.Part263.cell scalarRow13175.grid) (caps repair13175) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13175

theorem covarianceGood13175_payment :
    (retDist (paperDesignP 13175).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13175)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13175_payment



end BstLean.Part269.N13175

namespace BstLean.Part269.N13175
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13175}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13175.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13175) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13175).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13175 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13175) (by norm_num) BstLean.Part268.WorldRow13175.worldPackage rfl
    BstLean.Part268.WorldRow13175.product_lower (BstLean.Part268.WorldRow13175.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13175} (hw : c ∈ Hof BstLean.Part268.WorldRow13175.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13175) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13175) (by norm_num) BstLean.Part268.WorldRow13175.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13175} (hw : c ∈ Hof BstLean.Part268.WorldRow13175.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13175) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13175).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13175) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13175_eq : scalarRow13175.targetFrame = BstLean.Part268.agent13175.frame := by
  norm_num [scalarRow13175,BstLean.Part268.agent13175]

noncomputable def frameData13175 : BstLean.Part264b.FrameData 13175 :=
  BstLean.Part269.frameData_from_numerics (n := 13175) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13175.worldPackage rfl BstLean.Part268.WorldRow13175.product_lower (BstLean.Part268.WorldRow13175.producthi.2.trans (by norm_num))
    scalarRow13175 repair13175 covarianceInputs13175 (fun i hi => sourceNumerics13175 hi)
    BstLean.Part268.agent13175.frame targetFrame13175_eq


end BstLean.Part269.N13175

namespace BstLean.Part269.N13176
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13176 : scalarRow13176.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13176, BstLean.Part268.grid13176, BstLean.Part263.worldGrid]

theorem supplies13176 (j : Fin 43) : Supply 13176 (parameters j)
    (cellLower scalarRow13176.grid (sourceIndex j))
    (cellUpper scalarRow13176.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13176.grid grid_top_bounds13176 j

theorem radii13176 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13176.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13176 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13176 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13176.grid grid_top_bounds13176 j hθ

noncomputable def covarianceInputs13176 :
    BstLean.Part263.CovarianceInputs 13176 scalarRow13176.grid parameters (caps repair13176) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13176 grid_top_bounds13176 repair13176

noncomputable def covarianceEvent13176 : Set (AgFam 13176) :=
  BstLean.Part263.covarianceEvent 13176 scalarRow13176.grid parameters

theorem covarianceEvent13176_measurable : MeasurableSet covarianceEvent13176 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13176_payment :
    (retDist (paperDesignP 13176).toCentres).real
      (agentEv (paperDesignP 13176) covarianceEvent13176)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13176

theorem localCov13176 : BstLean.Part259.LocalCovarianceOn covarianceEvent13176
    (BstLean.Part263.cell scalarRow13176.grid) (caps repair13176) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13176

theorem covarianceGood13176_payment :
    (retDist (paperDesignP 13176).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13176)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13176_payment



end BstLean.Part269.N13176

namespace BstLean.Part269.N13176
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13176}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13176.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13176) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13176).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13176 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13176) (by norm_num) BstLean.Part268.WorldRow13176.worldPackage rfl
    BstLean.Part268.WorldRow13176.product_lower (BstLean.Part268.WorldRow13176.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13176} (hw : c ∈ Hof BstLean.Part268.WorldRow13176.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13176) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13176) (by norm_num) BstLean.Part268.WorldRow13176.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13176} (hw : c ∈ Hof BstLean.Part268.WorldRow13176.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13176) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13176).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13176) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13176_eq : scalarRow13176.targetFrame = BstLean.Part268.agent13176.frame := by
  norm_num [scalarRow13176,BstLean.Part268.agent13176]

noncomputable def frameData13176 : BstLean.Part264b.FrameData 13176 :=
  BstLean.Part269.frameData_from_numerics (n := 13176) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13176.worldPackage rfl BstLean.Part268.WorldRow13176.product_lower (BstLean.Part268.WorldRow13176.producthi.2.trans (by norm_num))
    scalarRow13176 repair13176 covarianceInputs13176 (fun i hi => sourceNumerics13176 hi)
    BstLean.Part268.agent13176.frame targetFrame13176_eq


end BstLean.Part269.N13176

namespace BstLean.Part269.N13177
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13177 : scalarRow13177.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13177, BstLean.Part268.grid13177, BstLean.Part263.worldGrid]

theorem supplies13177 (j : Fin 43) : Supply 13177 (parameters j)
    (cellLower scalarRow13177.grid (sourceIndex j))
    (cellUpper scalarRow13177.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13177.grid grid_top_bounds13177 j

theorem radii13177 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13177.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13177 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13177 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13177.grid grid_top_bounds13177 j hθ

noncomputable def covarianceInputs13177 :
    BstLean.Part263.CovarianceInputs 13177 scalarRow13177.grid parameters (caps repair13177) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13177 grid_top_bounds13177 repair13177

noncomputable def covarianceEvent13177 : Set (AgFam 13177) :=
  BstLean.Part263.covarianceEvent 13177 scalarRow13177.grid parameters

theorem covarianceEvent13177_measurable : MeasurableSet covarianceEvent13177 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13177_payment :
    (retDist (paperDesignP 13177).toCentres).real
      (agentEv (paperDesignP 13177) covarianceEvent13177)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13177

theorem localCov13177 : BstLean.Part259.LocalCovarianceOn covarianceEvent13177
    (BstLean.Part263.cell scalarRow13177.grid) (caps repair13177) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13177

theorem covarianceGood13177_payment :
    (retDist (paperDesignP 13177).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13177)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13177_payment



end BstLean.Part269.N13177

namespace BstLean.Part269.N13177
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13177}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13177.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13177) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13177).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13177 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13177) (by norm_num) BstLean.Part268.WorldRow13177.worldPackage rfl
    BstLean.Part268.WorldRow13177.product_lower (BstLean.Part268.WorldRow13177.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13177} (hw : c ∈ Hof BstLean.Part268.WorldRow13177.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13177) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13177) (by norm_num) BstLean.Part268.WorldRow13177.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13177} (hw : c ∈ Hof BstLean.Part268.WorldRow13177.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13177) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13177).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13177) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13177_eq : scalarRow13177.targetFrame = BstLean.Part268.agent13177.frame := by
  norm_num [scalarRow13177,BstLean.Part268.agent13177]

noncomputable def frameData13177 : BstLean.Part264b.FrameData 13177 :=
  BstLean.Part269.frameData_from_numerics (n := 13177) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13177.worldPackage rfl BstLean.Part268.WorldRow13177.product_lower (BstLean.Part268.WorldRow13177.producthi.2.trans (by norm_num))
    scalarRow13177 repair13177 covarianceInputs13177 (fun i hi => sourceNumerics13177 hi)
    BstLean.Part268.agent13177.frame targetFrame13177_eq


end BstLean.Part269.N13177

namespace BstLean.Part269.N13178
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13178 : scalarRow13178.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13178, BstLean.Part268.grid13178, BstLean.Part263.worldGrid]

theorem supplies13178 (j : Fin 43) : Supply 13178 (parameters j)
    (cellLower scalarRow13178.grid (sourceIndex j))
    (cellUpper scalarRow13178.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13178.grid grid_top_bounds13178 j

theorem radii13178 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13178.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13178 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13178 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13178.grid grid_top_bounds13178 j hθ

noncomputable def covarianceInputs13178 :
    BstLean.Part263.CovarianceInputs 13178 scalarRow13178.grid parameters (caps repair13178) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13178 grid_top_bounds13178 repair13178

noncomputable def covarianceEvent13178 : Set (AgFam 13178) :=
  BstLean.Part263.covarianceEvent 13178 scalarRow13178.grid parameters

theorem covarianceEvent13178_measurable : MeasurableSet covarianceEvent13178 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13178_payment :
    (retDist (paperDesignP 13178).toCentres).real
      (agentEv (paperDesignP 13178) covarianceEvent13178)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13178

theorem localCov13178 : BstLean.Part259.LocalCovarianceOn covarianceEvent13178
    (BstLean.Part263.cell scalarRow13178.grid) (caps repair13178) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13178

theorem covarianceGood13178_payment :
    (retDist (paperDesignP 13178).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13178)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13178_payment



end BstLean.Part269.N13178

namespace BstLean.Part269.N13178
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13178}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13178.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13178) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13178).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13178 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13178) (by norm_num) BstLean.Part268.WorldRow13178.worldPackage rfl
    BstLean.Part268.WorldRow13178.product_lower (BstLean.Part268.WorldRow13178.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13178} (hw : c ∈ Hof BstLean.Part268.WorldRow13178.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13178) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13178) (by norm_num) BstLean.Part268.WorldRow13178.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13178} (hw : c ∈ Hof BstLean.Part268.WorldRow13178.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13178) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13178).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13178) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13178_eq : scalarRow13178.targetFrame = BstLean.Part268.agent13178.frame := by
  norm_num [scalarRow13178,BstLean.Part268.agent13178]

noncomputable def frameData13178 : BstLean.Part264b.FrameData 13178 :=
  BstLean.Part269.frameData_from_numerics (n := 13178) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13178.worldPackage rfl BstLean.Part268.WorldRow13178.product_lower (BstLean.Part268.WorldRow13178.producthi.2.trans (by norm_num))
    scalarRow13178 repair13178 covarianceInputs13178 (fun i hi => sourceNumerics13178 hi)
    BstLean.Part268.agent13178.frame targetFrame13178_eq


end BstLean.Part269.N13178

namespace BstLean.Part269.N13179
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13179 : scalarRow13179.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13179, BstLean.Part268.grid13179, BstLean.Part263.worldGrid]

theorem supplies13179 (j : Fin 43) : Supply 13179 (parameters j)
    (cellLower scalarRow13179.grid (sourceIndex j))
    (cellUpper scalarRow13179.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13179.grid grid_top_bounds13179 j

theorem radii13179 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13179.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13179 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13179 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13179.grid grid_top_bounds13179 j hθ

noncomputable def covarianceInputs13179 :
    BstLean.Part263.CovarianceInputs 13179 scalarRow13179.grid parameters (caps repair13179) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13179 grid_top_bounds13179 repair13179

noncomputable def covarianceEvent13179 : Set (AgFam 13179) :=
  BstLean.Part263.covarianceEvent 13179 scalarRow13179.grid parameters

theorem covarianceEvent13179_measurable : MeasurableSet covarianceEvent13179 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13179_payment :
    (retDist (paperDesignP 13179).toCentres).real
      (agentEv (paperDesignP 13179) covarianceEvent13179)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13179

theorem localCov13179 : BstLean.Part259.LocalCovarianceOn covarianceEvent13179
    (BstLean.Part263.cell scalarRow13179.grid) (caps repair13179) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13179

theorem covarianceGood13179_payment :
    (retDist (paperDesignP 13179).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13179)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13179_payment



end BstLean.Part269.N13179

namespace BstLean.Part269.N13179
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13179}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13179.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13179) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13179).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13179 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13179) (by norm_num) BstLean.Part268.WorldRow13179.worldPackage rfl
    BstLean.Part268.WorldRow13179.product_lower (BstLean.Part268.WorldRow13179.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13179} (hw : c ∈ Hof BstLean.Part268.WorldRow13179.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13179) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13179) (by norm_num) BstLean.Part268.WorldRow13179.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13179} (hw : c ∈ Hof BstLean.Part268.WorldRow13179.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13179) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13179).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13179) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13179_eq : scalarRow13179.targetFrame = BstLean.Part268.agent13179.frame := by
  norm_num [scalarRow13179,BstLean.Part268.agent13179]

noncomputable def frameData13179 : BstLean.Part264b.FrameData 13179 :=
  BstLean.Part269.frameData_from_numerics (n := 13179) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13179.worldPackage rfl BstLean.Part268.WorldRow13179.product_lower (BstLean.Part268.WorldRow13179.producthi.2.trans (by norm_num))
    scalarRow13179 repair13179 covarianceInputs13179 (fun i hi => sourceNumerics13179 hi)
    BstLean.Part268.agent13179.frame targetFrame13179_eq


end BstLean.Part269.N13179
