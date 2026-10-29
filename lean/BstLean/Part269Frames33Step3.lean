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

namespace BstLean.Part269.N13190
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13190 : scalarRow13190.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13190, BstLean.Part268.grid13190, BstLean.Part263.worldGrid]

theorem supplies13190 (j : Fin 43) : Supply 13190 (parameters j)
    (cellLower scalarRow13190.grid (sourceIndex j))
    (cellUpper scalarRow13190.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13190.grid grid_top_bounds13190 j

theorem radii13190 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13190.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13190 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13190 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13190.grid grid_top_bounds13190 j hθ

noncomputable def covarianceInputs13190 :
    BstLean.Part263.CovarianceInputs 13190 scalarRow13190.grid parameters (caps repair13190) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13190 grid_top_bounds13190 repair13190

noncomputable def covarianceEvent13190 : Set (AgFam 13190) :=
  BstLean.Part263.covarianceEvent 13190 scalarRow13190.grid parameters

theorem covarianceEvent13190_measurable : MeasurableSet covarianceEvent13190 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13190_payment :
    (retDist (paperDesignP 13190).toCentres).real
      (agentEv (paperDesignP 13190) covarianceEvent13190)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13190

theorem localCov13190 : BstLean.Part259.LocalCovarianceOn covarianceEvent13190
    (BstLean.Part263.cell scalarRow13190.grid) (caps repair13190) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13190

theorem covarianceGood13190_payment :
    (retDist (paperDesignP 13190).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13190)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13190_payment



end BstLean.Part269.N13190

namespace BstLean.Part269.N13190
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13190}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13190.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13190) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13190).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13190 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13190) (by norm_num) BstLean.Part268.WorldRow13190.worldPackage rfl
    BstLean.Part268.WorldRow13190.product_lower (BstLean.Part268.WorldRow13190.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13190} (hw : c ∈ Hof BstLean.Part268.WorldRow13190.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13190) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13190) (by norm_num) BstLean.Part268.WorldRow13190.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13190} (hw : c ∈ Hof BstLean.Part268.WorldRow13190.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13190) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13190).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13190) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13190_eq : scalarRow13190.targetFrame = BstLean.Part268.agent13190.frame := by
  norm_num [scalarRow13190,BstLean.Part268.agent13190]

noncomputable def frameData13190 : BstLean.Part264b.FrameData 13190 :=
  BstLean.Part269.frameData_from_numerics (n := 13190) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13190.worldPackage rfl BstLean.Part268.WorldRow13190.product_lower (BstLean.Part268.WorldRow13190.producthi.2.trans (by norm_num))
    scalarRow13190 repair13190 covarianceInputs13190 (fun i hi => sourceNumerics13190 hi)
    BstLean.Part268.agent13190.frame targetFrame13190_eq


end BstLean.Part269.N13190

namespace BstLean.Part269.N13191
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13191 : scalarRow13191.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13191, BstLean.Part268.grid13191, BstLean.Part263.worldGrid]

theorem supplies13191 (j : Fin 43) : Supply 13191 (parameters j)
    (cellLower scalarRow13191.grid (sourceIndex j))
    (cellUpper scalarRow13191.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13191.grid grid_top_bounds13191 j

theorem radii13191 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13191.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13191 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13191 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13191.grid grid_top_bounds13191 j hθ

noncomputable def covarianceInputs13191 :
    BstLean.Part263.CovarianceInputs 13191 scalarRow13191.grid parameters (caps repair13191) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13191 grid_top_bounds13191 repair13191

noncomputable def covarianceEvent13191 : Set (AgFam 13191) :=
  BstLean.Part263.covarianceEvent 13191 scalarRow13191.grid parameters

theorem covarianceEvent13191_measurable : MeasurableSet covarianceEvent13191 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13191_payment :
    (retDist (paperDesignP 13191).toCentres).real
      (agentEv (paperDesignP 13191) covarianceEvent13191)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13191

theorem localCov13191 : BstLean.Part259.LocalCovarianceOn covarianceEvent13191
    (BstLean.Part263.cell scalarRow13191.grid) (caps repair13191) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13191

theorem covarianceGood13191_payment :
    (retDist (paperDesignP 13191).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13191)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13191_payment



end BstLean.Part269.N13191

namespace BstLean.Part269.N13191
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13191}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13191.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13191) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13191).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13191 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13191) (by norm_num) BstLean.Part268.WorldRow13191.worldPackage rfl
    BstLean.Part268.WorldRow13191.product_lower (BstLean.Part268.WorldRow13191.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13191} (hw : c ∈ Hof BstLean.Part268.WorldRow13191.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13191) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13191) (by norm_num) BstLean.Part268.WorldRow13191.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13191} (hw : c ∈ Hof BstLean.Part268.WorldRow13191.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13191) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13191).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13191) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13191_eq : scalarRow13191.targetFrame = BstLean.Part268.agent13191.frame := by
  norm_num [scalarRow13191,BstLean.Part268.agent13191]

noncomputable def frameData13191 : BstLean.Part264b.FrameData 13191 :=
  BstLean.Part269.frameData_from_numerics (n := 13191) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13191.worldPackage rfl BstLean.Part268.WorldRow13191.product_lower (BstLean.Part268.WorldRow13191.producthi.2.trans (by norm_num))
    scalarRow13191 repair13191 covarianceInputs13191 (fun i hi => sourceNumerics13191 hi)
    BstLean.Part268.agent13191.frame targetFrame13191_eq


end BstLean.Part269.N13191

namespace BstLean.Part269.N13192
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13192 : scalarRow13192.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13192, BstLean.Part268.grid13192, BstLean.Part263.worldGrid]

theorem supplies13192 (j : Fin 43) : Supply 13192 (parameters j)
    (cellLower scalarRow13192.grid (sourceIndex j))
    (cellUpper scalarRow13192.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13192.grid grid_top_bounds13192 j

theorem radii13192 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13192.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13192 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13192 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13192.grid grid_top_bounds13192 j hθ

noncomputable def covarianceInputs13192 :
    BstLean.Part263.CovarianceInputs 13192 scalarRow13192.grid parameters (caps repair13192) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13192 grid_top_bounds13192 repair13192

noncomputable def covarianceEvent13192 : Set (AgFam 13192) :=
  BstLean.Part263.covarianceEvent 13192 scalarRow13192.grid parameters

theorem covarianceEvent13192_measurable : MeasurableSet covarianceEvent13192 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13192_payment :
    (retDist (paperDesignP 13192).toCentres).real
      (agentEv (paperDesignP 13192) covarianceEvent13192)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13192

theorem localCov13192 : BstLean.Part259.LocalCovarianceOn covarianceEvent13192
    (BstLean.Part263.cell scalarRow13192.grid) (caps repair13192) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13192

theorem covarianceGood13192_payment :
    (retDist (paperDesignP 13192).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13192)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13192_payment



end BstLean.Part269.N13192

namespace BstLean.Part269.N13192
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13192}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13192.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13192) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13192).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13192 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13192) (by norm_num) BstLean.Part268.WorldRow13192.worldPackage rfl
    BstLean.Part268.WorldRow13192.product_lower (BstLean.Part268.WorldRow13192.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13192} (hw : c ∈ Hof BstLean.Part268.WorldRow13192.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13192) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13192) (by norm_num) BstLean.Part268.WorldRow13192.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13192} (hw : c ∈ Hof BstLean.Part268.WorldRow13192.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13192) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13192).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13192) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13192_eq : scalarRow13192.targetFrame = BstLean.Part268.agent13192.frame := by
  norm_num [scalarRow13192,BstLean.Part268.agent13192]

noncomputable def frameData13192 : BstLean.Part264b.FrameData 13192 :=
  BstLean.Part269.frameData_from_numerics (n := 13192) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13192.worldPackage rfl BstLean.Part268.WorldRow13192.product_lower (BstLean.Part268.WorldRow13192.producthi.2.trans (by norm_num))
    scalarRow13192 repair13192 covarianceInputs13192 (fun i hi => sourceNumerics13192 hi)
    BstLean.Part268.agent13192.frame targetFrame13192_eq


end BstLean.Part269.N13192

namespace BstLean.Part269.N13193
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13193 : scalarRow13193.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13193, BstLean.Part268.grid13193, BstLean.Part263.worldGrid]

theorem supplies13193 (j : Fin 43) : Supply 13193 (parameters j)
    (cellLower scalarRow13193.grid (sourceIndex j))
    (cellUpper scalarRow13193.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13193.grid grid_top_bounds13193 j

theorem radii13193 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13193.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13193 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13193 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13193.grid grid_top_bounds13193 j hθ

noncomputable def covarianceInputs13193 :
    BstLean.Part263.CovarianceInputs 13193 scalarRow13193.grid parameters (caps repair13193) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13193 grid_top_bounds13193 repair13193

noncomputable def covarianceEvent13193 : Set (AgFam 13193) :=
  BstLean.Part263.covarianceEvent 13193 scalarRow13193.grid parameters

theorem covarianceEvent13193_measurable : MeasurableSet covarianceEvent13193 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13193_payment :
    (retDist (paperDesignP 13193).toCentres).real
      (agentEv (paperDesignP 13193) covarianceEvent13193)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13193

theorem localCov13193 : BstLean.Part259.LocalCovarianceOn covarianceEvent13193
    (BstLean.Part263.cell scalarRow13193.grid) (caps repair13193) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13193

theorem covarianceGood13193_payment :
    (retDist (paperDesignP 13193).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13193)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13193_payment



end BstLean.Part269.N13193

namespace BstLean.Part269.N13193
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13193}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13193.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13193) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13193).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13193 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13193) (by norm_num) BstLean.Part268.WorldRow13193.worldPackage rfl
    BstLean.Part268.WorldRow13193.product_lower (BstLean.Part268.WorldRow13193.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13193} (hw : c ∈ Hof BstLean.Part268.WorldRow13193.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13193) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13193) (by norm_num) BstLean.Part268.WorldRow13193.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13193} (hw : c ∈ Hof BstLean.Part268.WorldRow13193.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13193) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13193).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13193) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13193_eq : scalarRow13193.targetFrame = BstLean.Part268.agent13193.frame := by
  norm_num [scalarRow13193,BstLean.Part268.agent13193]

noncomputable def frameData13193 : BstLean.Part264b.FrameData 13193 :=
  BstLean.Part269.frameData_from_numerics (n := 13193) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13193.worldPackage rfl BstLean.Part268.WorldRow13193.product_lower (BstLean.Part268.WorldRow13193.producthi.2.trans (by norm_num))
    scalarRow13193 repair13193 covarianceInputs13193 (fun i hi => sourceNumerics13193 hi)
    BstLean.Part268.agent13193.frame targetFrame13193_eq


end BstLean.Part269.N13193

namespace BstLean.Part269.N13194
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13194 : scalarRow13194.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13194, BstLean.Part268.grid13194, BstLean.Part263.worldGrid]

theorem supplies13194 (j : Fin 43) : Supply 13194 (parameters j)
    (cellLower scalarRow13194.grid (sourceIndex j))
    (cellUpper scalarRow13194.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13194.grid grid_top_bounds13194 j

theorem radii13194 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13194.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13194 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13194 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13194.grid grid_top_bounds13194 j hθ

noncomputable def covarianceInputs13194 :
    BstLean.Part263.CovarianceInputs 13194 scalarRow13194.grid parameters (caps repair13194) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13194 grid_top_bounds13194 repair13194

noncomputable def covarianceEvent13194 : Set (AgFam 13194) :=
  BstLean.Part263.covarianceEvent 13194 scalarRow13194.grid parameters

theorem covarianceEvent13194_measurable : MeasurableSet covarianceEvent13194 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13194_payment :
    (retDist (paperDesignP 13194).toCentres).real
      (agentEv (paperDesignP 13194) covarianceEvent13194)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13194

theorem localCov13194 : BstLean.Part259.LocalCovarianceOn covarianceEvent13194
    (BstLean.Part263.cell scalarRow13194.grid) (caps repair13194) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13194

theorem covarianceGood13194_payment :
    (retDist (paperDesignP 13194).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13194)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13194_payment



end BstLean.Part269.N13194

namespace BstLean.Part269.N13194
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13194}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13194.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13194) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13194).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13194 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13194) (by norm_num) BstLean.Part268.WorldRow13194.worldPackage rfl
    BstLean.Part268.WorldRow13194.product_lower (BstLean.Part268.WorldRow13194.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13194} (hw : c ∈ Hof BstLean.Part268.WorldRow13194.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13194) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13194) (by norm_num) BstLean.Part268.WorldRow13194.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13194} (hw : c ∈ Hof BstLean.Part268.WorldRow13194.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13194) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13194).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13194) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13194_eq : scalarRow13194.targetFrame = BstLean.Part268.agent13194.frame := by
  norm_num [scalarRow13194,BstLean.Part268.agent13194]

noncomputable def frameData13194 : BstLean.Part264b.FrameData 13194 :=
  BstLean.Part269.frameData_from_numerics (n := 13194) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13194.worldPackage rfl BstLean.Part268.WorldRow13194.product_lower (BstLean.Part268.WorldRow13194.producthi.2.trans (by norm_num))
    scalarRow13194 repair13194 covarianceInputs13194 (fun i hi => sourceNumerics13194 hi)
    BstLean.Part268.agent13194.frame targetFrame13194_eq


end BstLean.Part269.N13194
