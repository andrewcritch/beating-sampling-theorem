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

namespace BstLean.Part269.N13080
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13080 : scalarRow13080.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13080, BstLean.Part268.grid13080, BstLean.Part263.worldGrid]

theorem supplies13080 (j : Fin 43) : Supply 13080 (parameters j)
    (cellLower scalarRow13080.grid (sourceIndex j))
    (cellUpper scalarRow13080.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13080.grid grid_top_bounds13080 j

theorem radii13080 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13080.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13080 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13080 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13080.grid grid_top_bounds13080 j hθ

noncomputable def covarianceInputs13080 :
    BstLean.Part263.CovarianceInputs 13080 scalarRow13080.grid parameters (caps repair13080) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13080 grid_top_bounds13080 repair13080

noncomputable def covarianceEvent13080 : Set (AgFam 13080) :=
  BstLean.Part263.covarianceEvent 13080 scalarRow13080.grid parameters

theorem covarianceEvent13080_measurable : MeasurableSet covarianceEvent13080 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13080_payment :
    (retDist (paperDesignP 13080).toCentres).real
      (agentEv (paperDesignP 13080) covarianceEvent13080)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13080

theorem localCov13080 : BstLean.Part259.LocalCovarianceOn covarianceEvent13080
    (BstLean.Part263.cell scalarRow13080.grid) (caps repair13080) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13080

theorem covarianceGood13080_payment :
    (retDist (paperDesignP 13080).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13080)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13080_payment



end BstLean.Part269.N13080

namespace BstLean.Part269.N13080
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13080}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13080.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13080) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13080).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13080 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13080) (by norm_num) BstLean.Part268.WorldRow13080.worldPackage rfl
    BstLean.Part268.WorldRow13080.product_lower (BstLean.Part268.WorldRow13080.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13080} (hw : c ∈ Hof BstLean.Part268.WorldRow13080.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13080) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13080) (by norm_num) BstLean.Part268.WorldRow13080.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13080} (hw : c ∈ Hof BstLean.Part268.WorldRow13080.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13080) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13080).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13080) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13080_eq : scalarRow13080.targetFrame = BstLean.Part268.agent13080.frame := by
  norm_num [scalarRow13080,BstLean.Part268.agent13080]

noncomputable def frameData13080 : BstLean.Part264b.FrameData 13080 :=
  BstLean.Part269.frameData_from_numerics (n := 13080) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13080.worldPackage rfl BstLean.Part268.WorldRow13080.product_lower (BstLean.Part268.WorldRow13080.producthi.2.trans (by norm_num))
    scalarRow13080 repair13080 covarianceInputs13080 (fun i hi => sourceNumerics13080 hi)
    BstLean.Part268.agent13080.frame targetFrame13080_eq


end BstLean.Part269.N13080

namespace BstLean.Part269.N13081
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13081 : scalarRow13081.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13081, BstLean.Part268.grid13081, BstLean.Part263.worldGrid]

theorem supplies13081 (j : Fin 43) : Supply 13081 (parameters j)
    (cellLower scalarRow13081.grid (sourceIndex j))
    (cellUpper scalarRow13081.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13081.grid grid_top_bounds13081 j

theorem radii13081 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13081.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13081 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13081 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13081.grid grid_top_bounds13081 j hθ

noncomputable def covarianceInputs13081 :
    BstLean.Part263.CovarianceInputs 13081 scalarRow13081.grid parameters (caps repair13081) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13081 grid_top_bounds13081 repair13081

noncomputable def covarianceEvent13081 : Set (AgFam 13081) :=
  BstLean.Part263.covarianceEvent 13081 scalarRow13081.grid parameters

theorem covarianceEvent13081_measurable : MeasurableSet covarianceEvent13081 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13081_payment :
    (retDist (paperDesignP 13081).toCentres).real
      (agentEv (paperDesignP 13081) covarianceEvent13081)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13081

theorem localCov13081 : BstLean.Part259.LocalCovarianceOn covarianceEvent13081
    (BstLean.Part263.cell scalarRow13081.grid) (caps repair13081) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13081

theorem covarianceGood13081_payment :
    (retDist (paperDesignP 13081).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13081)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13081_payment



end BstLean.Part269.N13081

namespace BstLean.Part269.N13081
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13081}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13081.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13081) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13081).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13081 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13081) (by norm_num) BstLean.Part268.WorldRow13081.worldPackage rfl
    BstLean.Part268.WorldRow13081.product_lower (BstLean.Part268.WorldRow13081.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13081} (hw : c ∈ Hof BstLean.Part268.WorldRow13081.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13081) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13081) (by norm_num) BstLean.Part268.WorldRow13081.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13081} (hw : c ∈ Hof BstLean.Part268.WorldRow13081.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13081) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13081).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13081) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13081_eq : scalarRow13081.targetFrame = BstLean.Part268.agent13081.frame := by
  norm_num [scalarRow13081,BstLean.Part268.agent13081]

noncomputable def frameData13081 : BstLean.Part264b.FrameData 13081 :=
  BstLean.Part269.frameData_from_numerics (n := 13081) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13081.worldPackage rfl BstLean.Part268.WorldRow13081.product_lower (BstLean.Part268.WorldRow13081.producthi.2.trans (by norm_num))
    scalarRow13081 repair13081 covarianceInputs13081 (fun i hi => sourceNumerics13081 hi)
    BstLean.Part268.agent13081.frame targetFrame13081_eq


end BstLean.Part269.N13081

namespace BstLean.Part269.N13082
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13082 : scalarRow13082.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13082, BstLean.Part268.grid13082, BstLean.Part263.worldGrid]

theorem supplies13082 (j : Fin 43) : Supply 13082 (parameters j)
    (cellLower scalarRow13082.grid (sourceIndex j))
    (cellUpper scalarRow13082.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13082.grid grid_top_bounds13082 j

theorem radii13082 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13082.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13082 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13082 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13082.grid grid_top_bounds13082 j hθ

noncomputable def covarianceInputs13082 :
    BstLean.Part263.CovarianceInputs 13082 scalarRow13082.grid parameters (caps repair13082) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13082 grid_top_bounds13082 repair13082

noncomputable def covarianceEvent13082 : Set (AgFam 13082) :=
  BstLean.Part263.covarianceEvent 13082 scalarRow13082.grid parameters

theorem covarianceEvent13082_measurable : MeasurableSet covarianceEvent13082 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13082_payment :
    (retDist (paperDesignP 13082).toCentres).real
      (agentEv (paperDesignP 13082) covarianceEvent13082)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13082

theorem localCov13082 : BstLean.Part259.LocalCovarianceOn covarianceEvent13082
    (BstLean.Part263.cell scalarRow13082.grid) (caps repair13082) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13082

theorem covarianceGood13082_payment :
    (retDist (paperDesignP 13082).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13082)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13082_payment



end BstLean.Part269.N13082

namespace BstLean.Part269.N13082
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13082}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13082.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13082) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13082).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13082 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13082) (by norm_num) BstLean.Part268.WorldRow13082.worldPackage rfl
    BstLean.Part268.WorldRow13082.product_lower (BstLean.Part268.WorldRow13082.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13082} (hw : c ∈ Hof BstLean.Part268.WorldRow13082.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13082) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13082) (by norm_num) BstLean.Part268.WorldRow13082.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13082} (hw : c ∈ Hof BstLean.Part268.WorldRow13082.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13082) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13082).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13082) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13082_eq : scalarRow13082.targetFrame = BstLean.Part268.agent13082.frame := by
  norm_num [scalarRow13082,BstLean.Part268.agent13082]

noncomputable def frameData13082 : BstLean.Part264b.FrameData 13082 :=
  BstLean.Part269.frameData_from_numerics (n := 13082) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13082.worldPackage rfl BstLean.Part268.WorldRow13082.product_lower (BstLean.Part268.WorldRow13082.producthi.2.trans (by norm_num))
    scalarRow13082 repair13082 covarianceInputs13082 (fun i hi => sourceNumerics13082 hi)
    BstLean.Part268.agent13082.frame targetFrame13082_eq


end BstLean.Part269.N13082

namespace BstLean.Part269.N13083
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13083 : scalarRow13083.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13083, BstLean.Part268.grid13083, BstLean.Part263.worldGrid]

theorem supplies13083 (j : Fin 43) : Supply 13083 (parameters j)
    (cellLower scalarRow13083.grid (sourceIndex j))
    (cellUpper scalarRow13083.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13083.grid grid_top_bounds13083 j

theorem radii13083 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13083.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13083 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13083 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13083.grid grid_top_bounds13083 j hθ

noncomputable def covarianceInputs13083 :
    BstLean.Part263.CovarianceInputs 13083 scalarRow13083.grid parameters (caps repair13083) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13083 grid_top_bounds13083 repair13083

noncomputable def covarianceEvent13083 : Set (AgFam 13083) :=
  BstLean.Part263.covarianceEvent 13083 scalarRow13083.grid parameters

theorem covarianceEvent13083_measurable : MeasurableSet covarianceEvent13083 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13083_payment :
    (retDist (paperDesignP 13083).toCentres).real
      (agentEv (paperDesignP 13083) covarianceEvent13083)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13083

theorem localCov13083 : BstLean.Part259.LocalCovarianceOn covarianceEvent13083
    (BstLean.Part263.cell scalarRow13083.grid) (caps repair13083) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13083

theorem covarianceGood13083_payment :
    (retDist (paperDesignP 13083).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13083)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13083_payment



end BstLean.Part269.N13083

namespace BstLean.Part269.N13083
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13083}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13083.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13083) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13083).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13083 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13083) (by norm_num) BstLean.Part268.WorldRow13083.worldPackage rfl
    BstLean.Part268.WorldRow13083.product_lower (BstLean.Part268.WorldRow13083.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13083} (hw : c ∈ Hof BstLean.Part268.WorldRow13083.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13083) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13083) (by norm_num) BstLean.Part268.WorldRow13083.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13083} (hw : c ∈ Hof BstLean.Part268.WorldRow13083.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13083) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13083).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13083) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13083_eq : scalarRow13083.targetFrame = BstLean.Part268.agent13083.frame := by
  norm_num [scalarRow13083,BstLean.Part268.agent13083]

noncomputable def frameData13083 : BstLean.Part264b.FrameData 13083 :=
  BstLean.Part269.frameData_from_numerics (n := 13083) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13083.worldPackage rfl BstLean.Part268.WorldRow13083.product_lower (BstLean.Part268.WorldRow13083.producthi.2.trans (by norm_num))
    scalarRow13083 repair13083 covarianceInputs13083 (fun i hi => sourceNumerics13083 hi)
    BstLean.Part268.agent13083.frame targetFrame13083_eq


end BstLean.Part269.N13083

namespace BstLean.Part269.N13084
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13084 : scalarRow13084.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13084, BstLean.Part268.grid13084, BstLean.Part263.worldGrid]

theorem supplies13084 (j : Fin 43) : Supply 13084 (parameters j)
    (cellLower scalarRow13084.grid (sourceIndex j))
    (cellUpper scalarRow13084.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13084.grid grid_top_bounds13084 j

theorem radii13084 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13084.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13084 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13084 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13084.grid grid_top_bounds13084 j hθ

noncomputable def covarianceInputs13084 :
    BstLean.Part263.CovarianceInputs 13084 scalarRow13084.grid parameters (caps repair13084) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13084 grid_top_bounds13084 repair13084

noncomputable def covarianceEvent13084 : Set (AgFam 13084) :=
  BstLean.Part263.covarianceEvent 13084 scalarRow13084.grid parameters

theorem covarianceEvent13084_measurable : MeasurableSet covarianceEvent13084 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13084_payment :
    (retDist (paperDesignP 13084).toCentres).real
      (agentEv (paperDesignP 13084) covarianceEvent13084)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13084

theorem localCov13084 : BstLean.Part259.LocalCovarianceOn covarianceEvent13084
    (BstLean.Part263.cell scalarRow13084.grid) (caps repair13084) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13084

theorem covarianceGood13084_payment :
    (retDist (paperDesignP 13084).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13084)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13084_payment



end BstLean.Part269.N13084

namespace BstLean.Part269.N13084
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13084}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13084.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13084) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13084).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13084 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13084) (by norm_num) BstLean.Part268.WorldRow13084.worldPackage rfl
    BstLean.Part268.WorldRow13084.product_lower (BstLean.Part268.WorldRow13084.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13084} (hw : c ∈ Hof BstLean.Part268.WorldRow13084.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13084) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13084) (by norm_num) BstLean.Part268.WorldRow13084.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13084} (hw : c ∈ Hof BstLean.Part268.WorldRow13084.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13084) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13084).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13084) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13084_eq : scalarRow13084.targetFrame = BstLean.Part268.agent13084.frame := by
  norm_num [scalarRow13084,BstLean.Part268.agent13084]

noncomputable def frameData13084 : BstLean.Part264b.FrameData 13084 :=
  BstLean.Part269.frameData_from_numerics (n := 13084) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13084.worldPackage rfl BstLean.Part268.WorldRow13084.product_lower (BstLean.Part268.WorldRow13084.producthi.2.trans (by norm_num))
    scalarRow13084 repair13084 covarianceInputs13084 (fun i hi => sourceNumerics13084 hi)
    BstLean.Part268.agent13084.frame targetFrame13084_eq


end BstLean.Part269.N13084
