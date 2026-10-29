import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World30Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs30
import BstLean.Part269Rows30
import BstLean.Part269Sources30
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13100
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13100 : scalarRow13100.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13100, BstLean.Part268.grid13100, BstLean.Part263.worldGrid]

theorem supplies13100 (j : Fin 43) : Supply 13100 (parameters j)
    (cellLower scalarRow13100.grid (sourceIndex j))
    (cellUpper scalarRow13100.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13100.grid grid_top_bounds13100 j

theorem radii13100 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13100.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13100 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13100 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13100.grid grid_top_bounds13100 j hθ

noncomputable def covarianceInputs13100 :
    BstLean.Part263.CovarianceInputs 13100 scalarRow13100.grid parameters (caps repair13100) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13100 grid_top_bounds13100 repair13100

noncomputable def covarianceEvent13100 : Set (AgFam 13100) :=
  BstLean.Part263.covarianceEvent 13100 scalarRow13100.grid parameters

theorem covarianceEvent13100_measurable : MeasurableSet covarianceEvent13100 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13100_payment :
    (retDist (paperDesignP 13100).toCentres).real
      (agentEv (paperDesignP 13100) covarianceEvent13100)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13100

theorem localCov13100 : BstLean.Part259.LocalCovarianceOn covarianceEvent13100
    (BstLean.Part263.cell scalarRow13100.grid) (caps repair13100) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13100

theorem covarianceGood13100_payment :
    (retDist (paperDesignP 13100).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13100)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13100_payment



end BstLean.Part269.N13100

namespace BstLean.Part269.N13100
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13100}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13100.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13100) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13100).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13100 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13100) (by norm_num) BstLean.Part268.WorldRow13100.worldPackage rfl
    BstLean.Part268.WorldRow13100.product_lower (BstLean.Part268.WorldRow13100.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13100} (hw : c ∈ Hof BstLean.Part268.WorldRow13100.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13100) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13100) (by norm_num) BstLean.Part268.WorldRow13100.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13100} (hw : c ∈ Hof BstLean.Part268.WorldRow13100.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13100) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13100).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13100) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13100_eq : scalarRow13100.targetFrame = BstLean.Part268.agent13100.frame := by
  norm_num [scalarRow13100,BstLean.Part268.agent13100]

noncomputable def frameData13100 : BstLean.Part264b.FrameData 13100 :=
  BstLean.Part269.frameData_from_numerics (n := 13100) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13100.worldPackage rfl BstLean.Part268.WorldRow13100.product_lower (BstLean.Part268.WorldRow13100.producthi.2.trans (by norm_num))
    scalarRow13100 repair13100 covarianceInputs13100 (fun i hi => sourceNumerics13100 hi)
    BstLean.Part268.agent13100.frame targetFrame13100_eq


end BstLean.Part269.N13100

namespace BstLean.Part269.N13101
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13101 : scalarRow13101.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13101, BstLean.Part268.grid13101, BstLean.Part263.worldGrid]

theorem supplies13101 (j : Fin 43) : Supply 13101 (parameters j)
    (cellLower scalarRow13101.grid (sourceIndex j))
    (cellUpper scalarRow13101.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13101.grid grid_top_bounds13101 j

theorem radii13101 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13101.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13101 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13101 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13101.grid grid_top_bounds13101 j hθ

noncomputable def covarianceInputs13101 :
    BstLean.Part263.CovarianceInputs 13101 scalarRow13101.grid parameters (caps repair13101) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13101 grid_top_bounds13101 repair13101

noncomputable def covarianceEvent13101 : Set (AgFam 13101) :=
  BstLean.Part263.covarianceEvent 13101 scalarRow13101.grid parameters

theorem covarianceEvent13101_measurable : MeasurableSet covarianceEvent13101 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13101_payment :
    (retDist (paperDesignP 13101).toCentres).real
      (agentEv (paperDesignP 13101) covarianceEvent13101)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13101

theorem localCov13101 : BstLean.Part259.LocalCovarianceOn covarianceEvent13101
    (BstLean.Part263.cell scalarRow13101.grid) (caps repair13101) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13101

theorem covarianceGood13101_payment :
    (retDist (paperDesignP 13101).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13101)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13101_payment



end BstLean.Part269.N13101

namespace BstLean.Part269.N13101
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13101}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13101.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13101) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13101).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13101 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13101) (by norm_num) BstLean.Part268.WorldRow13101.worldPackage rfl
    BstLean.Part268.WorldRow13101.product_lower (BstLean.Part268.WorldRow13101.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13101} (hw : c ∈ Hof BstLean.Part268.WorldRow13101.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13101) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13101) (by norm_num) BstLean.Part268.WorldRow13101.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13101} (hw : c ∈ Hof BstLean.Part268.WorldRow13101.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13101) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13101).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13101) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13101_eq : scalarRow13101.targetFrame = BstLean.Part268.agent13101.frame := by
  norm_num [scalarRow13101,BstLean.Part268.agent13101]

noncomputable def frameData13101 : BstLean.Part264b.FrameData 13101 :=
  BstLean.Part269.frameData_from_numerics (n := 13101) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13101.worldPackage rfl BstLean.Part268.WorldRow13101.product_lower (BstLean.Part268.WorldRow13101.producthi.2.trans (by norm_num))
    scalarRow13101 repair13101 covarianceInputs13101 (fun i hi => sourceNumerics13101 hi)
    BstLean.Part268.agent13101.frame targetFrame13101_eq


end BstLean.Part269.N13101

namespace BstLean.Part269.N13102
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13102 : scalarRow13102.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13102, BstLean.Part268.grid13102, BstLean.Part263.worldGrid]

theorem supplies13102 (j : Fin 43) : Supply 13102 (parameters j)
    (cellLower scalarRow13102.grid (sourceIndex j))
    (cellUpper scalarRow13102.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13102.grid grid_top_bounds13102 j

theorem radii13102 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13102.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13102 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13102 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13102.grid grid_top_bounds13102 j hθ

noncomputable def covarianceInputs13102 :
    BstLean.Part263.CovarianceInputs 13102 scalarRow13102.grid parameters (caps repair13102) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13102 grid_top_bounds13102 repair13102

noncomputable def covarianceEvent13102 : Set (AgFam 13102) :=
  BstLean.Part263.covarianceEvent 13102 scalarRow13102.grid parameters

theorem covarianceEvent13102_measurable : MeasurableSet covarianceEvent13102 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13102_payment :
    (retDist (paperDesignP 13102).toCentres).real
      (agentEv (paperDesignP 13102) covarianceEvent13102)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13102

theorem localCov13102 : BstLean.Part259.LocalCovarianceOn covarianceEvent13102
    (BstLean.Part263.cell scalarRow13102.grid) (caps repair13102) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13102

theorem covarianceGood13102_payment :
    (retDist (paperDesignP 13102).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13102)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13102_payment



end BstLean.Part269.N13102

namespace BstLean.Part269.N13102
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13102}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13102.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13102) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13102).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13102 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13102) (by norm_num) BstLean.Part268.WorldRow13102.worldPackage rfl
    BstLean.Part268.WorldRow13102.product_lower (BstLean.Part268.WorldRow13102.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13102} (hw : c ∈ Hof BstLean.Part268.WorldRow13102.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13102) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13102) (by norm_num) BstLean.Part268.WorldRow13102.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13102} (hw : c ∈ Hof BstLean.Part268.WorldRow13102.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13102) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13102).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13102) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13102_eq : scalarRow13102.targetFrame = BstLean.Part268.agent13102.frame := by
  norm_num [scalarRow13102,BstLean.Part268.agent13102]

noncomputable def frameData13102 : BstLean.Part264b.FrameData 13102 :=
  BstLean.Part269.frameData_from_numerics (n := 13102) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13102.worldPackage rfl BstLean.Part268.WorldRow13102.product_lower (BstLean.Part268.WorldRow13102.producthi.2.trans (by norm_num))
    scalarRow13102 repair13102 covarianceInputs13102 (fun i hi => sourceNumerics13102 hi)
    BstLean.Part268.agent13102.frame targetFrame13102_eq


end BstLean.Part269.N13102

namespace BstLean.Part269.N13103
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13103 : scalarRow13103.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13103, BstLean.Part268.grid13103, BstLean.Part263.worldGrid]

theorem supplies13103 (j : Fin 43) : Supply 13103 (parameters j)
    (cellLower scalarRow13103.grid (sourceIndex j))
    (cellUpper scalarRow13103.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13103.grid grid_top_bounds13103 j

theorem radii13103 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13103.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13103 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13103 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13103.grid grid_top_bounds13103 j hθ

noncomputable def covarianceInputs13103 :
    BstLean.Part263.CovarianceInputs 13103 scalarRow13103.grid parameters (caps repair13103) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13103 grid_top_bounds13103 repair13103

noncomputable def covarianceEvent13103 : Set (AgFam 13103) :=
  BstLean.Part263.covarianceEvent 13103 scalarRow13103.grid parameters

theorem covarianceEvent13103_measurable : MeasurableSet covarianceEvent13103 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13103_payment :
    (retDist (paperDesignP 13103).toCentres).real
      (agentEv (paperDesignP 13103) covarianceEvent13103)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13103

theorem localCov13103 : BstLean.Part259.LocalCovarianceOn covarianceEvent13103
    (BstLean.Part263.cell scalarRow13103.grid) (caps repair13103) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13103

theorem covarianceGood13103_payment :
    (retDist (paperDesignP 13103).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13103)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13103_payment



end BstLean.Part269.N13103

namespace BstLean.Part269.N13103
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13103}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13103.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13103) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13103).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13103 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13103) (by norm_num) BstLean.Part268.WorldRow13103.worldPackage rfl
    BstLean.Part268.WorldRow13103.product_lower (BstLean.Part268.WorldRow13103.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13103} (hw : c ∈ Hof BstLean.Part268.WorldRow13103.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13103) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13103) (by norm_num) BstLean.Part268.WorldRow13103.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13103} (hw : c ∈ Hof BstLean.Part268.WorldRow13103.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13103) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13103).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13103) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13103_eq : scalarRow13103.targetFrame = BstLean.Part268.agent13103.frame := by
  norm_num [scalarRow13103,BstLean.Part268.agent13103]

noncomputable def frameData13103 : BstLean.Part264b.FrameData 13103 :=
  BstLean.Part269.frameData_from_numerics (n := 13103) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13103.worldPackage rfl BstLean.Part268.WorldRow13103.product_lower (BstLean.Part268.WorldRow13103.producthi.2.trans (by norm_num))
    scalarRow13103 repair13103 covarianceInputs13103 (fun i hi => sourceNumerics13103 hi)
    BstLean.Part268.agent13103.frame targetFrame13103_eq


end BstLean.Part269.N13103

namespace BstLean.Part269.N13104
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13104 : scalarRow13104.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13104, BstLean.Part268.grid13104, BstLean.Part263.worldGrid]

theorem supplies13104 (j : Fin 43) : Supply 13104 (parameters j)
    (cellLower scalarRow13104.grid (sourceIndex j))
    (cellUpper scalarRow13104.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13104.grid grid_top_bounds13104 j

theorem radii13104 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13104.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13104 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13104 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13104.grid grid_top_bounds13104 j hθ

noncomputable def covarianceInputs13104 :
    BstLean.Part263.CovarianceInputs 13104 scalarRow13104.grid parameters (caps repair13104) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13104 grid_top_bounds13104 repair13104

noncomputable def covarianceEvent13104 : Set (AgFam 13104) :=
  BstLean.Part263.covarianceEvent 13104 scalarRow13104.grid parameters

theorem covarianceEvent13104_measurable : MeasurableSet covarianceEvent13104 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13104_payment :
    (retDist (paperDesignP 13104).toCentres).real
      (agentEv (paperDesignP 13104) covarianceEvent13104)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13104

theorem localCov13104 : BstLean.Part259.LocalCovarianceOn covarianceEvent13104
    (BstLean.Part263.cell scalarRow13104.grid) (caps repair13104) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13104

theorem covarianceGood13104_payment :
    (retDist (paperDesignP 13104).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13104)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13104_payment



end BstLean.Part269.N13104

namespace BstLean.Part269.N13104
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13104}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13104.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13104) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13104).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13104 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13104) (by norm_num) BstLean.Part268.WorldRow13104.worldPackage rfl
    BstLean.Part268.WorldRow13104.product_lower (BstLean.Part268.WorldRow13104.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13104} (hw : c ∈ Hof BstLean.Part268.WorldRow13104.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13104) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13104) (by norm_num) BstLean.Part268.WorldRow13104.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13104} (hw : c ∈ Hof BstLean.Part268.WorldRow13104.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13104) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13104).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13104) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13104_eq : scalarRow13104.targetFrame = BstLean.Part268.agent13104.frame := by
  norm_num [scalarRow13104,BstLean.Part268.agent13104]

noncomputable def frameData13104 : BstLean.Part264b.FrameData 13104 :=
  BstLean.Part269.frameData_from_numerics (n := 13104) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13104.worldPackage rfl BstLean.Part268.WorldRow13104.product_lower (BstLean.Part268.WorldRow13104.producthi.2.trans (by norm_num))
    scalarRow13104 repair13104 covarianceInputs13104 (fun i hi => sourceNumerics13104 hi)
    BstLean.Part268.agent13104.frame targetFrame13104_eq


end BstLean.Part269.N13104
