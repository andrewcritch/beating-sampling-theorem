import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World26Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs26
import BstLean.Part269Rows26
import BstLean.Part269Sources26
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13000
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13000 : scalarRow13000.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13000, BstLean.Part268.grid13000, BstLean.Part263.worldGrid]

theorem supplies13000 (j : Fin 43) : Supply 13000 (parameters j)
    (cellLower scalarRow13000.grid (sourceIndex j))
    (cellUpper scalarRow13000.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13000.grid grid_top_bounds13000 j

theorem radii13000 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13000.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13000 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13000 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13000.grid grid_top_bounds13000 j hθ

noncomputable def covarianceInputs13000 :
    BstLean.Part263.CovarianceInputs 13000 scalarRow13000.grid parameters (caps repair13000) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13000 grid_top_bounds13000 repair13000

noncomputable def covarianceEvent13000 : Set (AgFam 13000) :=
  BstLean.Part263.covarianceEvent 13000 scalarRow13000.grid parameters

theorem covarianceEvent13000_measurable : MeasurableSet covarianceEvent13000 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13000_payment :
    (retDist (paperDesignP 13000).toCentres).real
      (agentEv (paperDesignP 13000) covarianceEvent13000)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13000

theorem localCov13000 : BstLean.Part259.LocalCovarianceOn covarianceEvent13000
    (BstLean.Part263.cell scalarRow13000.grid) (caps repair13000) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13000

theorem covarianceGood13000_payment :
    (retDist (paperDesignP 13000).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13000)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13000_payment



end BstLean.Part269.N13000

namespace BstLean.Part269.N13000
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13000}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13000.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13000) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13000).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13000 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13000) (by norm_num) BstLean.Part268.WorldRow13000.worldPackage rfl
    BstLean.Part268.WorldRow13000.product_lower (BstLean.Part268.WorldRow13000.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13000} (hw : c ∈ Hof BstLean.Part268.WorldRow13000.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13000) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13000) (by norm_num) BstLean.Part268.WorldRow13000.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13000} (hw : c ∈ Hof BstLean.Part268.WorldRow13000.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13000) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13000).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13000) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13000_eq : scalarRow13000.targetFrame = BstLean.Part268.agent13000.frame := by
  norm_num [scalarRow13000,BstLean.Part268.agent13000]

noncomputable def frameData13000 : BstLean.Part264b.FrameData 13000 :=
  BstLean.Part269.frameData_from_numerics (n := 13000) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13000.worldPackage rfl BstLean.Part268.WorldRow13000.product_lower (BstLean.Part268.WorldRow13000.producthi.2.trans (by norm_num))
    scalarRow13000 repair13000 covarianceInputs13000 (fun i hi => sourceNumerics13000 hi)
    BstLean.Part268.agent13000.frame targetFrame13000_eq


end BstLean.Part269.N13000

namespace BstLean.Part269.N13001
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13001 : scalarRow13001.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13001, BstLean.Part268.grid13001, BstLean.Part263.worldGrid]

theorem supplies13001 (j : Fin 43) : Supply 13001 (parameters j)
    (cellLower scalarRow13001.grid (sourceIndex j))
    (cellUpper scalarRow13001.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13001.grid grid_top_bounds13001 j

theorem radii13001 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13001.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13001 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13001 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13001.grid grid_top_bounds13001 j hθ

noncomputable def covarianceInputs13001 :
    BstLean.Part263.CovarianceInputs 13001 scalarRow13001.grid parameters (caps repair13001) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13001 grid_top_bounds13001 repair13001

noncomputable def covarianceEvent13001 : Set (AgFam 13001) :=
  BstLean.Part263.covarianceEvent 13001 scalarRow13001.grid parameters

theorem covarianceEvent13001_measurable : MeasurableSet covarianceEvent13001 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13001_payment :
    (retDist (paperDesignP 13001).toCentres).real
      (agentEv (paperDesignP 13001) covarianceEvent13001)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13001

theorem localCov13001 : BstLean.Part259.LocalCovarianceOn covarianceEvent13001
    (BstLean.Part263.cell scalarRow13001.grid) (caps repair13001) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13001

theorem covarianceGood13001_payment :
    (retDist (paperDesignP 13001).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13001)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13001_payment



end BstLean.Part269.N13001

namespace BstLean.Part269.N13001
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13001}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13001.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13001) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13001).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13001 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13001) (by norm_num) BstLean.Part268.WorldRow13001.worldPackage rfl
    BstLean.Part268.WorldRow13001.product_lower (BstLean.Part268.WorldRow13001.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13001} (hw : c ∈ Hof BstLean.Part268.WorldRow13001.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13001) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13001) (by norm_num) BstLean.Part268.WorldRow13001.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13001} (hw : c ∈ Hof BstLean.Part268.WorldRow13001.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13001) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13001).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13001) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13001_eq : scalarRow13001.targetFrame = BstLean.Part268.agent13001.frame := by
  norm_num [scalarRow13001,BstLean.Part268.agent13001]

noncomputable def frameData13001 : BstLean.Part264b.FrameData 13001 :=
  BstLean.Part269.frameData_from_numerics (n := 13001) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13001.worldPackage rfl BstLean.Part268.WorldRow13001.product_lower (BstLean.Part268.WorldRow13001.producthi.2.trans (by norm_num))
    scalarRow13001 repair13001 covarianceInputs13001 (fun i hi => sourceNumerics13001 hi)
    BstLean.Part268.agent13001.frame targetFrame13001_eq


end BstLean.Part269.N13001

namespace BstLean.Part269.N13002
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13002 : scalarRow13002.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13002, BstLean.Part268.grid13002, BstLean.Part263.worldGrid]

theorem supplies13002 (j : Fin 43) : Supply 13002 (parameters j)
    (cellLower scalarRow13002.grid (sourceIndex j))
    (cellUpper scalarRow13002.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13002.grid grid_top_bounds13002 j

theorem radii13002 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13002.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13002 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13002 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13002.grid grid_top_bounds13002 j hθ

noncomputable def covarianceInputs13002 :
    BstLean.Part263.CovarianceInputs 13002 scalarRow13002.grid parameters (caps repair13002) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13002 grid_top_bounds13002 repair13002

noncomputable def covarianceEvent13002 : Set (AgFam 13002) :=
  BstLean.Part263.covarianceEvent 13002 scalarRow13002.grid parameters

theorem covarianceEvent13002_measurable : MeasurableSet covarianceEvent13002 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13002_payment :
    (retDist (paperDesignP 13002).toCentres).real
      (agentEv (paperDesignP 13002) covarianceEvent13002)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13002

theorem localCov13002 : BstLean.Part259.LocalCovarianceOn covarianceEvent13002
    (BstLean.Part263.cell scalarRow13002.grid) (caps repair13002) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13002

theorem covarianceGood13002_payment :
    (retDist (paperDesignP 13002).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13002)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13002_payment



end BstLean.Part269.N13002

namespace BstLean.Part269.N13002
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13002}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13002.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13002) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13002).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13002 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13002) (by norm_num) BstLean.Part268.WorldRow13002.worldPackage rfl
    BstLean.Part268.WorldRow13002.product_lower (BstLean.Part268.WorldRow13002.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13002} (hw : c ∈ Hof BstLean.Part268.WorldRow13002.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13002) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13002) (by norm_num) BstLean.Part268.WorldRow13002.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13002} (hw : c ∈ Hof BstLean.Part268.WorldRow13002.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13002) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13002).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13002) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13002_eq : scalarRow13002.targetFrame = BstLean.Part268.agent13002.frame := by
  norm_num [scalarRow13002,BstLean.Part268.agent13002]

noncomputable def frameData13002 : BstLean.Part264b.FrameData 13002 :=
  BstLean.Part269.frameData_from_numerics (n := 13002) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13002.worldPackage rfl BstLean.Part268.WorldRow13002.product_lower (BstLean.Part268.WorldRow13002.producthi.2.trans (by norm_num))
    scalarRow13002 repair13002 covarianceInputs13002 (fun i hi => sourceNumerics13002 hi)
    BstLean.Part268.agent13002.frame targetFrame13002_eq


end BstLean.Part269.N13002

namespace BstLean.Part269.N13003
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13003 : scalarRow13003.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13003, BstLean.Part268.grid13003, BstLean.Part263.worldGrid]

theorem supplies13003 (j : Fin 43) : Supply 13003 (parameters j)
    (cellLower scalarRow13003.grid (sourceIndex j))
    (cellUpper scalarRow13003.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13003.grid grid_top_bounds13003 j

theorem radii13003 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13003.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13003 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13003 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13003.grid grid_top_bounds13003 j hθ

noncomputable def covarianceInputs13003 :
    BstLean.Part263.CovarianceInputs 13003 scalarRow13003.grid parameters (caps repair13003) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13003 grid_top_bounds13003 repair13003

noncomputable def covarianceEvent13003 : Set (AgFam 13003) :=
  BstLean.Part263.covarianceEvent 13003 scalarRow13003.grid parameters

theorem covarianceEvent13003_measurable : MeasurableSet covarianceEvent13003 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13003_payment :
    (retDist (paperDesignP 13003).toCentres).real
      (agentEv (paperDesignP 13003) covarianceEvent13003)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13003

theorem localCov13003 : BstLean.Part259.LocalCovarianceOn covarianceEvent13003
    (BstLean.Part263.cell scalarRow13003.grid) (caps repair13003) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13003

theorem covarianceGood13003_payment :
    (retDist (paperDesignP 13003).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13003)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13003_payment



end BstLean.Part269.N13003

namespace BstLean.Part269.N13003
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13003}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13003.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13003) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13003).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13003 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13003) (by norm_num) BstLean.Part268.WorldRow13003.worldPackage rfl
    BstLean.Part268.WorldRow13003.product_lower (BstLean.Part268.WorldRow13003.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13003} (hw : c ∈ Hof BstLean.Part268.WorldRow13003.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13003) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13003) (by norm_num) BstLean.Part268.WorldRow13003.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13003} (hw : c ∈ Hof BstLean.Part268.WorldRow13003.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13003) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13003).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13003) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13003_eq : scalarRow13003.targetFrame = BstLean.Part268.agent13003.frame := by
  norm_num [scalarRow13003,BstLean.Part268.agent13003]

noncomputable def frameData13003 : BstLean.Part264b.FrameData 13003 :=
  BstLean.Part269.frameData_from_numerics (n := 13003) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13003.worldPackage rfl BstLean.Part268.WorldRow13003.product_lower (BstLean.Part268.WorldRow13003.producthi.2.trans (by norm_num))
    scalarRow13003 repair13003 covarianceInputs13003 (fun i hi => sourceNumerics13003 hi)
    BstLean.Part268.agent13003.frame targetFrame13003_eq


end BstLean.Part269.N13003

namespace BstLean.Part269.N13004
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13004 : scalarRow13004.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13004, BstLean.Part268.grid13004, BstLean.Part263.worldGrid]

theorem supplies13004 (j : Fin 43) : Supply 13004 (parameters j)
    (cellLower scalarRow13004.grid (sourceIndex j))
    (cellUpper scalarRow13004.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13004.grid grid_top_bounds13004 j

theorem radii13004 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13004.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13004 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13004 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13004.grid grid_top_bounds13004 j hθ

noncomputable def covarianceInputs13004 :
    BstLean.Part263.CovarianceInputs 13004 scalarRow13004.grid parameters (caps repair13004) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13004 grid_top_bounds13004 repair13004

noncomputable def covarianceEvent13004 : Set (AgFam 13004) :=
  BstLean.Part263.covarianceEvent 13004 scalarRow13004.grid parameters

theorem covarianceEvent13004_measurable : MeasurableSet covarianceEvent13004 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13004_payment :
    (retDist (paperDesignP 13004).toCentres).real
      (agentEv (paperDesignP 13004) covarianceEvent13004)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13004

theorem localCov13004 : BstLean.Part259.LocalCovarianceOn covarianceEvent13004
    (BstLean.Part263.cell scalarRow13004.grid) (caps repair13004) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13004

theorem covarianceGood13004_payment :
    (retDist (paperDesignP 13004).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13004)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13004_payment



end BstLean.Part269.N13004

namespace BstLean.Part269.N13004
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13004}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13004.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13004) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13004).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13004 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13004) (by norm_num) BstLean.Part268.WorldRow13004.worldPackage rfl
    BstLean.Part268.WorldRow13004.product_lower (BstLean.Part268.WorldRow13004.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13004} (hw : c ∈ Hof BstLean.Part268.WorldRow13004.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13004) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13004) (by norm_num) BstLean.Part268.WorldRow13004.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13004} (hw : c ∈ Hof BstLean.Part268.WorldRow13004.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13004) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13004).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13004) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13004_eq : scalarRow13004.targetFrame = BstLean.Part268.agent13004.frame := by
  norm_num [scalarRow13004,BstLean.Part268.agent13004]

noncomputable def frameData13004 : BstLean.Part264b.FrameData 13004 :=
  BstLean.Part269.frameData_from_numerics (n := 13004) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13004.worldPackage rfl BstLean.Part268.WorldRow13004.product_lower (BstLean.Part268.WorldRow13004.producthi.2.trans (by norm_num))
    scalarRow13004 repair13004 covarianceInputs13004 (fun i hi => sourceNumerics13004 hi)
    BstLean.Part268.agent13004.frame targetFrame13004_eq


end BstLean.Part269.N13004
