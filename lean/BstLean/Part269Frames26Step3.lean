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

namespace BstLean.Part269.N13015
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13015 : scalarRow13015.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13015, BstLean.Part268.grid13015, BstLean.Part263.worldGrid]

theorem supplies13015 (j : Fin 43) : Supply 13015 (parameters j)
    (cellLower scalarRow13015.grid (sourceIndex j))
    (cellUpper scalarRow13015.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13015.grid grid_top_bounds13015 j

theorem radii13015 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13015.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13015 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13015 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13015.grid grid_top_bounds13015 j hθ

noncomputable def covarianceInputs13015 :
    BstLean.Part263.CovarianceInputs 13015 scalarRow13015.grid parameters (caps repair13015) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13015 grid_top_bounds13015 repair13015

noncomputable def covarianceEvent13015 : Set (AgFam 13015) :=
  BstLean.Part263.covarianceEvent 13015 scalarRow13015.grid parameters

theorem covarianceEvent13015_measurable : MeasurableSet covarianceEvent13015 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13015_payment :
    (retDist (paperDesignP 13015).toCentres).real
      (agentEv (paperDesignP 13015) covarianceEvent13015)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13015

theorem localCov13015 : BstLean.Part259.LocalCovarianceOn covarianceEvent13015
    (BstLean.Part263.cell scalarRow13015.grid) (caps repair13015) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13015

theorem covarianceGood13015_payment :
    (retDist (paperDesignP 13015).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13015)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13015_payment



end BstLean.Part269.N13015

namespace BstLean.Part269.N13015
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13015}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13015.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13015) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13015).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13015 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13015) (by norm_num) BstLean.Part268.WorldRow13015.worldPackage rfl
    BstLean.Part268.WorldRow13015.product_lower (BstLean.Part268.WorldRow13015.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13015} (hw : c ∈ Hof BstLean.Part268.WorldRow13015.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13015) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13015) (by norm_num) BstLean.Part268.WorldRow13015.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13015} (hw : c ∈ Hof BstLean.Part268.WorldRow13015.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13015) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13015).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13015) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13015_eq : scalarRow13015.targetFrame = BstLean.Part268.agent13015.frame := by
  norm_num [scalarRow13015,BstLean.Part268.agent13015]

noncomputable def frameData13015 : BstLean.Part264b.FrameData 13015 :=
  BstLean.Part269.frameData_from_numerics (n := 13015) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13015.worldPackage rfl BstLean.Part268.WorldRow13015.product_lower (BstLean.Part268.WorldRow13015.producthi.2.trans (by norm_num))
    scalarRow13015 repair13015 covarianceInputs13015 (fun i hi => sourceNumerics13015 hi)
    BstLean.Part268.agent13015.frame targetFrame13015_eq


end BstLean.Part269.N13015

namespace BstLean.Part269.N13016
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13016 : scalarRow13016.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13016, BstLean.Part268.grid13016, BstLean.Part263.worldGrid]

theorem supplies13016 (j : Fin 43) : Supply 13016 (parameters j)
    (cellLower scalarRow13016.grid (sourceIndex j))
    (cellUpper scalarRow13016.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13016.grid grid_top_bounds13016 j

theorem radii13016 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13016.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13016 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13016 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13016.grid grid_top_bounds13016 j hθ

noncomputable def covarianceInputs13016 :
    BstLean.Part263.CovarianceInputs 13016 scalarRow13016.grid parameters (caps repair13016) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13016 grid_top_bounds13016 repair13016

noncomputable def covarianceEvent13016 : Set (AgFam 13016) :=
  BstLean.Part263.covarianceEvent 13016 scalarRow13016.grid parameters

theorem covarianceEvent13016_measurable : MeasurableSet covarianceEvent13016 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13016_payment :
    (retDist (paperDesignP 13016).toCentres).real
      (agentEv (paperDesignP 13016) covarianceEvent13016)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13016

theorem localCov13016 : BstLean.Part259.LocalCovarianceOn covarianceEvent13016
    (BstLean.Part263.cell scalarRow13016.grid) (caps repair13016) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13016

theorem covarianceGood13016_payment :
    (retDist (paperDesignP 13016).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13016)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13016_payment



end BstLean.Part269.N13016

namespace BstLean.Part269.N13016
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13016}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13016.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13016) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13016).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13016 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13016) (by norm_num) BstLean.Part268.WorldRow13016.worldPackage rfl
    BstLean.Part268.WorldRow13016.product_lower (BstLean.Part268.WorldRow13016.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13016} (hw : c ∈ Hof BstLean.Part268.WorldRow13016.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13016) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13016) (by norm_num) BstLean.Part268.WorldRow13016.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13016} (hw : c ∈ Hof BstLean.Part268.WorldRow13016.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13016) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13016).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13016) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13016_eq : scalarRow13016.targetFrame = BstLean.Part268.agent13016.frame := by
  norm_num [scalarRow13016,BstLean.Part268.agent13016]

noncomputable def frameData13016 : BstLean.Part264b.FrameData 13016 :=
  BstLean.Part269.frameData_from_numerics (n := 13016) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13016.worldPackage rfl BstLean.Part268.WorldRow13016.product_lower (BstLean.Part268.WorldRow13016.producthi.2.trans (by norm_num))
    scalarRow13016 repair13016 covarianceInputs13016 (fun i hi => sourceNumerics13016 hi)
    BstLean.Part268.agent13016.frame targetFrame13016_eq


end BstLean.Part269.N13016

namespace BstLean.Part269.N13017
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13017 : scalarRow13017.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13017, BstLean.Part268.grid13017, BstLean.Part263.worldGrid]

theorem supplies13017 (j : Fin 43) : Supply 13017 (parameters j)
    (cellLower scalarRow13017.grid (sourceIndex j))
    (cellUpper scalarRow13017.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13017.grid grid_top_bounds13017 j

theorem radii13017 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13017.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13017 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13017 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13017.grid grid_top_bounds13017 j hθ

noncomputable def covarianceInputs13017 :
    BstLean.Part263.CovarianceInputs 13017 scalarRow13017.grid parameters (caps repair13017) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13017 grid_top_bounds13017 repair13017

noncomputable def covarianceEvent13017 : Set (AgFam 13017) :=
  BstLean.Part263.covarianceEvent 13017 scalarRow13017.grid parameters

theorem covarianceEvent13017_measurable : MeasurableSet covarianceEvent13017 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13017_payment :
    (retDist (paperDesignP 13017).toCentres).real
      (agentEv (paperDesignP 13017) covarianceEvent13017)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13017

theorem localCov13017 : BstLean.Part259.LocalCovarianceOn covarianceEvent13017
    (BstLean.Part263.cell scalarRow13017.grid) (caps repair13017) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13017

theorem covarianceGood13017_payment :
    (retDist (paperDesignP 13017).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13017)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13017_payment



end BstLean.Part269.N13017

namespace BstLean.Part269.N13017
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13017}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13017.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13017) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13017).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13017 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13017) (by norm_num) BstLean.Part268.WorldRow13017.worldPackage rfl
    BstLean.Part268.WorldRow13017.product_lower (BstLean.Part268.WorldRow13017.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13017} (hw : c ∈ Hof BstLean.Part268.WorldRow13017.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13017) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13017) (by norm_num) BstLean.Part268.WorldRow13017.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13017} (hw : c ∈ Hof BstLean.Part268.WorldRow13017.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13017) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13017).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13017) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13017_eq : scalarRow13017.targetFrame = BstLean.Part268.agent13017.frame := by
  norm_num [scalarRow13017,BstLean.Part268.agent13017]

noncomputable def frameData13017 : BstLean.Part264b.FrameData 13017 :=
  BstLean.Part269.frameData_from_numerics (n := 13017) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13017.worldPackage rfl BstLean.Part268.WorldRow13017.product_lower (BstLean.Part268.WorldRow13017.producthi.2.trans (by norm_num))
    scalarRow13017 repair13017 covarianceInputs13017 (fun i hi => sourceNumerics13017 hi)
    BstLean.Part268.agent13017.frame targetFrame13017_eq


end BstLean.Part269.N13017

namespace BstLean.Part269.N13018
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13018 : scalarRow13018.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13018, BstLean.Part268.grid13018, BstLean.Part263.worldGrid]

theorem supplies13018 (j : Fin 43) : Supply 13018 (parameters j)
    (cellLower scalarRow13018.grid (sourceIndex j))
    (cellUpper scalarRow13018.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13018.grid grid_top_bounds13018 j

theorem radii13018 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13018.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13018 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13018 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13018.grid grid_top_bounds13018 j hθ

noncomputable def covarianceInputs13018 :
    BstLean.Part263.CovarianceInputs 13018 scalarRow13018.grid parameters (caps repair13018) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13018 grid_top_bounds13018 repair13018

noncomputable def covarianceEvent13018 : Set (AgFam 13018) :=
  BstLean.Part263.covarianceEvent 13018 scalarRow13018.grid parameters

theorem covarianceEvent13018_measurable : MeasurableSet covarianceEvent13018 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13018_payment :
    (retDist (paperDesignP 13018).toCentres).real
      (agentEv (paperDesignP 13018) covarianceEvent13018)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13018

theorem localCov13018 : BstLean.Part259.LocalCovarianceOn covarianceEvent13018
    (BstLean.Part263.cell scalarRow13018.grid) (caps repair13018) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13018

theorem covarianceGood13018_payment :
    (retDist (paperDesignP 13018).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13018)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13018_payment



end BstLean.Part269.N13018

namespace BstLean.Part269.N13018
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13018}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13018.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13018) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13018).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13018 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13018) (by norm_num) BstLean.Part268.WorldRow13018.worldPackage rfl
    BstLean.Part268.WorldRow13018.product_lower (BstLean.Part268.WorldRow13018.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13018} (hw : c ∈ Hof BstLean.Part268.WorldRow13018.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13018) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13018) (by norm_num) BstLean.Part268.WorldRow13018.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13018} (hw : c ∈ Hof BstLean.Part268.WorldRow13018.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13018) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13018).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13018) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13018_eq : scalarRow13018.targetFrame = BstLean.Part268.agent13018.frame := by
  norm_num [scalarRow13018,BstLean.Part268.agent13018]

noncomputable def frameData13018 : BstLean.Part264b.FrameData 13018 :=
  BstLean.Part269.frameData_from_numerics (n := 13018) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13018.worldPackage rfl BstLean.Part268.WorldRow13018.product_lower (BstLean.Part268.WorldRow13018.producthi.2.trans (by norm_num))
    scalarRow13018 repair13018 covarianceInputs13018 (fun i hi => sourceNumerics13018 hi)
    BstLean.Part268.agent13018.frame targetFrame13018_eq


end BstLean.Part269.N13018

namespace BstLean.Part269.N13019
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13019 : scalarRow13019.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13019, BstLean.Part268.grid13019, BstLean.Part263.worldGrid]

theorem supplies13019 (j : Fin 43) : Supply 13019 (parameters j)
    (cellLower scalarRow13019.grid (sourceIndex j))
    (cellUpper scalarRow13019.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13019.grid grid_top_bounds13019 j

theorem radii13019 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13019.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13019 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13019 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13019.grid grid_top_bounds13019 j hθ

noncomputable def covarianceInputs13019 :
    BstLean.Part263.CovarianceInputs 13019 scalarRow13019.grid parameters (caps repair13019) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13019 grid_top_bounds13019 repair13019

noncomputable def covarianceEvent13019 : Set (AgFam 13019) :=
  BstLean.Part263.covarianceEvent 13019 scalarRow13019.grid parameters

theorem covarianceEvent13019_measurable : MeasurableSet covarianceEvent13019 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13019_payment :
    (retDist (paperDesignP 13019).toCentres).real
      (agentEv (paperDesignP 13019) covarianceEvent13019)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13019

theorem localCov13019 : BstLean.Part259.LocalCovarianceOn covarianceEvent13019
    (BstLean.Part263.cell scalarRow13019.grid) (caps repair13019) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13019

theorem covarianceGood13019_payment :
    (retDist (paperDesignP 13019).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13019)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13019_payment



end BstLean.Part269.N13019

namespace BstLean.Part269.N13019
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13019}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13019.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13019) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13019).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13019 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13019) (by norm_num) BstLean.Part268.WorldRow13019.worldPackage rfl
    BstLean.Part268.WorldRow13019.product_lower (BstLean.Part268.WorldRow13019.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13019} (hw : c ∈ Hof BstLean.Part268.WorldRow13019.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13019) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13019) (by norm_num) BstLean.Part268.WorldRow13019.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13019} (hw : c ∈ Hof BstLean.Part268.WorldRow13019.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13019) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13019).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13019) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13019_eq : scalarRow13019.targetFrame = BstLean.Part268.agent13019.frame := by
  norm_num [scalarRow13019,BstLean.Part268.agent13019]

noncomputable def frameData13019 : BstLean.Part264b.FrameData 13019 :=
  BstLean.Part269.frameData_from_numerics (n := 13019) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13019.worldPackage rfl BstLean.Part268.WorldRow13019.product_lower (BstLean.Part268.WorldRow13019.producthi.2.trans (by norm_num))
    scalarRow13019 repair13019 covarianceInputs13019 (fun i hi => sourceNumerics13019 hi)
    BstLean.Part268.agent13019.frame targetFrame13019_eq


end BstLean.Part269.N13019
