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

namespace BstLean.Part269.N13005
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13005 : scalarRow13005.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13005, BstLean.Part268.grid13005, BstLean.Part263.worldGrid]

theorem supplies13005 (j : Fin 43) : Supply 13005 (parameters j)
    (cellLower scalarRow13005.grid (sourceIndex j))
    (cellUpper scalarRow13005.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13005.grid grid_top_bounds13005 j

theorem radii13005 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13005.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13005 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13005 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13005.grid grid_top_bounds13005 j hθ

noncomputable def covarianceInputs13005 :
    BstLean.Part263.CovarianceInputs 13005 scalarRow13005.grid parameters (caps repair13005) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13005 grid_top_bounds13005 repair13005

noncomputable def covarianceEvent13005 : Set (AgFam 13005) :=
  BstLean.Part263.covarianceEvent 13005 scalarRow13005.grid parameters

theorem covarianceEvent13005_measurable : MeasurableSet covarianceEvent13005 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13005_payment :
    (retDist (paperDesignP 13005).toCentres).real
      (agentEv (paperDesignP 13005) covarianceEvent13005)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13005

theorem localCov13005 : BstLean.Part259.LocalCovarianceOn covarianceEvent13005
    (BstLean.Part263.cell scalarRow13005.grid) (caps repair13005) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13005

theorem covarianceGood13005_payment :
    (retDist (paperDesignP 13005).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13005)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13005_payment



end BstLean.Part269.N13005

namespace BstLean.Part269.N13005
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13005}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13005.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13005) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13005).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13005 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13005) (by norm_num) BstLean.Part268.WorldRow13005.worldPackage rfl
    BstLean.Part268.WorldRow13005.product_lower (BstLean.Part268.WorldRow13005.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13005} (hw : c ∈ Hof BstLean.Part268.WorldRow13005.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13005) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13005) (by norm_num) BstLean.Part268.WorldRow13005.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13005} (hw : c ∈ Hof BstLean.Part268.WorldRow13005.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13005) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13005).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13005) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13005_eq : scalarRow13005.targetFrame = BstLean.Part268.agent13005.frame := by
  norm_num [scalarRow13005,BstLean.Part268.agent13005]

noncomputable def frameData13005 : BstLean.Part264b.FrameData 13005 :=
  BstLean.Part269.frameData_from_numerics (n := 13005) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13005.worldPackage rfl BstLean.Part268.WorldRow13005.product_lower (BstLean.Part268.WorldRow13005.producthi.2.trans (by norm_num))
    scalarRow13005 repair13005 covarianceInputs13005 (fun i hi => sourceNumerics13005 hi)
    BstLean.Part268.agent13005.frame targetFrame13005_eq


end BstLean.Part269.N13005

namespace BstLean.Part269.N13006
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13006 : scalarRow13006.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13006, BstLean.Part268.grid13006, BstLean.Part263.worldGrid]

theorem supplies13006 (j : Fin 43) : Supply 13006 (parameters j)
    (cellLower scalarRow13006.grid (sourceIndex j))
    (cellUpper scalarRow13006.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13006.grid grid_top_bounds13006 j

theorem radii13006 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13006.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13006 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13006 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13006.grid grid_top_bounds13006 j hθ

noncomputable def covarianceInputs13006 :
    BstLean.Part263.CovarianceInputs 13006 scalarRow13006.grid parameters (caps repair13006) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13006 grid_top_bounds13006 repair13006

noncomputable def covarianceEvent13006 : Set (AgFam 13006) :=
  BstLean.Part263.covarianceEvent 13006 scalarRow13006.grid parameters

theorem covarianceEvent13006_measurable : MeasurableSet covarianceEvent13006 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13006_payment :
    (retDist (paperDesignP 13006).toCentres).real
      (agentEv (paperDesignP 13006) covarianceEvent13006)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13006

theorem localCov13006 : BstLean.Part259.LocalCovarianceOn covarianceEvent13006
    (BstLean.Part263.cell scalarRow13006.grid) (caps repair13006) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13006

theorem covarianceGood13006_payment :
    (retDist (paperDesignP 13006).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13006)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13006_payment



end BstLean.Part269.N13006

namespace BstLean.Part269.N13006
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13006}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13006.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13006) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13006).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13006 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13006) (by norm_num) BstLean.Part268.WorldRow13006.worldPackage rfl
    BstLean.Part268.WorldRow13006.product_lower (BstLean.Part268.WorldRow13006.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13006} (hw : c ∈ Hof BstLean.Part268.WorldRow13006.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13006) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13006) (by norm_num) BstLean.Part268.WorldRow13006.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13006} (hw : c ∈ Hof BstLean.Part268.WorldRow13006.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13006) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13006).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13006) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13006_eq : scalarRow13006.targetFrame = BstLean.Part268.agent13006.frame := by
  norm_num [scalarRow13006,BstLean.Part268.agent13006]

noncomputable def frameData13006 : BstLean.Part264b.FrameData 13006 :=
  BstLean.Part269.frameData_from_numerics (n := 13006) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13006.worldPackage rfl BstLean.Part268.WorldRow13006.product_lower (BstLean.Part268.WorldRow13006.producthi.2.trans (by norm_num))
    scalarRow13006 repair13006 covarianceInputs13006 (fun i hi => sourceNumerics13006 hi)
    BstLean.Part268.agent13006.frame targetFrame13006_eq


end BstLean.Part269.N13006

namespace BstLean.Part269.N13007
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13007 : scalarRow13007.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13007, BstLean.Part268.grid13007, BstLean.Part263.worldGrid]

theorem supplies13007 (j : Fin 43) : Supply 13007 (parameters j)
    (cellLower scalarRow13007.grid (sourceIndex j))
    (cellUpper scalarRow13007.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13007.grid grid_top_bounds13007 j

theorem radii13007 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13007.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13007 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13007 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13007.grid grid_top_bounds13007 j hθ

noncomputable def covarianceInputs13007 :
    BstLean.Part263.CovarianceInputs 13007 scalarRow13007.grid parameters (caps repair13007) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13007 grid_top_bounds13007 repair13007

noncomputable def covarianceEvent13007 : Set (AgFam 13007) :=
  BstLean.Part263.covarianceEvent 13007 scalarRow13007.grid parameters

theorem covarianceEvent13007_measurable : MeasurableSet covarianceEvent13007 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13007_payment :
    (retDist (paperDesignP 13007).toCentres).real
      (agentEv (paperDesignP 13007) covarianceEvent13007)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13007

theorem localCov13007 : BstLean.Part259.LocalCovarianceOn covarianceEvent13007
    (BstLean.Part263.cell scalarRow13007.grid) (caps repair13007) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13007

theorem covarianceGood13007_payment :
    (retDist (paperDesignP 13007).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13007)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13007_payment



end BstLean.Part269.N13007

namespace BstLean.Part269.N13007
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13007}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13007.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13007) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13007).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13007 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13007) (by norm_num) BstLean.Part268.WorldRow13007.worldPackage rfl
    BstLean.Part268.WorldRow13007.product_lower (BstLean.Part268.WorldRow13007.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13007} (hw : c ∈ Hof BstLean.Part268.WorldRow13007.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13007) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13007) (by norm_num) BstLean.Part268.WorldRow13007.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13007} (hw : c ∈ Hof BstLean.Part268.WorldRow13007.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13007) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13007).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13007) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13007_eq : scalarRow13007.targetFrame = BstLean.Part268.agent13007.frame := by
  norm_num [scalarRow13007,BstLean.Part268.agent13007]

noncomputable def frameData13007 : BstLean.Part264b.FrameData 13007 :=
  BstLean.Part269.frameData_from_numerics (n := 13007) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13007.worldPackage rfl BstLean.Part268.WorldRow13007.product_lower (BstLean.Part268.WorldRow13007.producthi.2.trans (by norm_num))
    scalarRow13007 repair13007 covarianceInputs13007 (fun i hi => sourceNumerics13007 hi)
    BstLean.Part268.agent13007.frame targetFrame13007_eq


end BstLean.Part269.N13007

namespace BstLean.Part269.N13008
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13008 : scalarRow13008.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13008, BstLean.Part268.grid13008, BstLean.Part263.worldGrid]

theorem supplies13008 (j : Fin 43) : Supply 13008 (parameters j)
    (cellLower scalarRow13008.grid (sourceIndex j))
    (cellUpper scalarRow13008.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13008.grid grid_top_bounds13008 j

theorem radii13008 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13008.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13008 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13008 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13008.grid grid_top_bounds13008 j hθ

noncomputable def covarianceInputs13008 :
    BstLean.Part263.CovarianceInputs 13008 scalarRow13008.grid parameters (caps repair13008) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13008 grid_top_bounds13008 repair13008

noncomputable def covarianceEvent13008 : Set (AgFam 13008) :=
  BstLean.Part263.covarianceEvent 13008 scalarRow13008.grid parameters

theorem covarianceEvent13008_measurable : MeasurableSet covarianceEvent13008 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13008_payment :
    (retDist (paperDesignP 13008).toCentres).real
      (agentEv (paperDesignP 13008) covarianceEvent13008)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13008

theorem localCov13008 : BstLean.Part259.LocalCovarianceOn covarianceEvent13008
    (BstLean.Part263.cell scalarRow13008.grid) (caps repair13008) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13008

theorem covarianceGood13008_payment :
    (retDist (paperDesignP 13008).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13008)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13008_payment



end BstLean.Part269.N13008

namespace BstLean.Part269.N13008
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13008}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13008.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13008) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13008).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13008 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13008) (by norm_num) BstLean.Part268.WorldRow13008.worldPackage rfl
    BstLean.Part268.WorldRow13008.product_lower (BstLean.Part268.WorldRow13008.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13008} (hw : c ∈ Hof BstLean.Part268.WorldRow13008.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13008) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13008) (by norm_num) BstLean.Part268.WorldRow13008.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13008} (hw : c ∈ Hof BstLean.Part268.WorldRow13008.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13008) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13008).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13008) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13008_eq : scalarRow13008.targetFrame = BstLean.Part268.agent13008.frame := by
  norm_num [scalarRow13008,BstLean.Part268.agent13008]

noncomputable def frameData13008 : BstLean.Part264b.FrameData 13008 :=
  BstLean.Part269.frameData_from_numerics (n := 13008) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13008.worldPackage rfl BstLean.Part268.WorldRow13008.product_lower (BstLean.Part268.WorldRow13008.producthi.2.trans (by norm_num))
    scalarRow13008 repair13008 covarianceInputs13008 (fun i hi => sourceNumerics13008 hi)
    BstLean.Part268.agent13008.frame targetFrame13008_eq


end BstLean.Part269.N13008

namespace BstLean.Part269.N13009
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13009 : scalarRow13009.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13009, BstLean.Part268.grid13009, BstLean.Part263.worldGrid]

theorem supplies13009 (j : Fin 43) : Supply 13009 (parameters j)
    (cellLower scalarRow13009.grid (sourceIndex j))
    (cellUpper scalarRow13009.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13009.grid grid_top_bounds13009 j

theorem radii13009 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13009.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13009 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13009 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13009.grid grid_top_bounds13009 j hθ

noncomputable def covarianceInputs13009 :
    BstLean.Part263.CovarianceInputs 13009 scalarRow13009.grid parameters (caps repair13009) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13009 grid_top_bounds13009 repair13009

noncomputable def covarianceEvent13009 : Set (AgFam 13009) :=
  BstLean.Part263.covarianceEvent 13009 scalarRow13009.grid parameters

theorem covarianceEvent13009_measurable : MeasurableSet covarianceEvent13009 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13009_payment :
    (retDist (paperDesignP 13009).toCentres).real
      (agentEv (paperDesignP 13009) covarianceEvent13009)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13009

theorem localCov13009 : BstLean.Part259.LocalCovarianceOn covarianceEvent13009
    (BstLean.Part263.cell scalarRow13009.grid) (caps repair13009) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13009

theorem covarianceGood13009_payment :
    (retDist (paperDesignP 13009).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13009)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13009_payment



end BstLean.Part269.N13009

namespace BstLean.Part269.N13009
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13009}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13009.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13009) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13009).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13009 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13009) (by norm_num) BstLean.Part268.WorldRow13009.worldPackage rfl
    BstLean.Part268.WorldRow13009.product_lower (BstLean.Part268.WorldRow13009.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13009} (hw : c ∈ Hof BstLean.Part268.WorldRow13009.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13009) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13009) (by norm_num) BstLean.Part268.WorldRow13009.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13009} (hw : c ∈ Hof BstLean.Part268.WorldRow13009.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13009) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13009).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13009) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13009_eq : scalarRow13009.targetFrame = BstLean.Part268.agent13009.frame := by
  norm_num [scalarRow13009,BstLean.Part268.agent13009]

noncomputable def frameData13009 : BstLean.Part264b.FrameData 13009 :=
  BstLean.Part269.frameData_from_numerics (n := 13009) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13009.worldPackage rfl BstLean.Part268.WorldRow13009.product_lower (BstLean.Part268.WorldRow13009.producthi.2.trans (by norm_num))
    scalarRow13009 repair13009 covarianceInputs13009 (fun i hi => sourceNumerics13009 hi)
    BstLean.Part268.agent13009.frame targetFrame13009_eq


end BstLean.Part269.N13009
