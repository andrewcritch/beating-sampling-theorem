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

namespace BstLean.Part269.N13010
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13010 : scalarRow13010.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13010, BstLean.Part268.grid13010, BstLean.Part263.worldGrid]

theorem supplies13010 (j : Fin 43) : Supply 13010 (parameters j)
    (cellLower scalarRow13010.grid (sourceIndex j))
    (cellUpper scalarRow13010.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13010.grid grid_top_bounds13010 j

theorem radii13010 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13010.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13010 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13010 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13010.grid grid_top_bounds13010 j hθ

noncomputable def covarianceInputs13010 :
    BstLean.Part263.CovarianceInputs 13010 scalarRow13010.grid parameters (caps repair13010) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13010 grid_top_bounds13010 repair13010

noncomputable def covarianceEvent13010 : Set (AgFam 13010) :=
  BstLean.Part263.covarianceEvent 13010 scalarRow13010.grid parameters

theorem covarianceEvent13010_measurable : MeasurableSet covarianceEvent13010 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13010_payment :
    (retDist (paperDesignP 13010).toCentres).real
      (agentEv (paperDesignP 13010) covarianceEvent13010)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13010

theorem localCov13010 : BstLean.Part259.LocalCovarianceOn covarianceEvent13010
    (BstLean.Part263.cell scalarRow13010.grid) (caps repair13010) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13010

theorem covarianceGood13010_payment :
    (retDist (paperDesignP 13010).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13010)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13010_payment



end BstLean.Part269.N13010

namespace BstLean.Part269.N13010
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13010}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13010.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13010) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13010).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13010 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13010) (by norm_num) BstLean.Part268.WorldRow13010.worldPackage rfl
    BstLean.Part268.WorldRow13010.product_lower (BstLean.Part268.WorldRow13010.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13010} (hw : c ∈ Hof BstLean.Part268.WorldRow13010.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13010) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13010) (by norm_num) BstLean.Part268.WorldRow13010.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13010} (hw : c ∈ Hof BstLean.Part268.WorldRow13010.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13010) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13010).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13010) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13010_eq : scalarRow13010.targetFrame = BstLean.Part268.agent13010.frame := by
  norm_num [scalarRow13010,BstLean.Part268.agent13010]

noncomputable def frameData13010 : BstLean.Part264b.FrameData 13010 :=
  BstLean.Part269.frameData_from_numerics (n := 13010) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13010.worldPackage rfl BstLean.Part268.WorldRow13010.product_lower (BstLean.Part268.WorldRow13010.producthi.2.trans (by norm_num))
    scalarRow13010 repair13010 covarianceInputs13010 (fun i hi => sourceNumerics13010 hi)
    BstLean.Part268.agent13010.frame targetFrame13010_eq


end BstLean.Part269.N13010

namespace BstLean.Part269.N13011
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13011 : scalarRow13011.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13011, BstLean.Part268.grid13011, BstLean.Part263.worldGrid]

theorem supplies13011 (j : Fin 43) : Supply 13011 (parameters j)
    (cellLower scalarRow13011.grid (sourceIndex j))
    (cellUpper scalarRow13011.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13011.grid grid_top_bounds13011 j

theorem radii13011 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13011.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13011 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13011 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13011.grid grid_top_bounds13011 j hθ

noncomputable def covarianceInputs13011 :
    BstLean.Part263.CovarianceInputs 13011 scalarRow13011.grid parameters (caps repair13011) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13011 grid_top_bounds13011 repair13011

noncomputable def covarianceEvent13011 : Set (AgFam 13011) :=
  BstLean.Part263.covarianceEvent 13011 scalarRow13011.grid parameters

theorem covarianceEvent13011_measurable : MeasurableSet covarianceEvent13011 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13011_payment :
    (retDist (paperDesignP 13011).toCentres).real
      (agentEv (paperDesignP 13011) covarianceEvent13011)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13011

theorem localCov13011 : BstLean.Part259.LocalCovarianceOn covarianceEvent13011
    (BstLean.Part263.cell scalarRow13011.grid) (caps repair13011) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13011

theorem covarianceGood13011_payment :
    (retDist (paperDesignP 13011).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13011)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13011_payment



end BstLean.Part269.N13011

namespace BstLean.Part269.N13011
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13011}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13011.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13011) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13011).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13011 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13011) (by norm_num) BstLean.Part268.WorldRow13011.worldPackage rfl
    BstLean.Part268.WorldRow13011.product_lower (BstLean.Part268.WorldRow13011.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13011} (hw : c ∈ Hof BstLean.Part268.WorldRow13011.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13011) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13011) (by norm_num) BstLean.Part268.WorldRow13011.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13011} (hw : c ∈ Hof BstLean.Part268.WorldRow13011.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13011) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13011).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13011) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13011_eq : scalarRow13011.targetFrame = BstLean.Part268.agent13011.frame := by
  norm_num [scalarRow13011,BstLean.Part268.agent13011]

noncomputable def frameData13011 : BstLean.Part264b.FrameData 13011 :=
  BstLean.Part269.frameData_from_numerics (n := 13011) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13011.worldPackage rfl BstLean.Part268.WorldRow13011.product_lower (BstLean.Part268.WorldRow13011.producthi.2.trans (by norm_num))
    scalarRow13011 repair13011 covarianceInputs13011 (fun i hi => sourceNumerics13011 hi)
    BstLean.Part268.agent13011.frame targetFrame13011_eq


end BstLean.Part269.N13011

namespace BstLean.Part269.N13012
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13012 : scalarRow13012.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13012, BstLean.Part268.grid13012, BstLean.Part263.worldGrid]

theorem supplies13012 (j : Fin 43) : Supply 13012 (parameters j)
    (cellLower scalarRow13012.grid (sourceIndex j))
    (cellUpper scalarRow13012.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13012.grid grid_top_bounds13012 j

theorem radii13012 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13012.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13012 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13012 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13012.grid grid_top_bounds13012 j hθ

noncomputable def covarianceInputs13012 :
    BstLean.Part263.CovarianceInputs 13012 scalarRow13012.grid parameters (caps repair13012) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13012 grid_top_bounds13012 repair13012

noncomputable def covarianceEvent13012 : Set (AgFam 13012) :=
  BstLean.Part263.covarianceEvent 13012 scalarRow13012.grid parameters

theorem covarianceEvent13012_measurable : MeasurableSet covarianceEvent13012 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13012_payment :
    (retDist (paperDesignP 13012).toCentres).real
      (agentEv (paperDesignP 13012) covarianceEvent13012)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13012

theorem localCov13012 : BstLean.Part259.LocalCovarianceOn covarianceEvent13012
    (BstLean.Part263.cell scalarRow13012.grid) (caps repair13012) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13012

theorem covarianceGood13012_payment :
    (retDist (paperDesignP 13012).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13012)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13012_payment



end BstLean.Part269.N13012

namespace BstLean.Part269.N13012
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13012}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13012.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13012) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13012).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13012 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13012) (by norm_num) BstLean.Part268.WorldRow13012.worldPackage rfl
    BstLean.Part268.WorldRow13012.product_lower (BstLean.Part268.WorldRow13012.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13012} (hw : c ∈ Hof BstLean.Part268.WorldRow13012.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13012) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13012) (by norm_num) BstLean.Part268.WorldRow13012.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13012} (hw : c ∈ Hof BstLean.Part268.WorldRow13012.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13012) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13012).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13012) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13012_eq : scalarRow13012.targetFrame = BstLean.Part268.agent13012.frame := by
  norm_num [scalarRow13012,BstLean.Part268.agent13012]

noncomputable def frameData13012 : BstLean.Part264b.FrameData 13012 :=
  BstLean.Part269.frameData_from_numerics (n := 13012) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13012.worldPackage rfl BstLean.Part268.WorldRow13012.product_lower (BstLean.Part268.WorldRow13012.producthi.2.trans (by norm_num))
    scalarRow13012 repair13012 covarianceInputs13012 (fun i hi => sourceNumerics13012 hi)
    BstLean.Part268.agent13012.frame targetFrame13012_eq


end BstLean.Part269.N13012

namespace BstLean.Part269.N13013
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13013 : scalarRow13013.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13013, BstLean.Part268.grid13013, BstLean.Part263.worldGrid]

theorem supplies13013 (j : Fin 43) : Supply 13013 (parameters j)
    (cellLower scalarRow13013.grid (sourceIndex j))
    (cellUpper scalarRow13013.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13013.grid grid_top_bounds13013 j

theorem radii13013 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13013.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13013 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13013 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13013.grid grid_top_bounds13013 j hθ

noncomputable def covarianceInputs13013 :
    BstLean.Part263.CovarianceInputs 13013 scalarRow13013.grid parameters (caps repair13013) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13013 grid_top_bounds13013 repair13013

noncomputable def covarianceEvent13013 : Set (AgFam 13013) :=
  BstLean.Part263.covarianceEvent 13013 scalarRow13013.grid parameters

theorem covarianceEvent13013_measurable : MeasurableSet covarianceEvent13013 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13013_payment :
    (retDist (paperDesignP 13013).toCentres).real
      (agentEv (paperDesignP 13013) covarianceEvent13013)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13013

theorem localCov13013 : BstLean.Part259.LocalCovarianceOn covarianceEvent13013
    (BstLean.Part263.cell scalarRow13013.grid) (caps repair13013) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13013

theorem covarianceGood13013_payment :
    (retDist (paperDesignP 13013).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13013)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13013_payment



end BstLean.Part269.N13013

namespace BstLean.Part269.N13013
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13013}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13013.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13013) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13013).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13013 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13013) (by norm_num) BstLean.Part268.WorldRow13013.worldPackage rfl
    BstLean.Part268.WorldRow13013.product_lower (BstLean.Part268.WorldRow13013.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13013} (hw : c ∈ Hof BstLean.Part268.WorldRow13013.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13013) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13013) (by norm_num) BstLean.Part268.WorldRow13013.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13013} (hw : c ∈ Hof BstLean.Part268.WorldRow13013.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13013) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13013).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13013) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13013_eq : scalarRow13013.targetFrame = BstLean.Part268.agent13013.frame := by
  norm_num [scalarRow13013,BstLean.Part268.agent13013]

noncomputable def frameData13013 : BstLean.Part264b.FrameData 13013 :=
  BstLean.Part269.frameData_from_numerics (n := 13013) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13013.worldPackage rfl BstLean.Part268.WorldRow13013.product_lower (BstLean.Part268.WorldRow13013.producthi.2.trans (by norm_num))
    scalarRow13013 repair13013 covarianceInputs13013 (fun i hi => sourceNumerics13013 hi)
    BstLean.Part268.agent13013.frame targetFrame13013_eq


end BstLean.Part269.N13013

namespace BstLean.Part269.N13014
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13014 : scalarRow13014.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13014, BstLean.Part268.grid13014, BstLean.Part263.worldGrid]

theorem supplies13014 (j : Fin 43) : Supply 13014 (parameters j)
    (cellLower scalarRow13014.grid (sourceIndex j))
    (cellUpper scalarRow13014.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13014.grid grid_top_bounds13014 j

theorem radii13014 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13014.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13014 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13014 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13014.grid grid_top_bounds13014 j hθ

noncomputable def covarianceInputs13014 :
    BstLean.Part263.CovarianceInputs 13014 scalarRow13014.grid parameters (caps repair13014) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13014 grid_top_bounds13014 repair13014

noncomputable def covarianceEvent13014 : Set (AgFam 13014) :=
  BstLean.Part263.covarianceEvent 13014 scalarRow13014.grid parameters

theorem covarianceEvent13014_measurable : MeasurableSet covarianceEvent13014 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13014_payment :
    (retDist (paperDesignP 13014).toCentres).real
      (agentEv (paperDesignP 13014) covarianceEvent13014)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13014

theorem localCov13014 : BstLean.Part259.LocalCovarianceOn covarianceEvent13014
    (BstLean.Part263.cell scalarRow13014.grid) (caps repair13014) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13014

theorem covarianceGood13014_payment :
    (retDist (paperDesignP 13014).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13014)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13014_payment



end BstLean.Part269.N13014

namespace BstLean.Part269.N13014
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13014}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13014.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13014) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13014).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13014 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13014) (by norm_num) BstLean.Part268.WorldRow13014.worldPackage rfl
    BstLean.Part268.WorldRow13014.product_lower (BstLean.Part268.WorldRow13014.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13014} (hw : c ∈ Hof BstLean.Part268.WorldRow13014.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13014) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13014) (by norm_num) BstLean.Part268.WorldRow13014.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13014} (hw : c ∈ Hof BstLean.Part268.WorldRow13014.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13014) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13014).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13014) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13014_eq : scalarRow13014.targetFrame = BstLean.Part268.agent13014.frame := by
  norm_num [scalarRow13014,BstLean.Part268.agent13014]

noncomputable def frameData13014 : BstLean.Part264b.FrameData 13014 :=
  BstLean.Part269.frameData_from_numerics (n := 13014) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13014.worldPackage rfl BstLean.Part268.WorldRow13014.product_lower (BstLean.Part268.WorldRow13014.producthi.2.trans (by norm_num))
    scalarRow13014 repair13014 covarianceInputs13014 (fun i hi => sourceNumerics13014 hi)
    BstLean.Part268.agent13014.frame targetFrame13014_eq


end BstLean.Part269.N13014
