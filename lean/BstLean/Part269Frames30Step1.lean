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

namespace BstLean.Part269.N13105
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13105 : scalarRow13105.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13105, BstLean.Part268.grid13105, BstLean.Part263.worldGrid]

theorem supplies13105 (j : Fin 43) : Supply 13105 (parameters j)
    (cellLower scalarRow13105.grid (sourceIndex j))
    (cellUpper scalarRow13105.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13105.grid grid_top_bounds13105 j

theorem radii13105 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13105.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13105 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13105 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13105.grid grid_top_bounds13105 j hθ

noncomputable def covarianceInputs13105 :
    BstLean.Part263.CovarianceInputs 13105 scalarRow13105.grid parameters (caps repair13105) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13105 grid_top_bounds13105 repair13105

noncomputable def covarianceEvent13105 : Set (AgFam 13105) :=
  BstLean.Part263.covarianceEvent 13105 scalarRow13105.grid parameters

theorem covarianceEvent13105_measurable : MeasurableSet covarianceEvent13105 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13105_payment :
    (retDist (paperDesignP 13105).toCentres).real
      (agentEv (paperDesignP 13105) covarianceEvent13105)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13105

theorem localCov13105 : BstLean.Part259.LocalCovarianceOn covarianceEvent13105
    (BstLean.Part263.cell scalarRow13105.grid) (caps repair13105) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13105

theorem covarianceGood13105_payment :
    (retDist (paperDesignP 13105).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13105)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13105_payment



end BstLean.Part269.N13105

namespace BstLean.Part269.N13105
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13105}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13105.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13105) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13105).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13105 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13105) (by norm_num) BstLean.Part268.WorldRow13105.worldPackage rfl
    BstLean.Part268.WorldRow13105.product_lower (BstLean.Part268.WorldRow13105.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13105} (hw : c ∈ Hof BstLean.Part268.WorldRow13105.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13105) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13105) (by norm_num) BstLean.Part268.WorldRow13105.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13105} (hw : c ∈ Hof BstLean.Part268.WorldRow13105.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13105) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13105).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13105) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13105_eq : scalarRow13105.targetFrame = BstLean.Part268.agent13105.frame := by
  norm_num [scalarRow13105,BstLean.Part268.agent13105]

noncomputable def frameData13105 : BstLean.Part264b.FrameData 13105 :=
  BstLean.Part269.frameData_from_numerics (n := 13105) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13105.worldPackage rfl BstLean.Part268.WorldRow13105.product_lower (BstLean.Part268.WorldRow13105.producthi.2.trans (by norm_num))
    scalarRow13105 repair13105 covarianceInputs13105 (fun i hi => sourceNumerics13105 hi)
    BstLean.Part268.agent13105.frame targetFrame13105_eq


end BstLean.Part269.N13105

namespace BstLean.Part269.N13106
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13106 : scalarRow13106.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13106, BstLean.Part268.grid13106, BstLean.Part263.worldGrid]

theorem supplies13106 (j : Fin 43) : Supply 13106 (parameters j)
    (cellLower scalarRow13106.grid (sourceIndex j))
    (cellUpper scalarRow13106.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13106.grid grid_top_bounds13106 j

theorem radii13106 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13106.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13106 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13106 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13106.grid grid_top_bounds13106 j hθ

noncomputable def covarianceInputs13106 :
    BstLean.Part263.CovarianceInputs 13106 scalarRow13106.grid parameters (caps repair13106) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13106 grid_top_bounds13106 repair13106

noncomputable def covarianceEvent13106 : Set (AgFam 13106) :=
  BstLean.Part263.covarianceEvent 13106 scalarRow13106.grid parameters

theorem covarianceEvent13106_measurable : MeasurableSet covarianceEvent13106 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13106_payment :
    (retDist (paperDesignP 13106).toCentres).real
      (agentEv (paperDesignP 13106) covarianceEvent13106)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13106

theorem localCov13106 : BstLean.Part259.LocalCovarianceOn covarianceEvent13106
    (BstLean.Part263.cell scalarRow13106.grid) (caps repair13106) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13106

theorem covarianceGood13106_payment :
    (retDist (paperDesignP 13106).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13106)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13106_payment



end BstLean.Part269.N13106

namespace BstLean.Part269.N13106
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13106}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13106.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13106) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13106).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13106 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13106) (by norm_num) BstLean.Part268.WorldRow13106.worldPackage rfl
    BstLean.Part268.WorldRow13106.product_lower (BstLean.Part268.WorldRow13106.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13106} (hw : c ∈ Hof BstLean.Part268.WorldRow13106.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13106) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13106) (by norm_num) BstLean.Part268.WorldRow13106.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13106} (hw : c ∈ Hof BstLean.Part268.WorldRow13106.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13106) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13106).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13106) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13106_eq : scalarRow13106.targetFrame = BstLean.Part268.agent13106.frame := by
  norm_num [scalarRow13106,BstLean.Part268.agent13106]

noncomputable def frameData13106 : BstLean.Part264b.FrameData 13106 :=
  BstLean.Part269.frameData_from_numerics (n := 13106) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13106.worldPackage rfl BstLean.Part268.WorldRow13106.product_lower (BstLean.Part268.WorldRow13106.producthi.2.trans (by norm_num))
    scalarRow13106 repair13106 covarianceInputs13106 (fun i hi => sourceNumerics13106 hi)
    BstLean.Part268.agent13106.frame targetFrame13106_eq


end BstLean.Part269.N13106

namespace BstLean.Part269.N13107
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13107 : scalarRow13107.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13107, BstLean.Part268.grid13107, BstLean.Part263.worldGrid]

theorem supplies13107 (j : Fin 43) : Supply 13107 (parameters j)
    (cellLower scalarRow13107.grid (sourceIndex j))
    (cellUpper scalarRow13107.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13107.grid grid_top_bounds13107 j

theorem radii13107 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13107.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13107 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13107 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13107.grid grid_top_bounds13107 j hθ

noncomputable def covarianceInputs13107 :
    BstLean.Part263.CovarianceInputs 13107 scalarRow13107.grid parameters (caps repair13107) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13107 grid_top_bounds13107 repair13107

noncomputable def covarianceEvent13107 : Set (AgFam 13107) :=
  BstLean.Part263.covarianceEvent 13107 scalarRow13107.grid parameters

theorem covarianceEvent13107_measurable : MeasurableSet covarianceEvent13107 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13107_payment :
    (retDist (paperDesignP 13107).toCentres).real
      (agentEv (paperDesignP 13107) covarianceEvent13107)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13107

theorem localCov13107 : BstLean.Part259.LocalCovarianceOn covarianceEvent13107
    (BstLean.Part263.cell scalarRow13107.grid) (caps repair13107) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13107

theorem covarianceGood13107_payment :
    (retDist (paperDesignP 13107).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13107)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13107_payment



end BstLean.Part269.N13107

namespace BstLean.Part269.N13107
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13107}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13107.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13107) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13107).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13107 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13107) (by norm_num) BstLean.Part268.WorldRow13107.worldPackage rfl
    BstLean.Part268.WorldRow13107.product_lower (BstLean.Part268.WorldRow13107.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13107} (hw : c ∈ Hof BstLean.Part268.WorldRow13107.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13107) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13107) (by norm_num) BstLean.Part268.WorldRow13107.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13107} (hw : c ∈ Hof BstLean.Part268.WorldRow13107.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13107) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13107).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13107) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13107_eq : scalarRow13107.targetFrame = BstLean.Part268.agent13107.frame := by
  norm_num [scalarRow13107,BstLean.Part268.agent13107]

noncomputable def frameData13107 : BstLean.Part264b.FrameData 13107 :=
  BstLean.Part269.frameData_from_numerics (n := 13107) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13107.worldPackage rfl BstLean.Part268.WorldRow13107.product_lower (BstLean.Part268.WorldRow13107.producthi.2.trans (by norm_num))
    scalarRow13107 repair13107 covarianceInputs13107 (fun i hi => sourceNumerics13107 hi)
    BstLean.Part268.agent13107.frame targetFrame13107_eq


end BstLean.Part269.N13107

namespace BstLean.Part269.N13108
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13108 : scalarRow13108.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13108, BstLean.Part268.grid13108, BstLean.Part263.worldGrid]

theorem supplies13108 (j : Fin 43) : Supply 13108 (parameters j)
    (cellLower scalarRow13108.grid (sourceIndex j))
    (cellUpper scalarRow13108.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13108.grid grid_top_bounds13108 j

theorem radii13108 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13108.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13108 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13108 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13108.grid grid_top_bounds13108 j hθ

noncomputable def covarianceInputs13108 :
    BstLean.Part263.CovarianceInputs 13108 scalarRow13108.grid parameters (caps repair13108) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13108 grid_top_bounds13108 repair13108

noncomputable def covarianceEvent13108 : Set (AgFam 13108) :=
  BstLean.Part263.covarianceEvent 13108 scalarRow13108.grid parameters

theorem covarianceEvent13108_measurable : MeasurableSet covarianceEvent13108 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13108_payment :
    (retDist (paperDesignP 13108).toCentres).real
      (agentEv (paperDesignP 13108) covarianceEvent13108)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13108

theorem localCov13108 : BstLean.Part259.LocalCovarianceOn covarianceEvent13108
    (BstLean.Part263.cell scalarRow13108.grid) (caps repair13108) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13108

theorem covarianceGood13108_payment :
    (retDist (paperDesignP 13108).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13108)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13108_payment



end BstLean.Part269.N13108

namespace BstLean.Part269.N13108
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13108}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13108.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13108) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13108).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13108 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13108) (by norm_num) BstLean.Part268.WorldRow13108.worldPackage rfl
    BstLean.Part268.WorldRow13108.product_lower (BstLean.Part268.WorldRow13108.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13108} (hw : c ∈ Hof BstLean.Part268.WorldRow13108.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13108) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13108) (by norm_num) BstLean.Part268.WorldRow13108.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13108} (hw : c ∈ Hof BstLean.Part268.WorldRow13108.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13108) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13108).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13108) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13108_eq : scalarRow13108.targetFrame = BstLean.Part268.agent13108.frame := by
  norm_num [scalarRow13108,BstLean.Part268.agent13108]

noncomputable def frameData13108 : BstLean.Part264b.FrameData 13108 :=
  BstLean.Part269.frameData_from_numerics (n := 13108) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13108.worldPackage rfl BstLean.Part268.WorldRow13108.product_lower (BstLean.Part268.WorldRow13108.producthi.2.trans (by norm_num))
    scalarRow13108 repair13108 covarianceInputs13108 (fun i hi => sourceNumerics13108 hi)
    BstLean.Part268.agent13108.frame targetFrame13108_eq


end BstLean.Part269.N13108

namespace BstLean.Part269.N13109
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13109 : scalarRow13109.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13109, BstLean.Part268.grid13109, BstLean.Part263.worldGrid]

theorem supplies13109 (j : Fin 43) : Supply 13109 (parameters j)
    (cellLower scalarRow13109.grid (sourceIndex j))
    (cellUpper scalarRow13109.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13109.grid grid_top_bounds13109 j

theorem radii13109 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13109.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13109 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13109 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13109.grid grid_top_bounds13109 j hθ

noncomputable def covarianceInputs13109 :
    BstLean.Part263.CovarianceInputs 13109 scalarRow13109.grid parameters (caps repair13109) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13109 grid_top_bounds13109 repair13109

noncomputable def covarianceEvent13109 : Set (AgFam 13109) :=
  BstLean.Part263.covarianceEvent 13109 scalarRow13109.grid parameters

theorem covarianceEvent13109_measurable : MeasurableSet covarianceEvent13109 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13109_payment :
    (retDist (paperDesignP 13109).toCentres).real
      (agentEv (paperDesignP 13109) covarianceEvent13109)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13109

theorem localCov13109 : BstLean.Part259.LocalCovarianceOn covarianceEvent13109
    (BstLean.Part263.cell scalarRow13109.grid) (caps repair13109) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13109

theorem covarianceGood13109_payment :
    (retDist (paperDesignP 13109).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13109)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13109_payment



end BstLean.Part269.N13109

namespace BstLean.Part269.N13109
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13109}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13109.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13109) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13109).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13109 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13109) (by norm_num) BstLean.Part268.WorldRow13109.worldPackage rfl
    BstLean.Part268.WorldRow13109.product_lower (BstLean.Part268.WorldRow13109.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13109} (hw : c ∈ Hof BstLean.Part268.WorldRow13109.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13109) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13109) (by norm_num) BstLean.Part268.WorldRow13109.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13109} (hw : c ∈ Hof BstLean.Part268.WorldRow13109.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13109) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13109).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13109) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13109_eq : scalarRow13109.targetFrame = BstLean.Part268.agent13109.frame := by
  norm_num [scalarRow13109,BstLean.Part268.agent13109]

noncomputable def frameData13109 : BstLean.Part264b.FrameData 13109 :=
  BstLean.Part269.frameData_from_numerics (n := 13109) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13109.worldPackage rfl BstLean.Part268.WorldRow13109.product_lower (BstLean.Part268.WorldRow13109.producthi.2.trans (by norm_num))
    scalarRow13109 repair13109 covarianceInputs13109 (fun i hi => sourceNumerics13109 hi)
    BstLean.Part268.agent13109.frame targetFrame13109_eq


end BstLean.Part269.N13109
