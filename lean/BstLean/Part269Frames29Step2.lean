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

namespace BstLean.Part269.N13085
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13085 : scalarRow13085.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13085, BstLean.Part268.grid13085, BstLean.Part263.worldGrid]

theorem supplies13085 (j : Fin 43) : Supply 13085 (parameters j)
    (cellLower scalarRow13085.grid (sourceIndex j))
    (cellUpper scalarRow13085.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13085.grid grid_top_bounds13085 j

theorem radii13085 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13085.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13085 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13085 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13085.grid grid_top_bounds13085 j hθ

noncomputable def covarianceInputs13085 :
    BstLean.Part263.CovarianceInputs 13085 scalarRow13085.grid parameters (caps repair13085) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13085 grid_top_bounds13085 repair13085

noncomputable def covarianceEvent13085 : Set (AgFam 13085) :=
  BstLean.Part263.covarianceEvent 13085 scalarRow13085.grid parameters

theorem covarianceEvent13085_measurable : MeasurableSet covarianceEvent13085 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13085_payment :
    (retDist (paperDesignP 13085).toCentres).real
      (agentEv (paperDesignP 13085) covarianceEvent13085)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13085

theorem localCov13085 : BstLean.Part259.LocalCovarianceOn covarianceEvent13085
    (BstLean.Part263.cell scalarRow13085.grid) (caps repair13085) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13085

theorem covarianceGood13085_payment :
    (retDist (paperDesignP 13085).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13085)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13085_payment



end BstLean.Part269.N13085

namespace BstLean.Part269.N13085
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13085}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13085.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13085) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13085).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13085 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13085) (by norm_num) BstLean.Part268.WorldRow13085.worldPackage rfl
    BstLean.Part268.WorldRow13085.product_lower (BstLean.Part268.WorldRow13085.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13085} (hw : c ∈ Hof BstLean.Part268.WorldRow13085.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13085) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13085) (by norm_num) BstLean.Part268.WorldRow13085.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13085} (hw : c ∈ Hof BstLean.Part268.WorldRow13085.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13085) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13085).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13085) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13085_eq : scalarRow13085.targetFrame = BstLean.Part268.agent13085.frame := by
  norm_num [scalarRow13085,BstLean.Part268.agent13085]

noncomputable def frameData13085 : BstLean.Part264b.FrameData 13085 :=
  BstLean.Part269.frameData_from_numerics (n := 13085) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13085.worldPackage rfl BstLean.Part268.WorldRow13085.product_lower (BstLean.Part268.WorldRow13085.producthi.2.trans (by norm_num))
    scalarRow13085 repair13085 covarianceInputs13085 (fun i hi => sourceNumerics13085 hi)
    BstLean.Part268.agent13085.frame targetFrame13085_eq


end BstLean.Part269.N13085

namespace BstLean.Part269.N13086
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13086 : scalarRow13086.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13086, BstLean.Part268.grid13086, BstLean.Part263.worldGrid]

theorem supplies13086 (j : Fin 43) : Supply 13086 (parameters j)
    (cellLower scalarRow13086.grid (sourceIndex j))
    (cellUpper scalarRow13086.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13086.grid grid_top_bounds13086 j

theorem radii13086 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13086.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13086 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13086 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13086.grid grid_top_bounds13086 j hθ

noncomputable def covarianceInputs13086 :
    BstLean.Part263.CovarianceInputs 13086 scalarRow13086.grid parameters (caps repair13086) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13086 grid_top_bounds13086 repair13086

noncomputable def covarianceEvent13086 : Set (AgFam 13086) :=
  BstLean.Part263.covarianceEvent 13086 scalarRow13086.grid parameters

theorem covarianceEvent13086_measurable : MeasurableSet covarianceEvent13086 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13086_payment :
    (retDist (paperDesignP 13086).toCentres).real
      (agentEv (paperDesignP 13086) covarianceEvent13086)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13086

theorem localCov13086 : BstLean.Part259.LocalCovarianceOn covarianceEvent13086
    (BstLean.Part263.cell scalarRow13086.grid) (caps repair13086) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13086

theorem covarianceGood13086_payment :
    (retDist (paperDesignP 13086).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13086)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13086_payment



end BstLean.Part269.N13086

namespace BstLean.Part269.N13086
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13086}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13086.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13086) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13086).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13086 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13086) (by norm_num) BstLean.Part268.WorldRow13086.worldPackage rfl
    BstLean.Part268.WorldRow13086.product_lower (BstLean.Part268.WorldRow13086.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13086} (hw : c ∈ Hof BstLean.Part268.WorldRow13086.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13086) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13086) (by norm_num) BstLean.Part268.WorldRow13086.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13086} (hw : c ∈ Hof BstLean.Part268.WorldRow13086.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13086) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13086).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13086) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13086_eq : scalarRow13086.targetFrame = BstLean.Part268.agent13086.frame := by
  norm_num [scalarRow13086,BstLean.Part268.agent13086]

noncomputable def frameData13086 : BstLean.Part264b.FrameData 13086 :=
  BstLean.Part269.frameData_from_numerics (n := 13086) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13086.worldPackage rfl BstLean.Part268.WorldRow13086.product_lower (BstLean.Part268.WorldRow13086.producthi.2.trans (by norm_num))
    scalarRow13086 repair13086 covarianceInputs13086 (fun i hi => sourceNumerics13086 hi)
    BstLean.Part268.agent13086.frame targetFrame13086_eq


end BstLean.Part269.N13086

namespace BstLean.Part269.N13087
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13087 : scalarRow13087.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13087, BstLean.Part268.grid13087, BstLean.Part263.worldGrid]

theorem supplies13087 (j : Fin 43) : Supply 13087 (parameters j)
    (cellLower scalarRow13087.grid (sourceIndex j))
    (cellUpper scalarRow13087.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13087.grid grid_top_bounds13087 j

theorem radii13087 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13087.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13087 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13087 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13087.grid grid_top_bounds13087 j hθ

noncomputable def covarianceInputs13087 :
    BstLean.Part263.CovarianceInputs 13087 scalarRow13087.grid parameters (caps repair13087) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13087 grid_top_bounds13087 repair13087

noncomputable def covarianceEvent13087 : Set (AgFam 13087) :=
  BstLean.Part263.covarianceEvent 13087 scalarRow13087.grid parameters

theorem covarianceEvent13087_measurable : MeasurableSet covarianceEvent13087 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13087_payment :
    (retDist (paperDesignP 13087).toCentres).real
      (agentEv (paperDesignP 13087) covarianceEvent13087)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13087

theorem localCov13087 : BstLean.Part259.LocalCovarianceOn covarianceEvent13087
    (BstLean.Part263.cell scalarRow13087.grid) (caps repair13087) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13087

theorem covarianceGood13087_payment :
    (retDist (paperDesignP 13087).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13087)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13087_payment



end BstLean.Part269.N13087

namespace BstLean.Part269.N13087
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13087}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13087.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13087) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13087).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13087 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13087) (by norm_num) BstLean.Part268.WorldRow13087.worldPackage rfl
    BstLean.Part268.WorldRow13087.product_lower (BstLean.Part268.WorldRow13087.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13087} (hw : c ∈ Hof BstLean.Part268.WorldRow13087.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13087) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13087) (by norm_num) BstLean.Part268.WorldRow13087.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13087} (hw : c ∈ Hof BstLean.Part268.WorldRow13087.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13087) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13087).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13087) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13087_eq : scalarRow13087.targetFrame = BstLean.Part268.agent13087.frame := by
  norm_num [scalarRow13087,BstLean.Part268.agent13087]

noncomputable def frameData13087 : BstLean.Part264b.FrameData 13087 :=
  BstLean.Part269.frameData_from_numerics (n := 13087) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13087.worldPackage rfl BstLean.Part268.WorldRow13087.product_lower (BstLean.Part268.WorldRow13087.producthi.2.trans (by norm_num))
    scalarRow13087 repair13087 covarianceInputs13087 (fun i hi => sourceNumerics13087 hi)
    BstLean.Part268.agent13087.frame targetFrame13087_eq


end BstLean.Part269.N13087

namespace BstLean.Part269.N13088
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13088 : scalarRow13088.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13088, BstLean.Part268.grid13088, BstLean.Part263.worldGrid]

theorem supplies13088 (j : Fin 43) : Supply 13088 (parameters j)
    (cellLower scalarRow13088.grid (sourceIndex j))
    (cellUpper scalarRow13088.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13088.grid grid_top_bounds13088 j

theorem radii13088 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13088.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13088 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13088 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13088.grid grid_top_bounds13088 j hθ

noncomputable def covarianceInputs13088 :
    BstLean.Part263.CovarianceInputs 13088 scalarRow13088.grid parameters (caps repair13088) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13088 grid_top_bounds13088 repair13088

noncomputable def covarianceEvent13088 : Set (AgFam 13088) :=
  BstLean.Part263.covarianceEvent 13088 scalarRow13088.grid parameters

theorem covarianceEvent13088_measurable : MeasurableSet covarianceEvent13088 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13088_payment :
    (retDist (paperDesignP 13088).toCentres).real
      (agentEv (paperDesignP 13088) covarianceEvent13088)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13088

theorem localCov13088 : BstLean.Part259.LocalCovarianceOn covarianceEvent13088
    (BstLean.Part263.cell scalarRow13088.grid) (caps repair13088) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13088

theorem covarianceGood13088_payment :
    (retDist (paperDesignP 13088).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13088)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13088_payment



end BstLean.Part269.N13088

namespace BstLean.Part269.N13088
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13088}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13088.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13088) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13088).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13088 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13088) (by norm_num) BstLean.Part268.WorldRow13088.worldPackage rfl
    BstLean.Part268.WorldRow13088.product_lower (BstLean.Part268.WorldRow13088.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13088} (hw : c ∈ Hof BstLean.Part268.WorldRow13088.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13088) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13088) (by norm_num) BstLean.Part268.WorldRow13088.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13088} (hw : c ∈ Hof BstLean.Part268.WorldRow13088.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13088) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13088).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13088) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13088_eq : scalarRow13088.targetFrame = BstLean.Part268.agent13088.frame := by
  norm_num [scalarRow13088,BstLean.Part268.agent13088]

noncomputable def frameData13088 : BstLean.Part264b.FrameData 13088 :=
  BstLean.Part269.frameData_from_numerics (n := 13088) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13088.worldPackage rfl BstLean.Part268.WorldRow13088.product_lower (BstLean.Part268.WorldRow13088.producthi.2.trans (by norm_num))
    scalarRow13088 repair13088 covarianceInputs13088 (fun i hi => sourceNumerics13088 hi)
    BstLean.Part268.agent13088.frame targetFrame13088_eq


end BstLean.Part269.N13088

namespace BstLean.Part269.N13089
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13089 : scalarRow13089.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13089, BstLean.Part268.grid13089, BstLean.Part263.worldGrid]

theorem supplies13089 (j : Fin 43) : Supply 13089 (parameters j)
    (cellLower scalarRow13089.grid (sourceIndex j))
    (cellUpper scalarRow13089.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13089.grid grid_top_bounds13089 j

theorem radii13089 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13089.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13089 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13089 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13089.grid grid_top_bounds13089 j hθ

noncomputable def covarianceInputs13089 :
    BstLean.Part263.CovarianceInputs 13089 scalarRow13089.grid parameters (caps repair13089) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13089 grid_top_bounds13089 repair13089

noncomputable def covarianceEvent13089 : Set (AgFam 13089) :=
  BstLean.Part263.covarianceEvent 13089 scalarRow13089.grid parameters

theorem covarianceEvent13089_measurable : MeasurableSet covarianceEvent13089 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13089_payment :
    (retDist (paperDesignP 13089).toCentres).real
      (agentEv (paperDesignP 13089) covarianceEvent13089)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13089

theorem localCov13089 : BstLean.Part259.LocalCovarianceOn covarianceEvent13089
    (BstLean.Part263.cell scalarRow13089.grid) (caps repair13089) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13089

theorem covarianceGood13089_payment :
    (retDist (paperDesignP 13089).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13089)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13089_payment



end BstLean.Part269.N13089

namespace BstLean.Part269.N13089
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13089}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13089.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13089) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13089).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13089 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13089) (by norm_num) BstLean.Part268.WorldRow13089.worldPackage rfl
    BstLean.Part268.WorldRow13089.product_lower (BstLean.Part268.WorldRow13089.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13089} (hw : c ∈ Hof BstLean.Part268.WorldRow13089.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13089) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13089) (by norm_num) BstLean.Part268.WorldRow13089.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13089} (hw : c ∈ Hof BstLean.Part268.WorldRow13089.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13089) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13089).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13089) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13089_eq : scalarRow13089.targetFrame = BstLean.Part268.agent13089.frame := by
  norm_num [scalarRow13089,BstLean.Part268.agent13089]

noncomputable def frameData13089 : BstLean.Part264b.FrameData 13089 :=
  BstLean.Part269.frameData_from_numerics (n := 13089) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13089.worldPackage rfl BstLean.Part268.WorldRow13089.product_lower (BstLean.Part268.WorldRow13089.producthi.2.trans (by norm_num))
    scalarRow13089 repair13089 covarianceInputs13089 (fun i hi => sourceNumerics13089 hi)
    BstLean.Part268.agent13089.frame targetFrame13089_eq


end BstLean.Part269.N13089
