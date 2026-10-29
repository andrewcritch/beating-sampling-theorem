import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World31Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs31
import BstLean.Part269Rows31
import BstLean.Part269Sources31
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13145
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13145 : scalarRow13145.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13145, BstLean.Part268.grid13145, BstLean.Part263.worldGrid]

theorem supplies13145 (j : Fin 43) : Supply 13145 (parameters j)
    (cellLower scalarRow13145.grid (sourceIndex j))
    (cellUpper scalarRow13145.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13145.grid grid_top_bounds13145 j

theorem radii13145 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13145.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13145 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13145 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13145.grid grid_top_bounds13145 j hθ

noncomputable def covarianceInputs13145 :
    BstLean.Part263.CovarianceInputs 13145 scalarRow13145.grid parameters (caps repair13145) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13145 grid_top_bounds13145 repair13145

noncomputable def covarianceEvent13145 : Set (AgFam 13145) :=
  BstLean.Part263.covarianceEvent 13145 scalarRow13145.grid parameters

theorem covarianceEvent13145_measurable : MeasurableSet covarianceEvent13145 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13145_payment :
    (retDist (paperDesignP 13145).toCentres).real
      (agentEv (paperDesignP 13145) covarianceEvent13145)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13145

theorem localCov13145 : BstLean.Part259.LocalCovarianceOn covarianceEvent13145
    (BstLean.Part263.cell scalarRow13145.grid) (caps repair13145) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13145

theorem covarianceGood13145_payment :
    (retDist (paperDesignP 13145).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13145)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13145_payment



end BstLean.Part269.N13145

namespace BstLean.Part269.N13145
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13145}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13145.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13145) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13145).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13145 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13145) (by norm_num) BstLean.Part268.WorldRow13145.worldPackage rfl
    BstLean.Part268.WorldRow13145.product_lower (BstLean.Part268.WorldRow13145.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13145} (hw : c ∈ Hof BstLean.Part268.WorldRow13145.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13145) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13145) (by norm_num) BstLean.Part268.WorldRow13145.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13145} (hw : c ∈ Hof BstLean.Part268.WorldRow13145.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13145) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13145).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13145) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13145_eq : scalarRow13145.targetFrame = BstLean.Part268.agent13145.frame := by
  norm_num [scalarRow13145,BstLean.Part268.agent13145]

noncomputable def frameData13145 : BstLean.Part264b.FrameData 13145 :=
  BstLean.Part269.frameData_from_numerics (n := 13145) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13145.worldPackage rfl BstLean.Part268.WorldRow13145.product_lower (BstLean.Part268.WorldRow13145.producthi.2.trans (by norm_num))
    scalarRow13145 repair13145 covarianceInputs13145 (fun i hi => sourceNumerics13145 hi)
    BstLean.Part268.agent13145.frame targetFrame13145_eq


end BstLean.Part269.N13145

namespace BstLean.Part269.N13146
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13146 : scalarRow13146.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13146, BstLean.Part268.grid13146, BstLean.Part263.worldGrid]

theorem supplies13146 (j : Fin 43) : Supply 13146 (parameters j)
    (cellLower scalarRow13146.grid (sourceIndex j))
    (cellUpper scalarRow13146.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13146.grid grid_top_bounds13146 j

theorem radii13146 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13146.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13146 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13146 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13146.grid grid_top_bounds13146 j hθ

noncomputable def covarianceInputs13146 :
    BstLean.Part263.CovarianceInputs 13146 scalarRow13146.grid parameters (caps repair13146) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13146 grid_top_bounds13146 repair13146

noncomputable def covarianceEvent13146 : Set (AgFam 13146) :=
  BstLean.Part263.covarianceEvent 13146 scalarRow13146.grid parameters

theorem covarianceEvent13146_measurable : MeasurableSet covarianceEvent13146 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13146_payment :
    (retDist (paperDesignP 13146).toCentres).real
      (agentEv (paperDesignP 13146) covarianceEvent13146)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13146

theorem localCov13146 : BstLean.Part259.LocalCovarianceOn covarianceEvent13146
    (BstLean.Part263.cell scalarRow13146.grid) (caps repair13146) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13146

theorem covarianceGood13146_payment :
    (retDist (paperDesignP 13146).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13146)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13146_payment



end BstLean.Part269.N13146

namespace BstLean.Part269.N13146
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13146}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13146.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13146) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13146).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13146 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13146) (by norm_num) BstLean.Part268.WorldRow13146.worldPackage rfl
    BstLean.Part268.WorldRow13146.product_lower (BstLean.Part268.WorldRow13146.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13146} (hw : c ∈ Hof BstLean.Part268.WorldRow13146.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13146) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13146) (by norm_num) BstLean.Part268.WorldRow13146.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13146} (hw : c ∈ Hof BstLean.Part268.WorldRow13146.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13146) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13146).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13146) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13146_eq : scalarRow13146.targetFrame = BstLean.Part268.agent13146.frame := by
  norm_num [scalarRow13146,BstLean.Part268.agent13146]

noncomputable def frameData13146 : BstLean.Part264b.FrameData 13146 :=
  BstLean.Part269.frameData_from_numerics (n := 13146) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13146.worldPackage rfl BstLean.Part268.WorldRow13146.product_lower (BstLean.Part268.WorldRow13146.producthi.2.trans (by norm_num))
    scalarRow13146 repair13146 covarianceInputs13146 (fun i hi => sourceNumerics13146 hi)
    BstLean.Part268.agent13146.frame targetFrame13146_eq


end BstLean.Part269.N13146

namespace BstLean.Part269.N13147
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13147 : scalarRow13147.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13147, BstLean.Part268.grid13147, BstLean.Part263.worldGrid]

theorem supplies13147 (j : Fin 43) : Supply 13147 (parameters j)
    (cellLower scalarRow13147.grid (sourceIndex j))
    (cellUpper scalarRow13147.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13147.grid grid_top_bounds13147 j

theorem radii13147 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13147.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13147 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13147 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13147.grid grid_top_bounds13147 j hθ

noncomputable def covarianceInputs13147 :
    BstLean.Part263.CovarianceInputs 13147 scalarRow13147.grid parameters (caps repair13147) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13147 grid_top_bounds13147 repair13147

noncomputable def covarianceEvent13147 : Set (AgFam 13147) :=
  BstLean.Part263.covarianceEvent 13147 scalarRow13147.grid parameters

theorem covarianceEvent13147_measurable : MeasurableSet covarianceEvent13147 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13147_payment :
    (retDist (paperDesignP 13147).toCentres).real
      (agentEv (paperDesignP 13147) covarianceEvent13147)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13147

theorem localCov13147 : BstLean.Part259.LocalCovarianceOn covarianceEvent13147
    (BstLean.Part263.cell scalarRow13147.grid) (caps repair13147) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13147

theorem covarianceGood13147_payment :
    (retDist (paperDesignP 13147).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13147)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13147_payment



end BstLean.Part269.N13147

namespace BstLean.Part269.N13147
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13147}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13147.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13147) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13147).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13147 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13147) (by norm_num) BstLean.Part268.WorldRow13147.worldPackage rfl
    BstLean.Part268.WorldRow13147.product_lower (BstLean.Part268.WorldRow13147.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13147} (hw : c ∈ Hof BstLean.Part268.WorldRow13147.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13147) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13147) (by norm_num) BstLean.Part268.WorldRow13147.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13147} (hw : c ∈ Hof BstLean.Part268.WorldRow13147.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13147) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13147).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13147) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13147_eq : scalarRow13147.targetFrame = BstLean.Part268.agent13147.frame := by
  norm_num [scalarRow13147,BstLean.Part268.agent13147]

noncomputable def frameData13147 : BstLean.Part264b.FrameData 13147 :=
  BstLean.Part269.frameData_from_numerics (n := 13147) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13147.worldPackage rfl BstLean.Part268.WorldRow13147.product_lower (BstLean.Part268.WorldRow13147.producthi.2.trans (by norm_num))
    scalarRow13147 repair13147 covarianceInputs13147 (fun i hi => sourceNumerics13147 hi)
    BstLean.Part268.agent13147.frame targetFrame13147_eq


end BstLean.Part269.N13147

namespace BstLean.Part269.N13148
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13148 : scalarRow13148.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13148, BstLean.Part268.grid13148, BstLean.Part263.worldGrid]

theorem supplies13148 (j : Fin 43) : Supply 13148 (parameters j)
    (cellLower scalarRow13148.grid (sourceIndex j))
    (cellUpper scalarRow13148.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13148.grid grid_top_bounds13148 j

theorem radii13148 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13148.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13148 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13148 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13148.grid grid_top_bounds13148 j hθ

noncomputable def covarianceInputs13148 :
    BstLean.Part263.CovarianceInputs 13148 scalarRow13148.grid parameters (caps repair13148) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13148 grid_top_bounds13148 repair13148

noncomputable def covarianceEvent13148 : Set (AgFam 13148) :=
  BstLean.Part263.covarianceEvent 13148 scalarRow13148.grid parameters

theorem covarianceEvent13148_measurable : MeasurableSet covarianceEvent13148 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13148_payment :
    (retDist (paperDesignP 13148).toCentres).real
      (agentEv (paperDesignP 13148) covarianceEvent13148)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13148

theorem localCov13148 : BstLean.Part259.LocalCovarianceOn covarianceEvent13148
    (BstLean.Part263.cell scalarRow13148.grid) (caps repair13148) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13148

theorem covarianceGood13148_payment :
    (retDist (paperDesignP 13148).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13148)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13148_payment



end BstLean.Part269.N13148

namespace BstLean.Part269.N13148
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13148}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13148.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13148) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13148).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13148 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13148) (by norm_num) BstLean.Part268.WorldRow13148.worldPackage rfl
    BstLean.Part268.WorldRow13148.product_lower (BstLean.Part268.WorldRow13148.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13148} (hw : c ∈ Hof BstLean.Part268.WorldRow13148.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13148) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13148) (by norm_num) BstLean.Part268.WorldRow13148.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13148} (hw : c ∈ Hof BstLean.Part268.WorldRow13148.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13148) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13148).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13148) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13148_eq : scalarRow13148.targetFrame = BstLean.Part268.agent13148.frame := by
  norm_num [scalarRow13148,BstLean.Part268.agent13148]

noncomputable def frameData13148 : BstLean.Part264b.FrameData 13148 :=
  BstLean.Part269.frameData_from_numerics (n := 13148) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13148.worldPackage rfl BstLean.Part268.WorldRow13148.product_lower (BstLean.Part268.WorldRow13148.producthi.2.trans (by norm_num))
    scalarRow13148 repair13148 covarianceInputs13148 (fun i hi => sourceNumerics13148 hi)
    BstLean.Part268.agent13148.frame targetFrame13148_eq


end BstLean.Part269.N13148

namespace BstLean.Part269.N13149
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13149 : scalarRow13149.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13149, BstLean.Part268.grid13149, BstLean.Part263.worldGrid]

theorem supplies13149 (j : Fin 43) : Supply 13149 (parameters j)
    (cellLower scalarRow13149.grid (sourceIndex j))
    (cellUpper scalarRow13149.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13149.grid grid_top_bounds13149 j

theorem radii13149 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13149.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13149 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13149 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13149.grid grid_top_bounds13149 j hθ

noncomputable def covarianceInputs13149 :
    BstLean.Part263.CovarianceInputs 13149 scalarRow13149.grid parameters (caps repair13149) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13149 grid_top_bounds13149 repair13149

noncomputable def covarianceEvent13149 : Set (AgFam 13149) :=
  BstLean.Part263.covarianceEvent 13149 scalarRow13149.grid parameters

theorem covarianceEvent13149_measurable : MeasurableSet covarianceEvent13149 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13149_payment :
    (retDist (paperDesignP 13149).toCentres).real
      (agentEv (paperDesignP 13149) covarianceEvent13149)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13149

theorem localCov13149 : BstLean.Part259.LocalCovarianceOn covarianceEvent13149
    (BstLean.Part263.cell scalarRow13149.grid) (caps repair13149) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13149

theorem covarianceGood13149_payment :
    (retDist (paperDesignP 13149).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13149)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13149_payment



end BstLean.Part269.N13149

namespace BstLean.Part269.N13149
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13149}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13149.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13149) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13149).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13149 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13149) (by norm_num) BstLean.Part268.WorldRow13149.worldPackage rfl
    BstLean.Part268.WorldRow13149.product_lower (BstLean.Part268.WorldRow13149.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13149} (hw : c ∈ Hof BstLean.Part268.WorldRow13149.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13149) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13149) (by norm_num) BstLean.Part268.WorldRow13149.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13149} (hw : c ∈ Hof BstLean.Part268.WorldRow13149.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13149) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13149).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13149) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13149_eq : scalarRow13149.targetFrame = BstLean.Part268.agent13149.frame := by
  norm_num [scalarRow13149,BstLean.Part268.agent13149]

noncomputable def frameData13149 : BstLean.Part264b.FrameData 13149 :=
  BstLean.Part269.frameData_from_numerics (n := 13149) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13149.worldPackage rfl BstLean.Part268.WorldRow13149.product_lower (BstLean.Part268.WorldRow13149.producthi.2.trans (by norm_num))
    scalarRow13149 repair13149 covarianceInputs13149 (fun i hi => sourceNumerics13149 hi)
    BstLean.Part268.agent13149.frame targetFrame13149_eq


end BstLean.Part269.N13149
