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

namespace BstLean.Part269.N13140
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13140 : scalarRow13140.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13140, BstLean.Part268.grid13140, BstLean.Part263.worldGrid]

theorem supplies13140 (j : Fin 43) : Supply 13140 (parameters j)
    (cellLower scalarRow13140.grid (sourceIndex j))
    (cellUpper scalarRow13140.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13140.grid grid_top_bounds13140 j

theorem radii13140 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13140.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13140 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13140 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13140.grid grid_top_bounds13140 j hθ

noncomputable def covarianceInputs13140 :
    BstLean.Part263.CovarianceInputs 13140 scalarRow13140.grid parameters (caps repair13140) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13140 grid_top_bounds13140 repair13140

noncomputable def covarianceEvent13140 : Set (AgFam 13140) :=
  BstLean.Part263.covarianceEvent 13140 scalarRow13140.grid parameters

theorem covarianceEvent13140_measurable : MeasurableSet covarianceEvent13140 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13140_payment :
    (retDist (paperDesignP 13140).toCentres).real
      (agentEv (paperDesignP 13140) covarianceEvent13140)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13140

theorem localCov13140 : BstLean.Part259.LocalCovarianceOn covarianceEvent13140
    (BstLean.Part263.cell scalarRow13140.grid) (caps repair13140) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13140

theorem covarianceGood13140_payment :
    (retDist (paperDesignP 13140).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13140)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13140_payment



end BstLean.Part269.N13140

namespace BstLean.Part269.N13140
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13140}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13140.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13140) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13140).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13140 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13140) (by norm_num) BstLean.Part268.WorldRow13140.worldPackage rfl
    BstLean.Part268.WorldRow13140.product_lower (BstLean.Part268.WorldRow13140.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13140} (hw : c ∈ Hof BstLean.Part268.WorldRow13140.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13140) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13140) (by norm_num) BstLean.Part268.WorldRow13140.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13140} (hw : c ∈ Hof BstLean.Part268.WorldRow13140.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13140) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13140).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13140) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13140_eq : scalarRow13140.targetFrame = BstLean.Part268.agent13140.frame := by
  norm_num [scalarRow13140,BstLean.Part268.agent13140]

noncomputable def frameData13140 : BstLean.Part264b.FrameData 13140 :=
  BstLean.Part269.frameData_from_numerics (n := 13140) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13140.worldPackage rfl BstLean.Part268.WorldRow13140.product_lower (BstLean.Part268.WorldRow13140.producthi.2.trans (by norm_num))
    scalarRow13140 repair13140 covarianceInputs13140 (fun i hi => sourceNumerics13140 hi)
    BstLean.Part268.agent13140.frame targetFrame13140_eq


end BstLean.Part269.N13140

namespace BstLean.Part269.N13141
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13141 : scalarRow13141.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13141, BstLean.Part268.grid13141, BstLean.Part263.worldGrid]

theorem supplies13141 (j : Fin 43) : Supply 13141 (parameters j)
    (cellLower scalarRow13141.grid (sourceIndex j))
    (cellUpper scalarRow13141.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13141.grid grid_top_bounds13141 j

theorem radii13141 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13141.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13141 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13141 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13141.grid grid_top_bounds13141 j hθ

noncomputable def covarianceInputs13141 :
    BstLean.Part263.CovarianceInputs 13141 scalarRow13141.grid parameters (caps repair13141) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13141 grid_top_bounds13141 repair13141

noncomputable def covarianceEvent13141 : Set (AgFam 13141) :=
  BstLean.Part263.covarianceEvent 13141 scalarRow13141.grid parameters

theorem covarianceEvent13141_measurable : MeasurableSet covarianceEvent13141 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13141_payment :
    (retDist (paperDesignP 13141).toCentres).real
      (agentEv (paperDesignP 13141) covarianceEvent13141)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13141

theorem localCov13141 : BstLean.Part259.LocalCovarianceOn covarianceEvent13141
    (BstLean.Part263.cell scalarRow13141.grid) (caps repair13141) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13141

theorem covarianceGood13141_payment :
    (retDist (paperDesignP 13141).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13141)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13141_payment



end BstLean.Part269.N13141

namespace BstLean.Part269.N13141
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13141}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13141.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13141) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13141).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13141 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13141) (by norm_num) BstLean.Part268.WorldRow13141.worldPackage rfl
    BstLean.Part268.WorldRow13141.product_lower (BstLean.Part268.WorldRow13141.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13141} (hw : c ∈ Hof BstLean.Part268.WorldRow13141.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13141) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13141) (by norm_num) BstLean.Part268.WorldRow13141.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13141} (hw : c ∈ Hof BstLean.Part268.WorldRow13141.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13141) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13141).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13141) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13141_eq : scalarRow13141.targetFrame = BstLean.Part268.agent13141.frame := by
  norm_num [scalarRow13141,BstLean.Part268.agent13141]

noncomputable def frameData13141 : BstLean.Part264b.FrameData 13141 :=
  BstLean.Part269.frameData_from_numerics (n := 13141) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13141.worldPackage rfl BstLean.Part268.WorldRow13141.product_lower (BstLean.Part268.WorldRow13141.producthi.2.trans (by norm_num))
    scalarRow13141 repair13141 covarianceInputs13141 (fun i hi => sourceNumerics13141 hi)
    BstLean.Part268.agent13141.frame targetFrame13141_eq


end BstLean.Part269.N13141

namespace BstLean.Part269.N13142
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13142 : scalarRow13142.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13142, BstLean.Part268.grid13142, BstLean.Part263.worldGrid]

theorem supplies13142 (j : Fin 43) : Supply 13142 (parameters j)
    (cellLower scalarRow13142.grid (sourceIndex j))
    (cellUpper scalarRow13142.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13142.grid grid_top_bounds13142 j

theorem radii13142 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13142.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13142 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13142 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13142.grid grid_top_bounds13142 j hθ

noncomputable def covarianceInputs13142 :
    BstLean.Part263.CovarianceInputs 13142 scalarRow13142.grid parameters (caps repair13142) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13142 grid_top_bounds13142 repair13142

noncomputable def covarianceEvent13142 : Set (AgFam 13142) :=
  BstLean.Part263.covarianceEvent 13142 scalarRow13142.grid parameters

theorem covarianceEvent13142_measurable : MeasurableSet covarianceEvent13142 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13142_payment :
    (retDist (paperDesignP 13142).toCentres).real
      (agentEv (paperDesignP 13142) covarianceEvent13142)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13142

theorem localCov13142 : BstLean.Part259.LocalCovarianceOn covarianceEvent13142
    (BstLean.Part263.cell scalarRow13142.grid) (caps repair13142) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13142

theorem covarianceGood13142_payment :
    (retDist (paperDesignP 13142).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13142)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13142_payment



end BstLean.Part269.N13142

namespace BstLean.Part269.N13142
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13142}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13142.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13142) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13142).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13142 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13142) (by norm_num) BstLean.Part268.WorldRow13142.worldPackage rfl
    BstLean.Part268.WorldRow13142.product_lower (BstLean.Part268.WorldRow13142.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13142} (hw : c ∈ Hof BstLean.Part268.WorldRow13142.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13142) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13142) (by norm_num) BstLean.Part268.WorldRow13142.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13142} (hw : c ∈ Hof BstLean.Part268.WorldRow13142.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13142) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13142).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13142) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13142_eq : scalarRow13142.targetFrame = BstLean.Part268.agent13142.frame := by
  norm_num [scalarRow13142,BstLean.Part268.agent13142]

noncomputable def frameData13142 : BstLean.Part264b.FrameData 13142 :=
  BstLean.Part269.frameData_from_numerics (n := 13142) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13142.worldPackage rfl BstLean.Part268.WorldRow13142.product_lower (BstLean.Part268.WorldRow13142.producthi.2.trans (by norm_num))
    scalarRow13142 repair13142 covarianceInputs13142 (fun i hi => sourceNumerics13142 hi)
    BstLean.Part268.agent13142.frame targetFrame13142_eq


end BstLean.Part269.N13142

namespace BstLean.Part269.N13143
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13143 : scalarRow13143.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13143, BstLean.Part268.grid13143, BstLean.Part263.worldGrid]

theorem supplies13143 (j : Fin 43) : Supply 13143 (parameters j)
    (cellLower scalarRow13143.grid (sourceIndex j))
    (cellUpper scalarRow13143.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13143.grid grid_top_bounds13143 j

theorem radii13143 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13143.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13143 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13143 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13143.grid grid_top_bounds13143 j hθ

noncomputable def covarianceInputs13143 :
    BstLean.Part263.CovarianceInputs 13143 scalarRow13143.grid parameters (caps repair13143) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13143 grid_top_bounds13143 repair13143

noncomputable def covarianceEvent13143 : Set (AgFam 13143) :=
  BstLean.Part263.covarianceEvent 13143 scalarRow13143.grid parameters

theorem covarianceEvent13143_measurable : MeasurableSet covarianceEvent13143 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13143_payment :
    (retDist (paperDesignP 13143).toCentres).real
      (agentEv (paperDesignP 13143) covarianceEvent13143)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13143

theorem localCov13143 : BstLean.Part259.LocalCovarianceOn covarianceEvent13143
    (BstLean.Part263.cell scalarRow13143.grid) (caps repair13143) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13143

theorem covarianceGood13143_payment :
    (retDist (paperDesignP 13143).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13143)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13143_payment



end BstLean.Part269.N13143

namespace BstLean.Part269.N13143
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13143}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13143.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13143) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13143).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13143 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13143) (by norm_num) BstLean.Part268.WorldRow13143.worldPackage rfl
    BstLean.Part268.WorldRow13143.product_lower (BstLean.Part268.WorldRow13143.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13143} (hw : c ∈ Hof BstLean.Part268.WorldRow13143.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13143) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13143) (by norm_num) BstLean.Part268.WorldRow13143.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13143} (hw : c ∈ Hof BstLean.Part268.WorldRow13143.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13143) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13143).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13143) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13143_eq : scalarRow13143.targetFrame = BstLean.Part268.agent13143.frame := by
  norm_num [scalarRow13143,BstLean.Part268.agent13143]

noncomputable def frameData13143 : BstLean.Part264b.FrameData 13143 :=
  BstLean.Part269.frameData_from_numerics (n := 13143) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13143.worldPackage rfl BstLean.Part268.WorldRow13143.product_lower (BstLean.Part268.WorldRow13143.producthi.2.trans (by norm_num))
    scalarRow13143 repair13143 covarianceInputs13143 (fun i hi => sourceNumerics13143 hi)
    BstLean.Part268.agent13143.frame targetFrame13143_eq


end BstLean.Part269.N13143

namespace BstLean.Part269.N13144
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13144 : scalarRow13144.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13144, BstLean.Part268.grid13144, BstLean.Part263.worldGrid]

theorem supplies13144 (j : Fin 43) : Supply 13144 (parameters j)
    (cellLower scalarRow13144.grid (sourceIndex j))
    (cellUpper scalarRow13144.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13144.grid grid_top_bounds13144 j

theorem radii13144 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13144.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13144 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13144 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13144.grid grid_top_bounds13144 j hθ

noncomputable def covarianceInputs13144 :
    BstLean.Part263.CovarianceInputs 13144 scalarRow13144.grid parameters (caps repair13144) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13144 grid_top_bounds13144 repair13144

noncomputable def covarianceEvent13144 : Set (AgFam 13144) :=
  BstLean.Part263.covarianceEvent 13144 scalarRow13144.grid parameters

theorem covarianceEvent13144_measurable : MeasurableSet covarianceEvent13144 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13144_payment :
    (retDist (paperDesignP 13144).toCentres).real
      (agentEv (paperDesignP 13144) covarianceEvent13144)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13144

theorem localCov13144 : BstLean.Part259.LocalCovarianceOn covarianceEvent13144
    (BstLean.Part263.cell scalarRow13144.grid) (caps repair13144) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13144

theorem covarianceGood13144_payment :
    (retDist (paperDesignP 13144).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13144)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13144_payment



end BstLean.Part269.N13144

namespace BstLean.Part269.N13144
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13144}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13144.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13144) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13144).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13144 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13144) (by norm_num) BstLean.Part268.WorldRow13144.worldPackage rfl
    BstLean.Part268.WorldRow13144.product_lower (BstLean.Part268.WorldRow13144.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13144} (hw : c ∈ Hof BstLean.Part268.WorldRow13144.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13144) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13144) (by norm_num) BstLean.Part268.WorldRow13144.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13144} (hw : c ∈ Hof BstLean.Part268.WorldRow13144.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13144) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13144).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13144) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13144_eq : scalarRow13144.targetFrame = BstLean.Part268.agent13144.frame := by
  norm_num [scalarRow13144,BstLean.Part268.agent13144]

noncomputable def frameData13144 : BstLean.Part264b.FrameData 13144 :=
  BstLean.Part269.frameData_from_numerics (n := 13144) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13144.worldPackage rfl BstLean.Part268.WorldRow13144.product_lower (BstLean.Part268.WorldRow13144.producthi.2.trans (by norm_num))
    scalarRow13144 repair13144 covarianceInputs13144 (fun i hi => sourceNumerics13144 hi)
    BstLean.Part268.agent13144.frame targetFrame13144_eq


end BstLean.Part269.N13144
