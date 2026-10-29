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

namespace BstLean.Part269.N13135
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13135 : scalarRow13135.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13135, BstLean.Part268.grid13135, BstLean.Part263.worldGrid]

theorem supplies13135 (j : Fin 43) : Supply 13135 (parameters j)
    (cellLower scalarRow13135.grid (sourceIndex j))
    (cellUpper scalarRow13135.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13135.grid grid_top_bounds13135 j

theorem radii13135 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13135.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13135 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13135 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13135.grid grid_top_bounds13135 j hθ

noncomputable def covarianceInputs13135 :
    BstLean.Part263.CovarianceInputs 13135 scalarRow13135.grid parameters (caps repair13135) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13135 grid_top_bounds13135 repair13135

noncomputable def covarianceEvent13135 : Set (AgFam 13135) :=
  BstLean.Part263.covarianceEvent 13135 scalarRow13135.grid parameters

theorem covarianceEvent13135_measurable : MeasurableSet covarianceEvent13135 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13135_payment :
    (retDist (paperDesignP 13135).toCentres).real
      (agentEv (paperDesignP 13135) covarianceEvent13135)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13135

theorem localCov13135 : BstLean.Part259.LocalCovarianceOn covarianceEvent13135
    (BstLean.Part263.cell scalarRow13135.grid) (caps repair13135) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13135

theorem covarianceGood13135_payment :
    (retDist (paperDesignP 13135).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13135)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13135_payment



end BstLean.Part269.N13135

namespace BstLean.Part269.N13135
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13135}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13135.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13135) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13135).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13135 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13135) (by norm_num) BstLean.Part268.WorldRow13135.worldPackage rfl
    BstLean.Part268.WorldRow13135.product_lower (BstLean.Part268.WorldRow13135.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13135} (hw : c ∈ Hof BstLean.Part268.WorldRow13135.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13135) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13135) (by norm_num) BstLean.Part268.WorldRow13135.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13135} (hw : c ∈ Hof BstLean.Part268.WorldRow13135.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13135) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13135).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13135) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13135_eq : scalarRow13135.targetFrame = BstLean.Part268.agent13135.frame := by
  norm_num [scalarRow13135,BstLean.Part268.agent13135]

noncomputable def frameData13135 : BstLean.Part264b.FrameData 13135 :=
  BstLean.Part269.frameData_from_numerics (n := 13135) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13135.worldPackage rfl BstLean.Part268.WorldRow13135.product_lower (BstLean.Part268.WorldRow13135.producthi.2.trans (by norm_num))
    scalarRow13135 repair13135 covarianceInputs13135 (fun i hi => sourceNumerics13135 hi)
    BstLean.Part268.agent13135.frame targetFrame13135_eq


end BstLean.Part269.N13135

namespace BstLean.Part269.N13136
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13136 : scalarRow13136.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13136, BstLean.Part268.grid13136, BstLean.Part263.worldGrid]

theorem supplies13136 (j : Fin 43) : Supply 13136 (parameters j)
    (cellLower scalarRow13136.grid (sourceIndex j))
    (cellUpper scalarRow13136.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13136.grid grid_top_bounds13136 j

theorem radii13136 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13136.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13136 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13136 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13136.grid grid_top_bounds13136 j hθ

noncomputable def covarianceInputs13136 :
    BstLean.Part263.CovarianceInputs 13136 scalarRow13136.grid parameters (caps repair13136) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13136 grid_top_bounds13136 repair13136

noncomputable def covarianceEvent13136 : Set (AgFam 13136) :=
  BstLean.Part263.covarianceEvent 13136 scalarRow13136.grid parameters

theorem covarianceEvent13136_measurable : MeasurableSet covarianceEvent13136 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13136_payment :
    (retDist (paperDesignP 13136).toCentres).real
      (agentEv (paperDesignP 13136) covarianceEvent13136)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13136

theorem localCov13136 : BstLean.Part259.LocalCovarianceOn covarianceEvent13136
    (BstLean.Part263.cell scalarRow13136.grid) (caps repair13136) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13136

theorem covarianceGood13136_payment :
    (retDist (paperDesignP 13136).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13136)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13136_payment



end BstLean.Part269.N13136

namespace BstLean.Part269.N13136
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13136}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13136.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13136) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13136).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13136 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13136) (by norm_num) BstLean.Part268.WorldRow13136.worldPackage rfl
    BstLean.Part268.WorldRow13136.product_lower (BstLean.Part268.WorldRow13136.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13136} (hw : c ∈ Hof BstLean.Part268.WorldRow13136.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13136) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13136) (by norm_num) BstLean.Part268.WorldRow13136.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13136} (hw : c ∈ Hof BstLean.Part268.WorldRow13136.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13136) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13136).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13136) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13136_eq : scalarRow13136.targetFrame = BstLean.Part268.agent13136.frame := by
  norm_num [scalarRow13136,BstLean.Part268.agent13136]

noncomputable def frameData13136 : BstLean.Part264b.FrameData 13136 :=
  BstLean.Part269.frameData_from_numerics (n := 13136) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13136.worldPackage rfl BstLean.Part268.WorldRow13136.product_lower (BstLean.Part268.WorldRow13136.producthi.2.trans (by norm_num))
    scalarRow13136 repair13136 covarianceInputs13136 (fun i hi => sourceNumerics13136 hi)
    BstLean.Part268.agent13136.frame targetFrame13136_eq


end BstLean.Part269.N13136

namespace BstLean.Part269.N13137
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13137 : scalarRow13137.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13137, BstLean.Part268.grid13137, BstLean.Part263.worldGrid]

theorem supplies13137 (j : Fin 43) : Supply 13137 (parameters j)
    (cellLower scalarRow13137.grid (sourceIndex j))
    (cellUpper scalarRow13137.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13137.grid grid_top_bounds13137 j

theorem radii13137 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13137.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13137 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13137 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13137.grid grid_top_bounds13137 j hθ

noncomputable def covarianceInputs13137 :
    BstLean.Part263.CovarianceInputs 13137 scalarRow13137.grid parameters (caps repair13137) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13137 grid_top_bounds13137 repair13137

noncomputable def covarianceEvent13137 : Set (AgFam 13137) :=
  BstLean.Part263.covarianceEvent 13137 scalarRow13137.grid parameters

theorem covarianceEvent13137_measurable : MeasurableSet covarianceEvent13137 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13137_payment :
    (retDist (paperDesignP 13137).toCentres).real
      (agentEv (paperDesignP 13137) covarianceEvent13137)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13137

theorem localCov13137 : BstLean.Part259.LocalCovarianceOn covarianceEvent13137
    (BstLean.Part263.cell scalarRow13137.grid) (caps repair13137) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13137

theorem covarianceGood13137_payment :
    (retDist (paperDesignP 13137).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13137)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13137_payment



end BstLean.Part269.N13137

namespace BstLean.Part269.N13137
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13137}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13137.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13137) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13137).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13137 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13137) (by norm_num) BstLean.Part268.WorldRow13137.worldPackage rfl
    BstLean.Part268.WorldRow13137.product_lower (BstLean.Part268.WorldRow13137.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13137} (hw : c ∈ Hof BstLean.Part268.WorldRow13137.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13137) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13137) (by norm_num) BstLean.Part268.WorldRow13137.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13137} (hw : c ∈ Hof BstLean.Part268.WorldRow13137.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13137) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13137).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13137) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13137_eq : scalarRow13137.targetFrame = BstLean.Part268.agent13137.frame := by
  norm_num [scalarRow13137,BstLean.Part268.agent13137]

noncomputable def frameData13137 : BstLean.Part264b.FrameData 13137 :=
  BstLean.Part269.frameData_from_numerics (n := 13137) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13137.worldPackage rfl BstLean.Part268.WorldRow13137.product_lower (BstLean.Part268.WorldRow13137.producthi.2.trans (by norm_num))
    scalarRow13137 repair13137 covarianceInputs13137 (fun i hi => sourceNumerics13137 hi)
    BstLean.Part268.agent13137.frame targetFrame13137_eq


end BstLean.Part269.N13137

namespace BstLean.Part269.N13138
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13138 : scalarRow13138.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13138, BstLean.Part268.grid13138, BstLean.Part263.worldGrid]

theorem supplies13138 (j : Fin 43) : Supply 13138 (parameters j)
    (cellLower scalarRow13138.grid (sourceIndex j))
    (cellUpper scalarRow13138.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13138.grid grid_top_bounds13138 j

theorem radii13138 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13138.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13138 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13138 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13138.grid grid_top_bounds13138 j hθ

noncomputable def covarianceInputs13138 :
    BstLean.Part263.CovarianceInputs 13138 scalarRow13138.grid parameters (caps repair13138) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13138 grid_top_bounds13138 repair13138

noncomputable def covarianceEvent13138 : Set (AgFam 13138) :=
  BstLean.Part263.covarianceEvent 13138 scalarRow13138.grid parameters

theorem covarianceEvent13138_measurable : MeasurableSet covarianceEvent13138 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13138_payment :
    (retDist (paperDesignP 13138).toCentres).real
      (agentEv (paperDesignP 13138) covarianceEvent13138)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13138

theorem localCov13138 : BstLean.Part259.LocalCovarianceOn covarianceEvent13138
    (BstLean.Part263.cell scalarRow13138.grid) (caps repair13138) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13138

theorem covarianceGood13138_payment :
    (retDist (paperDesignP 13138).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13138)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13138_payment



end BstLean.Part269.N13138

namespace BstLean.Part269.N13138
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13138}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13138.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13138) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13138).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13138 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13138) (by norm_num) BstLean.Part268.WorldRow13138.worldPackage rfl
    BstLean.Part268.WorldRow13138.product_lower (BstLean.Part268.WorldRow13138.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13138} (hw : c ∈ Hof BstLean.Part268.WorldRow13138.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13138) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13138) (by norm_num) BstLean.Part268.WorldRow13138.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13138} (hw : c ∈ Hof BstLean.Part268.WorldRow13138.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13138) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13138).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13138) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13138_eq : scalarRow13138.targetFrame = BstLean.Part268.agent13138.frame := by
  norm_num [scalarRow13138,BstLean.Part268.agent13138]

noncomputable def frameData13138 : BstLean.Part264b.FrameData 13138 :=
  BstLean.Part269.frameData_from_numerics (n := 13138) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13138.worldPackage rfl BstLean.Part268.WorldRow13138.product_lower (BstLean.Part268.WorldRow13138.producthi.2.trans (by norm_num))
    scalarRow13138 repair13138 covarianceInputs13138 (fun i hi => sourceNumerics13138 hi)
    BstLean.Part268.agent13138.frame targetFrame13138_eq


end BstLean.Part269.N13138

namespace BstLean.Part269.N13139
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13139 : scalarRow13139.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13139, BstLean.Part268.grid13139, BstLean.Part263.worldGrid]

theorem supplies13139 (j : Fin 43) : Supply 13139 (parameters j)
    (cellLower scalarRow13139.grid (sourceIndex j))
    (cellUpper scalarRow13139.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13139.grid grid_top_bounds13139 j

theorem radii13139 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13139.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13139 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13139 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13139.grid grid_top_bounds13139 j hθ

noncomputable def covarianceInputs13139 :
    BstLean.Part263.CovarianceInputs 13139 scalarRow13139.grid parameters (caps repair13139) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13139 grid_top_bounds13139 repair13139

noncomputable def covarianceEvent13139 : Set (AgFam 13139) :=
  BstLean.Part263.covarianceEvent 13139 scalarRow13139.grid parameters

theorem covarianceEvent13139_measurable : MeasurableSet covarianceEvent13139 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13139_payment :
    (retDist (paperDesignP 13139).toCentres).real
      (agentEv (paperDesignP 13139) covarianceEvent13139)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13139

theorem localCov13139 : BstLean.Part259.LocalCovarianceOn covarianceEvent13139
    (BstLean.Part263.cell scalarRow13139.grid) (caps repair13139) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13139

theorem covarianceGood13139_payment :
    (retDist (paperDesignP 13139).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13139)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13139_payment



end BstLean.Part269.N13139

namespace BstLean.Part269.N13139
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13139}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13139.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13139) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13139).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13139 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13139) (by norm_num) BstLean.Part268.WorldRow13139.worldPackage rfl
    BstLean.Part268.WorldRow13139.product_lower (BstLean.Part268.WorldRow13139.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13139} (hw : c ∈ Hof BstLean.Part268.WorldRow13139.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13139) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13139) (by norm_num) BstLean.Part268.WorldRow13139.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13139} (hw : c ∈ Hof BstLean.Part268.WorldRow13139.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13139) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13139).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13139) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13139_eq : scalarRow13139.targetFrame = BstLean.Part268.agent13139.frame := by
  norm_num [scalarRow13139,BstLean.Part268.agent13139]

noncomputable def frameData13139 : BstLean.Part264b.FrameData 13139 :=
  BstLean.Part269.frameData_from_numerics (n := 13139) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13139.worldPackage rfl BstLean.Part268.WorldRow13139.product_lower (BstLean.Part268.WorldRow13139.producthi.2.trans (by norm_num))
    scalarRow13139 repair13139 covarianceInputs13139 (fun i hi => sourceNumerics13139 hi)
    BstLean.Part268.agent13139.frame targetFrame13139_eq


end BstLean.Part269.N13139
