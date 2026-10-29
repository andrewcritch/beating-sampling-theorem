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

namespace BstLean.Part269.N13115
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13115 : scalarRow13115.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13115, BstLean.Part268.grid13115, BstLean.Part263.worldGrid]

theorem supplies13115 (j : Fin 43) : Supply 13115 (parameters j)
    (cellLower scalarRow13115.grid (sourceIndex j))
    (cellUpper scalarRow13115.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13115.grid grid_top_bounds13115 j

theorem radii13115 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13115.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13115 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13115 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13115.grid grid_top_bounds13115 j hθ

noncomputable def covarianceInputs13115 :
    BstLean.Part263.CovarianceInputs 13115 scalarRow13115.grid parameters (caps repair13115) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13115 grid_top_bounds13115 repair13115

noncomputable def covarianceEvent13115 : Set (AgFam 13115) :=
  BstLean.Part263.covarianceEvent 13115 scalarRow13115.grid parameters

theorem covarianceEvent13115_measurable : MeasurableSet covarianceEvent13115 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13115_payment :
    (retDist (paperDesignP 13115).toCentres).real
      (agentEv (paperDesignP 13115) covarianceEvent13115)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13115

theorem localCov13115 : BstLean.Part259.LocalCovarianceOn covarianceEvent13115
    (BstLean.Part263.cell scalarRow13115.grid) (caps repair13115) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13115

theorem covarianceGood13115_payment :
    (retDist (paperDesignP 13115).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13115)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13115_payment



end BstLean.Part269.N13115

namespace BstLean.Part269.N13115
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13115}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13115.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13115) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13115).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13115 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13115) (by norm_num) BstLean.Part268.WorldRow13115.worldPackage rfl
    BstLean.Part268.WorldRow13115.product_lower (BstLean.Part268.WorldRow13115.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13115} (hw : c ∈ Hof BstLean.Part268.WorldRow13115.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13115) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13115) (by norm_num) BstLean.Part268.WorldRow13115.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13115} (hw : c ∈ Hof BstLean.Part268.WorldRow13115.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13115) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13115).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13115) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13115_eq : scalarRow13115.targetFrame = BstLean.Part268.agent13115.frame := by
  norm_num [scalarRow13115,BstLean.Part268.agent13115]

noncomputable def frameData13115 : BstLean.Part264b.FrameData 13115 :=
  BstLean.Part269.frameData_from_numerics (n := 13115) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13115.worldPackage rfl BstLean.Part268.WorldRow13115.product_lower (BstLean.Part268.WorldRow13115.producthi.2.trans (by norm_num))
    scalarRow13115 repair13115 covarianceInputs13115 (fun i hi => sourceNumerics13115 hi)
    BstLean.Part268.agent13115.frame targetFrame13115_eq


end BstLean.Part269.N13115

namespace BstLean.Part269.N13116
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13116 : scalarRow13116.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13116, BstLean.Part268.grid13116, BstLean.Part263.worldGrid]

theorem supplies13116 (j : Fin 43) : Supply 13116 (parameters j)
    (cellLower scalarRow13116.grid (sourceIndex j))
    (cellUpper scalarRow13116.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13116.grid grid_top_bounds13116 j

theorem radii13116 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13116.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13116 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13116 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13116.grid grid_top_bounds13116 j hθ

noncomputable def covarianceInputs13116 :
    BstLean.Part263.CovarianceInputs 13116 scalarRow13116.grid parameters (caps repair13116) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13116 grid_top_bounds13116 repair13116

noncomputable def covarianceEvent13116 : Set (AgFam 13116) :=
  BstLean.Part263.covarianceEvent 13116 scalarRow13116.grid parameters

theorem covarianceEvent13116_measurable : MeasurableSet covarianceEvent13116 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13116_payment :
    (retDist (paperDesignP 13116).toCentres).real
      (agentEv (paperDesignP 13116) covarianceEvent13116)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13116

theorem localCov13116 : BstLean.Part259.LocalCovarianceOn covarianceEvent13116
    (BstLean.Part263.cell scalarRow13116.grid) (caps repair13116) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13116

theorem covarianceGood13116_payment :
    (retDist (paperDesignP 13116).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13116)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13116_payment



end BstLean.Part269.N13116

namespace BstLean.Part269.N13116
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13116}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13116.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13116) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13116).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13116 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13116) (by norm_num) BstLean.Part268.WorldRow13116.worldPackage rfl
    BstLean.Part268.WorldRow13116.product_lower (BstLean.Part268.WorldRow13116.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13116} (hw : c ∈ Hof BstLean.Part268.WorldRow13116.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13116) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13116) (by norm_num) BstLean.Part268.WorldRow13116.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13116} (hw : c ∈ Hof BstLean.Part268.WorldRow13116.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13116) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13116).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13116) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13116_eq : scalarRow13116.targetFrame = BstLean.Part268.agent13116.frame := by
  norm_num [scalarRow13116,BstLean.Part268.agent13116]

noncomputable def frameData13116 : BstLean.Part264b.FrameData 13116 :=
  BstLean.Part269.frameData_from_numerics (n := 13116) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13116.worldPackage rfl BstLean.Part268.WorldRow13116.product_lower (BstLean.Part268.WorldRow13116.producthi.2.trans (by norm_num))
    scalarRow13116 repair13116 covarianceInputs13116 (fun i hi => sourceNumerics13116 hi)
    BstLean.Part268.agent13116.frame targetFrame13116_eq


end BstLean.Part269.N13116

namespace BstLean.Part269.N13117
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13117 : scalarRow13117.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13117, BstLean.Part268.grid13117, BstLean.Part263.worldGrid]

theorem supplies13117 (j : Fin 43) : Supply 13117 (parameters j)
    (cellLower scalarRow13117.grid (sourceIndex j))
    (cellUpper scalarRow13117.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13117.grid grid_top_bounds13117 j

theorem radii13117 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13117.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13117 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13117 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13117.grid grid_top_bounds13117 j hθ

noncomputable def covarianceInputs13117 :
    BstLean.Part263.CovarianceInputs 13117 scalarRow13117.grid parameters (caps repair13117) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13117 grid_top_bounds13117 repair13117

noncomputable def covarianceEvent13117 : Set (AgFam 13117) :=
  BstLean.Part263.covarianceEvent 13117 scalarRow13117.grid parameters

theorem covarianceEvent13117_measurable : MeasurableSet covarianceEvent13117 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13117_payment :
    (retDist (paperDesignP 13117).toCentres).real
      (agentEv (paperDesignP 13117) covarianceEvent13117)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13117

theorem localCov13117 : BstLean.Part259.LocalCovarianceOn covarianceEvent13117
    (BstLean.Part263.cell scalarRow13117.grid) (caps repair13117) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13117

theorem covarianceGood13117_payment :
    (retDist (paperDesignP 13117).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13117)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13117_payment



end BstLean.Part269.N13117

namespace BstLean.Part269.N13117
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13117}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13117.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13117) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13117).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13117 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13117) (by norm_num) BstLean.Part268.WorldRow13117.worldPackage rfl
    BstLean.Part268.WorldRow13117.product_lower (BstLean.Part268.WorldRow13117.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13117} (hw : c ∈ Hof BstLean.Part268.WorldRow13117.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13117) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13117) (by norm_num) BstLean.Part268.WorldRow13117.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13117} (hw : c ∈ Hof BstLean.Part268.WorldRow13117.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13117) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13117).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13117) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13117_eq : scalarRow13117.targetFrame = BstLean.Part268.agent13117.frame := by
  norm_num [scalarRow13117,BstLean.Part268.agent13117]

noncomputable def frameData13117 : BstLean.Part264b.FrameData 13117 :=
  BstLean.Part269.frameData_from_numerics (n := 13117) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13117.worldPackage rfl BstLean.Part268.WorldRow13117.product_lower (BstLean.Part268.WorldRow13117.producthi.2.trans (by norm_num))
    scalarRow13117 repair13117 covarianceInputs13117 (fun i hi => sourceNumerics13117 hi)
    BstLean.Part268.agent13117.frame targetFrame13117_eq


end BstLean.Part269.N13117

namespace BstLean.Part269.N13118
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13118 : scalarRow13118.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13118, BstLean.Part268.grid13118, BstLean.Part263.worldGrid]

theorem supplies13118 (j : Fin 43) : Supply 13118 (parameters j)
    (cellLower scalarRow13118.grid (sourceIndex j))
    (cellUpper scalarRow13118.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13118.grid grid_top_bounds13118 j

theorem radii13118 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13118.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13118 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13118 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13118.grid grid_top_bounds13118 j hθ

noncomputable def covarianceInputs13118 :
    BstLean.Part263.CovarianceInputs 13118 scalarRow13118.grid parameters (caps repair13118) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13118 grid_top_bounds13118 repair13118

noncomputable def covarianceEvent13118 : Set (AgFam 13118) :=
  BstLean.Part263.covarianceEvent 13118 scalarRow13118.grid parameters

theorem covarianceEvent13118_measurable : MeasurableSet covarianceEvent13118 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13118_payment :
    (retDist (paperDesignP 13118).toCentres).real
      (agentEv (paperDesignP 13118) covarianceEvent13118)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13118

theorem localCov13118 : BstLean.Part259.LocalCovarianceOn covarianceEvent13118
    (BstLean.Part263.cell scalarRow13118.grid) (caps repair13118) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13118

theorem covarianceGood13118_payment :
    (retDist (paperDesignP 13118).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13118)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13118_payment



end BstLean.Part269.N13118

namespace BstLean.Part269.N13118
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13118}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13118.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13118) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13118).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13118 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13118) (by norm_num) BstLean.Part268.WorldRow13118.worldPackage rfl
    BstLean.Part268.WorldRow13118.product_lower (BstLean.Part268.WorldRow13118.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13118} (hw : c ∈ Hof BstLean.Part268.WorldRow13118.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13118) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13118) (by norm_num) BstLean.Part268.WorldRow13118.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13118} (hw : c ∈ Hof BstLean.Part268.WorldRow13118.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13118) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13118).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13118) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13118_eq : scalarRow13118.targetFrame = BstLean.Part268.agent13118.frame := by
  norm_num [scalarRow13118,BstLean.Part268.agent13118]

noncomputable def frameData13118 : BstLean.Part264b.FrameData 13118 :=
  BstLean.Part269.frameData_from_numerics (n := 13118) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13118.worldPackage rfl BstLean.Part268.WorldRow13118.product_lower (BstLean.Part268.WorldRow13118.producthi.2.trans (by norm_num))
    scalarRow13118 repair13118 covarianceInputs13118 (fun i hi => sourceNumerics13118 hi)
    BstLean.Part268.agent13118.frame targetFrame13118_eq


end BstLean.Part269.N13118

namespace BstLean.Part269.N13119
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13119 : scalarRow13119.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13119, BstLean.Part268.grid13119, BstLean.Part263.worldGrid]

theorem supplies13119 (j : Fin 43) : Supply 13119 (parameters j)
    (cellLower scalarRow13119.grid (sourceIndex j))
    (cellUpper scalarRow13119.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13119.grid grid_top_bounds13119 j

theorem radii13119 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13119.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13119 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13119 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13119.grid grid_top_bounds13119 j hθ

noncomputable def covarianceInputs13119 :
    BstLean.Part263.CovarianceInputs 13119 scalarRow13119.grid parameters (caps repair13119) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13119 grid_top_bounds13119 repair13119

noncomputable def covarianceEvent13119 : Set (AgFam 13119) :=
  BstLean.Part263.covarianceEvent 13119 scalarRow13119.grid parameters

theorem covarianceEvent13119_measurable : MeasurableSet covarianceEvent13119 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13119_payment :
    (retDist (paperDesignP 13119).toCentres).real
      (agentEv (paperDesignP 13119) covarianceEvent13119)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13119

theorem localCov13119 : BstLean.Part259.LocalCovarianceOn covarianceEvent13119
    (BstLean.Part263.cell scalarRow13119.grid) (caps repair13119) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13119

theorem covarianceGood13119_payment :
    (retDist (paperDesignP 13119).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13119)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13119_payment



end BstLean.Part269.N13119

namespace BstLean.Part269.N13119
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13119}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13119.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13119) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13119).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13119 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13119) (by norm_num) BstLean.Part268.WorldRow13119.worldPackage rfl
    BstLean.Part268.WorldRow13119.product_lower (BstLean.Part268.WorldRow13119.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13119} (hw : c ∈ Hof BstLean.Part268.WorldRow13119.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13119) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13119) (by norm_num) BstLean.Part268.WorldRow13119.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13119} (hw : c ∈ Hof BstLean.Part268.WorldRow13119.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13119) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13119).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13119) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13119_eq : scalarRow13119.targetFrame = BstLean.Part268.agent13119.frame := by
  norm_num [scalarRow13119,BstLean.Part268.agent13119]

noncomputable def frameData13119 : BstLean.Part264b.FrameData 13119 :=
  BstLean.Part269.frameData_from_numerics (n := 13119) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13119.worldPackage rfl BstLean.Part268.WorldRow13119.product_lower (BstLean.Part268.WorldRow13119.producthi.2.trans (by norm_num))
    scalarRow13119 repair13119 covarianceInputs13119 (fun i hi => sourceNumerics13119 hi)
    BstLean.Part268.agent13119.frame targetFrame13119_eq


end BstLean.Part269.N13119
