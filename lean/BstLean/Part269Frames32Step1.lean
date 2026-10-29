import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World32Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs32
import BstLean.Part269Rows32
import BstLean.Part269Sources32
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13155
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13155 : scalarRow13155.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13155, BstLean.Part268.grid13155, BstLean.Part263.worldGrid]

theorem supplies13155 (j : Fin 43) : Supply 13155 (parameters j)
    (cellLower scalarRow13155.grid (sourceIndex j))
    (cellUpper scalarRow13155.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13155.grid grid_top_bounds13155 j

theorem radii13155 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13155.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13155 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13155 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13155.grid grid_top_bounds13155 j hθ

noncomputable def covarianceInputs13155 :
    BstLean.Part263.CovarianceInputs 13155 scalarRow13155.grid parameters (caps repair13155) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13155 grid_top_bounds13155 repair13155

noncomputable def covarianceEvent13155 : Set (AgFam 13155) :=
  BstLean.Part263.covarianceEvent 13155 scalarRow13155.grid parameters

theorem covarianceEvent13155_measurable : MeasurableSet covarianceEvent13155 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13155_payment :
    (retDist (paperDesignP 13155).toCentres).real
      (agentEv (paperDesignP 13155) covarianceEvent13155)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13155

theorem localCov13155 : BstLean.Part259.LocalCovarianceOn covarianceEvent13155
    (BstLean.Part263.cell scalarRow13155.grid) (caps repair13155) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13155

theorem covarianceGood13155_payment :
    (retDist (paperDesignP 13155).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13155)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13155_payment



end BstLean.Part269.N13155

namespace BstLean.Part269.N13155
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13155}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13155.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13155) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13155).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13155 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13155) (by norm_num) BstLean.Part268.WorldRow13155.worldPackage rfl
    BstLean.Part268.WorldRow13155.product_lower (BstLean.Part268.WorldRow13155.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13155} (hw : c ∈ Hof BstLean.Part268.WorldRow13155.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13155) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13155) (by norm_num) BstLean.Part268.WorldRow13155.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13155} (hw : c ∈ Hof BstLean.Part268.WorldRow13155.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13155) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13155).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13155) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13155_eq : scalarRow13155.targetFrame = BstLean.Part268.agent13155.frame := by
  norm_num [scalarRow13155,BstLean.Part268.agent13155]

noncomputable def frameData13155 : BstLean.Part264b.FrameData 13155 :=
  BstLean.Part269.frameData_from_numerics (n := 13155) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13155.worldPackage rfl BstLean.Part268.WorldRow13155.product_lower (BstLean.Part268.WorldRow13155.producthi.2.trans (by norm_num))
    scalarRow13155 repair13155 covarianceInputs13155 (fun i hi => sourceNumerics13155 hi)
    BstLean.Part268.agent13155.frame targetFrame13155_eq


end BstLean.Part269.N13155

namespace BstLean.Part269.N13156
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13156 : scalarRow13156.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13156, BstLean.Part268.grid13156, BstLean.Part263.worldGrid]

theorem supplies13156 (j : Fin 43) : Supply 13156 (parameters j)
    (cellLower scalarRow13156.grid (sourceIndex j))
    (cellUpper scalarRow13156.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13156.grid grid_top_bounds13156 j

theorem radii13156 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13156.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13156 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13156 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13156.grid grid_top_bounds13156 j hθ

noncomputable def covarianceInputs13156 :
    BstLean.Part263.CovarianceInputs 13156 scalarRow13156.grid parameters (caps repair13156) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13156 grid_top_bounds13156 repair13156

noncomputable def covarianceEvent13156 : Set (AgFam 13156) :=
  BstLean.Part263.covarianceEvent 13156 scalarRow13156.grid parameters

theorem covarianceEvent13156_measurable : MeasurableSet covarianceEvent13156 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13156_payment :
    (retDist (paperDesignP 13156).toCentres).real
      (agentEv (paperDesignP 13156) covarianceEvent13156)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13156

theorem localCov13156 : BstLean.Part259.LocalCovarianceOn covarianceEvent13156
    (BstLean.Part263.cell scalarRow13156.grid) (caps repair13156) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13156

theorem covarianceGood13156_payment :
    (retDist (paperDesignP 13156).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13156)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13156_payment



end BstLean.Part269.N13156

namespace BstLean.Part269.N13156
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13156}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13156.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13156) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13156).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13156 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13156) (by norm_num) BstLean.Part268.WorldRow13156.worldPackage rfl
    BstLean.Part268.WorldRow13156.product_lower (BstLean.Part268.WorldRow13156.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13156} (hw : c ∈ Hof BstLean.Part268.WorldRow13156.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13156) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13156) (by norm_num) BstLean.Part268.WorldRow13156.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13156} (hw : c ∈ Hof BstLean.Part268.WorldRow13156.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13156) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13156).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13156) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13156_eq : scalarRow13156.targetFrame = BstLean.Part268.agent13156.frame := by
  norm_num [scalarRow13156,BstLean.Part268.agent13156]

noncomputable def frameData13156 : BstLean.Part264b.FrameData 13156 :=
  BstLean.Part269.frameData_from_numerics (n := 13156) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13156.worldPackage rfl BstLean.Part268.WorldRow13156.product_lower (BstLean.Part268.WorldRow13156.producthi.2.trans (by norm_num))
    scalarRow13156 repair13156 covarianceInputs13156 (fun i hi => sourceNumerics13156 hi)
    BstLean.Part268.agent13156.frame targetFrame13156_eq


end BstLean.Part269.N13156

namespace BstLean.Part269.N13157
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13157 : scalarRow13157.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13157, BstLean.Part268.grid13157, BstLean.Part263.worldGrid]

theorem supplies13157 (j : Fin 43) : Supply 13157 (parameters j)
    (cellLower scalarRow13157.grid (sourceIndex j))
    (cellUpper scalarRow13157.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13157.grid grid_top_bounds13157 j

theorem radii13157 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13157.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13157 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13157 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13157.grid grid_top_bounds13157 j hθ

noncomputable def covarianceInputs13157 :
    BstLean.Part263.CovarianceInputs 13157 scalarRow13157.grid parameters (caps repair13157) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13157 grid_top_bounds13157 repair13157

noncomputable def covarianceEvent13157 : Set (AgFam 13157) :=
  BstLean.Part263.covarianceEvent 13157 scalarRow13157.grid parameters

theorem covarianceEvent13157_measurable : MeasurableSet covarianceEvent13157 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13157_payment :
    (retDist (paperDesignP 13157).toCentres).real
      (agentEv (paperDesignP 13157) covarianceEvent13157)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13157

theorem localCov13157 : BstLean.Part259.LocalCovarianceOn covarianceEvent13157
    (BstLean.Part263.cell scalarRow13157.grid) (caps repair13157) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13157

theorem covarianceGood13157_payment :
    (retDist (paperDesignP 13157).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13157)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13157_payment



end BstLean.Part269.N13157

namespace BstLean.Part269.N13157
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13157}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13157.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13157) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13157).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13157 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13157) (by norm_num) BstLean.Part268.WorldRow13157.worldPackage rfl
    BstLean.Part268.WorldRow13157.product_lower (BstLean.Part268.WorldRow13157.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13157} (hw : c ∈ Hof BstLean.Part268.WorldRow13157.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13157) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13157) (by norm_num) BstLean.Part268.WorldRow13157.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13157} (hw : c ∈ Hof BstLean.Part268.WorldRow13157.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13157) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13157).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13157) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13157_eq : scalarRow13157.targetFrame = BstLean.Part268.agent13157.frame := by
  norm_num [scalarRow13157,BstLean.Part268.agent13157]

noncomputable def frameData13157 : BstLean.Part264b.FrameData 13157 :=
  BstLean.Part269.frameData_from_numerics (n := 13157) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13157.worldPackage rfl BstLean.Part268.WorldRow13157.product_lower (BstLean.Part268.WorldRow13157.producthi.2.trans (by norm_num))
    scalarRow13157 repair13157 covarianceInputs13157 (fun i hi => sourceNumerics13157 hi)
    BstLean.Part268.agent13157.frame targetFrame13157_eq


end BstLean.Part269.N13157

namespace BstLean.Part269.N13158
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13158 : scalarRow13158.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13158, BstLean.Part268.grid13158, BstLean.Part263.worldGrid]

theorem supplies13158 (j : Fin 43) : Supply 13158 (parameters j)
    (cellLower scalarRow13158.grid (sourceIndex j))
    (cellUpper scalarRow13158.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13158.grid grid_top_bounds13158 j

theorem radii13158 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13158.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13158 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13158 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13158.grid grid_top_bounds13158 j hθ

noncomputable def covarianceInputs13158 :
    BstLean.Part263.CovarianceInputs 13158 scalarRow13158.grid parameters (caps repair13158) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13158 grid_top_bounds13158 repair13158

noncomputable def covarianceEvent13158 : Set (AgFam 13158) :=
  BstLean.Part263.covarianceEvent 13158 scalarRow13158.grid parameters

theorem covarianceEvent13158_measurable : MeasurableSet covarianceEvent13158 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13158_payment :
    (retDist (paperDesignP 13158).toCentres).real
      (agentEv (paperDesignP 13158) covarianceEvent13158)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13158

theorem localCov13158 : BstLean.Part259.LocalCovarianceOn covarianceEvent13158
    (BstLean.Part263.cell scalarRow13158.grid) (caps repair13158) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13158

theorem covarianceGood13158_payment :
    (retDist (paperDesignP 13158).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13158)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13158_payment



end BstLean.Part269.N13158

namespace BstLean.Part269.N13158
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13158}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13158.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13158) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13158).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13158 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13158) (by norm_num) BstLean.Part268.WorldRow13158.worldPackage rfl
    BstLean.Part268.WorldRow13158.product_lower (BstLean.Part268.WorldRow13158.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13158} (hw : c ∈ Hof BstLean.Part268.WorldRow13158.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13158) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13158) (by norm_num) BstLean.Part268.WorldRow13158.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13158} (hw : c ∈ Hof BstLean.Part268.WorldRow13158.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13158) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13158).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13158) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13158_eq : scalarRow13158.targetFrame = BstLean.Part268.agent13158.frame := by
  norm_num [scalarRow13158,BstLean.Part268.agent13158]

noncomputable def frameData13158 : BstLean.Part264b.FrameData 13158 :=
  BstLean.Part269.frameData_from_numerics (n := 13158) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13158.worldPackage rfl BstLean.Part268.WorldRow13158.product_lower (BstLean.Part268.WorldRow13158.producthi.2.trans (by norm_num))
    scalarRow13158 repair13158 covarianceInputs13158 (fun i hi => sourceNumerics13158 hi)
    BstLean.Part268.agent13158.frame targetFrame13158_eq


end BstLean.Part269.N13158

namespace BstLean.Part269.N13159
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13159 : scalarRow13159.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13159, BstLean.Part268.grid13159, BstLean.Part263.worldGrid]

theorem supplies13159 (j : Fin 43) : Supply 13159 (parameters j)
    (cellLower scalarRow13159.grid (sourceIndex j))
    (cellUpper scalarRow13159.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13159.grid grid_top_bounds13159 j

theorem radii13159 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13159.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13159 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13159 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13159.grid grid_top_bounds13159 j hθ

noncomputable def covarianceInputs13159 :
    BstLean.Part263.CovarianceInputs 13159 scalarRow13159.grid parameters (caps repair13159) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13159 grid_top_bounds13159 repair13159

noncomputable def covarianceEvent13159 : Set (AgFam 13159) :=
  BstLean.Part263.covarianceEvent 13159 scalarRow13159.grid parameters

theorem covarianceEvent13159_measurable : MeasurableSet covarianceEvent13159 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13159_payment :
    (retDist (paperDesignP 13159).toCentres).real
      (agentEv (paperDesignP 13159) covarianceEvent13159)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13159

theorem localCov13159 : BstLean.Part259.LocalCovarianceOn covarianceEvent13159
    (BstLean.Part263.cell scalarRow13159.grid) (caps repair13159) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13159

theorem covarianceGood13159_payment :
    (retDist (paperDesignP 13159).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13159)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13159_payment



end BstLean.Part269.N13159

namespace BstLean.Part269.N13159
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13159}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13159.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13159) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13159).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13159 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13159) (by norm_num) BstLean.Part268.WorldRow13159.worldPackage rfl
    BstLean.Part268.WorldRow13159.product_lower (BstLean.Part268.WorldRow13159.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13159} (hw : c ∈ Hof BstLean.Part268.WorldRow13159.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13159) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13159) (by norm_num) BstLean.Part268.WorldRow13159.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13159} (hw : c ∈ Hof BstLean.Part268.WorldRow13159.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13159) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13159).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13159) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13159_eq : scalarRow13159.targetFrame = BstLean.Part268.agent13159.frame := by
  norm_num [scalarRow13159,BstLean.Part268.agent13159]

noncomputable def frameData13159 : BstLean.Part264b.FrameData 13159 :=
  BstLean.Part269.frameData_from_numerics (n := 13159) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13159.worldPackage rfl BstLean.Part268.WorldRow13159.product_lower (BstLean.Part268.WorldRow13159.producthi.2.trans (by norm_num))
    scalarRow13159 repair13159 covarianceInputs13159 (fun i hi => sourceNumerics13159 hi)
    BstLean.Part268.agent13159.frame targetFrame13159_eq


end BstLean.Part269.N13159
