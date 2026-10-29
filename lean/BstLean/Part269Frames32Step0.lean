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

namespace BstLean.Part269.N13150
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13150 : scalarRow13150.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13150, BstLean.Part268.grid13150, BstLean.Part263.worldGrid]

theorem supplies13150 (j : Fin 43) : Supply 13150 (parameters j)
    (cellLower scalarRow13150.grid (sourceIndex j))
    (cellUpper scalarRow13150.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13150.grid grid_top_bounds13150 j

theorem radii13150 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13150.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13150 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13150 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13150.grid grid_top_bounds13150 j hθ

noncomputable def covarianceInputs13150 :
    BstLean.Part263.CovarianceInputs 13150 scalarRow13150.grid parameters (caps repair13150) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13150 grid_top_bounds13150 repair13150

noncomputable def covarianceEvent13150 : Set (AgFam 13150) :=
  BstLean.Part263.covarianceEvent 13150 scalarRow13150.grid parameters

theorem covarianceEvent13150_measurable : MeasurableSet covarianceEvent13150 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13150_payment :
    (retDist (paperDesignP 13150).toCentres).real
      (agentEv (paperDesignP 13150) covarianceEvent13150)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13150

theorem localCov13150 : BstLean.Part259.LocalCovarianceOn covarianceEvent13150
    (BstLean.Part263.cell scalarRow13150.grid) (caps repair13150) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13150

theorem covarianceGood13150_payment :
    (retDist (paperDesignP 13150).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13150)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13150_payment



end BstLean.Part269.N13150

namespace BstLean.Part269.N13150
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13150}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13150.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13150) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13150).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13150 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13150) (by norm_num) BstLean.Part268.WorldRow13150.worldPackage rfl
    BstLean.Part268.WorldRow13150.product_lower (BstLean.Part268.WorldRow13150.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13150} (hw : c ∈ Hof BstLean.Part268.WorldRow13150.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13150) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13150) (by norm_num) BstLean.Part268.WorldRow13150.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13150} (hw : c ∈ Hof BstLean.Part268.WorldRow13150.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13150) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13150).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13150) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13150_eq : scalarRow13150.targetFrame = BstLean.Part268.agent13150.frame := by
  norm_num [scalarRow13150,BstLean.Part268.agent13150]

noncomputable def frameData13150 : BstLean.Part264b.FrameData 13150 :=
  BstLean.Part269.frameData_from_numerics (n := 13150) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13150.worldPackage rfl BstLean.Part268.WorldRow13150.product_lower (BstLean.Part268.WorldRow13150.producthi.2.trans (by norm_num))
    scalarRow13150 repair13150 covarianceInputs13150 (fun i hi => sourceNumerics13150 hi)
    BstLean.Part268.agent13150.frame targetFrame13150_eq


end BstLean.Part269.N13150

namespace BstLean.Part269.N13151
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13151 : scalarRow13151.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13151, BstLean.Part268.grid13151, BstLean.Part263.worldGrid]

theorem supplies13151 (j : Fin 43) : Supply 13151 (parameters j)
    (cellLower scalarRow13151.grid (sourceIndex j))
    (cellUpper scalarRow13151.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13151.grid grid_top_bounds13151 j

theorem radii13151 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13151.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13151 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13151 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13151.grid grid_top_bounds13151 j hθ

noncomputable def covarianceInputs13151 :
    BstLean.Part263.CovarianceInputs 13151 scalarRow13151.grid parameters (caps repair13151) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13151 grid_top_bounds13151 repair13151

noncomputable def covarianceEvent13151 : Set (AgFam 13151) :=
  BstLean.Part263.covarianceEvent 13151 scalarRow13151.grid parameters

theorem covarianceEvent13151_measurable : MeasurableSet covarianceEvent13151 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13151_payment :
    (retDist (paperDesignP 13151).toCentres).real
      (agentEv (paperDesignP 13151) covarianceEvent13151)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13151

theorem localCov13151 : BstLean.Part259.LocalCovarianceOn covarianceEvent13151
    (BstLean.Part263.cell scalarRow13151.grid) (caps repair13151) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13151

theorem covarianceGood13151_payment :
    (retDist (paperDesignP 13151).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13151)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13151_payment



end BstLean.Part269.N13151

namespace BstLean.Part269.N13151
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13151}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13151.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13151) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13151).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13151 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13151) (by norm_num) BstLean.Part268.WorldRow13151.worldPackage rfl
    BstLean.Part268.WorldRow13151.product_lower (BstLean.Part268.WorldRow13151.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13151} (hw : c ∈ Hof BstLean.Part268.WorldRow13151.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13151) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13151) (by norm_num) BstLean.Part268.WorldRow13151.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13151} (hw : c ∈ Hof BstLean.Part268.WorldRow13151.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13151) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13151).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13151) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13151_eq : scalarRow13151.targetFrame = BstLean.Part268.agent13151.frame := by
  norm_num [scalarRow13151,BstLean.Part268.agent13151]

noncomputable def frameData13151 : BstLean.Part264b.FrameData 13151 :=
  BstLean.Part269.frameData_from_numerics (n := 13151) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13151.worldPackage rfl BstLean.Part268.WorldRow13151.product_lower (BstLean.Part268.WorldRow13151.producthi.2.trans (by norm_num))
    scalarRow13151 repair13151 covarianceInputs13151 (fun i hi => sourceNumerics13151 hi)
    BstLean.Part268.agent13151.frame targetFrame13151_eq


end BstLean.Part269.N13151

namespace BstLean.Part269.N13152
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13152 : scalarRow13152.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13152, BstLean.Part268.grid13152, BstLean.Part263.worldGrid]

theorem supplies13152 (j : Fin 43) : Supply 13152 (parameters j)
    (cellLower scalarRow13152.grid (sourceIndex j))
    (cellUpper scalarRow13152.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13152.grid grid_top_bounds13152 j

theorem radii13152 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13152.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13152 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13152 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13152.grid grid_top_bounds13152 j hθ

noncomputable def covarianceInputs13152 :
    BstLean.Part263.CovarianceInputs 13152 scalarRow13152.grid parameters (caps repair13152) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13152 grid_top_bounds13152 repair13152

noncomputable def covarianceEvent13152 : Set (AgFam 13152) :=
  BstLean.Part263.covarianceEvent 13152 scalarRow13152.grid parameters

theorem covarianceEvent13152_measurable : MeasurableSet covarianceEvent13152 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13152_payment :
    (retDist (paperDesignP 13152).toCentres).real
      (agentEv (paperDesignP 13152) covarianceEvent13152)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13152

theorem localCov13152 : BstLean.Part259.LocalCovarianceOn covarianceEvent13152
    (BstLean.Part263.cell scalarRow13152.grid) (caps repair13152) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13152

theorem covarianceGood13152_payment :
    (retDist (paperDesignP 13152).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13152)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13152_payment



end BstLean.Part269.N13152

namespace BstLean.Part269.N13152
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13152}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13152.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13152) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13152).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13152 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13152) (by norm_num) BstLean.Part268.WorldRow13152.worldPackage rfl
    BstLean.Part268.WorldRow13152.product_lower (BstLean.Part268.WorldRow13152.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13152} (hw : c ∈ Hof BstLean.Part268.WorldRow13152.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13152) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13152) (by norm_num) BstLean.Part268.WorldRow13152.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13152} (hw : c ∈ Hof BstLean.Part268.WorldRow13152.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13152) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13152).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13152) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13152_eq : scalarRow13152.targetFrame = BstLean.Part268.agent13152.frame := by
  norm_num [scalarRow13152,BstLean.Part268.agent13152]

noncomputable def frameData13152 : BstLean.Part264b.FrameData 13152 :=
  BstLean.Part269.frameData_from_numerics (n := 13152) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13152.worldPackage rfl BstLean.Part268.WorldRow13152.product_lower (BstLean.Part268.WorldRow13152.producthi.2.trans (by norm_num))
    scalarRow13152 repair13152 covarianceInputs13152 (fun i hi => sourceNumerics13152 hi)
    BstLean.Part268.agent13152.frame targetFrame13152_eq


end BstLean.Part269.N13152

namespace BstLean.Part269.N13153
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13153 : scalarRow13153.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13153, BstLean.Part268.grid13153, BstLean.Part263.worldGrid]

theorem supplies13153 (j : Fin 43) : Supply 13153 (parameters j)
    (cellLower scalarRow13153.grid (sourceIndex j))
    (cellUpper scalarRow13153.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13153.grid grid_top_bounds13153 j

theorem radii13153 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13153.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13153 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13153 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13153.grid grid_top_bounds13153 j hθ

noncomputable def covarianceInputs13153 :
    BstLean.Part263.CovarianceInputs 13153 scalarRow13153.grid parameters (caps repair13153) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13153 grid_top_bounds13153 repair13153

noncomputable def covarianceEvent13153 : Set (AgFam 13153) :=
  BstLean.Part263.covarianceEvent 13153 scalarRow13153.grid parameters

theorem covarianceEvent13153_measurable : MeasurableSet covarianceEvent13153 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13153_payment :
    (retDist (paperDesignP 13153).toCentres).real
      (agentEv (paperDesignP 13153) covarianceEvent13153)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13153

theorem localCov13153 : BstLean.Part259.LocalCovarianceOn covarianceEvent13153
    (BstLean.Part263.cell scalarRow13153.grid) (caps repair13153) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13153

theorem covarianceGood13153_payment :
    (retDist (paperDesignP 13153).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13153)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13153_payment



end BstLean.Part269.N13153

namespace BstLean.Part269.N13153
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13153}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13153.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13153) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13153).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13153 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13153) (by norm_num) BstLean.Part268.WorldRow13153.worldPackage rfl
    BstLean.Part268.WorldRow13153.product_lower (BstLean.Part268.WorldRow13153.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13153} (hw : c ∈ Hof BstLean.Part268.WorldRow13153.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13153) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13153) (by norm_num) BstLean.Part268.WorldRow13153.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13153} (hw : c ∈ Hof BstLean.Part268.WorldRow13153.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13153) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13153).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13153) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13153_eq : scalarRow13153.targetFrame = BstLean.Part268.agent13153.frame := by
  norm_num [scalarRow13153,BstLean.Part268.agent13153]

noncomputable def frameData13153 : BstLean.Part264b.FrameData 13153 :=
  BstLean.Part269.frameData_from_numerics (n := 13153) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13153.worldPackage rfl BstLean.Part268.WorldRow13153.product_lower (BstLean.Part268.WorldRow13153.producthi.2.trans (by norm_num))
    scalarRow13153 repair13153 covarianceInputs13153 (fun i hi => sourceNumerics13153 hi)
    BstLean.Part268.agent13153.frame targetFrame13153_eq


end BstLean.Part269.N13153

namespace BstLean.Part269.N13154
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13154 : scalarRow13154.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13154, BstLean.Part268.grid13154, BstLean.Part263.worldGrid]

theorem supplies13154 (j : Fin 43) : Supply 13154 (parameters j)
    (cellLower scalarRow13154.grid (sourceIndex j))
    (cellUpper scalarRow13154.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13154.grid grid_top_bounds13154 j

theorem radii13154 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13154.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13154 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13154 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13154.grid grid_top_bounds13154 j hθ

noncomputable def covarianceInputs13154 :
    BstLean.Part263.CovarianceInputs 13154 scalarRow13154.grid parameters (caps repair13154) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13154 grid_top_bounds13154 repair13154

noncomputable def covarianceEvent13154 : Set (AgFam 13154) :=
  BstLean.Part263.covarianceEvent 13154 scalarRow13154.grid parameters

theorem covarianceEvent13154_measurable : MeasurableSet covarianceEvent13154 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13154_payment :
    (retDist (paperDesignP 13154).toCentres).real
      (agentEv (paperDesignP 13154) covarianceEvent13154)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13154

theorem localCov13154 : BstLean.Part259.LocalCovarianceOn covarianceEvent13154
    (BstLean.Part263.cell scalarRow13154.grid) (caps repair13154) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13154

theorem covarianceGood13154_payment :
    (retDist (paperDesignP 13154).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13154)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13154_payment



end BstLean.Part269.N13154

namespace BstLean.Part269.N13154
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13154}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13154.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13154) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13154).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13154 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13154) (by norm_num) BstLean.Part268.WorldRow13154.worldPackage rfl
    BstLean.Part268.WorldRow13154.product_lower (BstLean.Part268.WorldRow13154.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13154} (hw : c ∈ Hof BstLean.Part268.WorldRow13154.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13154) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13154) (by norm_num) BstLean.Part268.WorldRow13154.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13154} (hw : c ∈ Hof BstLean.Part268.WorldRow13154.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13154) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13154).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13154) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13154_eq : scalarRow13154.targetFrame = BstLean.Part268.agent13154.frame := by
  norm_num [scalarRow13154,BstLean.Part268.agent13154]

noncomputable def frameData13154 : BstLean.Part264b.FrameData 13154 :=
  BstLean.Part269.frameData_from_numerics (n := 13154) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13154.worldPackage rfl BstLean.Part268.WorldRow13154.product_lower (BstLean.Part268.WorldRow13154.producthi.2.trans (by norm_num))
    scalarRow13154 repair13154 covarianceInputs13154 (fun i hi => sourceNumerics13154 hi)
    BstLean.Part268.agent13154.frame targetFrame13154_eq


end BstLean.Part269.N13154
