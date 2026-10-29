import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World34Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269Frame13224
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs34
import BstLean.Part269Rows34
import BstLean.Part269Sources34
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13200
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13200 : scalarRow13200.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13200, BstLean.Part268.grid13200, BstLean.Part263.worldGrid]

theorem supplies13200 (j : Fin 43) : Supply 13200 (parameters j)
    (cellLower scalarRow13200.grid (sourceIndex j))
    (cellUpper scalarRow13200.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13200.grid grid_top_bounds13200 j

theorem radii13200 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13200.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13200 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13200 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13200.grid grid_top_bounds13200 j hθ

noncomputable def covarianceInputs13200 :
    BstLean.Part263.CovarianceInputs 13200 scalarRow13200.grid parameters (caps repair13200) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13200 grid_top_bounds13200 repair13200

noncomputable def covarianceEvent13200 : Set (AgFam 13200) :=
  BstLean.Part263.covarianceEvent 13200 scalarRow13200.grid parameters

theorem covarianceEvent13200_measurable : MeasurableSet covarianceEvent13200 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13200_payment :
    (retDist (paperDesignP 13200).toCentres).real
      (agentEv (paperDesignP 13200) covarianceEvent13200)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13200

theorem localCov13200 : BstLean.Part259.LocalCovarianceOn covarianceEvent13200
    (BstLean.Part263.cell scalarRow13200.grid) (caps repair13200) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13200

theorem covarianceGood13200_payment :
    (retDist (paperDesignP 13200).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13200)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13200_payment



end BstLean.Part269.N13200

namespace BstLean.Part269.N13200
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13200}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13200.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13200) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13200).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13200 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13200) (by norm_num) BstLean.Part268.WorldRow13200.worldPackage rfl
    BstLean.Part268.WorldRow13200.product_lower (BstLean.Part268.WorldRow13200.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13200} (hw : c ∈ Hof BstLean.Part268.WorldRow13200.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13200) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13200) (by norm_num) BstLean.Part268.WorldRow13200.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13200} (hw : c ∈ Hof BstLean.Part268.WorldRow13200.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13200) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13200).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13200) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13200_eq : scalarRow13200.targetFrame = BstLean.Part268.agent13200.frame := by
  norm_num [scalarRow13200,BstLean.Part268.agent13200]

noncomputable def frameData13200 : BstLean.Part264b.FrameData 13200 :=
  BstLean.Part269.frameData_from_numerics (n := 13200) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13200.worldPackage rfl BstLean.Part268.WorldRow13200.product_lower (BstLean.Part268.WorldRow13200.producthi.2.trans (by norm_num))
    scalarRow13200 repair13200 covarianceInputs13200 (fun i hi => sourceNumerics13200 hi)
    BstLean.Part268.agent13200.frame targetFrame13200_eq


end BstLean.Part269.N13200

namespace BstLean.Part269.N13201
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13201 : scalarRow13201.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13201, BstLean.Part268.grid13201, BstLean.Part263.worldGrid]

theorem supplies13201 (j : Fin 43) : Supply 13201 (parameters j)
    (cellLower scalarRow13201.grid (sourceIndex j))
    (cellUpper scalarRow13201.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13201.grid grid_top_bounds13201 j

theorem radii13201 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13201.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13201 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13201 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13201.grid grid_top_bounds13201 j hθ

noncomputable def covarianceInputs13201 :
    BstLean.Part263.CovarianceInputs 13201 scalarRow13201.grid parameters (caps repair13201) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13201 grid_top_bounds13201 repair13201

noncomputable def covarianceEvent13201 : Set (AgFam 13201) :=
  BstLean.Part263.covarianceEvent 13201 scalarRow13201.grid parameters

theorem covarianceEvent13201_measurable : MeasurableSet covarianceEvent13201 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13201_payment :
    (retDist (paperDesignP 13201).toCentres).real
      (agentEv (paperDesignP 13201) covarianceEvent13201)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13201

theorem localCov13201 : BstLean.Part259.LocalCovarianceOn covarianceEvent13201
    (BstLean.Part263.cell scalarRow13201.grid) (caps repair13201) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13201

theorem covarianceGood13201_payment :
    (retDist (paperDesignP 13201).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13201)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13201_payment



end BstLean.Part269.N13201

namespace BstLean.Part269.N13201
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13201}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13201.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13201) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13201).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13201 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13201) (by norm_num) BstLean.Part268.WorldRow13201.worldPackage rfl
    BstLean.Part268.WorldRow13201.product_lower (BstLean.Part268.WorldRow13201.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13201} (hw : c ∈ Hof BstLean.Part268.WorldRow13201.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13201) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13201) (by norm_num) BstLean.Part268.WorldRow13201.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13201} (hw : c ∈ Hof BstLean.Part268.WorldRow13201.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13201) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13201).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13201) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13201_eq : scalarRow13201.targetFrame = BstLean.Part268.agent13201.frame := by
  norm_num [scalarRow13201,BstLean.Part268.agent13201]

noncomputable def frameData13201 : BstLean.Part264b.FrameData 13201 :=
  BstLean.Part269.frameData_from_numerics (n := 13201) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13201.worldPackage rfl BstLean.Part268.WorldRow13201.product_lower (BstLean.Part268.WorldRow13201.producthi.2.trans (by norm_num))
    scalarRow13201 repair13201 covarianceInputs13201 (fun i hi => sourceNumerics13201 hi)
    BstLean.Part268.agent13201.frame targetFrame13201_eq


end BstLean.Part269.N13201

namespace BstLean.Part269.N13202
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13202 : scalarRow13202.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13202, BstLean.Part268.grid13202, BstLean.Part263.worldGrid]

theorem supplies13202 (j : Fin 43) : Supply 13202 (parameters j)
    (cellLower scalarRow13202.grid (sourceIndex j))
    (cellUpper scalarRow13202.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13202.grid grid_top_bounds13202 j

theorem radii13202 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13202.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13202 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13202 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13202.grid grid_top_bounds13202 j hθ

noncomputable def covarianceInputs13202 :
    BstLean.Part263.CovarianceInputs 13202 scalarRow13202.grid parameters (caps repair13202) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13202 grid_top_bounds13202 repair13202

noncomputable def covarianceEvent13202 : Set (AgFam 13202) :=
  BstLean.Part263.covarianceEvent 13202 scalarRow13202.grid parameters

theorem covarianceEvent13202_measurable : MeasurableSet covarianceEvent13202 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13202_payment :
    (retDist (paperDesignP 13202).toCentres).real
      (agentEv (paperDesignP 13202) covarianceEvent13202)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13202

theorem localCov13202 : BstLean.Part259.LocalCovarianceOn covarianceEvent13202
    (BstLean.Part263.cell scalarRow13202.grid) (caps repair13202) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13202

theorem covarianceGood13202_payment :
    (retDist (paperDesignP 13202).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13202)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13202_payment



end BstLean.Part269.N13202

namespace BstLean.Part269.N13202
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13202}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13202.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13202) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13202).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13202 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13202) (by norm_num) BstLean.Part268.WorldRow13202.worldPackage rfl
    BstLean.Part268.WorldRow13202.product_lower (BstLean.Part268.WorldRow13202.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13202} (hw : c ∈ Hof BstLean.Part268.WorldRow13202.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13202) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13202) (by norm_num) BstLean.Part268.WorldRow13202.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13202} (hw : c ∈ Hof BstLean.Part268.WorldRow13202.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13202) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13202).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13202) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13202_eq : scalarRow13202.targetFrame = BstLean.Part268.agent13202.frame := by
  norm_num [scalarRow13202,BstLean.Part268.agent13202]

noncomputable def frameData13202 : BstLean.Part264b.FrameData 13202 :=
  BstLean.Part269.frameData_from_numerics (n := 13202) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13202.worldPackage rfl BstLean.Part268.WorldRow13202.product_lower (BstLean.Part268.WorldRow13202.producthi.2.trans (by norm_num))
    scalarRow13202 repair13202 covarianceInputs13202 (fun i hi => sourceNumerics13202 hi)
    BstLean.Part268.agent13202.frame targetFrame13202_eq


end BstLean.Part269.N13202

namespace BstLean.Part269.N13203
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13203 : scalarRow13203.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13203, BstLean.Part268.grid13203, BstLean.Part263.worldGrid]

theorem supplies13203 (j : Fin 43) : Supply 13203 (parameters j)
    (cellLower scalarRow13203.grid (sourceIndex j))
    (cellUpper scalarRow13203.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13203.grid grid_top_bounds13203 j

theorem radii13203 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13203.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13203 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13203 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13203.grid grid_top_bounds13203 j hθ

noncomputable def covarianceInputs13203 :
    BstLean.Part263.CovarianceInputs 13203 scalarRow13203.grid parameters (caps repair13203) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13203 grid_top_bounds13203 repair13203

noncomputable def covarianceEvent13203 : Set (AgFam 13203) :=
  BstLean.Part263.covarianceEvent 13203 scalarRow13203.grid parameters

theorem covarianceEvent13203_measurable : MeasurableSet covarianceEvent13203 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13203_payment :
    (retDist (paperDesignP 13203).toCentres).real
      (agentEv (paperDesignP 13203) covarianceEvent13203)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13203

theorem localCov13203 : BstLean.Part259.LocalCovarianceOn covarianceEvent13203
    (BstLean.Part263.cell scalarRow13203.grid) (caps repair13203) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13203

theorem covarianceGood13203_payment :
    (retDist (paperDesignP 13203).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13203)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13203_payment



end BstLean.Part269.N13203

namespace BstLean.Part269.N13203
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13203}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13203.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13203) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13203).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13203 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13203) (by norm_num) BstLean.Part268.WorldRow13203.worldPackage rfl
    BstLean.Part268.WorldRow13203.product_lower (BstLean.Part268.WorldRow13203.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13203} (hw : c ∈ Hof BstLean.Part268.WorldRow13203.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13203) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13203) (by norm_num) BstLean.Part268.WorldRow13203.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13203} (hw : c ∈ Hof BstLean.Part268.WorldRow13203.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13203) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13203).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13203) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13203_eq : scalarRow13203.targetFrame = BstLean.Part268.agent13203.frame := by
  norm_num [scalarRow13203,BstLean.Part268.agent13203]

noncomputable def frameData13203 : BstLean.Part264b.FrameData 13203 :=
  BstLean.Part269.frameData_from_numerics (n := 13203) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13203.worldPackage rfl BstLean.Part268.WorldRow13203.product_lower (BstLean.Part268.WorldRow13203.producthi.2.trans (by norm_num))
    scalarRow13203 repair13203 covarianceInputs13203 (fun i hi => sourceNumerics13203 hi)
    BstLean.Part268.agent13203.frame targetFrame13203_eq


end BstLean.Part269.N13203

namespace BstLean.Part269.N13204
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13204 : scalarRow13204.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13204, BstLean.Part268.grid13204, BstLean.Part263.worldGrid]

theorem supplies13204 (j : Fin 43) : Supply 13204 (parameters j)
    (cellLower scalarRow13204.grid (sourceIndex j))
    (cellUpper scalarRow13204.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13204.grid grid_top_bounds13204 j

theorem radii13204 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13204.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13204 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13204 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13204.grid grid_top_bounds13204 j hθ

noncomputable def covarianceInputs13204 :
    BstLean.Part263.CovarianceInputs 13204 scalarRow13204.grid parameters (caps repair13204) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13204 grid_top_bounds13204 repair13204

noncomputable def covarianceEvent13204 : Set (AgFam 13204) :=
  BstLean.Part263.covarianceEvent 13204 scalarRow13204.grid parameters

theorem covarianceEvent13204_measurable : MeasurableSet covarianceEvent13204 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13204_payment :
    (retDist (paperDesignP 13204).toCentres).real
      (agentEv (paperDesignP 13204) covarianceEvent13204)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13204

theorem localCov13204 : BstLean.Part259.LocalCovarianceOn covarianceEvent13204
    (BstLean.Part263.cell scalarRow13204.grid) (caps repair13204) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13204

theorem covarianceGood13204_payment :
    (retDist (paperDesignP 13204).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13204)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13204_payment



end BstLean.Part269.N13204

namespace BstLean.Part269.N13204
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13204}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13204.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13204) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13204).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13204 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13204) (by norm_num) BstLean.Part268.WorldRow13204.worldPackage rfl
    BstLean.Part268.WorldRow13204.product_lower (BstLean.Part268.WorldRow13204.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13204} (hw : c ∈ Hof BstLean.Part268.WorldRow13204.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13204) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13204) (by norm_num) BstLean.Part268.WorldRow13204.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13204} (hw : c ∈ Hof BstLean.Part268.WorldRow13204.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13204) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13204).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13204) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13204_eq : scalarRow13204.targetFrame = BstLean.Part268.agent13204.frame := by
  norm_num [scalarRow13204,BstLean.Part268.agent13204]

noncomputable def frameData13204 : BstLean.Part264b.FrameData 13204 :=
  BstLean.Part269.frameData_from_numerics (n := 13204) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13204.worldPackage rfl BstLean.Part268.WorldRow13204.product_lower (BstLean.Part268.WorldRow13204.producthi.2.trans (by norm_num))
    scalarRow13204 repair13204 covarianceInputs13204 (fun i hi => sourceNumerics13204 hi)
    BstLean.Part268.agent13204.frame targetFrame13204_eq


end BstLean.Part269.N13204
