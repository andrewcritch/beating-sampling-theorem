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

namespace BstLean.Part269.N13160
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13160 : scalarRow13160.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13160, BstLean.Part268.grid13160, BstLean.Part263.worldGrid]

theorem supplies13160 (j : Fin 43) : Supply 13160 (parameters j)
    (cellLower scalarRow13160.grid (sourceIndex j))
    (cellUpper scalarRow13160.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13160.grid grid_top_bounds13160 j

theorem radii13160 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13160.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13160 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13160 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13160.grid grid_top_bounds13160 j hθ

noncomputable def covarianceInputs13160 :
    BstLean.Part263.CovarianceInputs 13160 scalarRow13160.grid parameters (caps repair13160) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13160 grid_top_bounds13160 repair13160

noncomputable def covarianceEvent13160 : Set (AgFam 13160) :=
  BstLean.Part263.covarianceEvent 13160 scalarRow13160.grid parameters

theorem covarianceEvent13160_measurable : MeasurableSet covarianceEvent13160 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13160_payment :
    (retDist (paperDesignP 13160).toCentres).real
      (agentEv (paperDesignP 13160) covarianceEvent13160)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13160

theorem localCov13160 : BstLean.Part259.LocalCovarianceOn covarianceEvent13160
    (BstLean.Part263.cell scalarRow13160.grid) (caps repair13160) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13160

theorem covarianceGood13160_payment :
    (retDist (paperDesignP 13160).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13160)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13160_payment



end BstLean.Part269.N13160

namespace BstLean.Part269.N13160
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13160}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13160.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13160) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13160).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13160 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13160) (by norm_num) BstLean.Part268.WorldRow13160.worldPackage rfl
    BstLean.Part268.WorldRow13160.product_lower (BstLean.Part268.WorldRow13160.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13160} (hw : c ∈ Hof BstLean.Part268.WorldRow13160.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13160) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13160) (by norm_num) BstLean.Part268.WorldRow13160.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13160} (hw : c ∈ Hof BstLean.Part268.WorldRow13160.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13160) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13160).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13160) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13160_eq : scalarRow13160.targetFrame = BstLean.Part268.agent13160.frame := by
  norm_num [scalarRow13160,BstLean.Part268.agent13160]

noncomputable def frameData13160 : BstLean.Part264b.FrameData 13160 :=
  BstLean.Part269.frameData_from_numerics (n := 13160) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13160.worldPackage rfl BstLean.Part268.WorldRow13160.product_lower (BstLean.Part268.WorldRow13160.producthi.2.trans (by norm_num))
    scalarRow13160 repair13160 covarianceInputs13160 (fun i hi => sourceNumerics13160 hi)
    BstLean.Part268.agent13160.frame targetFrame13160_eq


end BstLean.Part269.N13160

namespace BstLean.Part269.N13161
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13161 : scalarRow13161.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13161, BstLean.Part268.grid13161, BstLean.Part263.worldGrid]

theorem supplies13161 (j : Fin 43) : Supply 13161 (parameters j)
    (cellLower scalarRow13161.grid (sourceIndex j))
    (cellUpper scalarRow13161.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13161.grid grid_top_bounds13161 j

theorem radii13161 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13161.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13161 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13161 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13161.grid grid_top_bounds13161 j hθ

noncomputable def covarianceInputs13161 :
    BstLean.Part263.CovarianceInputs 13161 scalarRow13161.grid parameters (caps repair13161) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13161 grid_top_bounds13161 repair13161

noncomputable def covarianceEvent13161 : Set (AgFam 13161) :=
  BstLean.Part263.covarianceEvent 13161 scalarRow13161.grid parameters

theorem covarianceEvent13161_measurable : MeasurableSet covarianceEvent13161 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13161_payment :
    (retDist (paperDesignP 13161).toCentres).real
      (agentEv (paperDesignP 13161) covarianceEvent13161)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13161

theorem localCov13161 : BstLean.Part259.LocalCovarianceOn covarianceEvent13161
    (BstLean.Part263.cell scalarRow13161.grid) (caps repair13161) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13161

theorem covarianceGood13161_payment :
    (retDist (paperDesignP 13161).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13161)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13161_payment



end BstLean.Part269.N13161

namespace BstLean.Part269.N13161
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13161}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13161.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13161) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13161).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13161 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13161) (by norm_num) BstLean.Part268.WorldRow13161.worldPackage rfl
    BstLean.Part268.WorldRow13161.product_lower (BstLean.Part268.WorldRow13161.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13161} (hw : c ∈ Hof BstLean.Part268.WorldRow13161.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13161) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13161) (by norm_num) BstLean.Part268.WorldRow13161.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13161} (hw : c ∈ Hof BstLean.Part268.WorldRow13161.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13161) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13161).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13161) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13161_eq : scalarRow13161.targetFrame = BstLean.Part268.agent13161.frame := by
  norm_num [scalarRow13161,BstLean.Part268.agent13161]

noncomputable def frameData13161 : BstLean.Part264b.FrameData 13161 :=
  BstLean.Part269.frameData_from_numerics (n := 13161) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13161.worldPackage rfl BstLean.Part268.WorldRow13161.product_lower (BstLean.Part268.WorldRow13161.producthi.2.trans (by norm_num))
    scalarRow13161 repair13161 covarianceInputs13161 (fun i hi => sourceNumerics13161 hi)
    BstLean.Part268.agent13161.frame targetFrame13161_eq


end BstLean.Part269.N13161

namespace BstLean.Part269.N13162
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13162 : scalarRow13162.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13162, BstLean.Part268.grid13162, BstLean.Part263.worldGrid]

theorem supplies13162 (j : Fin 43) : Supply 13162 (parameters j)
    (cellLower scalarRow13162.grid (sourceIndex j))
    (cellUpper scalarRow13162.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13162.grid grid_top_bounds13162 j

theorem radii13162 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13162.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13162 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13162 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13162.grid grid_top_bounds13162 j hθ

noncomputable def covarianceInputs13162 :
    BstLean.Part263.CovarianceInputs 13162 scalarRow13162.grid parameters (caps repair13162) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13162 grid_top_bounds13162 repair13162

noncomputable def covarianceEvent13162 : Set (AgFam 13162) :=
  BstLean.Part263.covarianceEvent 13162 scalarRow13162.grid parameters

theorem covarianceEvent13162_measurable : MeasurableSet covarianceEvent13162 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13162_payment :
    (retDist (paperDesignP 13162).toCentres).real
      (agentEv (paperDesignP 13162) covarianceEvent13162)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13162

theorem localCov13162 : BstLean.Part259.LocalCovarianceOn covarianceEvent13162
    (BstLean.Part263.cell scalarRow13162.grid) (caps repair13162) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13162

theorem covarianceGood13162_payment :
    (retDist (paperDesignP 13162).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13162)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13162_payment



end BstLean.Part269.N13162

namespace BstLean.Part269.N13162
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13162}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13162.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13162) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13162).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13162 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13162) (by norm_num) BstLean.Part268.WorldRow13162.worldPackage rfl
    BstLean.Part268.WorldRow13162.product_lower (BstLean.Part268.WorldRow13162.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13162} (hw : c ∈ Hof BstLean.Part268.WorldRow13162.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13162) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13162) (by norm_num) BstLean.Part268.WorldRow13162.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13162} (hw : c ∈ Hof BstLean.Part268.WorldRow13162.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13162) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13162).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13162) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13162_eq : scalarRow13162.targetFrame = BstLean.Part268.agent13162.frame := by
  norm_num [scalarRow13162,BstLean.Part268.agent13162]

noncomputable def frameData13162 : BstLean.Part264b.FrameData 13162 :=
  BstLean.Part269.frameData_from_numerics (n := 13162) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13162.worldPackage rfl BstLean.Part268.WorldRow13162.product_lower (BstLean.Part268.WorldRow13162.producthi.2.trans (by norm_num))
    scalarRow13162 repair13162 covarianceInputs13162 (fun i hi => sourceNumerics13162 hi)
    BstLean.Part268.agent13162.frame targetFrame13162_eq


end BstLean.Part269.N13162

namespace BstLean.Part269.N13163
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13163 : scalarRow13163.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13163, BstLean.Part268.grid13163, BstLean.Part263.worldGrid]

theorem supplies13163 (j : Fin 43) : Supply 13163 (parameters j)
    (cellLower scalarRow13163.grid (sourceIndex j))
    (cellUpper scalarRow13163.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13163.grid grid_top_bounds13163 j

theorem radii13163 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13163.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13163 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13163 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13163.grid grid_top_bounds13163 j hθ

noncomputable def covarianceInputs13163 :
    BstLean.Part263.CovarianceInputs 13163 scalarRow13163.grid parameters (caps repair13163) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13163 grid_top_bounds13163 repair13163

noncomputable def covarianceEvent13163 : Set (AgFam 13163) :=
  BstLean.Part263.covarianceEvent 13163 scalarRow13163.grid parameters

theorem covarianceEvent13163_measurable : MeasurableSet covarianceEvent13163 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13163_payment :
    (retDist (paperDesignP 13163).toCentres).real
      (agentEv (paperDesignP 13163) covarianceEvent13163)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13163

theorem localCov13163 : BstLean.Part259.LocalCovarianceOn covarianceEvent13163
    (BstLean.Part263.cell scalarRow13163.grid) (caps repair13163) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13163

theorem covarianceGood13163_payment :
    (retDist (paperDesignP 13163).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13163)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13163_payment



end BstLean.Part269.N13163

namespace BstLean.Part269.N13163
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13163}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13163.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13163) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13163).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13163 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13163) (by norm_num) BstLean.Part268.WorldRow13163.worldPackage rfl
    BstLean.Part268.WorldRow13163.product_lower (BstLean.Part268.WorldRow13163.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13163} (hw : c ∈ Hof BstLean.Part268.WorldRow13163.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13163) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13163) (by norm_num) BstLean.Part268.WorldRow13163.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13163} (hw : c ∈ Hof BstLean.Part268.WorldRow13163.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13163) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13163).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13163) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13163_eq : scalarRow13163.targetFrame = BstLean.Part268.agent13163.frame := by
  norm_num [scalarRow13163,BstLean.Part268.agent13163]

noncomputable def frameData13163 : BstLean.Part264b.FrameData 13163 :=
  BstLean.Part269.frameData_from_numerics (n := 13163) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13163.worldPackage rfl BstLean.Part268.WorldRow13163.product_lower (BstLean.Part268.WorldRow13163.producthi.2.trans (by norm_num))
    scalarRow13163 repair13163 covarianceInputs13163 (fun i hi => sourceNumerics13163 hi)
    BstLean.Part268.agent13163.frame targetFrame13163_eq


end BstLean.Part269.N13163

namespace BstLean.Part269.N13164
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13164 : scalarRow13164.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13164, BstLean.Part268.grid13164, BstLean.Part263.worldGrid]

theorem supplies13164 (j : Fin 43) : Supply 13164 (parameters j)
    (cellLower scalarRow13164.grid (sourceIndex j))
    (cellUpper scalarRow13164.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13164.grid grid_top_bounds13164 j

theorem radii13164 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13164.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13164 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13164 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13164.grid grid_top_bounds13164 j hθ

noncomputable def covarianceInputs13164 :
    BstLean.Part263.CovarianceInputs 13164 scalarRow13164.grid parameters (caps repair13164) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13164 grid_top_bounds13164 repair13164

noncomputable def covarianceEvent13164 : Set (AgFam 13164) :=
  BstLean.Part263.covarianceEvent 13164 scalarRow13164.grid parameters

theorem covarianceEvent13164_measurable : MeasurableSet covarianceEvent13164 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13164_payment :
    (retDist (paperDesignP 13164).toCentres).real
      (agentEv (paperDesignP 13164) covarianceEvent13164)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13164

theorem localCov13164 : BstLean.Part259.LocalCovarianceOn covarianceEvent13164
    (BstLean.Part263.cell scalarRow13164.grid) (caps repair13164) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13164

theorem covarianceGood13164_payment :
    (retDist (paperDesignP 13164).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13164)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13164_payment



end BstLean.Part269.N13164

namespace BstLean.Part269.N13164
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13164}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13164.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13164) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13164).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13164 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13164) (by norm_num) BstLean.Part268.WorldRow13164.worldPackage rfl
    BstLean.Part268.WorldRow13164.product_lower (BstLean.Part268.WorldRow13164.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13164} (hw : c ∈ Hof BstLean.Part268.WorldRow13164.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13164) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13164) (by norm_num) BstLean.Part268.WorldRow13164.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13164} (hw : c ∈ Hof BstLean.Part268.WorldRow13164.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13164) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13164).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13164) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13164_eq : scalarRow13164.targetFrame = BstLean.Part268.agent13164.frame := by
  norm_num [scalarRow13164,BstLean.Part268.agent13164]

noncomputable def frameData13164 : BstLean.Part264b.FrameData 13164 :=
  BstLean.Part269.frameData_from_numerics (n := 13164) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13164.worldPackage rfl BstLean.Part268.WorldRow13164.product_lower (BstLean.Part268.WorldRow13164.producthi.2.trans (by norm_num))
    scalarRow13164 repair13164 covarianceInputs13164 (fun i hi => sourceNumerics13164 hi)
    BstLean.Part268.agent13164.frame targetFrame13164_eq


end BstLean.Part269.N13164
