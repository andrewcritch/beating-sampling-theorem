import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World28Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs28
import BstLean.Part269Rows28
import BstLean.Part269Sources28
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13070
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13070 : scalarRow13070.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13070, BstLean.Part268.grid13070, BstLean.Part263.worldGrid]

theorem supplies13070 (j : Fin 43) : Supply 13070 (parameters j)
    (cellLower scalarRow13070.grid (sourceIndex j))
    (cellUpper scalarRow13070.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13070.grid grid_top_bounds13070 j

theorem radii13070 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13070.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13070 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13070 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13070.grid grid_top_bounds13070 j hθ

noncomputable def covarianceInputs13070 :
    BstLean.Part263.CovarianceInputs 13070 scalarRow13070.grid parameters (caps repair13070) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13070 grid_top_bounds13070 repair13070

noncomputable def covarianceEvent13070 : Set (AgFam 13070) :=
  BstLean.Part263.covarianceEvent 13070 scalarRow13070.grid parameters

theorem covarianceEvent13070_measurable : MeasurableSet covarianceEvent13070 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13070_payment :
    (retDist (paperDesignP 13070).toCentres).real
      (agentEv (paperDesignP 13070) covarianceEvent13070)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13070

theorem localCov13070 : BstLean.Part259.LocalCovarianceOn covarianceEvent13070
    (BstLean.Part263.cell scalarRow13070.grid) (caps repair13070) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13070

theorem covarianceGood13070_payment :
    (retDist (paperDesignP 13070).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13070)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13070_payment



end BstLean.Part269.N13070

namespace BstLean.Part269.N13070
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13070}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13070.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13070) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13070).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13070 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13070) (by norm_num) BstLean.Part268.WorldRow13070.worldPackage rfl
    BstLean.Part268.WorldRow13070.product_lower (BstLean.Part268.WorldRow13070.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13070} (hw : c ∈ Hof BstLean.Part268.WorldRow13070.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13070) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13070) (by norm_num) BstLean.Part268.WorldRow13070.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13070} (hw : c ∈ Hof BstLean.Part268.WorldRow13070.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13070) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13070).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13070) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13070_eq : scalarRow13070.targetFrame = BstLean.Part268.agent13070.frame := by
  norm_num [scalarRow13070,BstLean.Part268.agent13070]

noncomputable def frameData13070 : BstLean.Part264b.FrameData 13070 :=
  BstLean.Part269.frameData_from_numerics (n := 13070) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13070.worldPackage rfl BstLean.Part268.WorldRow13070.product_lower (BstLean.Part268.WorldRow13070.producthi.2.trans (by norm_num))
    scalarRow13070 repair13070 covarianceInputs13070 (fun i hi => sourceNumerics13070 hi)
    BstLean.Part268.agent13070.frame targetFrame13070_eq


end BstLean.Part269.N13070

namespace BstLean.Part269.N13071
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13071 : scalarRow13071.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13071, BstLean.Part268.grid13071, BstLean.Part263.worldGrid]

theorem supplies13071 (j : Fin 43) : Supply 13071 (parameters j)
    (cellLower scalarRow13071.grid (sourceIndex j))
    (cellUpper scalarRow13071.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13071.grid grid_top_bounds13071 j

theorem radii13071 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13071.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13071 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13071 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13071.grid grid_top_bounds13071 j hθ

noncomputable def covarianceInputs13071 :
    BstLean.Part263.CovarianceInputs 13071 scalarRow13071.grid parameters (caps repair13071) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13071 grid_top_bounds13071 repair13071

noncomputable def covarianceEvent13071 : Set (AgFam 13071) :=
  BstLean.Part263.covarianceEvent 13071 scalarRow13071.grid parameters

theorem covarianceEvent13071_measurable : MeasurableSet covarianceEvent13071 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13071_payment :
    (retDist (paperDesignP 13071).toCentres).real
      (agentEv (paperDesignP 13071) covarianceEvent13071)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13071

theorem localCov13071 : BstLean.Part259.LocalCovarianceOn covarianceEvent13071
    (BstLean.Part263.cell scalarRow13071.grid) (caps repair13071) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13071

theorem covarianceGood13071_payment :
    (retDist (paperDesignP 13071).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13071)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13071_payment



end BstLean.Part269.N13071

namespace BstLean.Part269.N13071
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13071}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13071.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13071) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13071).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13071 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13071) (by norm_num) BstLean.Part268.WorldRow13071.worldPackage rfl
    BstLean.Part268.WorldRow13071.product_lower (BstLean.Part268.WorldRow13071.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13071} (hw : c ∈ Hof BstLean.Part268.WorldRow13071.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13071) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13071) (by norm_num) BstLean.Part268.WorldRow13071.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13071} (hw : c ∈ Hof BstLean.Part268.WorldRow13071.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13071) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13071).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13071) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13071_eq : scalarRow13071.targetFrame = BstLean.Part268.agent13071.frame := by
  norm_num [scalarRow13071,BstLean.Part268.agent13071]

noncomputable def frameData13071 : BstLean.Part264b.FrameData 13071 :=
  BstLean.Part269.frameData_from_numerics (n := 13071) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13071.worldPackage rfl BstLean.Part268.WorldRow13071.product_lower (BstLean.Part268.WorldRow13071.producthi.2.trans (by norm_num))
    scalarRow13071 repair13071 covarianceInputs13071 (fun i hi => sourceNumerics13071 hi)
    BstLean.Part268.agent13071.frame targetFrame13071_eq


end BstLean.Part269.N13071

namespace BstLean.Part269.N13072
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13072 : scalarRow13072.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13072, BstLean.Part268.grid13072, BstLean.Part263.worldGrid]

theorem supplies13072 (j : Fin 43) : Supply 13072 (parameters j)
    (cellLower scalarRow13072.grid (sourceIndex j))
    (cellUpper scalarRow13072.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13072.grid grid_top_bounds13072 j

theorem radii13072 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13072.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13072 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13072 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13072.grid grid_top_bounds13072 j hθ

noncomputable def covarianceInputs13072 :
    BstLean.Part263.CovarianceInputs 13072 scalarRow13072.grid parameters (caps repair13072) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13072 grid_top_bounds13072 repair13072

noncomputable def covarianceEvent13072 : Set (AgFam 13072) :=
  BstLean.Part263.covarianceEvent 13072 scalarRow13072.grid parameters

theorem covarianceEvent13072_measurable : MeasurableSet covarianceEvent13072 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13072_payment :
    (retDist (paperDesignP 13072).toCentres).real
      (agentEv (paperDesignP 13072) covarianceEvent13072)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13072

theorem localCov13072 : BstLean.Part259.LocalCovarianceOn covarianceEvent13072
    (BstLean.Part263.cell scalarRow13072.grid) (caps repair13072) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13072

theorem covarianceGood13072_payment :
    (retDist (paperDesignP 13072).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13072)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13072_payment



end BstLean.Part269.N13072

namespace BstLean.Part269.N13072
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13072}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13072.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13072) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13072).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13072 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13072) (by norm_num) BstLean.Part268.WorldRow13072.worldPackage rfl
    BstLean.Part268.WorldRow13072.product_lower (BstLean.Part268.WorldRow13072.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13072} (hw : c ∈ Hof BstLean.Part268.WorldRow13072.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13072) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13072) (by norm_num) BstLean.Part268.WorldRow13072.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13072} (hw : c ∈ Hof BstLean.Part268.WorldRow13072.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13072) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13072).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13072) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13072_eq : scalarRow13072.targetFrame = BstLean.Part268.agent13072.frame := by
  norm_num [scalarRow13072,BstLean.Part268.agent13072]

noncomputable def frameData13072 : BstLean.Part264b.FrameData 13072 :=
  BstLean.Part269.frameData_from_numerics (n := 13072) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13072.worldPackage rfl BstLean.Part268.WorldRow13072.product_lower (BstLean.Part268.WorldRow13072.producthi.2.trans (by norm_num))
    scalarRow13072 repair13072 covarianceInputs13072 (fun i hi => sourceNumerics13072 hi)
    BstLean.Part268.agent13072.frame targetFrame13072_eq


end BstLean.Part269.N13072

namespace BstLean.Part269.N13073
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13073 : scalarRow13073.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13073, BstLean.Part268.grid13073, BstLean.Part263.worldGrid]

theorem supplies13073 (j : Fin 43) : Supply 13073 (parameters j)
    (cellLower scalarRow13073.grid (sourceIndex j))
    (cellUpper scalarRow13073.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13073.grid grid_top_bounds13073 j

theorem radii13073 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13073.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13073 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13073 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13073.grid grid_top_bounds13073 j hθ

noncomputable def covarianceInputs13073 :
    BstLean.Part263.CovarianceInputs 13073 scalarRow13073.grid parameters (caps repair13073) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13073 grid_top_bounds13073 repair13073

noncomputable def covarianceEvent13073 : Set (AgFam 13073) :=
  BstLean.Part263.covarianceEvent 13073 scalarRow13073.grid parameters

theorem covarianceEvent13073_measurable : MeasurableSet covarianceEvent13073 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13073_payment :
    (retDist (paperDesignP 13073).toCentres).real
      (agentEv (paperDesignP 13073) covarianceEvent13073)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13073

theorem localCov13073 : BstLean.Part259.LocalCovarianceOn covarianceEvent13073
    (BstLean.Part263.cell scalarRow13073.grid) (caps repair13073) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13073

theorem covarianceGood13073_payment :
    (retDist (paperDesignP 13073).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13073)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13073_payment



end BstLean.Part269.N13073

namespace BstLean.Part269.N13073
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13073}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13073.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13073) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13073).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13073 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13073) (by norm_num) BstLean.Part268.WorldRow13073.worldPackage rfl
    BstLean.Part268.WorldRow13073.product_lower (BstLean.Part268.WorldRow13073.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13073} (hw : c ∈ Hof BstLean.Part268.WorldRow13073.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13073) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13073) (by norm_num) BstLean.Part268.WorldRow13073.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13073} (hw : c ∈ Hof BstLean.Part268.WorldRow13073.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13073) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13073).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13073) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13073_eq : scalarRow13073.targetFrame = BstLean.Part268.agent13073.frame := by
  norm_num [scalarRow13073,BstLean.Part268.agent13073]

noncomputable def frameData13073 : BstLean.Part264b.FrameData 13073 :=
  BstLean.Part269.frameData_from_numerics (n := 13073) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13073.worldPackage rfl BstLean.Part268.WorldRow13073.product_lower (BstLean.Part268.WorldRow13073.producthi.2.trans (by norm_num))
    scalarRow13073 repair13073 covarianceInputs13073 (fun i hi => sourceNumerics13073 hi)
    BstLean.Part268.agent13073.frame targetFrame13073_eq


end BstLean.Part269.N13073

namespace BstLean.Part269.N13074
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13074 : scalarRow13074.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13074, BstLean.Part268.grid13074, BstLean.Part263.worldGrid]

theorem supplies13074 (j : Fin 43) : Supply 13074 (parameters j)
    (cellLower scalarRow13074.grid (sourceIndex j))
    (cellUpper scalarRow13074.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13074.grid grid_top_bounds13074 j

theorem radii13074 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13074.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13074 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13074 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13074.grid grid_top_bounds13074 j hθ

noncomputable def covarianceInputs13074 :
    BstLean.Part263.CovarianceInputs 13074 scalarRow13074.grid parameters (caps repair13074) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13074 grid_top_bounds13074 repair13074

noncomputable def covarianceEvent13074 : Set (AgFam 13074) :=
  BstLean.Part263.covarianceEvent 13074 scalarRow13074.grid parameters

theorem covarianceEvent13074_measurable : MeasurableSet covarianceEvent13074 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13074_payment :
    (retDist (paperDesignP 13074).toCentres).real
      (agentEv (paperDesignP 13074) covarianceEvent13074)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13074

theorem localCov13074 : BstLean.Part259.LocalCovarianceOn covarianceEvent13074
    (BstLean.Part263.cell scalarRow13074.grid) (caps repair13074) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13074

theorem covarianceGood13074_payment :
    (retDist (paperDesignP 13074).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13074)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13074_payment



end BstLean.Part269.N13074

namespace BstLean.Part269.N13074
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13074}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13074.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13074) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13074).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13074 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13074) (by norm_num) BstLean.Part268.WorldRow13074.worldPackage rfl
    BstLean.Part268.WorldRow13074.product_lower (BstLean.Part268.WorldRow13074.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13074} (hw : c ∈ Hof BstLean.Part268.WorldRow13074.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13074) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13074) (by norm_num) BstLean.Part268.WorldRow13074.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13074} (hw : c ∈ Hof BstLean.Part268.WorldRow13074.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13074) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13074).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13074) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13074_eq : scalarRow13074.targetFrame = BstLean.Part268.agent13074.frame := by
  norm_num [scalarRow13074,BstLean.Part268.agent13074]

noncomputable def frameData13074 : BstLean.Part264b.FrameData 13074 :=
  BstLean.Part269.frameData_from_numerics (n := 13074) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13074.worldPackage rfl BstLean.Part268.WorldRow13074.product_lower (BstLean.Part268.WorldRow13074.producthi.2.trans (by norm_num))
    scalarRow13074 repair13074 covarianceInputs13074 (fun i hi => sourceNumerics13074 hi)
    BstLean.Part268.agent13074.frame targetFrame13074_eq


end BstLean.Part269.N13074
