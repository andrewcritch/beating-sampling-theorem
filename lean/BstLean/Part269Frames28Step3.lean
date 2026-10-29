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

namespace BstLean.Part269.N13065
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13065 : scalarRow13065.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13065, BstLean.Part268.grid13065, BstLean.Part263.worldGrid]

theorem supplies13065 (j : Fin 43) : Supply 13065 (parameters j)
    (cellLower scalarRow13065.grid (sourceIndex j))
    (cellUpper scalarRow13065.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13065.grid grid_top_bounds13065 j

theorem radii13065 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13065.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13065 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13065 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13065.grid grid_top_bounds13065 j hθ

noncomputable def covarianceInputs13065 :
    BstLean.Part263.CovarianceInputs 13065 scalarRow13065.grid parameters (caps repair13065) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13065 grid_top_bounds13065 repair13065

noncomputable def covarianceEvent13065 : Set (AgFam 13065) :=
  BstLean.Part263.covarianceEvent 13065 scalarRow13065.grid parameters

theorem covarianceEvent13065_measurable : MeasurableSet covarianceEvent13065 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13065_payment :
    (retDist (paperDesignP 13065).toCentres).real
      (agentEv (paperDesignP 13065) covarianceEvent13065)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13065

theorem localCov13065 : BstLean.Part259.LocalCovarianceOn covarianceEvent13065
    (BstLean.Part263.cell scalarRow13065.grid) (caps repair13065) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13065

theorem covarianceGood13065_payment :
    (retDist (paperDesignP 13065).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13065)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13065_payment



end BstLean.Part269.N13065

namespace BstLean.Part269.N13065
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13065}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13065.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13065) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13065).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13065 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13065) (by norm_num) BstLean.Part268.WorldRow13065.worldPackage rfl
    BstLean.Part268.WorldRow13065.product_lower (BstLean.Part268.WorldRow13065.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13065} (hw : c ∈ Hof BstLean.Part268.WorldRow13065.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13065) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13065) (by norm_num) BstLean.Part268.WorldRow13065.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13065} (hw : c ∈ Hof BstLean.Part268.WorldRow13065.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13065) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13065).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13065) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13065_eq : scalarRow13065.targetFrame = BstLean.Part268.agent13065.frame := by
  norm_num [scalarRow13065,BstLean.Part268.agent13065]

noncomputable def frameData13065 : BstLean.Part264b.FrameData 13065 :=
  BstLean.Part269.frameData_from_numerics (n := 13065) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13065.worldPackage rfl BstLean.Part268.WorldRow13065.product_lower (BstLean.Part268.WorldRow13065.producthi.2.trans (by norm_num))
    scalarRow13065 repair13065 covarianceInputs13065 (fun i hi => sourceNumerics13065 hi)
    BstLean.Part268.agent13065.frame targetFrame13065_eq


end BstLean.Part269.N13065

namespace BstLean.Part269.N13066
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13066 : scalarRow13066.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13066, BstLean.Part268.grid13066, BstLean.Part263.worldGrid]

theorem supplies13066 (j : Fin 43) : Supply 13066 (parameters j)
    (cellLower scalarRow13066.grid (sourceIndex j))
    (cellUpper scalarRow13066.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13066.grid grid_top_bounds13066 j

theorem radii13066 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13066.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13066 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13066 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13066.grid grid_top_bounds13066 j hθ

noncomputable def covarianceInputs13066 :
    BstLean.Part263.CovarianceInputs 13066 scalarRow13066.grid parameters (caps repair13066) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13066 grid_top_bounds13066 repair13066

noncomputable def covarianceEvent13066 : Set (AgFam 13066) :=
  BstLean.Part263.covarianceEvent 13066 scalarRow13066.grid parameters

theorem covarianceEvent13066_measurable : MeasurableSet covarianceEvent13066 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13066_payment :
    (retDist (paperDesignP 13066).toCentres).real
      (agentEv (paperDesignP 13066) covarianceEvent13066)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13066

theorem localCov13066 : BstLean.Part259.LocalCovarianceOn covarianceEvent13066
    (BstLean.Part263.cell scalarRow13066.grid) (caps repair13066) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13066

theorem covarianceGood13066_payment :
    (retDist (paperDesignP 13066).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13066)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13066_payment



end BstLean.Part269.N13066

namespace BstLean.Part269.N13066
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13066}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13066.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13066) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13066).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13066 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13066) (by norm_num) BstLean.Part268.WorldRow13066.worldPackage rfl
    BstLean.Part268.WorldRow13066.product_lower (BstLean.Part268.WorldRow13066.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13066} (hw : c ∈ Hof BstLean.Part268.WorldRow13066.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13066) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13066) (by norm_num) BstLean.Part268.WorldRow13066.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13066} (hw : c ∈ Hof BstLean.Part268.WorldRow13066.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13066) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13066).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13066) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13066_eq : scalarRow13066.targetFrame = BstLean.Part268.agent13066.frame := by
  norm_num [scalarRow13066,BstLean.Part268.agent13066]

noncomputable def frameData13066 : BstLean.Part264b.FrameData 13066 :=
  BstLean.Part269.frameData_from_numerics (n := 13066) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13066.worldPackage rfl BstLean.Part268.WorldRow13066.product_lower (BstLean.Part268.WorldRow13066.producthi.2.trans (by norm_num))
    scalarRow13066 repair13066 covarianceInputs13066 (fun i hi => sourceNumerics13066 hi)
    BstLean.Part268.agent13066.frame targetFrame13066_eq


end BstLean.Part269.N13066

namespace BstLean.Part269.N13067
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13067 : scalarRow13067.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13067, BstLean.Part268.grid13067, BstLean.Part263.worldGrid]

theorem supplies13067 (j : Fin 43) : Supply 13067 (parameters j)
    (cellLower scalarRow13067.grid (sourceIndex j))
    (cellUpper scalarRow13067.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13067.grid grid_top_bounds13067 j

theorem radii13067 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13067.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13067 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13067 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13067.grid grid_top_bounds13067 j hθ

noncomputable def covarianceInputs13067 :
    BstLean.Part263.CovarianceInputs 13067 scalarRow13067.grid parameters (caps repair13067) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13067 grid_top_bounds13067 repair13067

noncomputable def covarianceEvent13067 : Set (AgFam 13067) :=
  BstLean.Part263.covarianceEvent 13067 scalarRow13067.grid parameters

theorem covarianceEvent13067_measurable : MeasurableSet covarianceEvent13067 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13067_payment :
    (retDist (paperDesignP 13067).toCentres).real
      (agentEv (paperDesignP 13067) covarianceEvent13067)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13067

theorem localCov13067 : BstLean.Part259.LocalCovarianceOn covarianceEvent13067
    (BstLean.Part263.cell scalarRow13067.grid) (caps repair13067) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13067

theorem covarianceGood13067_payment :
    (retDist (paperDesignP 13067).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13067)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13067_payment



end BstLean.Part269.N13067

namespace BstLean.Part269.N13067
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13067}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13067.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13067) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13067).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13067 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13067) (by norm_num) BstLean.Part268.WorldRow13067.worldPackage rfl
    BstLean.Part268.WorldRow13067.product_lower (BstLean.Part268.WorldRow13067.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13067} (hw : c ∈ Hof BstLean.Part268.WorldRow13067.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13067) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13067) (by norm_num) BstLean.Part268.WorldRow13067.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13067} (hw : c ∈ Hof BstLean.Part268.WorldRow13067.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13067) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13067).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13067) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13067_eq : scalarRow13067.targetFrame = BstLean.Part268.agent13067.frame := by
  norm_num [scalarRow13067,BstLean.Part268.agent13067]

noncomputable def frameData13067 : BstLean.Part264b.FrameData 13067 :=
  BstLean.Part269.frameData_from_numerics (n := 13067) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13067.worldPackage rfl BstLean.Part268.WorldRow13067.product_lower (BstLean.Part268.WorldRow13067.producthi.2.trans (by norm_num))
    scalarRow13067 repair13067 covarianceInputs13067 (fun i hi => sourceNumerics13067 hi)
    BstLean.Part268.agent13067.frame targetFrame13067_eq


end BstLean.Part269.N13067

namespace BstLean.Part269.N13068
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13068 : scalarRow13068.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13068, BstLean.Part268.grid13068, BstLean.Part263.worldGrid]

theorem supplies13068 (j : Fin 43) : Supply 13068 (parameters j)
    (cellLower scalarRow13068.grid (sourceIndex j))
    (cellUpper scalarRow13068.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13068.grid grid_top_bounds13068 j

theorem radii13068 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13068.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13068 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13068 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13068.grid grid_top_bounds13068 j hθ

noncomputable def covarianceInputs13068 :
    BstLean.Part263.CovarianceInputs 13068 scalarRow13068.grid parameters (caps repair13068) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13068 grid_top_bounds13068 repair13068

noncomputable def covarianceEvent13068 : Set (AgFam 13068) :=
  BstLean.Part263.covarianceEvent 13068 scalarRow13068.grid parameters

theorem covarianceEvent13068_measurable : MeasurableSet covarianceEvent13068 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13068_payment :
    (retDist (paperDesignP 13068).toCentres).real
      (agentEv (paperDesignP 13068) covarianceEvent13068)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13068

theorem localCov13068 : BstLean.Part259.LocalCovarianceOn covarianceEvent13068
    (BstLean.Part263.cell scalarRow13068.grid) (caps repair13068) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13068

theorem covarianceGood13068_payment :
    (retDist (paperDesignP 13068).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13068)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13068_payment



end BstLean.Part269.N13068

namespace BstLean.Part269.N13068
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13068}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13068.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13068) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13068).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13068 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13068) (by norm_num) BstLean.Part268.WorldRow13068.worldPackage rfl
    BstLean.Part268.WorldRow13068.product_lower (BstLean.Part268.WorldRow13068.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13068} (hw : c ∈ Hof BstLean.Part268.WorldRow13068.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13068) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13068) (by norm_num) BstLean.Part268.WorldRow13068.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13068} (hw : c ∈ Hof BstLean.Part268.WorldRow13068.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13068) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13068).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13068) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13068_eq : scalarRow13068.targetFrame = BstLean.Part268.agent13068.frame := by
  norm_num [scalarRow13068,BstLean.Part268.agent13068]

noncomputable def frameData13068 : BstLean.Part264b.FrameData 13068 :=
  BstLean.Part269.frameData_from_numerics (n := 13068) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13068.worldPackage rfl BstLean.Part268.WorldRow13068.product_lower (BstLean.Part268.WorldRow13068.producthi.2.trans (by norm_num))
    scalarRow13068 repair13068 covarianceInputs13068 (fun i hi => sourceNumerics13068 hi)
    BstLean.Part268.agent13068.frame targetFrame13068_eq


end BstLean.Part269.N13068

namespace BstLean.Part269.N13069
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13069 : scalarRow13069.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13069, BstLean.Part268.grid13069, BstLean.Part263.worldGrid]

theorem supplies13069 (j : Fin 43) : Supply 13069 (parameters j)
    (cellLower scalarRow13069.grid (sourceIndex j))
    (cellUpper scalarRow13069.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13069.grid grid_top_bounds13069 j

theorem radii13069 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13069.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13069 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13069 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13069.grid grid_top_bounds13069 j hθ

noncomputable def covarianceInputs13069 :
    BstLean.Part263.CovarianceInputs 13069 scalarRow13069.grid parameters (caps repair13069) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13069 grid_top_bounds13069 repair13069

noncomputable def covarianceEvent13069 : Set (AgFam 13069) :=
  BstLean.Part263.covarianceEvent 13069 scalarRow13069.grid parameters

theorem covarianceEvent13069_measurable : MeasurableSet covarianceEvent13069 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13069_payment :
    (retDist (paperDesignP 13069).toCentres).real
      (agentEv (paperDesignP 13069) covarianceEvent13069)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13069

theorem localCov13069 : BstLean.Part259.LocalCovarianceOn covarianceEvent13069
    (BstLean.Part263.cell scalarRow13069.grid) (caps repair13069) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13069

theorem covarianceGood13069_payment :
    (retDist (paperDesignP 13069).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13069)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13069_payment



end BstLean.Part269.N13069

namespace BstLean.Part269.N13069
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13069}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13069.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13069) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13069).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13069 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13069) (by norm_num) BstLean.Part268.WorldRow13069.worldPackage rfl
    BstLean.Part268.WorldRow13069.product_lower (BstLean.Part268.WorldRow13069.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13069} (hw : c ∈ Hof BstLean.Part268.WorldRow13069.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13069) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13069) (by norm_num) BstLean.Part268.WorldRow13069.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13069} (hw : c ∈ Hof BstLean.Part268.WorldRow13069.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13069) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13069).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13069) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13069_eq : scalarRow13069.targetFrame = BstLean.Part268.agent13069.frame := by
  norm_num [scalarRow13069,BstLean.Part268.agent13069]

noncomputable def frameData13069 : BstLean.Part264b.FrameData 13069 :=
  BstLean.Part269.frameData_from_numerics (n := 13069) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13069.worldPackage rfl BstLean.Part268.WorldRow13069.product_lower (BstLean.Part268.WorldRow13069.producthi.2.trans (by norm_num))
    scalarRow13069 repair13069 covarianceInputs13069 (fun i hi => sourceNumerics13069 hi)
    BstLean.Part268.agent13069.frame targetFrame13069_eq


end BstLean.Part269.N13069
