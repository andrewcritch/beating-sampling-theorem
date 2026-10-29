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

namespace BstLean.Part269.N13060
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13060 : scalarRow13060.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13060, BstLean.Part268.grid13060, BstLean.Part263.worldGrid]

theorem supplies13060 (j : Fin 43) : Supply 13060 (parameters j)
    (cellLower scalarRow13060.grid (sourceIndex j))
    (cellUpper scalarRow13060.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13060.grid grid_top_bounds13060 j

theorem radii13060 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13060.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13060 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13060 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13060.grid grid_top_bounds13060 j hθ

noncomputable def covarianceInputs13060 :
    BstLean.Part263.CovarianceInputs 13060 scalarRow13060.grid parameters (caps repair13060) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13060 grid_top_bounds13060 repair13060

noncomputable def covarianceEvent13060 : Set (AgFam 13060) :=
  BstLean.Part263.covarianceEvent 13060 scalarRow13060.grid parameters

theorem covarianceEvent13060_measurable : MeasurableSet covarianceEvent13060 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13060_payment :
    (retDist (paperDesignP 13060).toCentres).real
      (agentEv (paperDesignP 13060) covarianceEvent13060)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13060

theorem localCov13060 : BstLean.Part259.LocalCovarianceOn covarianceEvent13060
    (BstLean.Part263.cell scalarRow13060.grid) (caps repair13060) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13060

theorem covarianceGood13060_payment :
    (retDist (paperDesignP 13060).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13060)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13060_payment



end BstLean.Part269.N13060

namespace BstLean.Part269.N13060
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13060}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13060.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13060) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13060).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13060 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13060) (by norm_num) BstLean.Part268.WorldRow13060.worldPackage rfl
    BstLean.Part268.WorldRow13060.product_lower (BstLean.Part268.WorldRow13060.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13060} (hw : c ∈ Hof BstLean.Part268.WorldRow13060.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13060) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13060) (by norm_num) BstLean.Part268.WorldRow13060.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13060} (hw : c ∈ Hof BstLean.Part268.WorldRow13060.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13060) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13060).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13060) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13060_eq : scalarRow13060.targetFrame = BstLean.Part268.agent13060.frame := by
  norm_num [scalarRow13060,BstLean.Part268.agent13060]

noncomputable def frameData13060 : BstLean.Part264b.FrameData 13060 :=
  BstLean.Part269.frameData_from_numerics (n := 13060) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13060.worldPackage rfl BstLean.Part268.WorldRow13060.product_lower (BstLean.Part268.WorldRow13060.producthi.2.trans (by norm_num))
    scalarRow13060 repair13060 covarianceInputs13060 (fun i hi => sourceNumerics13060 hi)
    BstLean.Part268.agent13060.frame targetFrame13060_eq


end BstLean.Part269.N13060

namespace BstLean.Part269.N13061
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13061 : scalarRow13061.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13061, BstLean.Part268.grid13061, BstLean.Part263.worldGrid]

theorem supplies13061 (j : Fin 43) : Supply 13061 (parameters j)
    (cellLower scalarRow13061.grid (sourceIndex j))
    (cellUpper scalarRow13061.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13061.grid grid_top_bounds13061 j

theorem radii13061 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13061.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13061 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13061 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13061.grid grid_top_bounds13061 j hθ

noncomputable def covarianceInputs13061 :
    BstLean.Part263.CovarianceInputs 13061 scalarRow13061.grid parameters (caps repair13061) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13061 grid_top_bounds13061 repair13061

noncomputable def covarianceEvent13061 : Set (AgFam 13061) :=
  BstLean.Part263.covarianceEvent 13061 scalarRow13061.grid parameters

theorem covarianceEvent13061_measurable : MeasurableSet covarianceEvent13061 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13061_payment :
    (retDist (paperDesignP 13061).toCentres).real
      (agentEv (paperDesignP 13061) covarianceEvent13061)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13061

theorem localCov13061 : BstLean.Part259.LocalCovarianceOn covarianceEvent13061
    (BstLean.Part263.cell scalarRow13061.grid) (caps repair13061) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13061

theorem covarianceGood13061_payment :
    (retDist (paperDesignP 13061).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13061)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13061_payment



end BstLean.Part269.N13061

namespace BstLean.Part269.N13061
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13061}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13061.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13061) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13061).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13061 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13061) (by norm_num) BstLean.Part268.WorldRow13061.worldPackage rfl
    BstLean.Part268.WorldRow13061.product_lower (BstLean.Part268.WorldRow13061.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13061} (hw : c ∈ Hof BstLean.Part268.WorldRow13061.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13061) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13061) (by norm_num) BstLean.Part268.WorldRow13061.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13061} (hw : c ∈ Hof BstLean.Part268.WorldRow13061.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13061) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13061).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13061) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13061_eq : scalarRow13061.targetFrame = BstLean.Part268.agent13061.frame := by
  norm_num [scalarRow13061,BstLean.Part268.agent13061]

noncomputable def frameData13061 : BstLean.Part264b.FrameData 13061 :=
  BstLean.Part269.frameData_from_numerics (n := 13061) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13061.worldPackage rfl BstLean.Part268.WorldRow13061.product_lower (BstLean.Part268.WorldRow13061.producthi.2.trans (by norm_num))
    scalarRow13061 repair13061 covarianceInputs13061 (fun i hi => sourceNumerics13061 hi)
    BstLean.Part268.agent13061.frame targetFrame13061_eq


end BstLean.Part269.N13061

namespace BstLean.Part269.N13062
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13062 : scalarRow13062.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13062, BstLean.Part268.grid13062, BstLean.Part263.worldGrid]

theorem supplies13062 (j : Fin 43) : Supply 13062 (parameters j)
    (cellLower scalarRow13062.grid (sourceIndex j))
    (cellUpper scalarRow13062.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13062.grid grid_top_bounds13062 j

theorem radii13062 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13062.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13062 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13062 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13062.grid grid_top_bounds13062 j hθ

noncomputable def covarianceInputs13062 :
    BstLean.Part263.CovarianceInputs 13062 scalarRow13062.grid parameters (caps repair13062) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13062 grid_top_bounds13062 repair13062

noncomputable def covarianceEvent13062 : Set (AgFam 13062) :=
  BstLean.Part263.covarianceEvent 13062 scalarRow13062.grid parameters

theorem covarianceEvent13062_measurable : MeasurableSet covarianceEvent13062 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13062_payment :
    (retDist (paperDesignP 13062).toCentres).real
      (agentEv (paperDesignP 13062) covarianceEvent13062)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13062

theorem localCov13062 : BstLean.Part259.LocalCovarianceOn covarianceEvent13062
    (BstLean.Part263.cell scalarRow13062.grid) (caps repair13062) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13062

theorem covarianceGood13062_payment :
    (retDist (paperDesignP 13062).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13062)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13062_payment



end BstLean.Part269.N13062

namespace BstLean.Part269.N13062
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13062}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13062.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13062) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13062).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13062 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13062) (by norm_num) BstLean.Part268.WorldRow13062.worldPackage rfl
    BstLean.Part268.WorldRow13062.product_lower (BstLean.Part268.WorldRow13062.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13062} (hw : c ∈ Hof BstLean.Part268.WorldRow13062.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13062) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13062) (by norm_num) BstLean.Part268.WorldRow13062.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13062} (hw : c ∈ Hof BstLean.Part268.WorldRow13062.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13062) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13062).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13062) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13062_eq : scalarRow13062.targetFrame = BstLean.Part268.agent13062.frame := by
  norm_num [scalarRow13062,BstLean.Part268.agent13062]

noncomputable def frameData13062 : BstLean.Part264b.FrameData 13062 :=
  BstLean.Part269.frameData_from_numerics (n := 13062) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13062.worldPackage rfl BstLean.Part268.WorldRow13062.product_lower (BstLean.Part268.WorldRow13062.producthi.2.trans (by norm_num))
    scalarRow13062 repair13062 covarianceInputs13062 (fun i hi => sourceNumerics13062 hi)
    BstLean.Part268.agent13062.frame targetFrame13062_eq


end BstLean.Part269.N13062

namespace BstLean.Part269.N13063
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13063 : scalarRow13063.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13063, BstLean.Part268.grid13063, BstLean.Part263.worldGrid]

theorem supplies13063 (j : Fin 43) : Supply 13063 (parameters j)
    (cellLower scalarRow13063.grid (sourceIndex j))
    (cellUpper scalarRow13063.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13063.grid grid_top_bounds13063 j

theorem radii13063 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13063.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13063 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13063 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13063.grid grid_top_bounds13063 j hθ

noncomputable def covarianceInputs13063 :
    BstLean.Part263.CovarianceInputs 13063 scalarRow13063.grid parameters (caps repair13063) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13063 grid_top_bounds13063 repair13063

noncomputable def covarianceEvent13063 : Set (AgFam 13063) :=
  BstLean.Part263.covarianceEvent 13063 scalarRow13063.grid parameters

theorem covarianceEvent13063_measurable : MeasurableSet covarianceEvent13063 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13063_payment :
    (retDist (paperDesignP 13063).toCentres).real
      (agentEv (paperDesignP 13063) covarianceEvent13063)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13063

theorem localCov13063 : BstLean.Part259.LocalCovarianceOn covarianceEvent13063
    (BstLean.Part263.cell scalarRow13063.grid) (caps repair13063) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13063

theorem covarianceGood13063_payment :
    (retDist (paperDesignP 13063).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13063)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13063_payment



end BstLean.Part269.N13063

namespace BstLean.Part269.N13063
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13063}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13063.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13063) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13063).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13063 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13063) (by norm_num) BstLean.Part268.WorldRow13063.worldPackage rfl
    BstLean.Part268.WorldRow13063.product_lower (BstLean.Part268.WorldRow13063.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13063} (hw : c ∈ Hof BstLean.Part268.WorldRow13063.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13063) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13063) (by norm_num) BstLean.Part268.WorldRow13063.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13063} (hw : c ∈ Hof BstLean.Part268.WorldRow13063.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13063) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13063).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13063) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13063_eq : scalarRow13063.targetFrame = BstLean.Part268.agent13063.frame := by
  norm_num [scalarRow13063,BstLean.Part268.agent13063]

noncomputable def frameData13063 : BstLean.Part264b.FrameData 13063 :=
  BstLean.Part269.frameData_from_numerics (n := 13063) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13063.worldPackage rfl BstLean.Part268.WorldRow13063.product_lower (BstLean.Part268.WorldRow13063.producthi.2.trans (by norm_num))
    scalarRow13063 repair13063 covarianceInputs13063 (fun i hi => sourceNumerics13063 hi)
    BstLean.Part268.agent13063.frame targetFrame13063_eq


end BstLean.Part269.N13063

namespace BstLean.Part269.N13064
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13064 : scalarRow13064.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13064, BstLean.Part268.grid13064, BstLean.Part263.worldGrid]

theorem supplies13064 (j : Fin 43) : Supply 13064 (parameters j)
    (cellLower scalarRow13064.grid (sourceIndex j))
    (cellUpper scalarRow13064.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13064.grid grid_top_bounds13064 j

theorem radii13064 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13064.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13064 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13064 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13064.grid grid_top_bounds13064 j hθ

noncomputable def covarianceInputs13064 :
    BstLean.Part263.CovarianceInputs 13064 scalarRow13064.grid parameters (caps repair13064) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13064 grid_top_bounds13064 repair13064

noncomputable def covarianceEvent13064 : Set (AgFam 13064) :=
  BstLean.Part263.covarianceEvent 13064 scalarRow13064.grid parameters

theorem covarianceEvent13064_measurable : MeasurableSet covarianceEvent13064 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13064_payment :
    (retDist (paperDesignP 13064).toCentres).real
      (agentEv (paperDesignP 13064) covarianceEvent13064)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13064

theorem localCov13064 : BstLean.Part259.LocalCovarianceOn covarianceEvent13064
    (BstLean.Part263.cell scalarRow13064.grid) (caps repair13064) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13064

theorem covarianceGood13064_payment :
    (retDist (paperDesignP 13064).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13064)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13064_payment



end BstLean.Part269.N13064

namespace BstLean.Part269.N13064
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13064}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13064.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13064) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13064).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13064 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13064) (by norm_num) BstLean.Part268.WorldRow13064.worldPackage rfl
    BstLean.Part268.WorldRow13064.product_lower (BstLean.Part268.WorldRow13064.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13064} (hw : c ∈ Hof BstLean.Part268.WorldRow13064.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13064) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13064) (by norm_num) BstLean.Part268.WorldRow13064.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13064} (hw : c ∈ Hof BstLean.Part268.WorldRow13064.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13064) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13064).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13064) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13064_eq : scalarRow13064.targetFrame = BstLean.Part268.agent13064.frame := by
  norm_num [scalarRow13064,BstLean.Part268.agent13064]

noncomputable def frameData13064 : BstLean.Part264b.FrameData 13064 :=
  BstLean.Part269.frameData_from_numerics (n := 13064) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13064.worldPackage rfl BstLean.Part268.WorldRow13064.product_lower (BstLean.Part268.WorldRow13064.producthi.2.trans (by norm_num))
    scalarRow13064 repair13064 covarianceInputs13064 (fun i hi => sourceNumerics13064 hi)
    BstLean.Part268.agent13064.frame targetFrame13064_eq


end BstLean.Part269.N13064
