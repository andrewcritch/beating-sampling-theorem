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

namespace BstLean.Part269.N13120
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13120 : scalarRow13120.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13120, BstLean.Part268.grid13120, BstLean.Part263.worldGrid]

theorem supplies13120 (j : Fin 43) : Supply 13120 (parameters j)
    (cellLower scalarRow13120.grid (sourceIndex j))
    (cellUpper scalarRow13120.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13120.grid grid_top_bounds13120 j

theorem radii13120 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13120.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13120 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13120 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13120.grid grid_top_bounds13120 j hθ

noncomputable def covarianceInputs13120 :
    BstLean.Part263.CovarianceInputs 13120 scalarRow13120.grid parameters (caps repair13120) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13120 grid_top_bounds13120 repair13120

noncomputable def covarianceEvent13120 : Set (AgFam 13120) :=
  BstLean.Part263.covarianceEvent 13120 scalarRow13120.grid parameters

theorem covarianceEvent13120_measurable : MeasurableSet covarianceEvent13120 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13120_payment :
    (retDist (paperDesignP 13120).toCentres).real
      (agentEv (paperDesignP 13120) covarianceEvent13120)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13120

theorem localCov13120 : BstLean.Part259.LocalCovarianceOn covarianceEvent13120
    (BstLean.Part263.cell scalarRow13120.grid) (caps repair13120) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13120

theorem covarianceGood13120_payment :
    (retDist (paperDesignP 13120).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13120)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13120_payment



end BstLean.Part269.N13120

namespace BstLean.Part269.N13120
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13120}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13120.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13120) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13120).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13120 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13120) (by norm_num) BstLean.Part268.WorldRow13120.worldPackage rfl
    BstLean.Part268.WorldRow13120.product_lower (BstLean.Part268.WorldRow13120.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13120} (hw : c ∈ Hof BstLean.Part268.WorldRow13120.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13120) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13120) (by norm_num) BstLean.Part268.WorldRow13120.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13120} (hw : c ∈ Hof BstLean.Part268.WorldRow13120.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13120) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13120).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13120) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13120_eq : scalarRow13120.targetFrame = BstLean.Part268.agent13120.frame := by
  norm_num [scalarRow13120,BstLean.Part268.agent13120]

noncomputable def frameData13120 : BstLean.Part264b.FrameData 13120 :=
  BstLean.Part269.frameData_from_numerics (n := 13120) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13120.worldPackage rfl BstLean.Part268.WorldRow13120.product_lower (BstLean.Part268.WorldRow13120.producthi.2.trans (by norm_num))
    scalarRow13120 repair13120 covarianceInputs13120 (fun i hi => sourceNumerics13120 hi)
    BstLean.Part268.agent13120.frame targetFrame13120_eq


end BstLean.Part269.N13120

namespace BstLean.Part269.N13121
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13121 : scalarRow13121.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13121, BstLean.Part268.grid13121, BstLean.Part263.worldGrid]

theorem supplies13121 (j : Fin 43) : Supply 13121 (parameters j)
    (cellLower scalarRow13121.grid (sourceIndex j))
    (cellUpper scalarRow13121.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13121.grid grid_top_bounds13121 j

theorem radii13121 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13121.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13121 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13121 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13121.grid grid_top_bounds13121 j hθ

noncomputable def covarianceInputs13121 :
    BstLean.Part263.CovarianceInputs 13121 scalarRow13121.grid parameters (caps repair13121) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13121 grid_top_bounds13121 repair13121

noncomputable def covarianceEvent13121 : Set (AgFam 13121) :=
  BstLean.Part263.covarianceEvent 13121 scalarRow13121.grid parameters

theorem covarianceEvent13121_measurable : MeasurableSet covarianceEvent13121 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13121_payment :
    (retDist (paperDesignP 13121).toCentres).real
      (agentEv (paperDesignP 13121) covarianceEvent13121)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13121

theorem localCov13121 : BstLean.Part259.LocalCovarianceOn covarianceEvent13121
    (BstLean.Part263.cell scalarRow13121.grid) (caps repair13121) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13121

theorem covarianceGood13121_payment :
    (retDist (paperDesignP 13121).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13121)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13121_payment



end BstLean.Part269.N13121

namespace BstLean.Part269.N13121
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13121}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13121.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13121) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13121).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13121 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13121) (by norm_num) BstLean.Part268.WorldRow13121.worldPackage rfl
    BstLean.Part268.WorldRow13121.product_lower (BstLean.Part268.WorldRow13121.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13121} (hw : c ∈ Hof BstLean.Part268.WorldRow13121.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13121) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13121) (by norm_num) BstLean.Part268.WorldRow13121.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13121} (hw : c ∈ Hof BstLean.Part268.WorldRow13121.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13121) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13121).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13121) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13121_eq : scalarRow13121.targetFrame = BstLean.Part268.agent13121.frame := by
  norm_num [scalarRow13121,BstLean.Part268.agent13121]

noncomputable def frameData13121 : BstLean.Part264b.FrameData 13121 :=
  BstLean.Part269.frameData_from_numerics (n := 13121) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13121.worldPackage rfl BstLean.Part268.WorldRow13121.product_lower (BstLean.Part268.WorldRow13121.producthi.2.trans (by norm_num))
    scalarRow13121 repair13121 covarianceInputs13121 (fun i hi => sourceNumerics13121 hi)
    BstLean.Part268.agent13121.frame targetFrame13121_eq


end BstLean.Part269.N13121

namespace BstLean.Part269.N13122
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13122 : scalarRow13122.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13122, BstLean.Part268.grid13122, BstLean.Part263.worldGrid]

theorem supplies13122 (j : Fin 43) : Supply 13122 (parameters j)
    (cellLower scalarRow13122.grid (sourceIndex j))
    (cellUpper scalarRow13122.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13122.grid grid_top_bounds13122 j

theorem radii13122 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13122.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13122 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13122 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13122.grid grid_top_bounds13122 j hθ

noncomputable def covarianceInputs13122 :
    BstLean.Part263.CovarianceInputs 13122 scalarRow13122.grid parameters (caps repair13122) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13122 grid_top_bounds13122 repair13122

noncomputable def covarianceEvent13122 : Set (AgFam 13122) :=
  BstLean.Part263.covarianceEvent 13122 scalarRow13122.grid parameters

theorem covarianceEvent13122_measurable : MeasurableSet covarianceEvent13122 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13122_payment :
    (retDist (paperDesignP 13122).toCentres).real
      (agentEv (paperDesignP 13122) covarianceEvent13122)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13122

theorem localCov13122 : BstLean.Part259.LocalCovarianceOn covarianceEvent13122
    (BstLean.Part263.cell scalarRow13122.grid) (caps repair13122) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13122

theorem covarianceGood13122_payment :
    (retDist (paperDesignP 13122).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13122)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13122_payment



end BstLean.Part269.N13122

namespace BstLean.Part269.N13122
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13122}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13122.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13122) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13122).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13122 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13122) (by norm_num) BstLean.Part268.WorldRow13122.worldPackage rfl
    BstLean.Part268.WorldRow13122.product_lower (BstLean.Part268.WorldRow13122.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13122} (hw : c ∈ Hof BstLean.Part268.WorldRow13122.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13122) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13122) (by norm_num) BstLean.Part268.WorldRow13122.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13122} (hw : c ∈ Hof BstLean.Part268.WorldRow13122.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13122) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13122).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13122) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13122_eq : scalarRow13122.targetFrame = BstLean.Part268.agent13122.frame := by
  norm_num [scalarRow13122,BstLean.Part268.agent13122]

noncomputable def frameData13122 : BstLean.Part264b.FrameData 13122 :=
  BstLean.Part269.frameData_from_numerics (n := 13122) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13122.worldPackage rfl BstLean.Part268.WorldRow13122.product_lower (BstLean.Part268.WorldRow13122.producthi.2.trans (by norm_num))
    scalarRow13122 repair13122 covarianceInputs13122 (fun i hi => sourceNumerics13122 hi)
    BstLean.Part268.agent13122.frame targetFrame13122_eq


end BstLean.Part269.N13122

namespace BstLean.Part269.N13123
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13123 : scalarRow13123.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13123, BstLean.Part268.grid13123, BstLean.Part263.worldGrid]

theorem supplies13123 (j : Fin 43) : Supply 13123 (parameters j)
    (cellLower scalarRow13123.grid (sourceIndex j))
    (cellUpper scalarRow13123.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13123.grid grid_top_bounds13123 j

theorem radii13123 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13123.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13123 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13123 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13123.grid grid_top_bounds13123 j hθ

noncomputable def covarianceInputs13123 :
    BstLean.Part263.CovarianceInputs 13123 scalarRow13123.grid parameters (caps repair13123) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13123 grid_top_bounds13123 repair13123

noncomputable def covarianceEvent13123 : Set (AgFam 13123) :=
  BstLean.Part263.covarianceEvent 13123 scalarRow13123.grid parameters

theorem covarianceEvent13123_measurable : MeasurableSet covarianceEvent13123 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13123_payment :
    (retDist (paperDesignP 13123).toCentres).real
      (agentEv (paperDesignP 13123) covarianceEvent13123)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13123

theorem localCov13123 : BstLean.Part259.LocalCovarianceOn covarianceEvent13123
    (BstLean.Part263.cell scalarRow13123.grid) (caps repair13123) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13123

theorem covarianceGood13123_payment :
    (retDist (paperDesignP 13123).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13123)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13123_payment



end BstLean.Part269.N13123

namespace BstLean.Part269.N13123
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13123}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13123.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13123) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13123).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13123 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13123) (by norm_num) BstLean.Part268.WorldRow13123.worldPackage rfl
    BstLean.Part268.WorldRow13123.product_lower (BstLean.Part268.WorldRow13123.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13123} (hw : c ∈ Hof BstLean.Part268.WorldRow13123.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13123) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13123) (by norm_num) BstLean.Part268.WorldRow13123.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13123} (hw : c ∈ Hof BstLean.Part268.WorldRow13123.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13123) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13123).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13123) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13123_eq : scalarRow13123.targetFrame = BstLean.Part268.agent13123.frame := by
  norm_num [scalarRow13123,BstLean.Part268.agent13123]

noncomputable def frameData13123 : BstLean.Part264b.FrameData 13123 :=
  BstLean.Part269.frameData_from_numerics (n := 13123) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13123.worldPackage rfl BstLean.Part268.WorldRow13123.product_lower (BstLean.Part268.WorldRow13123.producthi.2.trans (by norm_num))
    scalarRow13123 repair13123 covarianceInputs13123 (fun i hi => sourceNumerics13123 hi)
    BstLean.Part268.agent13123.frame targetFrame13123_eq


end BstLean.Part269.N13123

namespace BstLean.Part269.N13124
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13124 : scalarRow13124.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13124, BstLean.Part268.grid13124, BstLean.Part263.worldGrid]

theorem supplies13124 (j : Fin 43) : Supply 13124 (parameters j)
    (cellLower scalarRow13124.grid (sourceIndex j))
    (cellUpper scalarRow13124.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13124.grid grid_top_bounds13124 j

theorem radii13124 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13124.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13124 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13124 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13124.grid grid_top_bounds13124 j hθ

noncomputable def covarianceInputs13124 :
    BstLean.Part263.CovarianceInputs 13124 scalarRow13124.grid parameters (caps repair13124) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13124 grid_top_bounds13124 repair13124

noncomputable def covarianceEvent13124 : Set (AgFam 13124) :=
  BstLean.Part263.covarianceEvent 13124 scalarRow13124.grid parameters

theorem covarianceEvent13124_measurable : MeasurableSet covarianceEvent13124 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13124_payment :
    (retDist (paperDesignP 13124).toCentres).real
      (agentEv (paperDesignP 13124) covarianceEvent13124)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13124

theorem localCov13124 : BstLean.Part259.LocalCovarianceOn covarianceEvent13124
    (BstLean.Part263.cell scalarRow13124.grid) (caps repair13124) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13124

theorem covarianceGood13124_payment :
    (retDist (paperDesignP 13124).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13124)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13124_payment



end BstLean.Part269.N13124

namespace BstLean.Part269.N13124
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13124}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13124.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13124) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13124).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13124 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13124) (by norm_num) BstLean.Part268.WorldRow13124.worldPackage rfl
    BstLean.Part268.WorldRow13124.product_lower (BstLean.Part268.WorldRow13124.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13124} (hw : c ∈ Hof BstLean.Part268.WorldRow13124.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13124) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13124) (by norm_num) BstLean.Part268.WorldRow13124.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13124} (hw : c ∈ Hof BstLean.Part268.WorldRow13124.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13124) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13124).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13124) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13124_eq : scalarRow13124.targetFrame = BstLean.Part268.agent13124.frame := by
  norm_num [scalarRow13124,BstLean.Part268.agent13124]

noncomputable def frameData13124 : BstLean.Part264b.FrameData 13124 :=
  BstLean.Part269.frameData_from_numerics (n := 13124) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13124.worldPackage rfl BstLean.Part268.WorldRow13124.product_lower (BstLean.Part268.WorldRow13124.producthi.2.trans (by norm_num))
    scalarRow13124 repair13124 covarianceInputs13124 (fun i hi => sourceNumerics13124 hi)
    BstLean.Part268.agent13124.frame targetFrame13124_eq


end BstLean.Part269.N13124
