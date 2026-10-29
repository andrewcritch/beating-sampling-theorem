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

namespace BstLean.Part269.N13110
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13110 : scalarRow13110.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13110, BstLean.Part268.grid13110, BstLean.Part263.worldGrid]

theorem supplies13110 (j : Fin 43) : Supply 13110 (parameters j)
    (cellLower scalarRow13110.grid (sourceIndex j))
    (cellUpper scalarRow13110.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13110.grid grid_top_bounds13110 j

theorem radii13110 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13110.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13110 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13110 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13110.grid grid_top_bounds13110 j hθ

noncomputable def covarianceInputs13110 :
    BstLean.Part263.CovarianceInputs 13110 scalarRow13110.grid parameters (caps repair13110) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13110 grid_top_bounds13110 repair13110

noncomputable def covarianceEvent13110 : Set (AgFam 13110) :=
  BstLean.Part263.covarianceEvent 13110 scalarRow13110.grid parameters

theorem covarianceEvent13110_measurable : MeasurableSet covarianceEvent13110 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13110_payment :
    (retDist (paperDesignP 13110).toCentres).real
      (agentEv (paperDesignP 13110) covarianceEvent13110)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13110

theorem localCov13110 : BstLean.Part259.LocalCovarianceOn covarianceEvent13110
    (BstLean.Part263.cell scalarRow13110.grid) (caps repair13110) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13110

theorem covarianceGood13110_payment :
    (retDist (paperDesignP 13110).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13110)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13110_payment



end BstLean.Part269.N13110

namespace BstLean.Part269.N13110
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13110}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13110.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13110) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13110).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13110 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13110) (by norm_num) BstLean.Part268.WorldRow13110.worldPackage rfl
    BstLean.Part268.WorldRow13110.product_lower (BstLean.Part268.WorldRow13110.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13110} (hw : c ∈ Hof BstLean.Part268.WorldRow13110.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13110) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13110) (by norm_num) BstLean.Part268.WorldRow13110.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13110} (hw : c ∈ Hof BstLean.Part268.WorldRow13110.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13110) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13110).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13110) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13110_eq : scalarRow13110.targetFrame = BstLean.Part268.agent13110.frame := by
  norm_num [scalarRow13110,BstLean.Part268.agent13110]

noncomputable def frameData13110 : BstLean.Part264b.FrameData 13110 :=
  BstLean.Part269.frameData_from_numerics (n := 13110) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13110.worldPackage rfl BstLean.Part268.WorldRow13110.product_lower (BstLean.Part268.WorldRow13110.producthi.2.trans (by norm_num))
    scalarRow13110 repair13110 covarianceInputs13110 (fun i hi => sourceNumerics13110 hi)
    BstLean.Part268.agent13110.frame targetFrame13110_eq


end BstLean.Part269.N13110

namespace BstLean.Part269.N13111
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13111 : scalarRow13111.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13111, BstLean.Part268.grid13111, BstLean.Part263.worldGrid]

theorem supplies13111 (j : Fin 43) : Supply 13111 (parameters j)
    (cellLower scalarRow13111.grid (sourceIndex j))
    (cellUpper scalarRow13111.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13111.grid grid_top_bounds13111 j

theorem radii13111 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13111.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13111 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13111 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13111.grid grid_top_bounds13111 j hθ

noncomputable def covarianceInputs13111 :
    BstLean.Part263.CovarianceInputs 13111 scalarRow13111.grid parameters (caps repair13111) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13111 grid_top_bounds13111 repair13111

noncomputable def covarianceEvent13111 : Set (AgFam 13111) :=
  BstLean.Part263.covarianceEvent 13111 scalarRow13111.grid parameters

theorem covarianceEvent13111_measurable : MeasurableSet covarianceEvent13111 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13111_payment :
    (retDist (paperDesignP 13111).toCentres).real
      (agentEv (paperDesignP 13111) covarianceEvent13111)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13111

theorem localCov13111 : BstLean.Part259.LocalCovarianceOn covarianceEvent13111
    (BstLean.Part263.cell scalarRow13111.grid) (caps repair13111) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13111

theorem covarianceGood13111_payment :
    (retDist (paperDesignP 13111).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13111)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13111_payment



end BstLean.Part269.N13111

namespace BstLean.Part269.N13111
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13111}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13111.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13111) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13111).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13111 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13111) (by norm_num) BstLean.Part268.WorldRow13111.worldPackage rfl
    BstLean.Part268.WorldRow13111.product_lower (BstLean.Part268.WorldRow13111.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13111} (hw : c ∈ Hof BstLean.Part268.WorldRow13111.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13111) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13111) (by norm_num) BstLean.Part268.WorldRow13111.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13111} (hw : c ∈ Hof BstLean.Part268.WorldRow13111.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13111) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13111).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13111) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13111_eq : scalarRow13111.targetFrame = BstLean.Part268.agent13111.frame := by
  norm_num [scalarRow13111,BstLean.Part268.agent13111]

noncomputable def frameData13111 : BstLean.Part264b.FrameData 13111 :=
  BstLean.Part269.frameData_from_numerics (n := 13111) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13111.worldPackage rfl BstLean.Part268.WorldRow13111.product_lower (BstLean.Part268.WorldRow13111.producthi.2.trans (by norm_num))
    scalarRow13111 repair13111 covarianceInputs13111 (fun i hi => sourceNumerics13111 hi)
    BstLean.Part268.agent13111.frame targetFrame13111_eq


end BstLean.Part269.N13111

namespace BstLean.Part269.N13112
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13112 : scalarRow13112.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13112, BstLean.Part268.grid13112, BstLean.Part263.worldGrid]

theorem supplies13112 (j : Fin 43) : Supply 13112 (parameters j)
    (cellLower scalarRow13112.grid (sourceIndex j))
    (cellUpper scalarRow13112.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13112.grid grid_top_bounds13112 j

theorem radii13112 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13112.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13112 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13112 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13112.grid grid_top_bounds13112 j hθ

noncomputable def covarianceInputs13112 :
    BstLean.Part263.CovarianceInputs 13112 scalarRow13112.grid parameters (caps repair13112) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13112 grid_top_bounds13112 repair13112

noncomputable def covarianceEvent13112 : Set (AgFam 13112) :=
  BstLean.Part263.covarianceEvent 13112 scalarRow13112.grid parameters

theorem covarianceEvent13112_measurable : MeasurableSet covarianceEvent13112 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13112_payment :
    (retDist (paperDesignP 13112).toCentres).real
      (agentEv (paperDesignP 13112) covarianceEvent13112)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13112

theorem localCov13112 : BstLean.Part259.LocalCovarianceOn covarianceEvent13112
    (BstLean.Part263.cell scalarRow13112.grid) (caps repair13112) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13112

theorem covarianceGood13112_payment :
    (retDist (paperDesignP 13112).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13112)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13112_payment



end BstLean.Part269.N13112

namespace BstLean.Part269.N13112
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13112}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13112.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13112) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13112).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13112 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13112) (by norm_num) BstLean.Part268.WorldRow13112.worldPackage rfl
    BstLean.Part268.WorldRow13112.product_lower (BstLean.Part268.WorldRow13112.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13112} (hw : c ∈ Hof BstLean.Part268.WorldRow13112.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13112) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13112) (by norm_num) BstLean.Part268.WorldRow13112.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13112} (hw : c ∈ Hof BstLean.Part268.WorldRow13112.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13112) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13112).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13112) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13112_eq : scalarRow13112.targetFrame = BstLean.Part268.agent13112.frame := by
  norm_num [scalarRow13112,BstLean.Part268.agent13112]

noncomputable def frameData13112 : BstLean.Part264b.FrameData 13112 :=
  BstLean.Part269.frameData_from_numerics (n := 13112) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13112.worldPackage rfl BstLean.Part268.WorldRow13112.product_lower (BstLean.Part268.WorldRow13112.producthi.2.trans (by norm_num))
    scalarRow13112 repair13112 covarianceInputs13112 (fun i hi => sourceNumerics13112 hi)
    BstLean.Part268.agent13112.frame targetFrame13112_eq


end BstLean.Part269.N13112

namespace BstLean.Part269.N13113
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13113 : scalarRow13113.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13113, BstLean.Part268.grid13113, BstLean.Part263.worldGrid]

theorem supplies13113 (j : Fin 43) : Supply 13113 (parameters j)
    (cellLower scalarRow13113.grid (sourceIndex j))
    (cellUpper scalarRow13113.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13113.grid grid_top_bounds13113 j

theorem radii13113 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13113.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13113 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13113 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13113.grid grid_top_bounds13113 j hθ

noncomputable def covarianceInputs13113 :
    BstLean.Part263.CovarianceInputs 13113 scalarRow13113.grid parameters (caps repair13113) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13113 grid_top_bounds13113 repair13113

noncomputable def covarianceEvent13113 : Set (AgFam 13113) :=
  BstLean.Part263.covarianceEvent 13113 scalarRow13113.grid parameters

theorem covarianceEvent13113_measurable : MeasurableSet covarianceEvent13113 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13113_payment :
    (retDist (paperDesignP 13113).toCentres).real
      (agentEv (paperDesignP 13113) covarianceEvent13113)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13113

theorem localCov13113 : BstLean.Part259.LocalCovarianceOn covarianceEvent13113
    (BstLean.Part263.cell scalarRow13113.grid) (caps repair13113) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13113

theorem covarianceGood13113_payment :
    (retDist (paperDesignP 13113).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13113)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13113_payment



end BstLean.Part269.N13113

namespace BstLean.Part269.N13113
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13113}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13113.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13113) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13113).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13113 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13113) (by norm_num) BstLean.Part268.WorldRow13113.worldPackage rfl
    BstLean.Part268.WorldRow13113.product_lower (BstLean.Part268.WorldRow13113.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13113} (hw : c ∈ Hof BstLean.Part268.WorldRow13113.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13113) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13113) (by norm_num) BstLean.Part268.WorldRow13113.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13113} (hw : c ∈ Hof BstLean.Part268.WorldRow13113.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13113) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13113).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13113) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13113_eq : scalarRow13113.targetFrame = BstLean.Part268.agent13113.frame := by
  norm_num [scalarRow13113,BstLean.Part268.agent13113]

noncomputable def frameData13113 : BstLean.Part264b.FrameData 13113 :=
  BstLean.Part269.frameData_from_numerics (n := 13113) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13113.worldPackage rfl BstLean.Part268.WorldRow13113.product_lower (BstLean.Part268.WorldRow13113.producthi.2.trans (by norm_num))
    scalarRow13113 repair13113 covarianceInputs13113 (fun i hi => sourceNumerics13113 hi)
    BstLean.Part268.agent13113.frame targetFrame13113_eq


end BstLean.Part269.N13113

namespace BstLean.Part269.N13114
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13114 : scalarRow13114.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13114, BstLean.Part268.grid13114, BstLean.Part263.worldGrid]

theorem supplies13114 (j : Fin 43) : Supply 13114 (parameters j)
    (cellLower scalarRow13114.grid (sourceIndex j))
    (cellUpper scalarRow13114.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13114.grid grid_top_bounds13114 j

theorem radii13114 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13114.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13114 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13114 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13114.grid grid_top_bounds13114 j hθ

noncomputable def covarianceInputs13114 :
    BstLean.Part263.CovarianceInputs 13114 scalarRow13114.grid parameters (caps repair13114) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13114 grid_top_bounds13114 repair13114

noncomputable def covarianceEvent13114 : Set (AgFam 13114) :=
  BstLean.Part263.covarianceEvent 13114 scalarRow13114.grid parameters

theorem covarianceEvent13114_measurable : MeasurableSet covarianceEvent13114 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13114_payment :
    (retDist (paperDesignP 13114).toCentres).real
      (agentEv (paperDesignP 13114) covarianceEvent13114)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13114

theorem localCov13114 : BstLean.Part259.LocalCovarianceOn covarianceEvent13114
    (BstLean.Part263.cell scalarRow13114.grid) (caps repair13114) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13114

theorem covarianceGood13114_payment :
    (retDist (paperDesignP 13114).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13114)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13114_payment



end BstLean.Part269.N13114

namespace BstLean.Part269.N13114
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13114}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13114.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13114) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13114).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13114 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13114) (by norm_num) BstLean.Part268.WorldRow13114.worldPackage rfl
    BstLean.Part268.WorldRow13114.product_lower (BstLean.Part268.WorldRow13114.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13114} (hw : c ∈ Hof BstLean.Part268.WorldRow13114.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13114) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13114) (by norm_num) BstLean.Part268.WorldRow13114.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13114} (hw : c ∈ Hof BstLean.Part268.WorldRow13114.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13114) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13114).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13114) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13114_eq : scalarRow13114.targetFrame = BstLean.Part268.agent13114.frame := by
  norm_num [scalarRow13114,BstLean.Part268.agent13114]

noncomputable def frameData13114 : BstLean.Part264b.FrameData 13114 :=
  BstLean.Part269.frameData_from_numerics (n := 13114) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13114.worldPackage rfl BstLean.Part268.WorldRow13114.product_lower (BstLean.Part268.WorldRow13114.producthi.2.trans (by norm_num))
    scalarRow13114 repair13114 covarianceInputs13114 (fun i hi => sourceNumerics13114 hi)
    BstLean.Part268.agent13114.frame targetFrame13114_eq


end BstLean.Part269.N13114
