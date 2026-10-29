import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World2Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs2
import BstLean.Part269Rows2
import BstLean.Part269Sources2
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12415
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12415 : scalarRow12415.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12415, BstLean.Part268.grid12415, BstLean.Part263.worldGrid]

theorem supplies12415 (j : Fin 43) : Supply 12415 (parameters j)
    (cellLower scalarRow12415.grid (sourceIndex j))
    (cellUpper scalarRow12415.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12415.grid grid_top_bounds12415 j

theorem radii12415 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12415.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12415 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12415 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12415.grid grid_top_bounds12415 j hθ

noncomputable def covarianceInputs12415 :
    BstLean.Part263.CovarianceInputs 12415 scalarRow12415.grid parameters (caps repair12415) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12415 grid_top_bounds12415 repair12415

noncomputable def covarianceEvent12415 : Set (AgFam 12415) :=
  BstLean.Part263.covarianceEvent 12415 scalarRow12415.grid parameters

theorem covarianceEvent12415_measurable : MeasurableSet covarianceEvent12415 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12415_payment :
    (retDist (paperDesignP 12415).toCentres).real
      (agentEv (paperDesignP 12415) covarianceEvent12415)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12415

theorem localCov12415 : BstLean.Part259.LocalCovarianceOn covarianceEvent12415
    (BstLean.Part263.cell scalarRow12415.grid) (caps repair12415) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12415

theorem covarianceGood12415_payment :
    (retDist (paperDesignP 12415).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12415)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12415_payment



end BstLean.Part269.N12415

namespace BstLean.Part269.N12415
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12415}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12415.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12415) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12415).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12415 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12415) (by norm_num) BstLean.Part268.WorldRow12415.worldPackage rfl
    BstLean.Part268.WorldRow12415.product_lower (BstLean.Part268.WorldRow12415.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12415} (hw : c ∈ Hof BstLean.Part268.WorldRow12415.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12415) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12415) (by norm_num) BstLean.Part268.WorldRow12415.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12415} (hw : c ∈ Hof BstLean.Part268.WorldRow12415.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12415) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12415).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12415) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12415_eq : scalarRow12415.targetFrame = BstLean.Part268.agent12415.frame := by
  norm_num [scalarRow12415,BstLean.Part268.agent12415]

noncomputable def frameData12415 : BstLean.Part264b.FrameData 12415 :=
  BstLean.Part269.frameData_from_numerics (n := 12415) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12415.worldPackage rfl BstLean.Part268.WorldRow12415.product_lower (BstLean.Part268.WorldRow12415.producthi.2.trans (by norm_num))
    scalarRow12415 repair12415 covarianceInputs12415 (fun i hi => sourceNumerics12415 hi)
    BstLean.Part268.agent12415.frame targetFrame12415_eq


end BstLean.Part269.N12415

namespace BstLean.Part269.N12416
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12416 : scalarRow12416.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12416, BstLean.Part268.grid12416, BstLean.Part263.worldGrid]

theorem supplies12416 (j : Fin 43) : Supply 12416 (parameters j)
    (cellLower scalarRow12416.grid (sourceIndex j))
    (cellUpper scalarRow12416.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12416.grid grid_top_bounds12416 j

theorem radii12416 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12416.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12416 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12416 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12416.grid grid_top_bounds12416 j hθ

noncomputable def covarianceInputs12416 :
    BstLean.Part263.CovarianceInputs 12416 scalarRow12416.grid parameters (caps repair12416) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12416 grid_top_bounds12416 repair12416

noncomputable def covarianceEvent12416 : Set (AgFam 12416) :=
  BstLean.Part263.covarianceEvent 12416 scalarRow12416.grid parameters

theorem covarianceEvent12416_measurable : MeasurableSet covarianceEvent12416 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12416_payment :
    (retDist (paperDesignP 12416).toCentres).real
      (agentEv (paperDesignP 12416) covarianceEvent12416)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12416

theorem localCov12416 : BstLean.Part259.LocalCovarianceOn covarianceEvent12416
    (BstLean.Part263.cell scalarRow12416.grid) (caps repair12416) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12416

theorem covarianceGood12416_payment :
    (retDist (paperDesignP 12416).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12416)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12416_payment



end BstLean.Part269.N12416

namespace BstLean.Part269.N12416
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12416}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12416.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12416) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12416).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12416 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12416) (by norm_num) BstLean.Part268.WorldRow12416.worldPackage rfl
    BstLean.Part268.WorldRow12416.product_lower (BstLean.Part268.WorldRow12416.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12416} (hw : c ∈ Hof BstLean.Part268.WorldRow12416.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12416) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12416) (by norm_num) BstLean.Part268.WorldRow12416.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12416} (hw : c ∈ Hof BstLean.Part268.WorldRow12416.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12416) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12416).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12416) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12416_eq : scalarRow12416.targetFrame = BstLean.Part268.agent12416.frame := by
  norm_num [scalarRow12416,BstLean.Part268.agent12416]

noncomputable def frameData12416 : BstLean.Part264b.FrameData 12416 :=
  BstLean.Part269.frameData_from_numerics (n := 12416) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12416.worldPackage rfl BstLean.Part268.WorldRow12416.product_lower (BstLean.Part268.WorldRow12416.producthi.2.trans (by norm_num))
    scalarRow12416 repair12416 covarianceInputs12416 (fun i hi => sourceNumerics12416 hi)
    BstLean.Part268.agent12416.frame targetFrame12416_eq


end BstLean.Part269.N12416

namespace BstLean.Part269.N12417
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12417 : scalarRow12417.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12417, BstLean.Part268.grid12417, BstLean.Part263.worldGrid]

theorem supplies12417 (j : Fin 43) : Supply 12417 (parameters j)
    (cellLower scalarRow12417.grid (sourceIndex j))
    (cellUpper scalarRow12417.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12417.grid grid_top_bounds12417 j

theorem radii12417 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12417.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12417 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12417 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12417.grid grid_top_bounds12417 j hθ

noncomputable def covarianceInputs12417 :
    BstLean.Part263.CovarianceInputs 12417 scalarRow12417.grid parameters (caps repair12417) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12417 grid_top_bounds12417 repair12417

noncomputable def covarianceEvent12417 : Set (AgFam 12417) :=
  BstLean.Part263.covarianceEvent 12417 scalarRow12417.grid parameters

theorem covarianceEvent12417_measurable : MeasurableSet covarianceEvent12417 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12417_payment :
    (retDist (paperDesignP 12417).toCentres).real
      (agentEv (paperDesignP 12417) covarianceEvent12417)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12417

theorem localCov12417 : BstLean.Part259.LocalCovarianceOn covarianceEvent12417
    (BstLean.Part263.cell scalarRow12417.grid) (caps repair12417) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12417

theorem covarianceGood12417_payment :
    (retDist (paperDesignP 12417).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12417)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12417_payment



end BstLean.Part269.N12417

namespace BstLean.Part269.N12417
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12417}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12417.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12417) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12417).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12417 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12417) (by norm_num) BstLean.Part268.WorldRow12417.worldPackage rfl
    BstLean.Part268.WorldRow12417.product_lower (BstLean.Part268.WorldRow12417.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12417} (hw : c ∈ Hof BstLean.Part268.WorldRow12417.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12417) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12417) (by norm_num) BstLean.Part268.WorldRow12417.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12417} (hw : c ∈ Hof BstLean.Part268.WorldRow12417.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12417) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12417).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12417) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12417_eq : scalarRow12417.targetFrame = BstLean.Part268.agent12417.frame := by
  norm_num [scalarRow12417,BstLean.Part268.agent12417]

noncomputable def frameData12417 : BstLean.Part264b.FrameData 12417 :=
  BstLean.Part269.frameData_from_numerics (n := 12417) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12417.worldPackage rfl BstLean.Part268.WorldRow12417.product_lower (BstLean.Part268.WorldRow12417.producthi.2.trans (by norm_num))
    scalarRow12417 repair12417 covarianceInputs12417 (fun i hi => sourceNumerics12417 hi)
    BstLean.Part268.agent12417.frame targetFrame12417_eq


end BstLean.Part269.N12417

namespace BstLean.Part269.N12418
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12418 : scalarRow12418.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12418, BstLean.Part268.grid12418, BstLean.Part263.worldGrid]

theorem supplies12418 (j : Fin 43) : Supply 12418 (parameters j)
    (cellLower scalarRow12418.grid (sourceIndex j))
    (cellUpper scalarRow12418.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12418.grid grid_top_bounds12418 j

theorem radii12418 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12418.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12418 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12418 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12418.grid grid_top_bounds12418 j hθ

noncomputable def covarianceInputs12418 :
    BstLean.Part263.CovarianceInputs 12418 scalarRow12418.grid parameters (caps repair12418) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12418 grid_top_bounds12418 repair12418

noncomputable def covarianceEvent12418 : Set (AgFam 12418) :=
  BstLean.Part263.covarianceEvent 12418 scalarRow12418.grid parameters

theorem covarianceEvent12418_measurable : MeasurableSet covarianceEvent12418 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12418_payment :
    (retDist (paperDesignP 12418).toCentres).real
      (agentEv (paperDesignP 12418) covarianceEvent12418)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12418

theorem localCov12418 : BstLean.Part259.LocalCovarianceOn covarianceEvent12418
    (BstLean.Part263.cell scalarRow12418.grid) (caps repair12418) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12418

theorem covarianceGood12418_payment :
    (retDist (paperDesignP 12418).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12418)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12418_payment



end BstLean.Part269.N12418

namespace BstLean.Part269.N12418
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12418}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12418.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12418) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12418).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12418 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12418) (by norm_num) BstLean.Part268.WorldRow12418.worldPackage rfl
    BstLean.Part268.WorldRow12418.product_lower (BstLean.Part268.WorldRow12418.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12418} (hw : c ∈ Hof BstLean.Part268.WorldRow12418.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12418) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12418) (by norm_num) BstLean.Part268.WorldRow12418.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12418} (hw : c ∈ Hof BstLean.Part268.WorldRow12418.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12418) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12418).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12418) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12418_eq : scalarRow12418.targetFrame = BstLean.Part268.agent12418.frame := by
  norm_num [scalarRow12418,BstLean.Part268.agent12418]

noncomputable def frameData12418 : BstLean.Part264b.FrameData 12418 :=
  BstLean.Part269.frameData_from_numerics (n := 12418) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12418.worldPackage rfl BstLean.Part268.WorldRow12418.product_lower (BstLean.Part268.WorldRow12418.producthi.2.trans (by norm_num))
    scalarRow12418 repair12418 covarianceInputs12418 (fun i hi => sourceNumerics12418 hi)
    BstLean.Part268.agent12418.frame targetFrame12418_eq


end BstLean.Part269.N12418

namespace BstLean.Part269.N12419
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12419 : scalarRow12419.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12419, BstLean.Part268.grid12419, BstLean.Part263.worldGrid]

theorem supplies12419 (j : Fin 43) : Supply 12419 (parameters j)
    (cellLower scalarRow12419.grid (sourceIndex j))
    (cellUpper scalarRow12419.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12419.grid grid_top_bounds12419 j

theorem radii12419 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12419.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12419 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12419 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12419.grid grid_top_bounds12419 j hθ

noncomputable def covarianceInputs12419 :
    BstLean.Part263.CovarianceInputs 12419 scalarRow12419.grid parameters (caps repair12419) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12419 grid_top_bounds12419 repair12419

noncomputable def covarianceEvent12419 : Set (AgFam 12419) :=
  BstLean.Part263.covarianceEvent 12419 scalarRow12419.grid parameters

theorem covarianceEvent12419_measurable : MeasurableSet covarianceEvent12419 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12419_payment :
    (retDist (paperDesignP 12419).toCentres).real
      (agentEv (paperDesignP 12419) covarianceEvent12419)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12419

theorem localCov12419 : BstLean.Part259.LocalCovarianceOn covarianceEvent12419
    (BstLean.Part263.cell scalarRow12419.grid) (caps repair12419) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12419

theorem covarianceGood12419_payment :
    (retDist (paperDesignP 12419).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12419)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12419_payment



end BstLean.Part269.N12419

namespace BstLean.Part269.N12419
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12419}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12419.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12419) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12419).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12419 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12419) (by norm_num) BstLean.Part268.WorldRow12419.worldPackage rfl
    BstLean.Part268.WorldRow12419.product_lower (BstLean.Part268.WorldRow12419.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12419} (hw : c ∈ Hof BstLean.Part268.WorldRow12419.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12419) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12419) (by norm_num) BstLean.Part268.WorldRow12419.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12419} (hw : c ∈ Hof BstLean.Part268.WorldRow12419.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12419) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12419).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12419) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12419_eq : scalarRow12419.targetFrame = BstLean.Part268.agent12419.frame := by
  norm_num [scalarRow12419,BstLean.Part268.agent12419]

noncomputable def frameData12419 : BstLean.Part264b.FrameData 12419 :=
  BstLean.Part269.frameData_from_numerics (n := 12419) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12419.worldPackage rfl BstLean.Part268.WorldRow12419.product_lower (BstLean.Part268.WorldRow12419.producthi.2.trans (by norm_num))
    scalarRow12419 repair12419 covarianceInputs12419 (fun i hi => sourceNumerics12419 hi)
    BstLean.Part268.agent12419.frame targetFrame12419_eq


end BstLean.Part269.N12419
