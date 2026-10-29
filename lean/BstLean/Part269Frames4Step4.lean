import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World4Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs4
import BstLean.Part269Rows4
import BstLean.Part269Sources4
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12470
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12470 : scalarRow12470.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12470, BstLean.Part268.grid12470, BstLean.Part263.worldGrid]

theorem supplies12470 (j : Fin 43) : Supply 12470 (parameters j)
    (cellLower scalarRow12470.grid (sourceIndex j))
    (cellUpper scalarRow12470.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12470.grid grid_top_bounds12470 j

theorem radii12470 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12470.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12470 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12470 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12470.grid grid_top_bounds12470 j hθ

noncomputable def covarianceInputs12470 :
    BstLean.Part263.CovarianceInputs 12470 scalarRow12470.grid parameters (caps repair12470) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12470 grid_top_bounds12470 repair12470

noncomputable def covarianceEvent12470 : Set (AgFam 12470) :=
  BstLean.Part263.covarianceEvent 12470 scalarRow12470.grid parameters

theorem covarianceEvent12470_measurable : MeasurableSet covarianceEvent12470 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12470_payment :
    (retDist (paperDesignP 12470).toCentres).real
      (agentEv (paperDesignP 12470) covarianceEvent12470)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12470

theorem localCov12470 : BstLean.Part259.LocalCovarianceOn covarianceEvent12470
    (BstLean.Part263.cell scalarRow12470.grid) (caps repair12470) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12470

theorem covarianceGood12470_payment :
    (retDist (paperDesignP 12470).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12470)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12470_payment



end BstLean.Part269.N12470

namespace BstLean.Part269.N12470
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12470}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12470.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12470) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12470).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12470 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12470) (by norm_num) BstLean.Part268.WorldRow12470.worldPackage rfl
    BstLean.Part268.WorldRow12470.product_lower (BstLean.Part268.WorldRow12470.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12470} (hw : c ∈ Hof BstLean.Part268.WorldRow12470.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12470) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12470) (by norm_num) BstLean.Part268.WorldRow12470.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12470} (hw : c ∈ Hof BstLean.Part268.WorldRow12470.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12470) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12470).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12470) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12470_eq : scalarRow12470.targetFrame = BstLean.Part268.agent12470.frame := by
  norm_num [scalarRow12470,BstLean.Part268.agent12470]

noncomputable def frameData12470 : BstLean.Part264b.FrameData 12470 :=
  BstLean.Part269.frameData_from_numerics (n := 12470) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12470.worldPackage rfl BstLean.Part268.WorldRow12470.product_lower (BstLean.Part268.WorldRow12470.producthi.2.trans (by norm_num))
    scalarRow12470 repair12470 covarianceInputs12470 (fun i hi => sourceNumerics12470 hi)
    BstLean.Part268.agent12470.frame targetFrame12470_eq


end BstLean.Part269.N12470

namespace BstLean.Part269.N12471
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12471 : scalarRow12471.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12471, BstLean.Part268.grid12471, BstLean.Part263.worldGrid]

theorem supplies12471 (j : Fin 43) : Supply 12471 (parameters j)
    (cellLower scalarRow12471.grid (sourceIndex j))
    (cellUpper scalarRow12471.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12471.grid grid_top_bounds12471 j

theorem radii12471 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12471.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12471 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12471 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12471.grid grid_top_bounds12471 j hθ

noncomputable def covarianceInputs12471 :
    BstLean.Part263.CovarianceInputs 12471 scalarRow12471.grid parameters (caps repair12471) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12471 grid_top_bounds12471 repair12471

noncomputable def covarianceEvent12471 : Set (AgFam 12471) :=
  BstLean.Part263.covarianceEvent 12471 scalarRow12471.grid parameters

theorem covarianceEvent12471_measurable : MeasurableSet covarianceEvent12471 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12471_payment :
    (retDist (paperDesignP 12471).toCentres).real
      (agentEv (paperDesignP 12471) covarianceEvent12471)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12471

theorem localCov12471 : BstLean.Part259.LocalCovarianceOn covarianceEvent12471
    (BstLean.Part263.cell scalarRow12471.grid) (caps repair12471) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12471

theorem covarianceGood12471_payment :
    (retDist (paperDesignP 12471).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12471)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12471_payment



end BstLean.Part269.N12471

namespace BstLean.Part269.N12471
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12471}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12471.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12471) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12471).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12471 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12471) (by norm_num) BstLean.Part268.WorldRow12471.worldPackage rfl
    BstLean.Part268.WorldRow12471.product_lower (BstLean.Part268.WorldRow12471.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12471} (hw : c ∈ Hof BstLean.Part268.WorldRow12471.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12471) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12471) (by norm_num) BstLean.Part268.WorldRow12471.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12471} (hw : c ∈ Hof BstLean.Part268.WorldRow12471.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12471) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12471).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12471) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12471_eq : scalarRow12471.targetFrame = BstLean.Part268.agent12471.frame := by
  norm_num [scalarRow12471,BstLean.Part268.agent12471]

noncomputable def frameData12471 : BstLean.Part264b.FrameData 12471 :=
  BstLean.Part269.frameData_from_numerics (n := 12471) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12471.worldPackage rfl BstLean.Part268.WorldRow12471.product_lower (BstLean.Part268.WorldRow12471.producthi.2.trans (by norm_num))
    scalarRow12471 repair12471 covarianceInputs12471 (fun i hi => sourceNumerics12471 hi)
    BstLean.Part268.agent12471.frame targetFrame12471_eq


end BstLean.Part269.N12471

namespace BstLean.Part269.N12472
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12472 : scalarRow12472.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12472, BstLean.Part268.grid12472, BstLean.Part263.worldGrid]

theorem supplies12472 (j : Fin 43) : Supply 12472 (parameters j)
    (cellLower scalarRow12472.grid (sourceIndex j))
    (cellUpper scalarRow12472.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12472.grid grid_top_bounds12472 j

theorem radii12472 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12472.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12472 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12472 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12472.grid grid_top_bounds12472 j hθ

noncomputable def covarianceInputs12472 :
    BstLean.Part263.CovarianceInputs 12472 scalarRow12472.grid parameters (caps repair12472) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12472 grid_top_bounds12472 repair12472

noncomputable def covarianceEvent12472 : Set (AgFam 12472) :=
  BstLean.Part263.covarianceEvent 12472 scalarRow12472.grid parameters

theorem covarianceEvent12472_measurable : MeasurableSet covarianceEvent12472 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12472_payment :
    (retDist (paperDesignP 12472).toCentres).real
      (agentEv (paperDesignP 12472) covarianceEvent12472)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12472

theorem localCov12472 : BstLean.Part259.LocalCovarianceOn covarianceEvent12472
    (BstLean.Part263.cell scalarRow12472.grid) (caps repair12472) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12472

theorem covarianceGood12472_payment :
    (retDist (paperDesignP 12472).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12472)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12472_payment



end BstLean.Part269.N12472

namespace BstLean.Part269.N12472
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12472}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12472.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12472) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12472).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12472 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12472) (by norm_num) BstLean.Part268.WorldRow12472.worldPackage rfl
    BstLean.Part268.WorldRow12472.product_lower (BstLean.Part268.WorldRow12472.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12472} (hw : c ∈ Hof BstLean.Part268.WorldRow12472.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12472) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12472) (by norm_num) BstLean.Part268.WorldRow12472.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12472} (hw : c ∈ Hof BstLean.Part268.WorldRow12472.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12472) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12472).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12472) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12472_eq : scalarRow12472.targetFrame = BstLean.Part268.agent12472.frame := by
  norm_num [scalarRow12472,BstLean.Part268.agent12472]

noncomputable def frameData12472 : BstLean.Part264b.FrameData 12472 :=
  BstLean.Part269.frameData_from_numerics (n := 12472) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12472.worldPackage rfl BstLean.Part268.WorldRow12472.product_lower (BstLean.Part268.WorldRow12472.producthi.2.trans (by norm_num))
    scalarRow12472 repair12472 covarianceInputs12472 (fun i hi => sourceNumerics12472 hi)
    BstLean.Part268.agent12472.frame targetFrame12472_eq


end BstLean.Part269.N12472

namespace BstLean.Part269.N12473
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12473 : scalarRow12473.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12473, BstLean.Part268.grid12473, BstLean.Part263.worldGrid]

theorem supplies12473 (j : Fin 43) : Supply 12473 (parameters j)
    (cellLower scalarRow12473.grid (sourceIndex j))
    (cellUpper scalarRow12473.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12473.grid grid_top_bounds12473 j

theorem radii12473 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12473.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12473 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12473 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12473.grid grid_top_bounds12473 j hθ

noncomputable def covarianceInputs12473 :
    BstLean.Part263.CovarianceInputs 12473 scalarRow12473.grid parameters (caps repair12473) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12473 grid_top_bounds12473 repair12473

noncomputable def covarianceEvent12473 : Set (AgFam 12473) :=
  BstLean.Part263.covarianceEvent 12473 scalarRow12473.grid parameters

theorem covarianceEvent12473_measurable : MeasurableSet covarianceEvent12473 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12473_payment :
    (retDist (paperDesignP 12473).toCentres).real
      (agentEv (paperDesignP 12473) covarianceEvent12473)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12473

theorem localCov12473 : BstLean.Part259.LocalCovarianceOn covarianceEvent12473
    (BstLean.Part263.cell scalarRow12473.grid) (caps repair12473) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12473

theorem covarianceGood12473_payment :
    (retDist (paperDesignP 12473).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12473)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12473_payment



end BstLean.Part269.N12473

namespace BstLean.Part269.N12473
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12473}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12473.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12473) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12473).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12473 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12473) (by norm_num) BstLean.Part268.WorldRow12473.worldPackage rfl
    BstLean.Part268.WorldRow12473.product_lower (BstLean.Part268.WorldRow12473.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12473} (hw : c ∈ Hof BstLean.Part268.WorldRow12473.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12473) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12473) (by norm_num) BstLean.Part268.WorldRow12473.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12473} (hw : c ∈ Hof BstLean.Part268.WorldRow12473.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12473) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12473).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12473) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12473_eq : scalarRow12473.targetFrame = BstLean.Part268.agent12473.frame := by
  norm_num [scalarRow12473,BstLean.Part268.agent12473]

noncomputable def frameData12473 : BstLean.Part264b.FrameData 12473 :=
  BstLean.Part269.frameData_from_numerics (n := 12473) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12473.worldPackage rfl BstLean.Part268.WorldRow12473.product_lower (BstLean.Part268.WorldRow12473.producthi.2.trans (by norm_num))
    scalarRow12473 repair12473 covarianceInputs12473 (fun i hi => sourceNumerics12473 hi)
    BstLean.Part268.agent12473.frame targetFrame12473_eq


end BstLean.Part269.N12473

namespace BstLean.Part269.N12474
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12474 : scalarRow12474.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12474, BstLean.Part268.grid12474, BstLean.Part263.worldGrid]

theorem supplies12474 (j : Fin 43) : Supply 12474 (parameters j)
    (cellLower scalarRow12474.grid (sourceIndex j))
    (cellUpper scalarRow12474.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12474.grid grid_top_bounds12474 j

theorem radii12474 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12474.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12474 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12474 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12474.grid grid_top_bounds12474 j hθ

noncomputable def covarianceInputs12474 :
    BstLean.Part263.CovarianceInputs 12474 scalarRow12474.grid parameters (caps repair12474) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12474 grid_top_bounds12474 repair12474

noncomputable def covarianceEvent12474 : Set (AgFam 12474) :=
  BstLean.Part263.covarianceEvent 12474 scalarRow12474.grid parameters

theorem covarianceEvent12474_measurable : MeasurableSet covarianceEvent12474 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12474_payment :
    (retDist (paperDesignP 12474).toCentres).real
      (agentEv (paperDesignP 12474) covarianceEvent12474)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12474

theorem localCov12474 : BstLean.Part259.LocalCovarianceOn covarianceEvent12474
    (BstLean.Part263.cell scalarRow12474.grid) (caps repair12474) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12474

theorem covarianceGood12474_payment :
    (retDist (paperDesignP 12474).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12474)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12474_payment



end BstLean.Part269.N12474

namespace BstLean.Part269.N12474
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12474}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12474.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12474) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12474).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12474 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12474) (by norm_num) BstLean.Part268.WorldRow12474.worldPackage rfl
    BstLean.Part268.WorldRow12474.product_lower (BstLean.Part268.WorldRow12474.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12474} (hw : c ∈ Hof BstLean.Part268.WorldRow12474.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12474) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12474) (by norm_num) BstLean.Part268.WorldRow12474.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12474} (hw : c ∈ Hof BstLean.Part268.WorldRow12474.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12474) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12474).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12474) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12474_eq : scalarRow12474.targetFrame = BstLean.Part268.agent12474.frame := by
  norm_num [scalarRow12474,BstLean.Part268.agent12474]

noncomputable def frameData12474 : BstLean.Part264b.FrameData 12474 :=
  BstLean.Part269.frameData_from_numerics (n := 12474) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12474.worldPackage rfl BstLean.Part268.WorldRow12474.product_lower (BstLean.Part268.WorldRow12474.producthi.2.trans (by norm_num))
    scalarRow12474 repair12474 covarianceInputs12474 (fun i hi => sourceNumerics12474 hi)
    BstLean.Part268.agent12474.frame targetFrame12474_eq


end BstLean.Part269.N12474
