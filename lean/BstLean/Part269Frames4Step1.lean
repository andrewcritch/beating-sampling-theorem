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

namespace BstLean.Part269.N12455
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12455 : scalarRow12455.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12455, BstLean.Part268.grid12455, BstLean.Part263.worldGrid]

theorem supplies12455 (j : Fin 43) : Supply 12455 (parameters j)
    (cellLower scalarRow12455.grid (sourceIndex j))
    (cellUpper scalarRow12455.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12455.grid grid_top_bounds12455 j

theorem radii12455 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12455.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12455 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12455 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12455.grid grid_top_bounds12455 j hθ

noncomputable def covarianceInputs12455 :
    BstLean.Part263.CovarianceInputs 12455 scalarRow12455.grid parameters (caps repair12455) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12455 grid_top_bounds12455 repair12455

noncomputable def covarianceEvent12455 : Set (AgFam 12455) :=
  BstLean.Part263.covarianceEvent 12455 scalarRow12455.grid parameters

theorem covarianceEvent12455_measurable : MeasurableSet covarianceEvent12455 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12455_payment :
    (retDist (paperDesignP 12455).toCentres).real
      (agentEv (paperDesignP 12455) covarianceEvent12455)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12455

theorem localCov12455 : BstLean.Part259.LocalCovarianceOn covarianceEvent12455
    (BstLean.Part263.cell scalarRow12455.grid) (caps repair12455) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12455

theorem covarianceGood12455_payment :
    (retDist (paperDesignP 12455).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12455)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12455_payment



end BstLean.Part269.N12455

namespace BstLean.Part269.N12455
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12455}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12455.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12455) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12455).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12455 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12455) (by norm_num) BstLean.Part268.WorldRow12455.worldPackage rfl
    BstLean.Part268.WorldRow12455.product_lower (BstLean.Part268.WorldRow12455.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12455} (hw : c ∈ Hof BstLean.Part268.WorldRow12455.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12455) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12455) (by norm_num) BstLean.Part268.WorldRow12455.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12455} (hw : c ∈ Hof BstLean.Part268.WorldRow12455.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12455) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12455).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12455) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12455_eq : scalarRow12455.targetFrame = BstLean.Part268.agent12455.frame := by
  norm_num [scalarRow12455,BstLean.Part268.agent12455]

noncomputable def frameData12455 : BstLean.Part264b.FrameData 12455 :=
  BstLean.Part269.frameData_from_numerics (n := 12455) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12455.worldPackage rfl BstLean.Part268.WorldRow12455.product_lower (BstLean.Part268.WorldRow12455.producthi.2.trans (by norm_num))
    scalarRow12455 repair12455 covarianceInputs12455 (fun i hi => sourceNumerics12455 hi)
    BstLean.Part268.agent12455.frame targetFrame12455_eq


end BstLean.Part269.N12455

namespace BstLean.Part269.N12456
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12456 : scalarRow12456.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12456, BstLean.Part268.grid12456, BstLean.Part263.worldGrid]

theorem supplies12456 (j : Fin 43) : Supply 12456 (parameters j)
    (cellLower scalarRow12456.grid (sourceIndex j))
    (cellUpper scalarRow12456.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12456.grid grid_top_bounds12456 j

theorem radii12456 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12456.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12456 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12456 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12456.grid grid_top_bounds12456 j hθ

noncomputable def covarianceInputs12456 :
    BstLean.Part263.CovarianceInputs 12456 scalarRow12456.grid parameters (caps repair12456) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12456 grid_top_bounds12456 repair12456

noncomputable def covarianceEvent12456 : Set (AgFam 12456) :=
  BstLean.Part263.covarianceEvent 12456 scalarRow12456.grid parameters

theorem covarianceEvent12456_measurable : MeasurableSet covarianceEvent12456 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12456_payment :
    (retDist (paperDesignP 12456).toCentres).real
      (agentEv (paperDesignP 12456) covarianceEvent12456)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12456

theorem localCov12456 : BstLean.Part259.LocalCovarianceOn covarianceEvent12456
    (BstLean.Part263.cell scalarRow12456.grid) (caps repair12456) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12456

theorem covarianceGood12456_payment :
    (retDist (paperDesignP 12456).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12456)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12456_payment



end BstLean.Part269.N12456

namespace BstLean.Part269.N12456
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12456}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12456.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12456) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12456).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12456 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12456) (by norm_num) BstLean.Part268.WorldRow12456.worldPackage rfl
    BstLean.Part268.WorldRow12456.product_lower (BstLean.Part268.WorldRow12456.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12456} (hw : c ∈ Hof BstLean.Part268.WorldRow12456.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12456) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12456) (by norm_num) BstLean.Part268.WorldRow12456.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12456} (hw : c ∈ Hof BstLean.Part268.WorldRow12456.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12456) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12456).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12456) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12456_eq : scalarRow12456.targetFrame = BstLean.Part268.agent12456.frame := by
  norm_num [scalarRow12456,BstLean.Part268.agent12456]

noncomputable def frameData12456 : BstLean.Part264b.FrameData 12456 :=
  BstLean.Part269.frameData_from_numerics (n := 12456) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12456.worldPackage rfl BstLean.Part268.WorldRow12456.product_lower (BstLean.Part268.WorldRow12456.producthi.2.trans (by norm_num))
    scalarRow12456 repair12456 covarianceInputs12456 (fun i hi => sourceNumerics12456 hi)
    BstLean.Part268.agent12456.frame targetFrame12456_eq


end BstLean.Part269.N12456

namespace BstLean.Part269.N12457
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12457 : scalarRow12457.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12457, BstLean.Part268.grid12457, BstLean.Part263.worldGrid]

theorem supplies12457 (j : Fin 43) : Supply 12457 (parameters j)
    (cellLower scalarRow12457.grid (sourceIndex j))
    (cellUpper scalarRow12457.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12457.grid grid_top_bounds12457 j

theorem radii12457 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12457.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12457 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12457 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12457.grid grid_top_bounds12457 j hθ

noncomputable def covarianceInputs12457 :
    BstLean.Part263.CovarianceInputs 12457 scalarRow12457.grid parameters (caps repair12457) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12457 grid_top_bounds12457 repair12457

noncomputable def covarianceEvent12457 : Set (AgFam 12457) :=
  BstLean.Part263.covarianceEvent 12457 scalarRow12457.grid parameters

theorem covarianceEvent12457_measurable : MeasurableSet covarianceEvent12457 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12457_payment :
    (retDist (paperDesignP 12457).toCentres).real
      (agentEv (paperDesignP 12457) covarianceEvent12457)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12457

theorem localCov12457 : BstLean.Part259.LocalCovarianceOn covarianceEvent12457
    (BstLean.Part263.cell scalarRow12457.grid) (caps repair12457) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12457

theorem covarianceGood12457_payment :
    (retDist (paperDesignP 12457).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12457)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12457_payment



end BstLean.Part269.N12457

namespace BstLean.Part269.N12457
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12457}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12457.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12457) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12457).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12457 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12457) (by norm_num) BstLean.Part268.WorldRow12457.worldPackage rfl
    BstLean.Part268.WorldRow12457.product_lower (BstLean.Part268.WorldRow12457.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12457} (hw : c ∈ Hof BstLean.Part268.WorldRow12457.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12457) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12457) (by norm_num) BstLean.Part268.WorldRow12457.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12457} (hw : c ∈ Hof BstLean.Part268.WorldRow12457.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12457) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12457).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12457) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12457_eq : scalarRow12457.targetFrame = BstLean.Part268.agent12457.frame := by
  norm_num [scalarRow12457,BstLean.Part268.agent12457]

noncomputable def frameData12457 : BstLean.Part264b.FrameData 12457 :=
  BstLean.Part269.frameData_from_numerics (n := 12457) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12457.worldPackage rfl BstLean.Part268.WorldRow12457.product_lower (BstLean.Part268.WorldRow12457.producthi.2.trans (by norm_num))
    scalarRow12457 repair12457 covarianceInputs12457 (fun i hi => sourceNumerics12457 hi)
    BstLean.Part268.agent12457.frame targetFrame12457_eq


end BstLean.Part269.N12457

namespace BstLean.Part269.N12458
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12458 : scalarRow12458.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12458, BstLean.Part268.grid12458, BstLean.Part263.worldGrid]

theorem supplies12458 (j : Fin 43) : Supply 12458 (parameters j)
    (cellLower scalarRow12458.grid (sourceIndex j))
    (cellUpper scalarRow12458.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12458.grid grid_top_bounds12458 j

theorem radii12458 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12458.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12458 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12458 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12458.grid grid_top_bounds12458 j hθ

noncomputable def covarianceInputs12458 :
    BstLean.Part263.CovarianceInputs 12458 scalarRow12458.grid parameters (caps repair12458) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12458 grid_top_bounds12458 repair12458

noncomputable def covarianceEvent12458 : Set (AgFam 12458) :=
  BstLean.Part263.covarianceEvent 12458 scalarRow12458.grid parameters

theorem covarianceEvent12458_measurable : MeasurableSet covarianceEvent12458 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12458_payment :
    (retDist (paperDesignP 12458).toCentres).real
      (agentEv (paperDesignP 12458) covarianceEvent12458)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12458

theorem localCov12458 : BstLean.Part259.LocalCovarianceOn covarianceEvent12458
    (BstLean.Part263.cell scalarRow12458.grid) (caps repair12458) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12458

theorem covarianceGood12458_payment :
    (retDist (paperDesignP 12458).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12458)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12458_payment



end BstLean.Part269.N12458

namespace BstLean.Part269.N12458
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12458}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12458.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12458) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12458).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12458 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12458) (by norm_num) BstLean.Part268.WorldRow12458.worldPackage rfl
    BstLean.Part268.WorldRow12458.product_lower (BstLean.Part268.WorldRow12458.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12458} (hw : c ∈ Hof BstLean.Part268.WorldRow12458.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12458) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12458) (by norm_num) BstLean.Part268.WorldRow12458.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12458} (hw : c ∈ Hof BstLean.Part268.WorldRow12458.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12458) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12458).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12458) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12458_eq : scalarRow12458.targetFrame = BstLean.Part268.agent12458.frame := by
  norm_num [scalarRow12458,BstLean.Part268.agent12458]

noncomputable def frameData12458 : BstLean.Part264b.FrameData 12458 :=
  BstLean.Part269.frameData_from_numerics (n := 12458) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12458.worldPackage rfl BstLean.Part268.WorldRow12458.product_lower (BstLean.Part268.WorldRow12458.producthi.2.trans (by norm_num))
    scalarRow12458 repair12458 covarianceInputs12458 (fun i hi => sourceNumerics12458 hi)
    BstLean.Part268.agent12458.frame targetFrame12458_eq


end BstLean.Part269.N12458

namespace BstLean.Part269.N12459
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12459 : scalarRow12459.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12459, BstLean.Part268.grid12459, BstLean.Part263.worldGrid]

theorem supplies12459 (j : Fin 43) : Supply 12459 (parameters j)
    (cellLower scalarRow12459.grid (sourceIndex j))
    (cellUpper scalarRow12459.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12459.grid grid_top_bounds12459 j

theorem radii12459 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12459.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12459 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12459 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12459.grid grid_top_bounds12459 j hθ

noncomputable def covarianceInputs12459 :
    BstLean.Part263.CovarianceInputs 12459 scalarRow12459.grid parameters (caps repair12459) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12459 grid_top_bounds12459 repair12459

noncomputable def covarianceEvent12459 : Set (AgFam 12459) :=
  BstLean.Part263.covarianceEvent 12459 scalarRow12459.grid parameters

theorem covarianceEvent12459_measurable : MeasurableSet covarianceEvent12459 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12459_payment :
    (retDist (paperDesignP 12459).toCentres).real
      (agentEv (paperDesignP 12459) covarianceEvent12459)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12459

theorem localCov12459 : BstLean.Part259.LocalCovarianceOn covarianceEvent12459
    (BstLean.Part263.cell scalarRow12459.grid) (caps repair12459) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12459

theorem covarianceGood12459_payment :
    (retDist (paperDesignP 12459).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12459)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12459_payment



end BstLean.Part269.N12459

namespace BstLean.Part269.N12459
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12459}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12459.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12459) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12459).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12459 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12459) (by norm_num) BstLean.Part268.WorldRow12459.worldPackage rfl
    BstLean.Part268.WorldRow12459.product_lower (BstLean.Part268.WorldRow12459.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12459} (hw : c ∈ Hof BstLean.Part268.WorldRow12459.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12459) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12459) (by norm_num) BstLean.Part268.WorldRow12459.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12459} (hw : c ∈ Hof BstLean.Part268.WorldRow12459.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12459) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12459).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12459) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12459_eq : scalarRow12459.targetFrame = BstLean.Part268.agent12459.frame := by
  norm_num [scalarRow12459,BstLean.Part268.agent12459]

noncomputable def frameData12459 : BstLean.Part264b.FrameData 12459 :=
  BstLean.Part269.frameData_from_numerics (n := 12459) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12459.worldPackage rfl BstLean.Part268.WorldRow12459.product_lower (BstLean.Part268.WorldRow12459.producthi.2.trans (by norm_num))
    scalarRow12459 repair12459 covarianceInputs12459 (fun i hi => sourceNumerics12459 hi)
    BstLean.Part268.agent12459.frame targetFrame12459_eq


end BstLean.Part269.N12459
