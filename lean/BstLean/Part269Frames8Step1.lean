import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World8Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs8
import BstLean.Part269Rows8
import BstLean.Part269Sources8
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12555
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12555 : scalarRow12555.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12555, BstLean.Part268.grid12555, BstLean.Part263.worldGrid]

theorem supplies12555 (j : Fin 43) : Supply 12555 (parameters j)
    (cellLower scalarRow12555.grid (sourceIndex j))
    (cellUpper scalarRow12555.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12555.grid grid_top_bounds12555 j

theorem radii12555 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12555.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12555 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12555 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12555.grid grid_top_bounds12555 j hθ

noncomputable def covarianceInputs12555 :
    BstLean.Part263.CovarianceInputs 12555 scalarRow12555.grid parameters (caps repair12555) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12555 grid_top_bounds12555 repair12555

noncomputable def covarianceEvent12555 : Set (AgFam 12555) :=
  BstLean.Part263.covarianceEvent 12555 scalarRow12555.grid parameters

theorem covarianceEvent12555_measurable : MeasurableSet covarianceEvent12555 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12555_payment :
    (retDist (paperDesignP 12555).toCentres).real
      (agentEv (paperDesignP 12555) covarianceEvent12555)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12555

theorem localCov12555 : BstLean.Part259.LocalCovarianceOn covarianceEvent12555
    (BstLean.Part263.cell scalarRow12555.grid) (caps repair12555) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12555

theorem covarianceGood12555_payment :
    (retDist (paperDesignP 12555).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12555)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12555_payment



end BstLean.Part269.N12555

namespace BstLean.Part269.N12555
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12555}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12555.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12555) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12555).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12555 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12555) (by norm_num) BstLean.Part268.WorldRow12555.worldPackage rfl
    BstLean.Part268.WorldRow12555.product_lower (BstLean.Part268.WorldRow12555.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12555} (hw : c ∈ Hof BstLean.Part268.WorldRow12555.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12555) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12555) (by norm_num) BstLean.Part268.WorldRow12555.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12555} (hw : c ∈ Hof BstLean.Part268.WorldRow12555.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12555) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12555).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12555) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12555_eq : scalarRow12555.targetFrame = BstLean.Part268.agent12555.frame := by
  norm_num [scalarRow12555,BstLean.Part268.agent12555]

noncomputable def frameData12555 : BstLean.Part264b.FrameData 12555 :=
  BstLean.Part269.frameData_from_numerics (n := 12555) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12555.worldPackage rfl BstLean.Part268.WorldRow12555.product_lower (BstLean.Part268.WorldRow12555.producthi.2.trans (by norm_num))
    scalarRow12555 repair12555 covarianceInputs12555 (fun i hi => sourceNumerics12555 hi)
    BstLean.Part268.agent12555.frame targetFrame12555_eq


end BstLean.Part269.N12555

namespace BstLean.Part269.N12556
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12556 : scalarRow12556.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12556, BstLean.Part268.grid12556, BstLean.Part263.worldGrid]

theorem supplies12556 (j : Fin 43) : Supply 12556 (parameters j)
    (cellLower scalarRow12556.grid (sourceIndex j))
    (cellUpper scalarRow12556.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12556.grid grid_top_bounds12556 j

theorem radii12556 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12556.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12556 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12556 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12556.grid grid_top_bounds12556 j hθ

noncomputable def covarianceInputs12556 :
    BstLean.Part263.CovarianceInputs 12556 scalarRow12556.grid parameters (caps repair12556) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12556 grid_top_bounds12556 repair12556

noncomputable def covarianceEvent12556 : Set (AgFam 12556) :=
  BstLean.Part263.covarianceEvent 12556 scalarRow12556.grid parameters

theorem covarianceEvent12556_measurable : MeasurableSet covarianceEvent12556 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12556_payment :
    (retDist (paperDesignP 12556).toCentres).real
      (agentEv (paperDesignP 12556) covarianceEvent12556)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12556

theorem localCov12556 : BstLean.Part259.LocalCovarianceOn covarianceEvent12556
    (BstLean.Part263.cell scalarRow12556.grid) (caps repair12556) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12556

theorem covarianceGood12556_payment :
    (retDist (paperDesignP 12556).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12556)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12556_payment



end BstLean.Part269.N12556

namespace BstLean.Part269.N12556
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12556}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12556.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12556) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12556).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12556 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12556) (by norm_num) BstLean.Part268.WorldRow12556.worldPackage rfl
    BstLean.Part268.WorldRow12556.product_lower (BstLean.Part268.WorldRow12556.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12556} (hw : c ∈ Hof BstLean.Part268.WorldRow12556.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12556) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12556) (by norm_num) BstLean.Part268.WorldRow12556.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12556} (hw : c ∈ Hof BstLean.Part268.WorldRow12556.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12556) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12556).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12556) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12556_eq : scalarRow12556.targetFrame = BstLean.Part268.agent12556.frame := by
  norm_num [scalarRow12556,BstLean.Part268.agent12556]

noncomputable def frameData12556 : BstLean.Part264b.FrameData 12556 :=
  BstLean.Part269.frameData_from_numerics (n := 12556) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12556.worldPackage rfl BstLean.Part268.WorldRow12556.product_lower (BstLean.Part268.WorldRow12556.producthi.2.trans (by norm_num))
    scalarRow12556 repair12556 covarianceInputs12556 (fun i hi => sourceNumerics12556 hi)
    BstLean.Part268.agent12556.frame targetFrame12556_eq


end BstLean.Part269.N12556

namespace BstLean.Part269.N12557
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12557 : scalarRow12557.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12557, BstLean.Part268.grid12557, BstLean.Part263.worldGrid]

theorem supplies12557 (j : Fin 43) : Supply 12557 (parameters j)
    (cellLower scalarRow12557.grid (sourceIndex j))
    (cellUpper scalarRow12557.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12557.grid grid_top_bounds12557 j

theorem radii12557 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12557.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12557 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12557 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12557.grid grid_top_bounds12557 j hθ

noncomputable def covarianceInputs12557 :
    BstLean.Part263.CovarianceInputs 12557 scalarRow12557.grid parameters (caps repair12557) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12557 grid_top_bounds12557 repair12557

noncomputable def covarianceEvent12557 : Set (AgFam 12557) :=
  BstLean.Part263.covarianceEvent 12557 scalarRow12557.grid parameters

theorem covarianceEvent12557_measurable : MeasurableSet covarianceEvent12557 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12557_payment :
    (retDist (paperDesignP 12557).toCentres).real
      (agentEv (paperDesignP 12557) covarianceEvent12557)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12557

theorem localCov12557 : BstLean.Part259.LocalCovarianceOn covarianceEvent12557
    (BstLean.Part263.cell scalarRow12557.grid) (caps repair12557) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12557

theorem covarianceGood12557_payment :
    (retDist (paperDesignP 12557).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12557)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12557_payment



end BstLean.Part269.N12557

namespace BstLean.Part269.N12557
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12557}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12557.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12557) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12557).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12557 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12557) (by norm_num) BstLean.Part268.WorldRow12557.worldPackage rfl
    BstLean.Part268.WorldRow12557.product_lower (BstLean.Part268.WorldRow12557.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12557} (hw : c ∈ Hof BstLean.Part268.WorldRow12557.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12557) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12557) (by norm_num) BstLean.Part268.WorldRow12557.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12557} (hw : c ∈ Hof BstLean.Part268.WorldRow12557.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12557) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12557).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12557) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12557_eq : scalarRow12557.targetFrame = BstLean.Part268.agent12557.frame := by
  norm_num [scalarRow12557,BstLean.Part268.agent12557]

noncomputable def frameData12557 : BstLean.Part264b.FrameData 12557 :=
  BstLean.Part269.frameData_from_numerics (n := 12557) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12557.worldPackage rfl BstLean.Part268.WorldRow12557.product_lower (BstLean.Part268.WorldRow12557.producthi.2.trans (by norm_num))
    scalarRow12557 repair12557 covarianceInputs12557 (fun i hi => sourceNumerics12557 hi)
    BstLean.Part268.agent12557.frame targetFrame12557_eq


end BstLean.Part269.N12557

namespace BstLean.Part269.N12558
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12558 : scalarRow12558.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12558, BstLean.Part268.grid12558, BstLean.Part263.worldGrid]

theorem supplies12558 (j : Fin 43) : Supply 12558 (parameters j)
    (cellLower scalarRow12558.grid (sourceIndex j))
    (cellUpper scalarRow12558.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12558.grid grid_top_bounds12558 j

theorem radii12558 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12558.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12558 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12558 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12558.grid grid_top_bounds12558 j hθ

noncomputable def covarianceInputs12558 :
    BstLean.Part263.CovarianceInputs 12558 scalarRow12558.grid parameters (caps repair12558) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12558 grid_top_bounds12558 repair12558

noncomputable def covarianceEvent12558 : Set (AgFam 12558) :=
  BstLean.Part263.covarianceEvent 12558 scalarRow12558.grid parameters

theorem covarianceEvent12558_measurable : MeasurableSet covarianceEvent12558 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12558_payment :
    (retDist (paperDesignP 12558).toCentres).real
      (agentEv (paperDesignP 12558) covarianceEvent12558)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12558

theorem localCov12558 : BstLean.Part259.LocalCovarianceOn covarianceEvent12558
    (BstLean.Part263.cell scalarRow12558.grid) (caps repair12558) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12558

theorem covarianceGood12558_payment :
    (retDist (paperDesignP 12558).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12558)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12558_payment



end BstLean.Part269.N12558

namespace BstLean.Part269.N12558
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12558}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12558.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12558) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12558).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12558 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12558) (by norm_num) BstLean.Part268.WorldRow12558.worldPackage rfl
    BstLean.Part268.WorldRow12558.product_lower (BstLean.Part268.WorldRow12558.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12558} (hw : c ∈ Hof BstLean.Part268.WorldRow12558.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12558) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12558) (by norm_num) BstLean.Part268.WorldRow12558.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12558} (hw : c ∈ Hof BstLean.Part268.WorldRow12558.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12558) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12558).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12558) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12558_eq : scalarRow12558.targetFrame = BstLean.Part268.agent12558.frame := by
  norm_num [scalarRow12558,BstLean.Part268.agent12558]

noncomputable def frameData12558 : BstLean.Part264b.FrameData 12558 :=
  BstLean.Part269.frameData_from_numerics (n := 12558) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12558.worldPackage rfl BstLean.Part268.WorldRow12558.product_lower (BstLean.Part268.WorldRow12558.producthi.2.trans (by norm_num))
    scalarRow12558 repair12558 covarianceInputs12558 (fun i hi => sourceNumerics12558 hi)
    BstLean.Part268.agent12558.frame targetFrame12558_eq


end BstLean.Part269.N12558

namespace BstLean.Part269.N12559
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12559 : scalarRow12559.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12559, BstLean.Part268.grid12559, BstLean.Part263.worldGrid]

theorem supplies12559 (j : Fin 43) : Supply 12559 (parameters j)
    (cellLower scalarRow12559.grid (sourceIndex j))
    (cellUpper scalarRow12559.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12559.grid grid_top_bounds12559 j

theorem radii12559 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12559.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12559 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12559 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12559.grid grid_top_bounds12559 j hθ

noncomputable def covarianceInputs12559 :
    BstLean.Part263.CovarianceInputs 12559 scalarRow12559.grid parameters (caps repair12559) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12559 grid_top_bounds12559 repair12559

noncomputable def covarianceEvent12559 : Set (AgFam 12559) :=
  BstLean.Part263.covarianceEvent 12559 scalarRow12559.grid parameters

theorem covarianceEvent12559_measurable : MeasurableSet covarianceEvent12559 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12559_payment :
    (retDist (paperDesignP 12559).toCentres).real
      (agentEv (paperDesignP 12559) covarianceEvent12559)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12559

theorem localCov12559 : BstLean.Part259.LocalCovarianceOn covarianceEvent12559
    (BstLean.Part263.cell scalarRow12559.grid) (caps repair12559) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12559

theorem covarianceGood12559_payment :
    (retDist (paperDesignP 12559).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12559)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12559_payment



end BstLean.Part269.N12559

namespace BstLean.Part269.N12559
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12559}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12559.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12559) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12559).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12559 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12559) (by norm_num) BstLean.Part268.WorldRow12559.worldPackage rfl
    BstLean.Part268.WorldRow12559.product_lower (BstLean.Part268.WorldRow12559.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12559} (hw : c ∈ Hof BstLean.Part268.WorldRow12559.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12559) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12559) (by norm_num) BstLean.Part268.WorldRow12559.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12559} (hw : c ∈ Hof BstLean.Part268.WorldRow12559.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12559) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12559).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12559) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12559_eq : scalarRow12559.targetFrame = BstLean.Part268.agent12559.frame := by
  norm_num [scalarRow12559,BstLean.Part268.agent12559]

noncomputable def frameData12559 : BstLean.Part264b.FrameData 12559 :=
  BstLean.Part269.frameData_from_numerics (n := 12559) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12559.worldPackage rfl BstLean.Part268.WorldRow12559.product_lower (BstLean.Part268.WorldRow12559.producthi.2.trans (by norm_num))
    scalarRow12559 repair12559 covarianceInputs12559 (fun i hi => sourceNumerics12559 hi)
    BstLean.Part268.agent12559.frame targetFrame12559_eq


end BstLean.Part269.N12559
