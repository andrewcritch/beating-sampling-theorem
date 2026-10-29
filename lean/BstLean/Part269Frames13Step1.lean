import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World13Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs13
import BstLean.Part269Rows13
import BstLean.Part269Sources13
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12680
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12680 : scalarRow12680.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12680, BstLean.Part268.grid12680, BstLean.Part263.worldGrid]

theorem supplies12680 (j : Fin 43) : Supply 12680 (parameters j)
    (cellLower scalarRow12680.grid (sourceIndex j))
    (cellUpper scalarRow12680.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12680.grid grid_top_bounds12680 j

theorem radii12680 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12680.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12680 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12680 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12680.grid grid_top_bounds12680 j hθ

noncomputable def covarianceInputs12680 :
    BstLean.Part263.CovarianceInputs 12680 scalarRow12680.grid parameters (caps repair12680) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12680 grid_top_bounds12680 repair12680

noncomputable def covarianceEvent12680 : Set (AgFam 12680) :=
  BstLean.Part263.covarianceEvent 12680 scalarRow12680.grid parameters

theorem covarianceEvent12680_measurable : MeasurableSet covarianceEvent12680 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12680_payment :
    (retDist (paperDesignP 12680).toCentres).real
      (agentEv (paperDesignP 12680) covarianceEvent12680)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12680

theorem localCov12680 : BstLean.Part259.LocalCovarianceOn covarianceEvent12680
    (BstLean.Part263.cell scalarRow12680.grid) (caps repair12680) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12680

theorem covarianceGood12680_payment :
    (retDist (paperDesignP 12680).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12680)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12680_payment



end BstLean.Part269.N12680

namespace BstLean.Part269.N12680
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12680}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12680.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12680) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12680).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12680 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12680) (by norm_num) BstLean.Part268.WorldRow12680.worldPackage rfl
    BstLean.Part268.WorldRow12680.product_lower (BstLean.Part268.WorldRow12680.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12680} (hw : c ∈ Hof BstLean.Part268.WorldRow12680.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12680) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12680) (by norm_num) BstLean.Part268.WorldRow12680.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12680} (hw : c ∈ Hof BstLean.Part268.WorldRow12680.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12680) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12680).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12680) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12680_eq : scalarRow12680.targetFrame = BstLean.Part268.agent12680.frame := by
  norm_num [scalarRow12680,BstLean.Part268.agent12680]

noncomputable def frameData12680 : BstLean.Part264b.FrameData 12680 :=
  BstLean.Part269.frameData_from_numerics (n := 12680) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12680.worldPackage rfl BstLean.Part268.WorldRow12680.product_lower (BstLean.Part268.WorldRow12680.producthi.2.trans (by norm_num))
    scalarRow12680 repair12680 covarianceInputs12680 (fun i hi => sourceNumerics12680 hi)
    BstLean.Part268.agent12680.frame targetFrame12680_eq


end BstLean.Part269.N12680

namespace BstLean.Part269.N12681
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12681 : scalarRow12681.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12681, BstLean.Part268.grid12681, BstLean.Part263.worldGrid]

theorem supplies12681 (j : Fin 43) : Supply 12681 (parameters j)
    (cellLower scalarRow12681.grid (sourceIndex j))
    (cellUpper scalarRow12681.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12681.grid grid_top_bounds12681 j

theorem radii12681 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12681.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12681 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12681 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12681.grid grid_top_bounds12681 j hθ

noncomputable def covarianceInputs12681 :
    BstLean.Part263.CovarianceInputs 12681 scalarRow12681.grid parameters (caps repair12681) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12681 grid_top_bounds12681 repair12681

noncomputable def covarianceEvent12681 : Set (AgFam 12681) :=
  BstLean.Part263.covarianceEvent 12681 scalarRow12681.grid parameters

theorem covarianceEvent12681_measurable : MeasurableSet covarianceEvent12681 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12681_payment :
    (retDist (paperDesignP 12681).toCentres).real
      (agentEv (paperDesignP 12681) covarianceEvent12681)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12681

theorem localCov12681 : BstLean.Part259.LocalCovarianceOn covarianceEvent12681
    (BstLean.Part263.cell scalarRow12681.grid) (caps repair12681) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12681

theorem covarianceGood12681_payment :
    (retDist (paperDesignP 12681).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12681)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12681_payment



end BstLean.Part269.N12681

namespace BstLean.Part269.N12681
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12681}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12681.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12681) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12681).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12681 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12681) (by norm_num) BstLean.Part268.WorldRow12681.worldPackage rfl
    BstLean.Part268.WorldRow12681.product_lower (BstLean.Part268.WorldRow12681.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12681} (hw : c ∈ Hof BstLean.Part268.WorldRow12681.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12681) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12681) (by norm_num) BstLean.Part268.WorldRow12681.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12681} (hw : c ∈ Hof BstLean.Part268.WorldRow12681.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12681) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12681).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12681) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12681_eq : scalarRow12681.targetFrame = BstLean.Part268.agent12681.frame := by
  norm_num [scalarRow12681,BstLean.Part268.agent12681]

noncomputable def frameData12681 : BstLean.Part264b.FrameData 12681 :=
  BstLean.Part269.frameData_from_numerics (n := 12681) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12681.worldPackage rfl BstLean.Part268.WorldRow12681.product_lower (BstLean.Part268.WorldRow12681.producthi.2.trans (by norm_num))
    scalarRow12681 repair12681 covarianceInputs12681 (fun i hi => sourceNumerics12681 hi)
    BstLean.Part268.agent12681.frame targetFrame12681_eq


end BstLean.Part269.N12681

namespace BstLean.Part269.N12682
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12682 : scalarRow12682.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12682, BstLean.Part268.grid12682, BstLean.Part263.worldGrid]

theorem supplies12682 (j : Fin 43) : Supply 12682 (parameters j)
    (cellLower scalarRow12682.grid (sourceIndex j))
    (cellUpper scalarRow12682.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12682.grid grid_top_bounds12682 j

theorem radii12682 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12682.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12682 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12682 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12682.grid grid_top_bounds12682 j hθ

noncomputable def covarianceInputs12682 :
    BstLean.Part263.CovarianceInputs 12682 scalarRow12682.grid parameters (caps repair12682) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12682 grid_top_bounds12682 repair12682

noncomputable def covarianceEvent12682 : Set (AgFam 12682) :=
  BstLean.Part263.covarianceEvent 12682 scalarRow12682.grid parameters

theorem covarianceEvent12682_measurable : MeasurableSet covarianceEvent12682 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12682_payment :
    (retDist (paperDesignP 12682).toCentres).real
      (agentEv (paperDesignP 12682) covarianceEvent12682)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12682

theorem localCov12682 : BstLean.Part259.LocalCovarianceOn covarianceEvent12682
    (BstLean.Part263.cell scalarRow12682.grid) (caps repair12682) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12682

theorem covarianceGood12682_payment :
    (retDist (paperDesignP 12682).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12682)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12682_payment



end BstLean.Part269.N12682

namespace BstLean.Part269.N12682
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12682}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12682.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12682) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12682).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12682 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12682) (by norm_num) BstLean.Part268.WorldRow12682.worldPackage rfl
    BstLean.Part268.WorldRow12682.product_lower (BstLean.Part268.WorldRow12682.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12682} (hw : c ∈ Hof BstLean.Part268.WorldRow12682.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12682) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12682) (by norm_num) BstLean.Part268.WorldRow12682.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12682} (hw : c ∈ Hof BstLean.Part268.WorldRow12682.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12682) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12682).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12682) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12682_eq : scalarRow12682.targetFrame = BstLean.Part268.agent12682.frame := by
  norm_num [scalarRow12682,BstLean.Part268.agent12682]

noncomputable def frameData12682 : BstLean.Part264b.FrameData 12682 :=
  BstLean.Part269.frameData_from_numerics (n := 12682) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12682.worldPackage rfl BstLean.Part268.WorldRow12682.product_lower (BstLean.Part268.WorldRow12682.producthi.2.trans (by norm_num))
    scalarRow12682 repair12682 covarianceInputs12682 (fun i hi => sourceNumerics12682 hi)
    BstLean.Part268.agent12682.frame targetFrame12682_eq


end BstLean.Part269.N12682

namespace BstLean.Part269.N12683
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12683 : scalarRow12683.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12683, BstLean.Part268.grid12683, BstLean.Part263.worldGrid]

theorem supplies12683 (j : Fin 43) : Supply 12683 (parameters j)
    (cellLower scalarRow12683.grid (sourceIndex j))
    (cellUpper scalarRow12683.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12683.grid grid_top_bounds12683 j

theorem radii12683 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12683.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12683 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12683 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12683.grid grid_top_bounds12683 j hθ

noncomputable def covarianceInputs12683 :
    BstLean.Part263.CovarianceInputs 12683 scalarRow12683.grid parameters (caps repair12683) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12683 grid_top_bounds12683 repair12683

noncomputable def covarianceEvent12683 : Set (AgFam 12683) :=
  BstLean.Part263.covarianceEvent 12683 scalarRow12683.grid parameters

theorem covarianceEvent12683_measurable : MeasurableSet covarianceEvent12683 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12683_payment :
    (retDist (paperDesignP 12683).toCentres).real
      (agentEv (paperDesignP 12683) covarianceEvent12683)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12683

theorem localCov12683 : BstLean.Part259.LocalCovarianceOn covarianceEvent12683
    (BstLean.Part263.cell scalarRow12683.grid) (caps repair12683) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12683

theorem covarianceGood12683_payment :
    (retDist (paperDesignP 12683).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12683)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12683_payment



end BstLean.Part269.N12683

namespace BstLean.Part269.N12683
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12683}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12683.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12683) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12683).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12683 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12683) (by norm_num) BstLean.Part268.WorldRow12683.worldPackage rfl
    BstLean.Part268.WorldRow12683.product_lower (BstLean.Part268.WorldRow12683.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12683} (hw : c ∈ Hof BstLean.Part268.WorldRow12683.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12683) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12683) (by norm_num) BstLean.Part268.WorldRow12683.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12683} (hw : c ∈ Hof BstLean.Part268.WorldRow12683.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12683) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12683).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12683) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12683_eq : scalarRow12683.targetFrame = BstLean.Part268.agent12683.frame := by
  norm_num [scalarRow12683,BstLean.Part268.agent12683]

noncomputable def frameData12683 : BstLean.Part264b.FrameData 12683 :=
  BstLean.Part269.frameData_from_numerics (n := 12683) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12683.worldPackage rfl BstLean.Part268.WorldRow12683.product_lower (BstLean.Part268.WorldRow12683.producthi.2.trans (by norm_num))
    scalarRow12683 repair12683 covarianceInputs12683 (fun i hi => sourceNumerics12683 hi)
    BstLean.Part268.agent12683.frame targetFrame12683_eq


end BstLean.Part269.N12683

namespace BstLean.Part269.N12684
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12684 : scalarRow12684.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12684, BstLean.Part268.grid12684, BstLean.Part263.worldGrid]

theorem supplies12684 (j : Fin 43) : Supply 12684 (parameters j)
    (cellLower scalarRow12684.grid (sourceIndex j))
    (cellUpper scalarRow12684.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12684.grid grid_top_bounds12684 j

theorem radii12684 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12684.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12684 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12684 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12684.grid grid_top_bounds12684 j hθ

noncomputable def covarianceInputs12684 :
    BstLean.Part263.CovarianceInputs 12684 scalarRow12684.grid parameters (caps repair12684) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12684 grid_top_bounds12684 repair12684

noncomputable def covarianceEvent12684 : Set (AgFam 12684) :=
  BstLean.Part263.covarianceEvent 12684 scalarRow12684.grid parameters

theorem covarianceEvent12684_measurable : MeasurableSet covarianceEvent12684 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12684_payment :
    (retDist (paperDesignP 12684).toCentres).real
      (agentEv (paperDesignP 12684) covarianceEvent12684)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12684

theorem localCov12684 : BstLean.Part259.LocalCovarianceOn covarianceEvent12684
    (BstLean.Part263.cell scalarRow12684.grid) (caps repair12684) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12684

theorem covarianceGood12684_payment :
    (retDist (paperDesignP 12684).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12684)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12684_payment



end BstLean.Part269.N12684

namespace BstLean.Part269.N12684
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12684}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12684.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12684) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12684).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12684 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12684) (by norm_num) BstLean.Part268.WorldRow12684.worldPackage rfl
    BstLean.Part268.WorldRow12684.product_lower (BstLean.Part268.WorldRow12684.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12684} (hw : c ∈ Hof BstLean.Part268.WorldRow12684.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12684) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12684) (by norm_num) BstLean.Part268.WorldRow12684.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12684} (hw : c ∈ Hof BstLean.Part268.WorldRow12684.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12684) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12684).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12684) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12684_eq : scalarRow12684.targetFrame = BstLean.Part268.agent12684.frame := by
  norm_num [scalarRow12684,BstLean.Part268.agent12684]

noncomputable def frameData12684 : BstLean.Part264b.FrameData 12684 :=
  BstLean.Part269.frameData_from_numerics (n := 12684) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12684.worldPackage rfl BstLean.Part268.WorldRow12684.product_lower (BstLean.Part268.WorldRow12684.producthi.2.trans (by norm_num))
    scalarRow12684 repair12684 covarianceInputs12684 (fun i hi => sourceNumerics12684 hi)
    BstLean.Part268.agent12684.frame targetFrame12684_eq


end BstLean.Part269.N12684
