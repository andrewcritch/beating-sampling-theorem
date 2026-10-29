import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World14Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs14
import BstLean.Part269Rows14
import BstLean.Part269Sources14
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12705
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12705 : scalarRow12705.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12705, BstLean.Part268.grid12705, BstLean.Part263.worldGrid]

theorem supplies12705 (j : Fin 43) : Supply 12705 (parameters j)
    (cellLower scalarRow12705.grid (sourceIndex j))
    (cellUpper scalarRow12705.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12705.grid grid_top_bounds12705 j

theorem radii12705 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12705.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12705 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12705 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12705.grid grid_top_bounds12705 j hθ

noncomputable def covarianceInputs12705 :
    BstLean.Part263.CovarianceInputs 12705 scalarRow12705.grid parameters (caps repair12705) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12705 grid_top_bounds12705 repair12705

noncomputable def covarianceEvent12705 : Set (AgFam 12705) :=
  BstLean.Part263.covarianceEvent 12705 scalarRow12705.grid parameters

theorem covarianceEvent12705_measurable : MeasurableSet covarianceEvent12705 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12705_payment :
    (retDist (paperDesignP 12705).toCentres).real
      (agentEv (paperDesignP 12705) covarianceEvent12705)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12705

theorem localCov12705 : BstLean.Part259.LocalCovarianceOn covarianceEvent12705
    (BstLean.Part263.cell scalarRow12705.grid) (caps repair12705) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12705

theorem covarianceGood12705_payment :
    (retDist (paperDesignP 12705).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12705)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12705_payment



end BstLean.Part269.N12705

namespace BstLean.Part269.N12705
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12705}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12705.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12705) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12705).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12705 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12705) (by norm_num) BstLean.Part268.WorldRow12705.worldPackage rfl
    BstLean.Part268.WorldRow12705.product_lower (BstLean.Part268.WorldRow12705.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12705} (hw : c ∈ Hof BstLean.Part268.WorldRow12705.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12705) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12705) (by norm_num) BstLean.Part268.WorldRow12705.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12705} (hw : c ∈ Hof BstLean.Part268.WorldRow12705.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12705) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12705).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12705) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12705_eq : scalarRow12705.targetFrame = BstLean.Part268.agent12705.frame := by
  norm_num [scalarRow12705,BstLean.Part268.agent12705]

noncomputable def frameData12705 : BstLean.Part264b.FrameData 12705 :=
  BstLean.Part269.frameData_from_numerics (n := 12705) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12705.worldPackage rfl BstLean.Part268.WorldRow12705.product_lower (BstLean.Part268.WorldRow12705.producthi.2.trans (by norm_num))
    scalarRow12705 repair12705 covarianceInputs12705 (fun i hi => sourceNumerics12705 hi)
    BstLean.Part268.agent12705.frame targetFrame12705_eq


end BstLean.Part269.N12705

namespace BstLean.Part269.N12706
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12706 : scalarRow12706.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12706, BstLean.Part268.grid12706, BstLean.Part263.worldGrid]

theorem supplies12706 (j : Fin 43) : Supply 12706 (parameters j)
    (cellLower scalarRow12706.grid (sourceIndex j))
    (cellUpper scalarRow12706.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12706.grid grid_top_bounds12706 j

theorem radii12706 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12706.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12706 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12706 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12706.grid grid_top_bounds12706 j hθ

noncomputable def covarianceInputs12706 :
    BstLean.Part263.CovarianceInputs 12706 scalarRow12706.grid parameters (caps repair12706) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12706 grid_top_bounds12706 repair12706

noncomputable def covarianceEvent12706 : Set (AgFam 12706) :=
  BstLean.Part263.covarianceEvent 12706 scalarRow12706.grid parameters

theorem covarianceEvent12706_measurable : MeasurableSet covarianceEvent12706 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12706_payment :
    (retDist (paperDesignP 12706).toCentres).real
      (agentEv (paperDesignP 12706) covarianceEvent12706)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12706

theorem localCov12706 : BstLean.Part259.LocalCovarianceOn covarianceEvent12706
    (BstLean.Part263.cell scalarRow12706.grid) (caps repair12706) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12706

theorem covarianceGood12706_payment :
    (retDist (paperDesignP 12706).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12706)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12706_payment



end BstLean.Part269.N12706

namespace BstLean.Part269.N12706
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12706}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12706.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12706) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12706).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12706 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12706) (by norm_num) BstLean.Part268.WorldRow12706.worldPackage rfl
    BstLean.Part268.WorldRow12706.product_lower (BstLean.Part268.WorldRow12706.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12706} (hw : c ∈ Hof BstLean.Part268.WorldRow12706.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12706) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12706) (by norm_num) BstLean.Part268.WorldRow12706.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12706} (hw : c ∈ Hof BstLean.Part268.WorldRow12706.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12706) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12706).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12706) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12706_eq : scalarRow12706.targetFrame = BstLean.Part268.agent12706.frame := by
  norm_num [scalarRow12706,BstLean.Part268.agent12706]

noncomputable def frameData12706 : BstLean.Part264b.FrameData 12706 :=
  BstLean.Part269.frameData_from_numerics (n := 12706) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12706.worldPackage rfl BstLean.Part268.WorldRow12706.product_lower (BstLean.Part268.WorldRow12706.producthi.2.trans (by norm_num))
    scalarRow12706 repair12706 covarianceInputs12706 (fun i hi => sourceNumerics12706 hi)
    BstLean.Part268.agent12706.frame targetFrame12706_eq


end BstLean.Part269.N12706

namespace BstLean.Part269.N12707
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12707 : scalarRow12707.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12707, BstLean.Part268.grid12707, BstLean.Part263.worldGrid]

theorem supplies12707 (j : Fin 43) : Supply 12707 (parameters j)
    (cellLower scalarRow12707.grid (sourceIndex j))
    (cellUpper scalarRow12707.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12707.grid grid_top_bounds12707 j

theorem radii12707 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12707.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12707 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12707 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12707.grid grid_top_bounds12707 j hθ

noncomputable def covarianceInputs12707 :
    BstLean.Part263.CovarianceInputs 12707 scalarRow12707.grid parameters (caps repair12707) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12707 grid_top_bounds12707 repair12707

noncomputable def covarianceEvent12707 : Set (AgFam 12707) :=
  BstLean.Part263.covarianceEvent 12707 scalarRow12707.grid parameters

theorem covarianceEvent12707_measurable : MeasurableSet covarianceEvent12707 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12707_payment :
    (retDist (paperDesignP 12707).toCentres).real
      (agentEv (paperDesignP 12707) covarianceEvent12707)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12707

theorem localCov12707 : BstLean.Part259.LocalCovarianceOn covarianceEvent12707
    (BstLean.Part263.cell scalarRow12707.grid) (caps repair12707) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12707

theorem covarianceGood12707_payment :
    (retDist (paperDesignP 12707).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12707)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12707_payment



end BstLean.Part269.N12707

namespace BstLean.Part269.N12707
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12707}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12707.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12707) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12707).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12707 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12707) (by norm_num) BstLean.Part268.WorldRow12707.worldPackage rfl
    BstLean.Part268.WorldRow12707.product_lower (BstLean.Part268.WorldRow12707.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12707} (hw : c ∈ Hof BstLean.Part268.WorldRow12707.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12707) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12707) (by norm_num) BstLean.Part268.WorldRow12707.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12707} (hw : c ∈ Hof BstLean.Part268.WorldRow12707.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12707) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12707).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12707) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12707_eq : scalarRow12707.targetFrame = BstLean.Part268.agent12707.frame := by
  norm_num [scalarRow12707,BstLean.Part268.agent12707]

noncomputable def frameData12707 : BstLean.Part264b.FrameData 12707 :=
  BstLean.Part269.frameData_from_numerics (n := 12707) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12707.worldPackage rfl BstLean.Part268.WorldRow12707.product_lower (BstLean.Part268.WorldRow12707.producthi.2.trans (by norm_num))
    scalarRow12707 repair12707 covarianceInputs12707 (fun i hi => sourceNumerics12707 hi)
    BstLean.Part268.agent12707.frame targetFrame12707_eq


end BstLean.Part269.N12707

namespace BstLean.Part269.N12708
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12708 : scalarRow12708.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12708, BstLean.Part268.grid12708, BstLean.Part263.worldGrid]

theorem supplies12708 (j : Fin 43) : Supply 12708 (parameters j)
    (cellLower scalarRow12708.grid (sourceIndex j))
    (cellUpper scalarRow12708.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12708.grid grid_top_bounds12708 j

theorem radii12708 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12708.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12708 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12708 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12708.grid grid_top_bounds12708 j hθ

noncomputable def covarianceInputs12708 :
    BstLean.Part263.CovarianceInputs 12708 scalarRow12708.grid parameters (caps repair12708) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12708 grid_top_bounds12708 repair12708

noncomputable def covarianceEvent12708 : Set (AgFam 12708) :=
  BstLean.Part263.covarianceEvent 12708 scalarRow12708.grid parameters

theorem covarianceEvent12708_measurable : MeasurableSet covarianceEvent12708 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12708_payment :
    (retDist (paperDesignP 12708).toCentres).real
      (agentEv (paperDesignP 12708) covarianceEvent12708)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12708

theorem localCov12708 : BstLean.Part259.LocalCovarianceOn covarianceEvent12708
    (BstLean.Part263.cell scalarRow12708.grid) (caps repair12708) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12708

theorem covarianceGood12708_payment :
    (retDist (paperDesignP 12708).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12708)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12708_payment



end BstLean.Part269.N12708

namespace BstLean.Part269.N12708
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12708}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12708.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12708) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12708).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12708 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12708) (by norm_num) BstLean.Part268.WorldRow12708.worldPackage rfl
    BstLean.Part268.WorldRow12708.product_lower (BstLean.Part268.WorldRow12708.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12708} (hw : c ∈ Hof BstLean.Part268.WorldRow12708.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12708) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12708) (by norm_num) BstLean.Part268.WorldRow12708.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12708} (hw : c ∈ Hof BstLean.Part268.WorldRow12708.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12708) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12708).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12708) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12708_eq : scalarRow12708.targetFrame = BstLean.Part268.agent12708.frame := by
  norm_num [scalarRow12708,BstLean.Part268.agent12708]

noncomputable def frameData12708 : BstLean.Part264b.FrameData 12708 :=
  BstLean.Part269.frameData_from_numerics (n := 12708) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12708.worldPackage rfl BstLean.Part268.WorldRow12708.product_lower (BstLean.Part268.WorldRow12708.producthi.2.trans (by norm_num))
    scalarRow12708 repair12708 covarianceInputs12708 (fun i hi => sourceNumerics12708 hi)
    BstLean.Part268.agent12708.frame targetFrame12708_eq


end BstLean.Part269.N12708

namespace BstLean.Part269.N12709
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12709 : scalarRow12709.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12709, BstLean.Part268.grid12709, BstLean.Part263.worldGrid]

theorem supplies12709 (j : Fin 43) : Supply 12709 (parameters j)
    (cellLower scalarRow12709.grid (sourceIndex j))
    (cellUpper scalarRow12709.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12709.grid grid_top_bounds12709 j

theorem radii12709 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12709.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12709 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12709 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12709.grid grid_top_bounds12709 j hθ

noncomputable def covarianceInputs12709 :
    BstLean.Part263.CovarianceInputs 12709 scalarRow12709.grid parameters (caps repair12709) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12709 grid_top_bounds12709 repair12709

noncomputable def covarianceEvent12709 : Set (AgFam 12709) :=
  BstLean.Part263.covarianceEvent 12709 scalarRow12709.grid parameters

theorem covarianceEvent12709_measurable : MeasurableSet covarianceEvent12709 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12709_payment :
    (retDist (paperDesignP 12709).toCentres).real
      (agentEv (paperDesignP 12709) covarianceEvent12709)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12709

theorem localCov12709 : BstLean.Part259.LocalCovarianceOn covarianceEvent12709
    (BstLean.Part263.cell scalarRow12709.grid) (caps repair12709) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12709

theorem covarianceGood12709_payment :
    (retDist (paperDesignP 12709).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12709)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12709_payment



end BstLean.Part269.N12709

namespace BstLean.Part269.N12709
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12709}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12709.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12709) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12709).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12709 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12709) (by norm_num) BstLean.Part268.WorldRow12709.worldPackage rfl
    BstLean.Part268.WorldRow12709.product_lower (BstLean.Part268.WorldRow12709.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12709} (hw : c ∈ Hof BstLean.Part268.WorldRow12709.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12709) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12709) (by norm_num) BstLean.Part268.WorldRow12709.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12709} (hw : c ∈ Hof BstLean.Part268.WorldRow12709.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12709) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12709).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12709) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12709_eq : scalarRow12709.targetFrame = BstLean.Part268.agent12709.frame := by
  norm_num [scalarRow12709,BstLean.Part268.agent12709]

noncomputable def frameData12709 : BstLean.Part264b.FrameData 12709 :=
  BstLean.Part269.frameData_from_numerics (n := 12709) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12709.worldPackage rfl BstLean.Part268.WorldRow12709.product_lower (BstLean.Part268.WorldRow12709.producthi.2.trans (by norm_num))
    scalarRow12709 repair12709 covarianceInputs12709 (fun i hi => sourceNumerics12709 hi)
    BstLean.Part268.agent12709.frame targetFrame12709_eq


end BstLean.Part269.N12709
