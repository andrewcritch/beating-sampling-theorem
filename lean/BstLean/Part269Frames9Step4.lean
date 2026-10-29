import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World9Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs9
import BstLean.Part269Rows9
import BstLean.Part269Sources9
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12595
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12595 : scalarRow12595.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12595, BstLean.Part268.grid12595, BstLean.Part263.worldGrid]

theorem supplies12595 (j : Fin 43) : Supply 12595 (parameters j)
    (cellLower scalarRow12595.grid (sourceIndex j))
    (cellUpper scalarRow12595.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12595.grid grid_top_bounds12595 j

theorem radii12595 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12595.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12595 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12595 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12595.grid grid_top_bounds12595 j hθ

noncomputable def covarianceInputs12595 :
    BstLean.Part263.CovarianceInputs 12595 scalarRow12595.grid parameters (caps repair12595) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12595 grid_top_bounds12595 repair12595

noncomputable def covarianceEvent12595 : Set (AgFam 12595) :=
  BstLean.Part263.covarianceEvent 12595 scalarRow12595.grid parameters

theorem covarianceEvent12595_measurable : MeasurableSet covarianceEvent12595 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12595_payment :
    (retDist (paperDesignP 12595).toCentres).real
      (agentEv (paperDesignP 12595) covarianceEvent12595)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12595

theorem localCov12595 : BstLean.Part259.LocalCovarianceOn covarianceEvent12595
    (BstLean.Part263.cell scalarRow12595.grid) (caps repair12595) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12595

theorem covarianceGood12595_payment :
    (retDist (paperDesignP 12595).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12595)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12595_payment



end BstLean.Part269.N12595

namespace BstLean.Part269.N12595
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12595}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12595.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12595) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12595).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12595 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12595) (by norm_num) BstLean.Part268.WorldRow12595.worldPackage rfl
    BstLean.Part268.WorldRow12595.product_lower (BstLean.Part268.WorldRow12595.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12595} (hw : c ∈ Hof BstLean.Part268.WorldRow12595.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12595) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12595) (by norm_num) BstLean.Part268.WorldRow12595.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12595} (hw : c ∈ Hof BstLean.Part268.WorldRow12595.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12595) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12595).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12595) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12595_eq : scalarRow12595.targetFrame = BstLean.Part268.agent12595.frame := by
  norm_num [scalarRow12595,BstLean.Part268.agent12595]

noncomputable def frameData12595 : BstLean.Part264b.FrameData 12595 :=
  BstLean.Part269.frameData_from_numerics (n := 12595) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12595.worldPackage rfl BstLean.Part268.WorldRow12595.product_lower (BstLean.Part268.WorldRow12595.producthi.2.trans (by norm_num))
    scalarRow12595 repair12595 covarianceInputs12595 (fun i hi => sourceNumerics12595 hi)
    BstLean.Part268.agent12595.frame targetFrame12595_eq


end BstLean.Part269.N12595

namespace BstLean.Part269.N12596
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12596 : scalarRow12596.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12596, BstLean.Part268.grid12596, BstLean.Part263.worldGrid]

theorem supplies12596 (j : Fin 43) : Supply 12596 (parameters j)
    (cellLower scalarRow12596.grid (sourceIndex j))
    (cellUpper scalarRow12596.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12596.grid grid_top_bounds12596 j

theorem radii12596 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12596.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12596 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12596 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12596.grid grid_top_bounds12596 j hθ

noncomputable def covarianceInputs12596 :
    BstLean.Part263.CovarianceInputs 12596 scalarRow12596.grid parameters (caps repair12596) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12596 grid_top_bounds12596 repair12596

noncomputable def covarianceEvent12596 : Set (AgFam 12596) :=
  BstLean.Part263.covarianceEvent 12596 scalarRow12596.grid parameters

theorem covarianceEvent12596_measurable : MeasurableSet covarianceEvent12596 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12596_payment :
    (retDist (paperDesignP 12596).toCentres).real
      (agentEv (paperDesignP 12596) covarianceEvent12596)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12596

theorem localCov12596 : BstLean.Part259.LocalCovarianceOn covarianceEvent12596
    (BstLean.Part263.cell scalarRow12596.grid) (caps repair12596) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12596

theorem covarianceGood12596_payment :
    (retDist (paperDesignP 12596).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12596)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12596_payment



end BstLean.Part269.N12596

namespace BstLean.Part269.N12596
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12596}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12596.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12596) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12596).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12596 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12596) (by norm_num) BstLean.Part268.WorldRow12596.worldPackage rfl
    BstLean.Part268.WorldRow12596.product_lower (BstLean.Part268.WorldRow12596.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12596} (hw : c ∈ Hof BstLean.Part268.WorldRow12596.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12596) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12596) (by norm_num) BstLean.Part268.WorldRow12596.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12596} (hw : c ∈ Hof BstLean.Part268.WorldRow12596.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12596) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12596).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12596) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12596_eq : scalarRow12596.targetFrame = BstLean.Part268.agent12596.frame := by
  norm_num [scalarRow12596,BstLean.Part268.agent12596]

noncomputable def frameData12596 : BstLean.Part264b.FrameData 12596 :=
  BstLean.Part269.frameData_from_numerics (n := 12596) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12596.worldPackage rfl BstLean.Part268.WorldRow12596.product_lower (BstLean.Part268.WorldRow12596.producthi.2.trans (by norm_num))
    scalarRow12596 repair12596 covarianceInputs12596 (fun i hi => sourceNumerics12596 hi)
    BstLean.Part268.agent12596.frame targetFrame12596_eq


end BstLean.Part269.N12596

namespace BstLean.Part269.N12597
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12597 : scalarRow12597.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12597, BstLean.Part268.grid12597, BstLean.Part263.worldGrid]

theorem supplies12597 (j : Fin 43) : Supply 12597 (parameters j)
    (cellLower scalarRow12597.grid (sourceIndex j))
    (cellUpper scalarRow12597.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12597.grid grid_top_bounds12597 j

theorem radii12597 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12597.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12597 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12597 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12597.grid grid_top_bounds12597 j hθ

noncomputable def covarianceInputs12597 :
    BstLean.Part263.CovarianceInputs 12597 scalarRow12597.grid parameters (caps repair12597) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12597 grid_top_bounds12597 repair12597

noncomputable def covarianceEvent12597 : Set (AgFam 12597) :=
  BstLean.Part263.covarianceEvent 12597 scalarRow12597.grid parameters

theorem covarianceEvent12597_measurable : MeasurableSet covarianceEvent12597 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12597_payment :
    (retDist (paperDesignP 12597).toCentres).real
      (agentEv (paperDesignP 12597) covarianceEvent12597)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12597

theorem localCov12597 : BstLean.Part259.LocalCovarianceOn covarianceEvent12597
    (BstLean.Part263.cell scalarRow12597.grid) (caps repair12597) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12597

theorem covarianceGood12597_payment :
    (retDist (paperDesignP 12597).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12597)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12597_payment



end BstLean.Part269.N12597

namespace BstLean.Part269.N12597
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12597}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12597.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12597) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12597).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12597 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12597) (by norm_num) BstLean.Part268.WorldRow12597.worldPackage rfl
    BstLean.Part268.WorldRow12597.product_lower (BstLean.Part268.WorldRow12597.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12597} (hw : c ∈ Hof BstLean.Part268.WorldRow12597.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12597) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12597) (by norm_num) BstLean.Part268.WorldRow12597.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12597} (hw : c ∈ Hof BstLean.Part268.WorldRow12597.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12597) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12597).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12597) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12597_eq : scalarRow12597.targetFrame = BstLean.Part268.agent12597.frame := by
  norm_num [scalarRow12597,BstLean.Part268.agent12597]

noncomputable def frameData12597 : BstLean.Part264b.FrameData 12597 :=
  BstLean.Part269.frameData_from_numerics (n := 12597) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12597.worldPackage rfl BstLean.Part268.WorldRow12597.product_lower (BstLean.Part268.WorldRow12597.producthi.2.trans (by norm_num))
    scalarRow12597 repair12597 covarianceInputs12597 (fun i hi => sourceNumerics12597 hi)
    BstLean.Part268.agent12597.frame targetFrame12597_eq


end BstLean.Part269.N12597

namespace BstLean.Part269.N12598
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12598 : scalarRow12598.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12598, BstLean.Part268.grid12598, BstLean.Part263.worldGrid]

theorem supplies12598 (j : Fin 43) : Supply 12598 (parameters j)
    (cellLower scalarRow12598.grid (sourceIndex j))
    (cellUpper scalarRow12598.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12598.grid grid_top_bounds12598 j

theorem radii12598 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12598.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12598 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12598 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12598.grid grid_top_bounds12598 j hθ

noncomputable def covarianceInputs12598 :
    BstLean.Part263.CovarianceInputs 12598 scalarRow12598.grid parameters (caps repair12598) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12598 grid_top_bounds12598 repair12598

noncomputable def covarianceEvent12598 : Set (AgFam 12598) :=
  BstLean.Part263.covarianceEvent 12598 scalarRow12598.grid parameters

theorem covarianceEvent12598_measurable : MeasurableSet covarianceEvent12598 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12598_payment :
    (retDist (paperDesignP 12598).toCentres).real
      (agentEv (paperDesignP 12598) covarianceEvent12598)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12598

theorem localCov12598 : BstLean.Part259.LocalCovarianceOn covarianceEvent12598
    (BstLean.Part263.cell scalarRow12598.grid) (caps repair12598) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12598

theorem covarianceGood12598_payment :
    (retDist (paperDesignP 12598).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12598)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12598_payment



end BstLean.Part269.N12598

namespace BstLean.Part269.N12598
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12598}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12598.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12598) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12598).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12598 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12598) (by norm_num) BstLean.Part268.WorldRow12598.worldPackage rfl
    BstLean.Part268.WorldRow12598.product_lower (BstLean.Part268.WorldRow12598.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12598} (hw : c ∈ Hof BstLean.Part268.WorldRow12598.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12598) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12598) (by norm_num) BstLean.Part268.WorldRow12598.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12598} (hw : c ∈ Hof BstLean.Part268.WorldRow12598.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12598) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12598).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12598) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12598_eq : scalarRow12598.targetFrame = BstLean.Part268.agent12598.frame := by
  norm_num [scalarRow12598,BstLean.Part268.agent12598]

noncomputable def frameData12598 : BstLean.Part264b.FrameData 12598 :=
  BstLean.Part269.frameData_from_numerics (n := 12598) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12598.worldPackage rfl BstLean.Part268.WorldRow12598.product_lower (BstLean.Part268.WorldRow12598.producthi.2.trans (by norm_num))
    scalarRow12598 repair12598 covarianceInputs12598 (fun i hi => sourceNumerics12598 hi)
    BstLean.Part268.agent12598.frame targetFrame12598_eq


end BstLean.Part269.N12598

namespace BstLean.Part269.N12599
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12599 : scalarRow12599.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12599, BstLean.Part268.grid12599, BstLean.Part263.worldGrid]

theorem supplies12599 (j : Fin 43) : Supply 12599 (parameters j)
    (cellLower scalarRow12599.grid (sourceIndex j))
    (cellUpper scalarRow12599.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12599.grid grid_top_bounds12599 j

theorem radii12599 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12599.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12599 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12599 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12599.grid grid_top_bounds12599 j hθ

noncomputable def covarianceInputs12599 :
    BstLean.Part263.CovarianceInputs 12599 scalarRow12599.grid parameters (caps repair12599) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12599 grid_top_bounds12599 repair12599

noncomputable def covarianceEvent12599 : Set (AgFam 12599) :=
  BstLean.Part263.covarianceEvent 12599 scalarRow12599.grid parameters

theorem covarianceEvent12599_measurable : MeasurableSet covarianceEvent12599 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12599_payment :
    (retDist (paperDesignP 12599).toCentres).real
      (agentEv (paperDesignP 12599) covarianceEvent12599)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12599

theorem localCov12599 : BstLean.Part259.LocalCovarianceOn covarianceEvent12599
    (BstLean.Part263.cell scalarRow12599.grid) (caps repair12599) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12599

theorem covarianceGood12599_payment :
    (retDist (paperDesignP 12599).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12599)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12599_payment



end BstLean.Part269.N12599

namespace BstLean.Part269.N12599
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12599}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12599.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12599) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12599).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12599 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12599) (by norm_num) BstLean.Part268.WorldRow12599.worldPackage rfl
    BstLean.Part268.WorldRow12599.product_lower (BstLean.Part268.WorldRow12599.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12599} (hw : c ∈ Hof BstLean.Part268.WorldRow12599.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12599) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12599) (by norm_num) BstLean.Part268.WorldRow12599.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12599} (hw : c ∈ Hof BstLean.Part268.WorldRow12599.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12599) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12599).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12599) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12599_eq : scalarRow12599.targetFrame = BstLean.Part268.agent12599.frame := by
  norm_num [scalarRow12599,BstLean.Part268.agent12599]

noncomputable def frameData12599 : BstLean.Part264b.FrameData 12599 :=
  BstLean.Part269.frameData_from_numerics (n := 12599) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12599.worldPackage rfl BstLean.Part268.WorldRow12599.product_lower (BstLean.Part268.WorldRow12599.producthi.2.trans (by norm_num))
    scalarRow12599 repair12599 covarianceInputs12599 (fun i hi => sourceNumerics12599 hi)
    BstLean.Part268.agent12599.frame targetFrame12599_eq


end BstLean.Part269.N12599
