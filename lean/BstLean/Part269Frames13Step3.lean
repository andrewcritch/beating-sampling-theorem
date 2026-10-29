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

namespace BstLean.Part269.N12690
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12690 : scalarRow12690.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12690, BstLean.Part268.grid12690, BstLean.Part263.worldGrid]

theorem supplies12690 (j : Fin 43) : Supply 12690 (parameters j)
    (cellLower scalarRow12690.grid (sourceIndex j))
    (cellUpper scalarRow12690.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12690.grid grid_top_bounds12690 j

theorem radii12690 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12690.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12690 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12690 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12690.grid grid_top_bounds12690 j hθ

noncomputable def covarianceInputs12690 :
    BstLean.Part263.CovarianceInputs 12690 scalarRow12690.grid parameters (caps repair12690) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12690 grid_top_bounds12690 repair12690

noncomputable def covarianceEvent12690 : Set (AgFam 12690) :=
  BstLean.Part263.covarianceEvent 12690 scalarRow12690.grid parameters

theorem covarianceEvent12690_measurable : MeasurableSet covarianceEvent12690 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12690_payment :
    (retDist (paperDesignP 12690).toCentres).real
      (agentEv (paperDesignP 12690) covarianceEvent12690)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12690

theorem localCov12690 : BstLean.Part259.LocalCovarianceOn covarianceEvent12690
    (BstLean.Part263.cell scalarRow12690.grid) (caps repair12690) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12690

theorem covarianceGood12690_payment :
    (retDist (paperDesignP 12690).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12690)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12690_payment



end BstLean.Part269.N12690

namespace BstLean.Part269.N12690
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12690}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12690.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12690) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12690).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12690 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12690) (by norm_num) BstLean.Part268.WorldRow12690.worldPackage rfl
    BstLean.Part268.WorldRow12690.product_lower (BstLean.Part268.WorldRow12690.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12690} (hw : c ∈ Hof BstLean.Part268.WorldRow12690.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12690) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12690) (by norm_num) BstLean.Part268.WorldRow12690.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12690} (hw : c ∈ Hof BstLean.Part268.WorldRow12690.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12690) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12690).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12690) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12690_eq : scalarRow12690.targetFrame = BstLean.Part268.agent12690.frame := by
  norm_num [scalarRow12690,BstLean.Part268.agent12690]

noncomputable def frameData12690 : BstLean.Part264b.FrameData 12690 :=
  BstLean.Part269.frameData_from_numerics (n := 12690) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12690.worldPackage rfl BstLean.Part268.WorldRow12690.product_lower (BstLean.Part268.WorldRow12690.producthi.2.trans (by norm_num))
    scalarRow12690 repair12690 covarianceInputs12690 (fun i hi => sourceNumerics12690 hi)
    BstLean.Part268.agent12690.frame targetFrame12690_eq


end BstLean.Part269.N12690

namespace BstLean.Part269.N12691
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12691 : scalarRow12691.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12691, BstLean.Part268.grid12691, BstLean.Part263.worldGrid]

theorem supplies12691 (j : Fin 43) : Supply 12691 (parameters j)
    (cellLower scalarRow12691.grid (sourceIndex j))
    (cellUpper scalarRow12691.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12691.grid grid_top_bounds12691 j

theorem radii12691 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12691.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12691 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12691 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12691.grid grid_top_bounds12691 j hθ

noncomputable def covarianceInputs12691 :
    BstLean.Part263.CovarianceInputs 12691 scalarRow12691.grid parameters (caps repair12691) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12691 grid_top_bounds12691 repair12691

noncomputable def covarianceEvent12691 : Set (AgFam 12691) :=
  BstLean.Part263.covarianceEvent 12691 scalarRow12691.grid parameters

theorem covarianceEvent12691_measurable : MeasurableSet covarianceEvent12691 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12691_payment :
    (retDist (paperDesignP 12691).toCentres).real
      (agentEv (paperDesignP 12691) covarianceEvent12691)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12691

theorem localCov12691 : BstLean.Part259.LocalCovarianceOn covarianceEvent12691
    (BstLean.Part263.cell scalarRow12691.grid) (caps repair12691) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12691

theorem covarianceGood12691_payment :
    (retDist (paperDesignP 12691).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12691)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12691_payment



end BstLean.Part269.N12691

namespace BstLean.Part269.N12691
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12691}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12691.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12691) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12691).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12691 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12691) (by norm_num) BstLean.Part268.WorldRow12691.worldPackage rfl
    BstLean.Part268.WorldRow12691.product_lower (BstLean.Part268.WorldRow12691.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12691} (hw : c ∈ Hof BstLean.Part268.WorldRow12691.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12691) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12691) (by norm_num) BstLean.Part268.WorldRow12691.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12691} (hw : c ∈ Hof BstLean.Part268.WorldRow12691.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12691) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12691).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12691) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12691_eq : scalarRow12691.targetFrame = BstLean.Part268.agent12691.frame := by
  norm_num [scalarRow12691,BstLean.Part268.agent12691]

noncomputable def frameData12691 : BstLean.Part264b.FrameData 12691 :=
  BstLean.Part269.frameData_from_numerics (n := 12691) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12691.worldPackage rfl BstLean.Part268.WorldRow12691.product_lower (BstLean.Part268.WorldRow12691.producthi.2.trans (by norm_num))
    scalarRow12691 repair12691 covarianceInputs12691 (fun i hi => sourceNumerics12691 hi)
    BstLean.Part268.agent12691.frame targetFrame12691_eq


end BstLean.Part269.N12691

namespace BstLean.Part269.N12692
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12692 : scalarRow12692.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12692, BstLean.Part268.grid12692, BstLean.Part263.worldGrid]

theorem supplies12692 (j : Fin 43) : Supply 12692 (parameters j)
    (cellLower scalarRow12692.grid (sourceIndex j))
    (cellUpper scalarRow12692.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12692.grid grid_top_bounds12692 j

theorem radii12692 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12692.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12692 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12692 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12692.grid grid_top_bounds12692 j hθ

noncomputable def covarianceInputs12692 :
    BstLean.Part263.CovarianceInputs 12692 scalarRow12692.grid parameters (caps repair12692) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12692 grid_top_bounds12692 repair12692

noncomputable def covarianceEvent12692 : Set (AgFam 12692) :=
  BstLean.Part263.covarianceEvent 12692 scalarRow12692.grid parameters

theorem covarianceEvent12692_measurable : MeasurableSet covarianceEvent12692 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12692_payment :
    (retDist (paperDesignP 12692).toCentres).real
      (agentEv (paperDesignP 12692) covarianceEvent12692)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12692

theorem localCov12692 : BstLean.Part259.LocalCovarianceOn covarianceEvent12692
    (BstLean.Part263.cell scalarRow12692.grid) (caps repair12692) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12692

theorem covarianceGood12692_payment :
    (retDist (paperDesignP 12692).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12692)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12692_payment



end BstLean.Part269.N12692

namespace BstLean.Part269.N12692
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12692}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12692.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12692) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12692).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12692 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12692) (by norm_num) BstLean.Part268.WorldRow12692.worldPackage rfl
    BstLean.Part268.WorldRow12692.product_lower (BstLean.Part268.WorldRow12692.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12692} (hw : c ∈ Hof BstLean.Part268.WorldRow12692.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12692) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12692) (by norm_num) BstLean.Part268.WorldRow12692.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12692} (hw : c ∈ Hof BstLean.Part268.WorldRow12692.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12692) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12692).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12692) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12692_eq : scalarRow12692.targetFrame = BstLean.Part268.agent12692.frame := by
  norm_num [scalarRow12692,BstLean.Part268.agent12692]

noncomputable def frameData12692 : BstLean.Part264b.FrameData 12692 :=
  BstLean.Part269.frameData_from_numerics (n := 12692) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12692.worldPackage rfl BstLean.Part268.WorldRow12692.product_lower (BstLean.Part268.WorldRow12692.producthi.2.trans (by norm_num))
    scalarRow12692 repair12692 covarianceInputs12692 (fun i hi => sourceNumerics12692 hi)
    BstLean.Part268.agent12692.frame targetFrame12692_eq


end BstLean.Part269.N12692

namespace BstLean.Part269.N12693
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12693 : scalarRow12693.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12693, BstLean.Part268.grid12693, BstLean.Part263.worldGrid]

theorem supplies12693 (j : Fin 43) : Supply 12693 (parameters j)
    (cellLower scalarRow12693.grid (sourceIndex j))
    (cellUpper scalarRow12693.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12693.grid grid_top_bounds12693 j

theorem radii12693 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12693.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12693 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12693 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12693.grid grid_top_bounds12693 j hθ

noncomputable def covarianceInputs12693 :
    BstLean.Part263.CovarianceInputs 12693 scalarRow12693.grid parameters (caps repair12693) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12693 grid_top_bounds12693 repair12693

noncomputable def covarianceEvent12693 : Set (AgFam 12693) :=
  BstLean.Part263.covarianceEvent 12693 scalarRow12693.grid parameters

theorem covarianceEvent12693_measurable : MeasurableSet covarianceEvent12693 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12693_payment :
    (retDist (paperDesignP 12693).toCentres).real
      (agentEv (paperDesignP 12693) covarianceEvent12693)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12693

theorem localCov12693 : BstLean.Part259.LocalCovarianceOn covarianceEvent12693
    (BstLean.Part263.cell scalarRow12693.grid) (caps repair12693) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12693

theorem covarianceGood12693_payment :
    (retDist (paperDesignP 12693).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12693)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12693_payment



end BstLean.Part269.N12693

namespace BstLean.Part269.N12693
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12693}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12693.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12693) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12693).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12693 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12693) (by norm_num) BstLean.Part268.WorldRow12693.worldPackage rfl
    BstLean.Part268.WorldRow12693.product_lower (BstLean.Part268.WorldRow12693.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12693} (hw : c ∈ Hof BstLean.Part268.WorldRow12693.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12693) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12693) (by norm_num) BstLean.Part268.WorldRow12693.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12693} (hw : c ∈ Hof BstLean.Part268.WorldRow12693.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12693) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12693).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12693) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12693_eq : scalarRow12693.targetFrame = BstLean.Part268.agent12693.frame := by
  norm_num [scalarRow12693,BstLean.Part268.agent12693]

noncomputable def frameData12693 : BstLean.Part264b.FrameData 12693 :=
  BstLean.Part269.frameData_from_numerics (n := 12693) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12693.worldPackage rfl BstLean.Part268.WorldRow12693.product_lower (BstLean.Part268.WorldRow12693.producthi.2.trans (by norm_num))
    scalarRow12693 repair12693 covarianceInputs12693 (fun i hi => sourceNumerics12693 hi)
    BstLean.Part268.agent12693.frame targetFrame12693_eq


end BstLean.Part269.N12693

namespace BstLean.Part269.N12694
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12694 : scalarRow12694.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12694, BstLean.Part268.grid12694, BstLean.Part263.worldGrid]

theorem supplies12694 (j : Fin 43) : Supply 12694 (parameters j)
    (cellLower scalarRow12694.grid (sourceIndex j))
    (cellUpper scalarRow12694.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12694.grid grid_top_bounds12694 j

theorem radii12694 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12694.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12694 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12694 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12694.grid grid_top_bounds12694 j hθ

noncomputable def covarianceInputs12694 :
    BstLean.Part263.CovarianceInputs 12694 scalarRow12694.grid parameters (caps repair12694) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12694 grid_top_bounds12694 repair12694

noncomputable def covarianceEvent12694 : Set (AgFam 12694) :=
  BstLean.Part263.covarianceEvent 12694 scalarRow12694.grid parameters

theorem covarianceEvent12694_measurable : MeasurableSet covarianceEvent12694 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12694_payment :
    (retDist (paperDesignP 12694).toCentres).real
      (agentEv (paperDesignP 12694) covarianceEvent12694)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12694

theorem localCov12694 : BstLean.Part259.LocalCovarianceOn covarianceEvent12694
    (BstLean.Part263.cell scalarRow12694.grid) (caps repair12694) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12694

theorem covarianceGood12694_payment :
    (retDist (paperDesignP 12694).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12694)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12694_payment



end BstLean.Part269.N12694

namespace BstLean.Part269.N12694
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12694}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12694.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12694) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12694).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12694 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12694) (by norm_num) BstLean.Part268.WorldRow12694.worldPackage rfl
    BstLean.Part268.WorldRow12694.product_lower (BstLean.Part268.WorldRow12694.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12694} (hw : c ∈ Hof BstLean.Part268.WorldRow12694.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12694) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12694) (by norm_num) BstLean.Part268.WorldRow12694.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12694} (hw : c ∈ Hof BstLean.Part268.WorldRow12694.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12694) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12694).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12694) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12694_eq : scalarRow12694.targetFrame = BstLean.Part268.agent12694.frame := by
  norm_num [scalarRow12694,BstLean.Part268.agent12694]

noncomputable def frameData12694 : BstLean.Part264b.FrameData 12694 :=
  BstLean.Part269.frameData_from_numerics (n := 12694) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12694.worldPackage rfl BstLean.Part268.WorldRow12694.product_lower (BstLean.Part268.WorldRow12694.producthi.2.trans (by norm_num))
    scalarRow12694 repair12694 covarianceInputs12694 (fun i hi => sourceNumerics12694 hi)
    BstLean.Part268.agent12694.frame targetFrame12694_eq


end BstLean.Part269.N12694
