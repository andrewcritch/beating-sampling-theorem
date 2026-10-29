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

namespace BstLean.Part269.N12565
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12565 : scalarRow12565.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12565, BstLean.Part268.grid12565, BstLean.Part263.worldGrid]

theorem supplies12565 (j : Fin 43) : Supply 12565 (parameters j)
    (cellLower scalarRow12565.grid (sourceIndex j))
    (cellUpper scalarRow12565.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12565.grid grid_top_bounds12565 j

theorem radii12565 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12565.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12565 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12565 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12565.grid grid_top_bounds12565 j hθ

noncomputable def covarianceInputs12565 :
    BstLean.Part263.CovarianceInputs 12565 scalarRow12565.grid parameters (caps repair12565) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12565 grid_top_bounds12565 repair12565

noncomputable def covarianceEvent12565 : Set (AgFam 12565) :=
  BstLean.Part263.covarianceEvent 12565 scalarRow12565.grid parameters

theorem covarianceEvent12565_measurable : MeasurableSet covarianceEvent12565 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12565_payment :
    (retDist (paperDesignP 12565).toCentres).real
      (agentEv (paperDesignP 12565) covarianceEvent12565)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12565

theorem localCov12565 : BstLean.Part259.LocalCovarianceOn covarianceEvent12565
    (BstLean.Part263.cell scalarRow12565.grid) (caps repair12565) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12565

theorem covarianceGood12565_payment :
    (retDist (paperDesignP 12565).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12565)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12565_payment



end BstLean.Part269.N12565

namespace BstLean.Part269.N12565
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12565}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12565.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12565) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12565).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12565 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12565) (by norm_num) BstLean.Part268.WorldRow12565.worldPackage rfl
    BstLean.Part268.WorldRow12565.product_lower (BstLean.Part268.WorldRow12565.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12565} (hw : c ∈ Hof BstLean.Part268.WorldRow12565.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12565) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12565) (by norm_num) BstLean.Part268.WorldRow12565.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12565} (hw : c ∈ Hof BstLean.Part268.WorldRow12565.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12565) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12565).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12565) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12565_eq : scalarRow12565.targetFrame = BstLean.Part268.agent12565.frame := by
  norm_num [scalarRow12565,BstLean.Part268.agent12565]

noncomputable def frameData12565 : BstLean.Part264b.FrameData 12565 :=
  BstLean.Part269.frameData_from_numerics (n := 12565) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12565.worldPackage rfl BstLean.Part268.WorldRow12565.product_lower (BstLean.Part268.WorldRow12565.producthi.2.trans (by norm_num))
    scalarRow12565 repair12565 covarianceInputs12565 (fun i hi => sourceNumerics12565 hi)
    BstLean.Part268.agent12565.frame targetFrame12565_eq


end BstLean.Part269.N12565

namespace BstLean.Part269.N12566
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12566 : scalarRow12566.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12566, BstLean.Part268.grid12566, BstLean.Part263.worldGrid]

theorem supplies12566 (j : Fin 43) : Supply 12566 (parameters j)
    (cellLower scalarRow12566.grid (sourceIndex j))
    (cellUpper scalarRow12566.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12566.grid grid_top_bounds12566 j

theorem radii12566 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12566.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12566 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12566 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12566.grid grid_top_bounds12566 j hθ

noncomputable def covarianceInputs12566 :
    BstLean.Part263.CovarianceInputs 12566 scalarRow12566.grid parameters (caps repair12566) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12566 grid_top_bounds12566 repair12566

noncomputable def covarianceEvent12566 : Set (AgFam 12566) :=
  BstLean.Part263.covarianceEvent 12566 scalarRow12566.grid parameters

theorem covarianceEvent12566_measurable : MeasurableSet covarianceEvent12566 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12566_payment :
    (retDist (paperDesignP 12566).toCentres).real
      (agentEv (paperDesignP 12566) covarianceEvent12566)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12566

theorem localCov12566 : BstLean.Part259.LocalCovarianceOn covarianceEvent12566
    (BstLean.Part263.cell scalarRow12566.grid) (caps repair12566) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12566

theorem covarianceGood12566_payment :
    (retDist (paperDesignP 12566).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12566)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12566_payment



end BstLean.Part269.N12566

namespace BstLean.Part269.N12566
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12566}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12566.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12566) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12566).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12566 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12566) (by norm_num) BstLean.Part268.WorldRow12566.worldPackage rfl
    BstLean.Part268.WorldRow12566.product_lower (BstLean.Part268.WorldRow12566.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12566} (hw : c ∈ Hof BstLean.Part268.WorldRow12566.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12566) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12566) (by norm_num) BstLean.Part268.WorldRow12566.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12566} (hw : c ∈ Hof BstLean.Part268.WorldRow12566.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12566) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12566).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12566) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12566_eq : scalarRow12566.targetFrame = BstLean.Part268.agent12566.frame := by
  norm_num [scalarRow12566,BstLean.Part268.agent12566]

noncomputable def frameData12566 : BstLean.Part264b.FrameData 12566 :=
  BstLean.Part269.frameData_from_numerics (n := 12566) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12566.worldPackage rfl BstLean.Part268.WorldRow12566.product_lower (BstLean.Part268.WorldRow12566.producthi.2.trans (by norm_num))
    scalarRow12566 repair12566 covarianceInputs12566 (fun i hi => sourceNumerics12566 hi)
    BstLean.Part268.agent12566.frame targetFrame12566_eq


end BstLean.Part269.N12566

namespace BstLean.Part269.N12567
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12567 : scalarRow12567.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12567, BstLean.Part268.grid12567, BstLean.Part263.worldGrid]

theorem supplies12567 (j : Fin 43) : Supply 12567 (parameters j)
    (cellLower scalarRow12567.grid (sourceIndex j))
    (cellUpper scalarRow12567.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12567.grid grid_top_bounds12567 j

theorem radii12567 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12567.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12567 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12567 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12567.grid grid_top_bounds12567 j hθ

noncomputable def covarianceInputs12567 :
    BstLean.Part263.CovarianceInputs 12567 scalarRow12567.grid parameters (caps repair12567) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12567 grid_top_bounds12567 repair12567

noncomputable def covarianceEvent12567 : Set (AgFam 12567) :=
  BstLean.Part263.covarianceEvent 12567 scalarRow12567.grid parameters

theorem covarianceEvent12567_measurable : MeasurableSet covarianceEvent12567 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12567_payment :
    (retDist (paperDesignP 12567).toCentres).real
      (agentEv (paperDesignP 12567) covarianceEvent12567)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12567

theorem localCov12567 : BstLean.Part259.LocalCovarianceOn covarianceEvent12567
    (BstLean.Part263.cell scalarRow12567.grid) (caps repair12567) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12567

theorem covarianceGood12567_payment :
    (retDist (paperDesignP 12567).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12567)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12567_payment



end BstLean.Part269.N12567

namespace BstLean.Part269.N12567
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12567}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12567.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12567) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12567).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12567 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12567) (by norm_num) BstLean.Part268.WorldRow12567.worldPackage rfl
    BstLean.Part268.WorldRow12567.product_lower (BstLean.Part268.WorldRow12567.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12567} (hw : c ∈ Hof BstLean.Part268.WorldRow12567.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12567) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12567) (by norm_num) BstLean.Part268.WorldRow12567.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12567} (hw : c ∈ Hof BstLean.Part268.WorldRow12567.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12567) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12567).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12567) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12567_eq : scalarRow12567.targetFrame = BstLean.Part268.agent12567.frame := by
  norm_num [scalarRow12567,BstLean.Part268.agent12567]

noncomputable def frameData12567 : BstLean.Part264b.FrameData 12567 :=
  BstLean.Part269.frameData_from_numerics (n := 12567) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12567.worldPackage rfl BstLean.Part268.WorldRow12567.product_lower (BstLean.Part268.WorldRow12567.producthi.2.trans (by norm_num))
    scalarRow12567 repair12567 covarianceInputs12567 (fun i hi => sourceNumerics12567 hi)
    BstLean.Part268.agent12567.frame targetFrame12567_eq


end BstLean.Part269.N12567

namespace BstLean.Part269.N12568
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12568 : scalarRow12568.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12568, BstLean.Part268.grid12568, BstLean.Part263.worldGrid]

theorem supplies12568 (j : Fin 43) : Supply 12568 (parameters j)
    (cellLower scalarRow12568.grid (sourceIndex j))
    (cellUpper scalarRow12568.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12568.grid grid_top_bounds12568 j

theorem radii12568 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12568.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12568 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12568 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12568.grid grid_top_bounds12568 j hθ

noncomputable def covarianceInputs12568 :
    BstLean.Part263.CovarianceInputs 12568 scalarRow12568.grid parameters (caps repair12568) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12568 grid_top_bounds12568 repair12568

noncomputable def covarianceEvent12568 : Set (AgFam 12568) :=
  BstLean.Part263.covarianceEvent 12568 scalarRow12568.grid parameters

theorem covarianceEvent12568_measurable : MeasurableSet covarianceEvent12568 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12568_payment :
    (retDist (paperDesignP 12568).toCentres).real
      (agentEv (paperDesignP 12568) covarianceEvent12568)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12568

theorem localCov12568 : BstLean.Part259.LocalCovarianceOn covarianceEvent12568
    (BstLean.Part263.cell scalarRow12568.grid) (caps repair12568) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12568

theorem covarianceGood12568_payment :
    (retDist (paperDesignP 12568).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12568)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12568_payment



end BstLean.Part269.N12568

namespace BstLean.Part269.N12568
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12568}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12568.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12568) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12568).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12568 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12568) (by norm_num) BstLean.Part268.WorldRow12568.worldPackage rfl
    BstLean.Part268.WorldRow12568.product_lower (BstLean.Part268.WorldRow12568.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12568} (hw : c ∈ Hof BstLean.Part268.WorldRow12568.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12568) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12568) (by norm_num) BstLean.Part268.WorldRow12568.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12568} (hw : c ∈ Hof BstLean.Part268.WorldRow12568.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12568) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12568).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12568) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12568_eq : scalarRow12568.targetFrame = BstLean.Part268.agent12568.frame := by
  norm_num [scalarRow12568,BstLean.Part268.agent12568]

noncomputable def frameData12568 : BstLean.Part264b.FrameData 12568 :=
  BstLean.Part269.frameData_from_numerics (n := 12568) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12568.worldPackage rfl BstLean.Part268.WorldRow12568.product_lower (BstLean.Part268.WorldRow12568.producthi.2.trans (by norm_num))
    scalarRow12568 repair12568 covarianceInputs12568 (fun i hi => sourceNumerics12568 hi)
    BstLean.Part268.agent12568.frame targetFrame12568_eq


end BstLean.Part269.N12568

namespace BstLean.Part269.N12569
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12569 : scalarRow12569.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12569, BstLean.Part268.grid12569, BstLean.Part263.worldGrid]

theorem supplies12569 (j : Fin 43) : Supply 12569 (parameters j)
    (cellLower scalarRow12569.grid (sourceIndex j))
    (cellUpper scalarRow12569.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12569.grid grid_top_bounds12569 j

theorem radii12569 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12569.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12569 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12569 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12569.grid grid_top_bounds12569 j hθ

noncomputable def covarianceInputs12569 :
    BstLean.Part263.CovarianceInputs 12569 scalarRow12569.grid parameters (caps repair12569) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12569 grid_top_bounds12569 repair12569

noncomputable def covarianceEvent12569 : Set (AgFam 12569) :=
  BstLean.Part263.covarianceEvent 12569 scalarRow12569.grid parameters

theorem covarianceEvent12569_measurable : MeasurableSet covarianceEvent12569 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12569_payment :
    (retDist (paperDesignP 12569).toCentres).real
      (agentEv (paperDesignP 12569) covarianceEvent12569)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12569

theorem localCov12569 : BstLean.Part259.LocalCovarianceOn covarianceEvent12569
    (BstLean.Part263.cell scalarRow12569.grid) (caps repair12569) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12569

theorem covarianceGood12569_payment :
    (retDist (paperDesignP 12569).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12569)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12569_payment



end BstLean.Part269.N12569

namespace BstLean.Part269.N12569
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12569}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12569.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12569) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12569).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12569 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12569) (by norm_num) BstLean.Part268.WorldRow12569.worldPackage rfl
    BstLean.Part268.WorldRow12569.product_lower (BstLean.Part268.WorldRow12569.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12569} (hw : c ∈ Hof BstLean.Part268.WorldRow12569.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12569) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12569) (by norm_num) BstLean.Part268.WorldRow12569.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12569} (hw : c ∈ Hof BstLean.Part268.WorldRow12569.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12569) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12569).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12569) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12569_eq : scalarRow12569.targetFrame = BstLean.Part268.agent12569.frame := by
  norm_num [scalarRow12569,BstLean.Part268.agent12569]

noncomputable def frameData12569 : BstLean.Part264b.FrameData 12569 :=
  BstLean.Part269.frameData_from_numerics (n := 12569) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12569.worldPackage rfl BstLean.Part268.WorldRow12569.product_lower (BstLean.Part268.WorldRow12569.producthi.2.trans (by norm_num))
    scalarRow12569 repair12569 covarianceInputs12569 (fun i hi => sourceNumerics12569 hi)
    BstLean.Part268.agent12569.frame targetFrame12569_eq


end BstLean.Part269.N12569
