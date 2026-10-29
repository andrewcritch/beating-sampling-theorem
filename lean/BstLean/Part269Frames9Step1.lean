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

namespace BstLean.Part269.N12580
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12580 : scalarRow12580.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12580, BstLean.Part268.grid12580, BstLean.Part263.worldGrid]

theorem supplies12580 (j : Fin 43) : Supply 12580 (parameters j)
    (cellLower scalarRow12580.grid (sourceIndex j))
    (cellUpper scalarRow12580.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12580.grid grid_top_bounds12580 j

theorem radii12580 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12580.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12580 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12580 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12580.grid grid_top_bounds12580 j hθ

noncomputable def covarianceInputs12580 :
    BstLean.Part263.CovarianceInputs 12580 scalarRow12580.grid parameters (caps repair12580) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12580 grid_top_bounds12580 repair12580

noncomputable def covarianceEvent12580 : Set (AgFam 12580) :=
  BstLean.Part263.covarianceEvent 12580 scalarRow12580.grid parameters

theorem covarianceEvent12580_measurable : MeasurableSet covarianceEvent12580 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12580_payment :
    (retDist (paperDesignP 12580).toCentres).real
      (agentEv (paperDesignP 12580) covarianceEvent12580)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12580

theorem localCov12580 : BstLean.Part259.LocalCovarianceOn covarianceEvent12580
    (BstLean.Part263.cell scalarRow12580.grid) (caps repair12580) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12580

theorem covarianceGood12580_payment :
    (retDist (paperDesignP 12580).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12580)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12580_payment



end BstLean.Part269.N12580

namespace BstLean.Part269.N12580
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12580}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12580.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12580) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12580).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12580 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12580) (by norm_num) BstLean.Part268.WorldRow12580.worldPackage rfl
    BstLean.Part268.WorldRow12580.product_lower (BstLean.Part268.WorldRow12580.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12580} (hw : c ∈ Hof BstLean.Part268.WorldRow12580.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12580) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12580) (by norm_num) BstLean.Part268.WorldRow12580.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12580} (hw : c ∈ Hof BstLean.Part268.WorldRow12580.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12580) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12580).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12580) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12580_eq : scalarRow12580.targetFrame = BstLean.Part268.agent12580.frame := by
  norm_num [scalarRow12580,BstLean.Part268.agent12580]

noncomputable def frameData12580 : BstLean.Part264b.FrameData 12580 :=
  BstLean.Part269.frameData_from_numerics (n := 12580) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12580.worldPackage rfl BstLean.Part268.WorldRow12580.product_lower (BstLean.Part268.WorldRow12580.producthi.2.trans (by norm_num))
    scalarRow12580 repair12580 covarianceInputs12580 (fun i hi => sourceNumerics12580 hi)
    BstLean.Part268.agent12580.frame targetFrame12580_eq


end BstLean.Part269.N12580

namespace BstLean.Part269.N12581
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12581 : scalarRow12581.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12581, BstLean.Part268.grid12581, BstLean.Part263.worldGrid]

theorem supplies12581 (j : Fin 43) : Supply 12581 (parameters j)
    (cellLower scalarRow12581.grid (sourceIndex j))
    (cellUpper scalarRow12581.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12581.grid grid_top_bounds12581 j

theorem radii12581 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12581.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12581 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12581 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12581.grid grid_top_bounds12581 j hθ

noncomputable def covarianceInputs12581 :
    BstLean.Part263.CovarianceInputs 12581 scalarRow12581.grid parameters (caps repair12581) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12581 grid_top_bounds12581 repair12581

noncomputable def covarianceEvent12581 : Set (AgFam 12581) :=
  BstLean.Part263.covarianceEvent 12581 scalarRow12581.grid parameters

theorem covarianceEvent12581_measurable : MeasurableSet covarianceEvent12581 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12581_payment :
    (retDist (paperDesignP 12581).toCentres).real
      (agentEv (paperDesignP 12581) covarianceEvent12581)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12581

theorem localCov12581 : BstLean.Part259.LocalCovarianceOn covarianceEvent12581
    (BstLean.Part263.cell scalarRow12581.grid) (caps repair12581) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12581

theorem covarianceGood12581_payment :
    (retDist (paperDesignP 12581).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12581)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12581_payment



end BstLean.Part269.N12581

namespace BstLean.Part269.N12581
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12581}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12581.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12581) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12581).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12581 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12581) (by norm_num) BstLean.Part268.WorldRow12581.worldPackage rfl
    BstLean.Part268.WorldRow12581.product_lower (BstLean.Part268.WorldRow12581.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12581} (hw : c ∈ Hof BstLean.Part268.WorldRow12581.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12581) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12581) (by norm_num) BstLean.Part268.WorldRow12581.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12581} (hw : c ∈ Hof BstLean.Part268.WorldRow12581.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12581) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12581).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12581) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12581_eq : scalarRow12581.targetFrame = BstLean.Part268.agent12581.frame := by
  norm_num [scalarRow12581,BstLean.Part268.agent12581]

noncomputable def frameData12581 : BstLean.Part264b.FrameData 12581 :=
  BstLean.Part269.frameData_from_numerics (n := 12581) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12581.worldPackage rfl BstLean.Part268.WorldRow12581.product_lower (BstLean.Part268.WorldRow12581.producthi.2.trans (by norm_num))
    scalarRow12581 repair12581 covarianceInputs12581 (fun i hi => sourceNumerics12581 hi)
    BstLean.Part268.agent12581.frame targetFrame12581_eq


end BstLean.Part269.N12581

namespace BstLean.Part269.N12582
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12582 : scalarRow12582.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12582, BstLean.Part268.grid12582, BstLean.Part263.worldGrid]

theorem supplies12582 (j : Fin 43) : Supply 12582 (parameters j)
    (cellLower scalarRow12582.grid (sourceIndex j))
    (cellUpper scalarRow12582.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12582.grid grid_top_bounds12582 j

theorem radii12582 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12582.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12582 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12582 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12582.grid grid_top_bounds12582 j hθ

noncomputable def covarianceInputs12582 :
    BstLean.Part263.CovarianceInputs 12582 scalarRow12582.grid parameters (caps repair12582) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12582 grid_top_bounds12582 repair12582

noncomputable def covarianceEvent12582 : Set (AgFam 12582) :=
  BstLean.Part263.covarianceEvent 12582 scalarRow12582.grid parameters

theorem covarianceEvent12582_measurable : MeasurableSet covarianceEvent12582 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12582_payment :
    (retDist (paperDesignP 12582).toCentres).real
      (agentEv (paperDesignP 12582) covarianceEvent12582)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12582

theorem localCov12582 : BstLean.Part259.LocalCovarianceOn covarianceEvent12582
    (BstLean.Part263.cell scalarRow12582.grid) (caps repair12582) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12582

theorem covarianceGood12582_payment :
    (retDist (paperDesignP 12582).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12582)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12582_payment



end BstLean.Part269.N12582

namespace BstLean.Part269.N12582
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12582}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12582.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12582) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12582).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12582 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12582) (by norm_num) BstLean.Part268.WorldRow12582.worldPackage rfl
    BstLean.Part268.WorldRow12582.product_lower (BstLean.Part268.WorldRow12582.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12582} (hw : c ∈ Hof BstLean.Part268.WorldRow12582.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12582) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12582) (by norm_num) BstLean.Part268.WorldRow12582.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12582} (hw : c ∈ Hof BstLean.Part268.WorldRow12582.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12582) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12582).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12582) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12582_eq : scalarRow12582.targetFrame = BstLean.Part268.agent12582.frame := by
  norm_num [scalarRow12582,BstLean.Part268.agent12582]

noncomputable def frameData12582 : BstLean.Part264b.FrameData 12582 :=
  BstLean.Part269.frameData_from_numerics (n := 12582) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12582.worldPackage rfl BstLean.Part268.WorldRow12582.product_lower (BstLean.Part268.WorldRow12582.producthi.2.trans (by norm_num))
    scalarRow12582 repair12582 covarianceInputs12582 (fun i hi => sourceNumerics12582 hi)
    BstLean.Part268.agent12582.frame targetFrame12582_eq


end BstLean.Part269.N12582

namespace BstLean.Part269.N12583
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12583 : scalarRow12583.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12583, BstLean.Part268.grid12583, BstLean.Part263.worldGrid]

theorem supplies12583 (j : Fin 43) : Supply 12583 (parameters j)
    (cellLower scalarRow12583.grid (sourceIndex j))
    (cellUpper scalarRow12583.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12583.grid grid_top_bounds12583 j

theorem radii12583 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12583.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12583 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12583 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12583.grid grid_top_bounds12583 j hθ

noncomputable def covarianceInputs12583 :
    BstLean.Part263.CovarianceInputs 12583 scalarRow12583.grid parameters (caps repair12583) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12583 grid_top_bounds12583 repair12583

noncomputable def covarianceEvent12583 : Set (AgFam 12583) :=
  BstLean.Part263.covarianceEvent 12583 scalarRow12583.grid parameters

theorem covarianceEvent12583_measurable : MeasurableSet covarianceEvent12583 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12583_payment :
    (retDist (paperDesignP 12583).toCentres).real
      (agentEv (paperDesignP 12583) covarianceEvent12583)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12583

theorem localCov12583 : BstLean.Part259.LocalCovarianceOn covarianceEvent12583
    (BstLean.Part263.cell scalarRow12583.grid) (caps repair12583) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12583

theorem covarianceGood12583_payment :
    (retDist (paperDesignP 12583).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12583)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12583_payment



end BstLean.Part269.N12583

namespace BstLean.Part269.N12583
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12583}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12583.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12583) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12583).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12583 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12583) (by norm_num) BstLean.Part268.WorldRow12583.worldPackage rfl
    BstLean.Part268.WorldRow12583.product_lower (BstLean.Part268.WorldRow12583.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12583} (hw : c ∈ Hof BstLean.Part268.WorldRow12583.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12583) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12583) (by norm_num) BstLean.Part268.WorldRow12583.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12583} (hw : c ∈ Hof BstLean.Part268.WorldRow12583.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12583) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12583).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12583) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12583_eq : scalarRow12583.targetFrame = BstLean.Part268.agent12583.frame := by
  norm_num [scalarRow12583,BstLean.Part268.agent12583]

noncomputable def frameData12583 : BstLean.Part264b.FrameData 12583 :=
  BstLean.Part269.frameData_from_numerics (n := 12583) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12583.worldPackage rfl BstLean.Part268.WorldRow12583.product_lower (BstLean.Part268.WorldRow12583.producthi.2.trans (by norm_num))
    scalarRow12583 repair12583 covarianceInputs12583 (fun i hi => sourceNumerics12583 hi)
    BstLean.Part268.agent12583.frame targetFrame12583_eq


end BstLean.Part269.N12583

namespace BstLean.Part269.N12584
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12584 : scalarRow12584.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12584, BstLean.Part268.grid12584, BstLean.Part263.worldGrid]

theorem supplies12584 (j : Fin 43) : Supply 12584 (parameters j)
    (cellLower scalarRow12584.grid (sourceIndex j))
    (cellUpper scalarRow12584.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12584.grid grid_top_bounds12584 j

theorem radii12584 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12584.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12584 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12584 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12584.grid grid_top_bounds12584 j hθ

noncomputable def covarianceInputs12584 :
    BstLean.Part263.CovarianceInputs 12584 scalarRow12584.grid parameters (caps repair12584) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12584 grid_top_bounds12584 repair12584

noncomputable def covarianceEvent12584 : Set (AgFam 12584) :=
  BstLean.Part263.covarianceEvent 12584 scalarRow12584.grid parameters

theorem covarianceEvent12584_measurable : MeasurableSet covarianceEvent12584 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12584_payment :
    (retDist (paperDesignP 12584).toCentres).real
      (agentEv (paperDesignP 12584) covarianceEvent12584)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12584

theorem localCov12584 : BstLean.Part259.LocalCovarianceOn covarianceEvent12584
    (BstLean.Part263.cell scalarRow12584.grid) (caps repair12584) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12584

theorem covarianceGood12584_payment :
    (retDist (paperDesignP 12584).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12584)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12584_payment



end BstLean.Part269.N12584

namespace BstLean.Part269.N12584
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12584}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12584.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12584) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12584).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12584 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12584) (by norm_num) BstLean.Part268.WorldRow12584.worldPackage rfl
    BstLean.Part268.WorldRow12584.product_lower (BstLean.Part268.WorldRow12584.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12584} (hw : c ∈ Hof BstLean.Part268.WorldRow12584.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12584) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12584) (by norm_num) BstLean.Part268.WorldRow12584.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12584} (hw : c ∈ Hof BstLean.Part268.WorldRow12584.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12584) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12584).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12584) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12584_eq : scalarRow12584.targetFrame = BstLean.Part268.agent12584.frame := by
  norm_num [scalarRow12584,BstLean.Part268.agent12584]

noncomputable def frameData12584 : BstLean.Part264b.FrameData 12584 :=
  BstLean.Part269.frameData_from_numerics (n := 12584) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12584.worldPackage rfl BstLean.Part268.WorldRow12584.product_lower (BstLean.Part268.WorldRow12584.producthi.2.trans (by norm_num))
    scalarRow12584 repair12584 covarianceInputs12584 (fun i hi => sourceNumerics12584 hi)
    BstLean.Part268.agent12584.frame targetFrame12584_eq


end BstLean.Part269.N12584
