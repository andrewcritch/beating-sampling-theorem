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

namespace BstLean.Part269.N12715
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12715 : scalarRow12715.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12715, BstLean.Part268.grid12715, BstLean.Part263.worldGrid]

theorem supplies12715 (j : Fin 43) : Supply 12715 (parameters j)
    (cellLower scalarRow12715.grid (sourceIndex j))
    (cellUpper scalarRow12715.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12715.grid grid_top_bounds12715 j

theorem radii12715 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12715.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12715 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12715 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12715.grid grid_top_bounds12715 j hθ

noncomputable def covarianceInputs12715 :
    BstLean.Part263.CovarianceInputs 12715 scalarRow12715.grid parameters (caps repair12715) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12715 grid_top_bounds12715 repair12715

noncomputable def covarianceEvent12715 : Set (AgFam 12715) :=
  BstLean.Part263.covarianceEvent 12715 scalarRow12715.grid parameters

theorem covarianceEvent12715_measurable : MeasurableSet covarianceEvent12715 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12715_payment :
    (retDist (paperDesignP 12715).toCentres).real
      (agentEv (paperDesignP 12715) covarianceEvent12715)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12715

theorem localCov12715 : BstLean.Part259.LocalCovarianceOn covarianceEvent12715
    (BstLean.Part263.cell scalarRow12715.grid) (caps repair12715) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12715

theorem covarianceGood12715_payment :
    (retDist (paperDesignP 12715).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12715)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12715_payment



end BstLean.Part269.N12715

namespace BstLean.Part269.N12715
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12715}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12715.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12715) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12715).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12715 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12715) (by norm_num) BstLean.Part268.WorldRow12715.worldPackage rfl
    BstLean.Part268.WorldRow12715.product_lower (BstLean.Part268.WorldRow12715.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12715} (hw : c ∈ Hof BstLean.Part268.WorldRow12715.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12715) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12715) (by norm_num) BstLean.Part268.WorldRow12715.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12715} (hw : c ∈ Hof BstLean.Part268.WorldRow12715.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12715) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12715).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12715) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12715_eq : scalarRow12715.targetFrame = BstLean.Part268.agent12715.frame := by
  norm_num [scalarRow12715,BstLean.Part268.agent12715]

noncomputable def frameData12715 : BstLean.Part264b.FrameData 12715 :=
  BstLean.Part269.frameData_from_numerics (n := 12715) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12715.worldPackage rfl BstLean.Part268.WorldRow12715.product_lower (BstLean.Part268.WorldRow12715.producthi.2.trans (by norm_num))
    scalarRow12715 repair12715 covarianceInputs12715 (fun i hi => sourceNumerics12715 hi)
    BstLean.Part268.agent12715.frame targetFrame12715_eq


end BstLean.Part269.N12715

namespace BstLean.Part269.N12716
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12716 : scalarRow12716.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12716, BstLean.Part268.grid12716, BstLean.Part263.worldGrid]

theorem supplies12716 (j : Fin 43) : Supply 12716 (parameters j)
    (cellLower scalarRow12716.grid (sourceIndex j))
    (cellUpper scalarRow12716.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12716.grid grid_top_bounds12716 j

theorem radii12716 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12716.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12716 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12716 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12716.grid grid_top_bounds12716 j hθ

noncomputable def covarianceInputs12716 :
    BstLean.Part263.CovarianceInputs 12716 scalarRow12716.grid parameters (caps repair12716) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12716 grid_top_bounds12716 repair12716

noncomputable def covarianceEvent12716 : Set (AgFam 12716) :=
  BstLean.Part263.covarianceEvent 12716 scalarRow12716.grid parameters

theorem covarianceEvent12716_measurable : MeasurableSet covarianceEvent12716 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12716_payment :
    (retDist (paperDesignP 12716).toCentres).real
      (agentEv (paperDesignP 12716) covarianceEvent12716)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12716

theorem localCov12716 : BstLean.Part259.LocalCovarianceOn covarianceEvent12716
    (BstLean.Part263.cell scalarRow12716.grid) (caps repair12716) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12716

theorem covarianceGood12716_payment :
    (retDist (paperDesignP 12716).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12716)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12716_payment



end BstLean.Part269.N12716

namespace BstLean.Part269.N12716
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12716}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12716.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12716) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12716).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12716 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12716) (by norm_num) BstLean.Part268.WorldRow12716.worldPackage rfl
    BstLean.Part268.WorldRow12716.product_lower (BstLean.Part268.WorldRow12716.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12716} (hw : c ∈ Hof BstLean.Part268.WorldRow12716.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12716) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12716) (by norm_num) BstLean.Part268.WorldRow12716.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12716} (hw : c ∈ Hof BstLean.Part268.WorldRow12716.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12716) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12716).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12716) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12716_eq : scalarRow12716.targetFrame = BstLean.Part268.agent12716.frame := by
  norm_num [scalarRow12716,BstLean.Part268.agent12716]

noncomputable def frameData12716 : BstLean.Part264b.FrameData 12716 :=
  BstLean.Part269.frameData_from_numerics (n := 12716) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12716.worldPackage rfl BstLean.Part268.WorldRow12716.product_lower (BstLean.Part268.WorldRow12716.producthi.2.trans (by norm_num))
    scalarRow12716 repair12716 covarianceInputs12716 (fun i hi => sourceNumerics12716 hi)
    BstLean.Part268.agent12716.frame targetFrame12716_eq


end BstLean.Part269.N12716

namespace BstLean.Part269.N12717
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12717 : scalarRow12717.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12717, BstLean.Part268.grid12717, BstLean.Part263.worldGrid]

theorem supplies12717 (j : Fin 43) : Supply 12717 (parameters j)
    (cellLower scalarRow12717.grid (sourceIndex j))
    (cellUpper scalarRow12717.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12717.grid grid_top_bounds12717 j

theorem radii12717 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12717.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12717 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12717 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12717.grid grid_top_bounds12717 j hθ

noncomputable def covarianceInputs12717 :
    BstLean.Part263.CovarianceInputs 12717 scalarRow12717.grid parameters (caps repair12717) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12717 grid_top_bounds12717 repair12717

noncomputable def covarianceEvent12717 : Set (AgFam 12717) :=
  BstLean.Part263.covarianceEvent 12717 scalarRow12717.grid parameters

theorem covarianceEvent12717_measurable : MeasurableSet covarianceEvent12717 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12717_payment :
    (retDist (paperDesignP 12717).toCentres).real
      (agentEv (paperDesignP 12717) covarianceEvent12717)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12717

theorem localCov12717 : BstLean.Part259.LocalCovarianceOn covarianceEvent12717
    (BstLean.Part263.cell scalarRow12717.grid) (caps repair12717) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12717

theorem covarianceGood12717_payment :
    (retDist (paperDesignP 12717).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12717)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12717_payment



end BstLean.Part269.N12717

namespace BstLean.Part269.N12717
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12717}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12717.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12717) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12717).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12717 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12717) (by norm_num) BstLean.Part268.WorldRow12717.worldPackage rfl
    BstLean.Part268.WorldRow12717.product_lower (BstLean.Part268.WorldRow12717.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12717} (hw : c ∈ Hof BstLean.Part268.WorldRow12717.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12717) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12717) (by norm_num) BstLean.Part268.WorldRow12717.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12717} (hw : c ∈ Hof BstLean.Part268.WorldRow12717.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12717) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12717).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12717) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12717_eq : scalarRow12717.targetFrame = BstLean.Part268.agent12717.frame := by
  norm_num [scalarRow12717,BstLean.Part268.agent12717]

noncomputable def frameData12717 : BstLean.Part264b.FrameData 12717 :=
  BstLean.Part269.frameData_from_numerics (n := 12717) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12717.worldPackage rfl BstLean.Part268.WorldRow12717.product_lower (BstLean.Part268.WorldRow12717.producthi.2.trans (by norm_num))
    scalarRow12717 repair12717 covarianceInputs12717 (fun i hi => sourceNumerics12717 hi)
    BstLean.Part268.agent12717.frame targetFrame12717_eq


end BstLean.Part269.N12717

namespace BstLean.Part269.N12718
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12718 : scalarRow12718.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12718, BstLean.Part268.grid12718, BstLean.Part263.worldGrid]

theorem supplies12718 (j : Fin 43) : Supply 12718 (parameters j)
    (cellLower scalarRow12718.grid (sourceIndex j))
    (cellUpper scalarRow12718.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12718.grid grid_top_bounds12718 j

theorem radii12718 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12718.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12718 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12718 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12718.grid grid_top_bounds12718 j hθ

noncomputable def covarianceInputs12718 :
    BstLean.Part263.CovarianceInputs 12718 scalarRow12718.grid parameters (caps repair12718) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12718 grid_top_bounds12718 repair12718

noncomputable def covarianceEvent12718 : Set (AgFam 12718) :=
  BstLean.Part263.covarianceEvent 12718 scalarRow12718.grid parameters

theorem covarianceEvent12718_measurable : MeasurableSet covarianceEvent12718 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12718_payment :
    (retDist (paperDesignP 12718).toCentres).real
      (agentEv (paperDesignP 12718) covarianceEvent12718)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12718

theorem localCov12718 : BstLean.Part259.LocalCovarianceOn covarianceEvent12718
    (BstLean.Part263.cell scalarRow12718.grid) (caps repair12718) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12718

theorem covarianceGood12718_payment :
    (retDist (paperDesignP 12718).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12718)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12718_payment



end BstLean.Part269.N12718

namespace BstLean.Part269.N12718
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12718}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12718.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12718) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12718).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12718 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12718) (by norm_num) BstLean.Part268.WorldRow12718.worldPackage rfl
    BstLean.Part268.WorldRow12718.product_lower (BstLean.Part268.WorldRow12718.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12718} (hw : c ∈ Hof BstLean.Part268.WorldRow12718.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12718) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12718) (by norm_num) BstLean.Part268.WorldRow12718.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12718} (hw : c ∈ Hof BstLean.Part268.WorldRow12718.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12718) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12718).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12718) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12718_eq : scalarRow12718.targetFrame = BstLean.Part268.agent12718.frame := by
  norm_num [scalarRow12718,BstLean.Part268.agent12718]

noncomputable def frameData12718 : BstLean.Part264b.FrameData 12718 :=
  BstLean.Part269.frameData_from_numerics (n := 12718) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12718.worldPackage rfl BstLean.Part268.WorldRow12718.product_lower (BstLean.Part268.WorldRow12718.producthi.2.trans (by norm_num))
    scalarRow12718 repair12718 covarianceInputs12718 (fun i hi => sourceNumerics12718 hi)
    BstLean.Part268.agent12718.frame targetFrame12718_eq


end BstLean.Part269.N12718

namespace BstLean.Part269.N12719
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12719 : scalarRow12719.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12719, BstLean.Part268.grid12719, BstLean.Part263.worldGrid]

theorem supplies12719 (j : Fin 43) : Supply 12719 (parameters j)
    (cellLower scalarRow12719.grid (sourceIndex j))
    (cellUpper scalarRow12719.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12719.grid grid_top_bounds12719 j

theorem radii12719 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12719.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12719 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12719 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12719.grid grid_top_bounds12719 j hθ

noncomputable def covarianceInputs12719 :
    BstLean.Part263.CovarianceInputs 12719 scalarRow12719.grid parameters (caps repair12719) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12719 grid_top_bounds12719 repair12719

noncomputable def covarianceEvent12719 : Set (AgFam 12719) :=
  BstLean.Part263.covarianceEvent 12719 scalarRow12719.grid parameters

theorem covarianceEvent12719_measurable : MeasurableSet covarianceEvent12719 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12719_payment :
    (retDist (paperDesignP 12719).toCentres).real
      (agentEv (paperDesignP 12719) covarianceEvent12719)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12719

theorem localCov12719 : BstLean.Part259.LocalCovarianceOn covarianceEvent12719
    (BstLean.Part263.cell scalarRow12719.grid) (caps repair12719) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12719

theorem covarianceGood12719_payment :
    (retDist (paperDesignP 12719).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12719)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12719_payment



end BstLean.Part269.N12719

namespace BstLean.Part269.N12719
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12719}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12719.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12719) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12719).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12719 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12719) (by norm_num) BstLean.Part268.WorldRow12719.worldPackage rfl
    BstLean.Part268.WorldRow12719.product_lower (BstLean.Part268.WorldRow12719.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12719} (hw : c ∈ Hof BstLean.Part268.WorldRow12719.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12719) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12719) (by norm_num) BstLean.Part268.WorldRow12719.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12719} (hw : c ∈ Hof BstLean.Part268.WorldRow12719.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12719) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12719).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12719) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12719_eq : scalarRow12719.targetFrame = BstLean.Part268.agent12719.frame := by
  norm_num [scalarRow12719,BstLean.Part268.agent12719]

noncomputable def frameData12719 : BstLean.Part264b.FrameData 12719 :=
  BstLean.Part269.frameData_from_numerics (n := 12719) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12719.worldPackage rfl BstLean.Part268.WorldRow12719.product_lower (BstLean.Part268.WorldRow12719.producthi.2.trans (by norm_num))
    scalarRow12719 repair12719 covarianceInputs12719 (fun i hi => sourceNumerics12719 hi)
    BstLean.Part268.agent12719.frame targetFrame12719_eq


end BstLean.Part269.N12719
