import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World17Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs17
import BstLean.Part269Rows17
import BstLean.Part269Sources17
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12775
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12775 : scalarRow12775.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12775, BstLean.Part268.grid12775, BstLean.Part263.worldGrid]

theorem supplies12775 (j : Fin 43) : Supply 12775 (parameters j)
    (cellLower scalarRow12775.grid (sourceIndex j))
    (cellUpper scalarRow12775.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12775.grid grid_top_bounds12775 j

theorem radii12775 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12775.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12775 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12775 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12775.grid grid_top_bounds12775 j hθ

noncomputable def covarianceInputs12775 :
    BstLean.Part263.CovarianceInputs 12775 scalarRow12775.grid parameters (caps repair12775) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12775 grid_top_bounds12775 repair12775

noncomputable def covarianceEvent12775 : Set (AgFam 12775) :=
  BstLean.Part263.covarianceEvent 12775 scalarRow12775.grid parameters

theorem covarianceEvent12775_measurable : MeasurableSet covarianceEvent12775 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12775_payment :
    (retDist (paperDesignP 12775).toCentres).real
      (agentEv (paperDesignP 12775) covarianceEvent12775)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12775

theorem localCov12775 : BstLean.Part259.LocalCovarianceOn covarianceEvent12775
    (BstLean.Part263.cell scalarRow12775.grid) (caps repair12775) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12775

theorem covarianceGood12775_payment :
    (retDist (paperDesignP 12775).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12775)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12775_payment



end BstLean.Part269.N12775

namespace BstLean.Part269.N12775
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12775}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12775.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12775) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12775).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12775 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12775) (by norm_num) BstLean.Part268.WorldRow12775.worldPackage rfl
    BstLean.Part268.WorldRow12775.product_lower (BstLean.Part268.WorldRow12775.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12775} (hw : c ∈ Hof BstLean.Part268.WorldRow12775.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12775) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12775) (by norm_num) BstLean.Part268.WorldRow12775.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12775} (hw : c ∈ Hof BstLean.Part268.WorldRow12775.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12775) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12775).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12775) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12775_eq : scalarRow12775.targetFrame = BstLean.Part268.agent12775.frame := by
  norm_num [scalarRow12775,BstLean.Part268.agent12775]

noncomputable def frameData12775 : BstLean.Part264b.FrameData 12775 :=
  BstLean.Part269.frameData_from_numerics (n := 12775) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12775.worldPackage rfl BstLean.Part268.WorldRow12775.product_lower (BstLean.Part268.WorldRow12775.producthi.2.trans (by norm_num))
    scalarRow12775 repair12775 covarianceInputs12775 (fun i hi => sourceNumerics12775 hi)
    BstLean.Part268.agent12775.frame targetFrame12775_eq


end BstLean.Part269.N12775

namespace BstLean.Part269.N12776
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12776 : scalarRow12776.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12776, BstLean.Part268.grid12776, BstLean.Part263.worldGrid]

theorem supplies12776 (j : Fin 43) : Supply 12776 (parameters j)
    (cellLower scalarRow12776.grid (sourceIndex j))
    (cellUpper scalarRow12776.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12776.grid grid_top_bounds12776 j

theorem radii12776 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12776.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12776 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12776 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12776.grid grid_top_bounds12776 j hθ

noncomputable def covarianceInputs12776 :
    BstLean.Part263.CovarianceInputs 12776 scalarRow12776.grid parameters (caps repair12776) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12776 grid_top_bounds12776 repair12776

noncomputable def covarianceEvent12776 : Set (AgFam 12776) :=
  BstLean.Part263.covarianceEvent 12776 scalarRow12776.grid parameters

theorem covarianceEvent12776_measurable : MeasurableSet covarianceEvent12776 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12776_payment :
    (retDist (paperDesignP 12776).toCentres).real
      (agentEv (paperDesignP 12776) covarianceEvent12776)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12776

theorem localCov12776 : BstLean.Part259.LocalCovarianceOn covarianceEvent12776
    (BstLean.Part263.cell scalarRow12776.grid) (caps repair12776) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12776

theorem covarianceGood12776_payment :
    (retDist (paperDesignP 12776).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12776)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12776_payment



end BstLean.Part269.N12776

namespace BstLean.Part269.N12776
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12776}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12776.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12776) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12776).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12776 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12776) (by norm_num) BstLean.Part268.WorldRow12776.worldPackage rfl
    BstLean.Part268.WorldRow12776.product_lower (BstLean.Part268.WorldRow12776.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12776} (hw : c ∈ Hof BstLean.Part268.WorldRow12776.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12776) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12776) (by norm_num) BstLean.Part268.WorldRow12776.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12776} (hw : c ∈ Hof BstLean.Part268.WorldRow12776.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12776) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12776).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12776) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12776_eq : scalarRow12776.targetFrame = BstLean.Part268.agent12776.frame := by
  norm_num [scalarRow12776,BstLean.Part268.agent12776]

noncomputable def frameData12776 : BstLean.Part264b.FrameData 12776 :=
  BstLean.Part269.frameData_from_numerics (n := 12776) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12776.worldPackage rfl BstLean.Part268.WorldRow12776.product_lower (BstLean.Part268.WorldRow12776.producthi.2.trans (by norm_num))
    scalarRow12776 repair12776 covarianceInputs12776 (fun i hi => sourceNumerics12776 hi)
    BstLean.Part268.agent12776.frame targetFrame12776_eq


end BstLean.Part269.N12776

namespace BstLean.Part269.N12777
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12777 : scalarRow12777.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12777, BstLean.Part268.grid12777, BstLean.Part263.worldGrid]

theorem supplies12777 (j : Fin 43) : Supply 12777 (parameters j)
    (cellLower scalarRow12777.grid (sourceIndex j))
    (cellUpper scalarRow12777.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12777.grid grid_top_bounds12777 j

theorem radii12777 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12777.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12777 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12777 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12777.grid grid_top_bounds12777 j hθ

noncomputable def covarianceInputs12777 :
    BstLean.Part263.CovarianceInputs 12777 scalarRow12777.grid parameters (caps repair12777) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12777 grid_top_bounds12777 repair12777

noncomputable def covarianceEvent12777 : Set (AgFam 12777) :=
  BstLean.Part263.covarianceEvent 12777 scalarRow12777.grid parameters

theorem covarianceEvent12777_measurable : MeasurableSet covarianceEvent12777 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12777_payment :
    (retDist (paperDesignP 12777).toCentres).real
      (agentEv (paperDesignP 12777) covarianceEvent12777)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12777

theorem localCov12777 : BstLean.Part259.LocalCovarianceOn covarianceEvent12777
    (BstLean.Part263.cell scalarRow12777.grid) (caps repair12777) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12777

theorem covarianceGood12777_payment :
    (retDist (paperDesignP 12777).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12777)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12777_payment



end BstLean.Part269.N12777

namespace BstLean.Part269.N12777
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12777}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12777.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12777) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12777).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12777 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12777) (by norm_num) BstLean.Part268.WorldRow12777.worldPackage rfl
    BstLean.Part268.WorldRow12777.product_lower (BstLean.Part268.WorldRow12777.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12777} (hw : c ∈ Hof BstLean.Part268.WorldRow12777.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12777) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12777) (by norm_num) BstLean.Part268.WorldRow12777.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12777} (hw : c ∈ Hof BstLean.Part268.WorldRow12777.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12777) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12777).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12777) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12777_eq : scalarRow12777.targetFrame = BstLean.Part268.agent12777.frame := by
  norm_num [scalarRow12777,BstLean.Part268.agent12777]

noncomputable def frameData12777 : BstLean.Part264b.FrameData 12777 :=
  BstLean.Part269.frameData_from_numerics (n := 12777) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12777.worldPackage rfl BstLean.Part268.WorldRow12777.product_lower (BstLean.Part268.WorldRow12777.producthi.2.trans (by norm_num))
    scalarRow12777 repair12777 covarianceInputs12777 (fun i hi => sourceNumerics12777 hi)
    BstLean.Part268.agent12777.frame targetFrame12777_eq


end BstLean.Part269.N12777

namespace BstLean.Part269.N12778
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12778 : scalarRow12778.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12778, BstLean.Part268.grid12778, BstLean.Part263.worldGrid]

theorem supplies12778 (j : Fin 43) : Supply 12778 (parameters j)
    (cellLower scalarRow12778.grid (sourceIndex j))
    (cellUpper scalarRow12778.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12778.grid grid_top_bounds12778 j

theorem radii12778 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12778.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12778 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12778 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12778.grid grid_top_bounds12778 j hθ

noncomputable def covarianceInputs12778 :
    BstLean.Part263.CovarianceInputs 12778 scalarRow12778.grid parameters (caps repair12778) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12778 grid_top_bounds12778 repair12778

noncomputable def covarianceEvent12778 : Set (AgFam 12778) :=
  BstLean.Part263.covarianceEvent 12778 scalarRow12778.grid parameters

theorem covarianceEvent12778_measurable : MeasurableSet covarianceEvent12778 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12778_payment :
    (retDist (paperDesignP 12778).toCentres).real
      (agentEv (paperDesignP 12778) covarianceEvent12778)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12778

theorem localCov12778 : BstLean.Part259.LocalCovarianceOn covarianceEvent12778
    (BstLean.Part263.cell scalarRow12778.grid) (caps repair12778) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12778

theorem covarianceGood12778_payment :
    (retDist (paperDesignP 12778).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12778)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12778_payment



end BstLean.Part269.N12778

namespace BstLean.Part269.N12778
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12778}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12778.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12778) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12778).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12778 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12778) (by norm_num) BstLean.Part268.WorldRow12778.worldPackage rfl
    BstLean.Part268.WorldRow12778.product_lower (BstLean.Part268.WorldRow12778.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12778} (hw : c ∈ Hof BstLean.Part268.WorldRow12778.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12778) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12778) (by norm_num) BstLean.Part268.WorldRow12778.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12778} (hw : c ∈ Hof BstLean.Part268.WorldRow12778.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12778) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12778).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12778) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12778_eq : scalarRow12778.targetFrame = BstLean.Part268.agent12778.frame := by
  norm_num [scalarRow12778,BstLean.Part268.agent12778]

noncomputable def frameData12778 : BstLean.Part264b.FrameData 12778 :=
  BstLean.Part269.frameData_from_numerics (n := 12778) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12778.worldPackage rfl BstLean.Part268.WorldRow12778.product_lower (BstLean.Part268.WorldRow12778.producthi.2.trans (by norm_num))
    scalarRow12778 repair12778 covarianceInputs12778 (fun i hi => sourceNumerics12778 hi)
    BstLean.Part268.agent12778.frame targetFrame12778_eq


end BstLean.Part269.N12778

namespace BstLean.Part269.N12779
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12779 : scalarRow12779.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12779, BstLean.Part268.grid12779, BstLean.Part263.worldGrid]

theorem supplies12779 (j : Fin 43) : Supply 12779 (parameters j)
    (cellLower scalarRow12779.grid (sourceIndex j))
    (cellUpper scalarRow12779.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12779.grid grid_top_bounds12779 j

theorem radii12779 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12779.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12779 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12779 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12779.grid grid_top_bounds12779 j hθ

noncomputable def covarianceInputs12779 :
    BstLean.Part263.CovarianceInputs 12779 scalarRow12779.grid parameters (caps repair12779) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12779 grid_top_bounds12779 repair12779

noncomputable def covarianceEvent12779 : Set (AgFam 12779) :=
  BstLean.Part263.covarianceEvent 12779 scalarRow12779.grid parameters

theorem covarianceEvent12779_measurable : MeasurableSet covarianceEvent12779 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12779_payment :
    (retDist (paperDesignP 12779).toCentres).real
      (agentEv (paperDesignP 12779) covarianceEvent12779)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12779

theorem localCov12779 : BstLean.Part259.LocalCovarianceOn covarianceEvent12779
    (BstLean.Part263.cell scalarRow12779.grid) (caps repair12779) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12779

theorem covarianceGood12779_payment :
    (retDist (paperDesignP 12779).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12779)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12779_payment



end BstLean.Part269.N12779

namespace BstLean.Part269.N12779
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12779}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12779.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12779) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12779).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12779 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12779) (by norm_num) BstLean.Part268.WorldRow12779.worldPackage rfl
    BstLean.Part268.WorldRow12779.product_lower (BstLean.Part268.WorldRow12779.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12779} (hw : c ∈ Hof BstLean.Part268.WorldRow12779.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12779) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12779) (by norm_num) BstLean.Part268.WorldRow12779.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12779} (hw : c ∈ Hof BstLean.Part268.WorldRow12779.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12779) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12779).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12779) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12779_eq : scalarRow12779.targetFrame = BstLean.Part268.agent12779.frame := by
  norm_num [scalarRow12779,BstLean.Part268.agent12779]

noncomputable def frameData12779 : BstLean.Part264b.FrameData 12779 :=
  BstLean.Part269.frameData_from_numerics (n := 12779) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12779.worldPackage rfl BstLean.Part268.WorldRow12779.product_lower (BstLean.Part268.WorldRow12779.producthi.2.trans (by norm_num))
    scalarRow12779 repair12779 covarianceInputs12779 (fun i hi => sourceNumerics12779 hi)
    BstLean.Part268.agent12779.frame targetFrame12779_eq


end BstLean.Part269.N12779
