import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World12Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs12
import BstLean.Part269Rows12
import BstLean.Part269Sources12
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12665
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12665 : scalarRow12665.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12665, BstLean.Part268.grid12665, BstLean.Part263.worldGrid]

theorem supplies12665 (j : Fin 43) : Supply 12665 (parameters j)
    (cellLower scalarRow12665.grid (sourceIndex j))
    (cellUpper scalarRow12665.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12665.grid grid_top_bounds12665 j

theorem radii12665 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12665.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12665 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12665 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12665.grid grid_top_bounds12665 j hθ

noncomputable def covarianceInputs12665 :
    BstLean.Part263.CovarianceInputs 12665 scalarRow12665.grid parameters (caps repair12665) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12665 grid_top_bounds12665 repair12665

noncomputable def covarianceEvent12665 : Set (AgFam 12665) :=
  BstLean.Part263.covarianceEvent 12665 scalarRow12665.grid parameters

theorem covarianceEvent12665_measurable : MeasurableSet covarianceEvent12665 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12665_payment :
    (retDist (paperDesignP 12665).toCentres).real
      (agentEv (paperDesignP 12665) covarianceEvent12665)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12665

theorem localCov12665 : BstLean.Part259.LocalCovarianceOn covarianceEvent12665
    (BstLean.Part263.cell scalarRow12665.grid) (caps repair12665) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12665

theorem covarianceGood12665_payment :
    (retDist (paperDesignP 12665).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12665)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12665_payment



end BstLean.Part269.N12665

namespace BstLean.Part269.N12665
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12665}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12665.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12665) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12665).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12665 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12665) (by norm_num) BstLean.Part268.WorldRow12665.worldPackage rfl
    BstLean.Part268.WorldRow12665.product_lower (BstLean.Part268.WorldRow12665.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12665} (hw : c ∈ Hof BstLean.Part268.WorldRow12665.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12665) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12665) (by norm_num) BstLean.Part268.WorldRow12665.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12665} (hw : c ∈ Hof BstLean.Part268.WorldRow12665.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12665) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12665).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12665) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12665_eq : scalarRow12665.targetFrame = BstLean.Part268.agent12665.frame := by
  norm_num [scalarRow12665,BstLean.Part268.agent12665]

noncomputable def frameData12665 : BstLean.Part264b.FrameData 12665 :=
  BstLean.Part269.frameData_from_numerics (n := 12665) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12665.worldPackage rfl BstLean.Part268.WorldRow12665.product_lower (BstLean.Part268.WorldRow12665.producthi.2.trans (by norm_num))
    scalarRow12665 repair12665 covarianceInputs12665 (fun i hi => sourceNumerics12665 hi)
    BstLean.Part268.agent12665.frame targetFrame12665_eq


end BstLean.Part269.N12665

namespace BstLean.Part269.N12666
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12666 : scalarRow12666.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12666, BstLean.Part268.grid12666, BstLean.Part263.worldGrid]

theorem supplies12666 (j : Fin 43) : Supply 12666 (parameters j)
    (cellLower scalarRow12666.grid (sourceIndex j))
    (cellUpper scalarRow12666.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12666.grid grid_top_bounds12666 j

theorem radii12666 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12666.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12666 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12666 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12666.grid grid_top_bounds12666 j hθ

noncomputable def covarianceInputs12666 :
    BstLean.Part263.CovarianceInputs 12666 scalarRow12666.grid parameters (caps repair12666) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12666 grid_top_bounds12666 repair12666

noncomputable def covarianceEvent12666 : Set (AgFam 12666) :=
  BstLean.Part263.covarianceEvent 12666 scalarRow12666.grid parameters

theorem covarianceEvent12666_measurable : MeasurableSet covarianceEvent12666 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12666_payment :
    (retDist (paperDesignP 12666).toCentres).real
      (agentEv (paperDesignP 12666) covarianceEvent12666)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12666

theorem localCov12666 : BstLean.Part259.LocalCovarianceOn covarianceEvent12666
    (BstLean.Part263.cell scalarRow12666.grid) (caps repair12666) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12666

theorem covarianceGood12666_payment :
    (retDist (paperDesignP 12666).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12666)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12666_payment



end BstLean.Part269.N12666

namespace BstLean.Part269.N12666
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12666}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12666.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12666) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12666).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12666 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12666) (by norm_num) BstLean.Part268.WorldRow12666.worldPackage rfl
    BstLean.Part268.WorldRow12666.product_lower (BstLean.Part268.WorldRow12666.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12666} (hw : c ∈ Hof BstLean.Part268.WorldRow12666.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12666) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12666) (by norm_num) BstLean.Part268.WorldRow12666.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12666} (hw : c ∈ Hof BstLean.Part268.WorldRow12666.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12666) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12666).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12666) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12666_eq : scalarRow12666.targetFrame = BstLean.Part268.agent12666.frame := by
  norm_num [scalarRow12666,BstLean.Part268.agent12666]

noncomputable def frameData12666 : BstLean.Part264b.FrameData 12666 :=
  BstLean.Part269.frameData_from_numerics (n := 12666) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12666.worldPackage rfl BstLean.Part268.WorldRow12666.product_lower (BstLean.Part268.WorldRow12666.producthi.2.trans (by norm_num))
    scalarRow12666 repair12666 covarianceInputs12666 (fun i hi => sourceNumerics12666 hi)
    BstLean.Part268.agent12666.frame targetFrame12666_eq


end BstLean.Part269.N12666

namespace BstLean.Part269.N12667
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12667 : scalarRow12667.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12667, BstLean.Part268.grid12667, BstLean.Part263.worldGrid]

theorem supplies12667 (j : Fin 43) : Supply 12667 (parameters j)
    (cellLower scalarRow12667.grid (sourceIndex j))
    (cellUpper scalarRow12667.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12667.grid grid_top_bounds12667 j

theorem radii12667 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12667.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12667 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12667 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12667.grid grid_top_bounds12667 j hθ

noncomputable def covarianceInputs12667 :
    BstLean.Part263.CovarianceInputs 12667 scalarRow12667.grid parameters (caps repair12667) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12667 grid_top_bounds12667 repair12667

noncomputable def covarianceEvent12667 : Set (AgFam 12667) :=
  BstLean.Part263.covarianceEvent 12667 scalarRow12667.grid parameters

theorem covarianceEvent12667_measurable : MeasurableSet covarianceEvent12667 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12667_payment :
    (retDist (paperDesignP 12667).toCentres).real
      (agentEv (paperDesignP 12667) covarianceEvent12667)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12667

theorem localCov12667 : BstLean.Part259.LocalCovarianceOn covarianceEvent12667
    (BstLean.Part263.cell scalarRow12667.grid) (caps repair12667) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12667

theorem covarianceGood12667_payment :
    (retDist (paperDesignP 12667).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12667)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12667_payment



end BstLean.Part269.N12667

namespace BstLean.Part269.N12667
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12667}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12667.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12667) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12667).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12667 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12667) (by norm_num) BstLean.Part268.WorldRow12667.worldPackage rfl
    BstLean.Part268.WorldRow12667.product_lower (BstLean.Part268.WorldRow12667.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12667} (hw : c ∈ Hof BstLean.Part268.WorldRow12667.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12667) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12667) (by norm_num) BstLean.Part268.WorldRow12667.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12667} (hw : c ∈ Hof BstLean.Part268.WorldRow12667.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12667) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12667).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12667) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12667_eq : scalarRow12667.targetFrame = BstLean.Part268.agent12667.frame := by
  norm_num [scalarRow12667,BstLean.Part268.agent12667]

noncomputable def frameData12667 : BstLean.Part264b.FrameData 12667 :=
  BstLean.Part269.frameData_from_numerics (n := 12667) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12667.worldPackage rfl BstLean.Part268.WorldRow12667.product_lower (BstLean.Part268.WorldRow12667.producthi.2.trans (by norm_num))
    scalarRow12667 repair12667 covarianceInputs12667 (fun i hi => sourceNumerics12667 hi)
    BstLean.Part268.agent12667.frame targetFrame12667_eq


end BstLean.Part269.N12667

namespace BstLean.Part269.N12668
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12668 : scalarRow12668.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12668, BstLean.Part268.grid12668, BstLean.Part263.worldGrid]

theorem supplies12668 (j : Fin 43) : Supply 12668 (parameters j)
    (cellLower scalarRow12668.grid (sourceIndex j))
    (cellUpper scalarRow12668.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12668.grid grid_top_bounds12668 j

theorem radii12668 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12668.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12668 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12668 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12668.grid grid_top_bounds12668 j hθ

noncomputable def covarianceInputs12668 :
    BstLean.Part263.CovarianceInputs 12668 scalarRow12668.grid parameters (caps repair12668) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12668 grid_top_bounds12668 repair12668

noncomputable def covarianceEvent12668 : Set (AgFam 12668) :=
  BstLean.Part263.covarianceEvent 12668 scalarRow12668.grid parameters

theorem covarianceEvent12668_measurable : MeasurableSet covarianceEvent12668 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12668_payment :
    (retDist (paperDesignP 12668).toCentres).real
      (agentEv (paperDesignP 12668) covarianceEvent12668)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12668

theorem localCov12668 : BstLean.Part259.LocalCovarianceOn covarianceEvent12668
    (BstLean.Part263.cell scalarRow12668.grid) (caps repair12668) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12668

theorem covarianceGood12668_payment :
    (retDist (paperDesignP 12668).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12668)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12668_payment



end BstLean.Part269.N12668

namespace BstLean.Part269.N12668
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12668}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12668.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12668) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12668).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12668 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12668) (by norm_num) BstLean.Part268.WorldRow12668.worldPackage rfl
    BstLean.Part268.WorldRow12668.product_lower (BstLean.Part268.WorldRow12668.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12668} (hw : c ∈ Hof BstLean.Part268.WorldRow12668.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12668) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12668) (by norm_num) BstLean.Part268.WorldRow12668.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12668} (hw : c ∈ Hof BstLean.Part268.WorldRow12668.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12668) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12668).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12668) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12668_eq : scalarRow12668.targetFrame = BstLean.Part268.agent12668.frame := by
  norm_num [scalarRow12668,BstLean.Part268.agent12668]

noncomputable def frameData12668 : BstLean.Part264b.FrameData 12668 :=
  BstLean.Part269.frameData_from_numerics (n := 12668) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12668.worldPackage rfl BstLean.Part268.WorldRow12668.product_lower (BstLean.Part268.WorldRow12668.producthi.2.trans (by norm_num))
    scalarRow12668 repair12668 covarianceInputs12668 (fun i hi => sourceNumerics12668 hi)
    BstLean.Part268.agent12668.frame targetFrame12668_eq


end BstLean.Part269.N12668

namespace BstLean.Part269.N12669
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12669 : scalarRow12669.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12669, BstLean.Part268.grid12669, BstLean.Part263.worldGrid]

theorem supplies12669 (j : Fin 43) : Supply 12669 (parameters j)
    (cellLower scalarRow12669.grid (sourceIndex j))
    (cellUpper scalarRow12669.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12669.grid grid_top_bounds12669 j

theorem radii12669 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12669.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12669 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12669 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12669.grid grid_top_bounds12669 j hθ

noncomputable def covarianceInputs12669 :
    BstLean.Part263.CovarianceInputs 12669 scalarRow12669.grid parameters (caps repair12669) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12669 grid_top_bounds12669 repair12669

noncomputable def covarianceEvent12669 : Set (AgFam 12669) :=
  BstLean.Part263.covarianceEvent 12669 scalarRow12669.grid parameters

theorem covarianceEvent12669_measurable : MeasurableSet covarianceEvent12669 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12669_payment :
    (retDist (paperDesignP 12669).toCentres).real
      (agentEv (paperDesignP 12669) covarianceEvent12669)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12669

theorem localCov12669 : BstLean.Part259.LocalCovarianceOn covarianceEvent12669
    (BstLean.Part263.cell scalarRow12669.grid) (caps repair12669) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12669

theorem covarianceGood12669_payment :
    (retDist (paperDesignP 12669).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12669)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12669_payment



end BstLean.Part269.N12669

namespace BstLean.Part269.N12669
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12669}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12669.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12669) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12669).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12669 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12669) (by norm_num) BstLean.Part268.WorldRow12669.worldPackage rfl
    BstLean.Part268.WorldRow12669.product_lower (BstLean.Part268.WorldRow12669.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12669} (hw : c ∈ Hof BstLean.Part268.WorldRow12669.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12669) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12669) (by norm_num) BstLean.Part268.WorldRow12669.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12669} (hw : c ∈ Hof BstLean.Part268.WorldRow12669.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12669) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12669).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12669) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12669_eq : scalarRow12669.targetFrame = BstLean.Part268.agent12669.frame := by
  norm_num [scalarRow12669,BstLean.Part268.agent12669]

noncomputable def frameData12669 : BstLean.Part264b.FrameData 12669 :=
  BstLean.Part269.frameData_from_numerics (n := 12669) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12669.worldPackage rfl BstLean.Part268.WorldRow12669.product_lower (BstLean.Part268.WorldRow12669.producthi.2.trans (by norm_num))
    scalarRow12669 repair12669 covarianceInputs12669 (fun i hi => sourceNumerics12669 hi)
    BstLean.Part268.agent12669.frame targetFrame12669_eq


end BstLean.Part269.N12669
