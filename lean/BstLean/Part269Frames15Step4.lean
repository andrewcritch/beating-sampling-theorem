import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World15Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs15
import BstLean.Part269Rows15
import BstLean.Part269Sources15
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12745
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12745 : scalarRow12745.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12745, BstLean.Part268.grid12745, BstLean.Part263.worldGrid]

theorem supplies12745 (j : Fin 43) : Supply 12745 (parameters j)
    (cellLower scalarRow12745.grid (sourceIndex j))
    (cellUpper scalarRow12745.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12745.grid grid_top_bounds12745 j

theorem radii12745 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12745.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12745 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12745 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12745.grid grid_top_bounds12745 j hθ

noncomputable def covarianceInputs12745 :
    BstLean.Part263.CovarianceInputs 12745 scalarRow12745.grid parameters (caps repair12745) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12745 grid_top_bounds12745 repair12745

noncomputable def covarianceEvent12745 : Set (AgFam 12745) :=
  BstLean.Part263.covarianceEvent 12745 scalarRow12745.grid parameters

theorem covarianceEvent12745_measurable : MeasurableSet covarianceEvent12745 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12745_payment :
    (retDist (paperDesignP 12745).toCentres).real
      (agentEv (paperDesignP 12745) covarianceEvent12745)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12745

theorem localCov12745 : BstLean.Part259.LocalCovarianceOn covarianceEvent12745
    (BstLean.Part263.cell scalarRow12745.grid) (caps repair12745) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12745

theorem covarianceGood12745_payment :
    (retDist (paperDesignP 12745).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12745)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12745_payment



end BstLean.Part269.N12745

namespace BstLean.Part269.N12745
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12745}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12745.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12745) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12745).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12745 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12745) (by norm_num) BstLean.Part268.WorldRow12745.worldPackage rfl
    BstLean.Part268.WorldRow12745.product_lower (BstLean.Part268.WorldRow12745.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12745} (hw : c ∈ Hof BstLean.Part268.WorldRow12745.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12745) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12745) (by norm_num) BstLean.Part268.WorldRow12745.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12745} (hw : c ∈ Hof BstLean.Part268.WorldRow12745.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12745) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12745).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12745) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12745_eq : scalarRow12745.targetFrame = BstLean.Part268.agent12745.frame := by
  norm_num [scalarRow12745,BstLean.Part268.agent12745]

noncomputable def frameData12745 : BstLean.Part264b.FrameData 12745 :=
  BstLean.Part269.frameData_from_numerics (n := 12745) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12745.worldPackage rfl BstLean.Part268.WorldRow12745.product_lower (BstLean.Part268.WorldRow12745.producthi.2.trans (by norm_num))
    scalarRow12745 repair12745 covarianceInputs12745 (fun i hi => sourceNumerics12745 hi)
    BstLean.Part268.agent12745.frame targetFrame12745_eq


end BstLean.Part269.N12745

namespace BstLean.Part269.N12746
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12746 : scalarRow12746.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12746, BstLean.Part268.grid12746, BstLean.Part263.worldGrid]

theorem supplies12746 (j : Fin 43) : Supply 12746 (parameters j)
    (cellLower scalarRow12746.grid (sourceIndex j))
    (cellUpper scalarRow12746.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12746.grid grid_top_bounds12746 j

theorem radii12746 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12746.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12746 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12746 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12746.grid grid_top_bounds12746 j hθ

noncomputable def covarianceInputs12746 :
    BstLean.Part263.CovarianceInputs 12746 scalarRow12746.grid parameters (caps repair12746) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12746 grid_top_bounds12746 repair12746

noncomputable def covarianceEvent12746 : Set (AgFam 12746) :=
  BstLean.Part263.covarianceEvent 12746 scalarRow12746.grid parameters

theorem covarianceEvent12746_measurable : MeasurableSet covarianceEvent12746 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12746_payment :
    (retDist (paperDesignP 12746).toCentres).real
      (agentEv (paperDesignP 12746) covarianceEvent12746)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12746

theorem localCov12746 : BstLean.Part259.LocalCovarianceOn covarianceEvent12746
    (BstLean.Part263.cell scalarRow12746.grid) (caps repair12746) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12746

theorem covarianceGood12746_payment :
    (retDist (paperDesignP 12746).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12746)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12746_payment



end BstLean.Part269.N12746

namespace BstLean.Part269.N12746
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12746}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12746.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12746) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12746).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12746 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12746) (by norm_num) BstLean.Part268.WorldRow12746.worldPackage rfl
    BstLean.Part268.WorldRow12746.product_lower (BstLean.Part268.WorldRow12746.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12746} (hw : c ∈ Hof BstLean.Part268.WorldRow12746.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12746) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12746) (by norm_num) BstLean.Part268.WorldRow12746.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12746} (hw : c ∈ Hof BstLean.Part268.WorldRow12746.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12746) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12746).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12746) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12746_eq : scalarRow12746.targetFrame = BstLean.Part268.agent12746.frame := by
  norm_num [scalarRow12746,BstLean.Part268.agent12746]

noncomputable def frameData12746 : BstLean.Part264b.FrameData 12746 :=
  BstLean.Part269.frameData_from_numerics (n := 12746) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12746.worldPackage rfl BstLean.Part268.WorldRow12746.product_lower (BstLean.Part268.WorldRow12746.producthi.2.trans (by norm_num))
    scalarRow12746 repair12746 covarianceInputs12746 (fun i hi => sourceNumerics12746 hi)
    BstLean.Part268.agent12746.frame targetFrame12746_eq


end BstLean.Part269.N12746

namespace BstLean.Part269.N12747
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12747 : scalarRow12747.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12747, BstLean.Part268.grid12747, BstLean.Part263.worldGrid]

theorem supplies12747 (j : Fin 43) : Supply 12747 (parameters j)
    (cellLower scalarRow12747.grid (sourceIndex j))
    (cellUpper scalarRow12747.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12747.grid grid_top_bounds12747 j

theorem radii12747 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12747.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12747 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12747 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12747.grid grid_top_bounds12747 j hθ

noncomputable def covarianceInputs12747 :
    BstLean.Part263.CovarianceInputs 12747 scalarRow12747.grid parameters (caps repair12747) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12747 grid_top_bounds12747 repair12747

noncomputable def covarianceEvent12747 : Set (AgFam 12747) :=
  BstLean.Part263.covarianceEvent 12747 scalarRow12747.grid parameters

theorem covarianceEvent12747_measurable : MeasurableSet covarianceEvent12747 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12747_payment :
    (retDist (paperDesignP 12747).toCentres).real
      (agentEv (paperDesignP 12747) covarianceEvent12747)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12747

theorem localCov12747 : BstLean.Part259.LocalCovarianceOn covarianceEvent12747
    (BstLean.Part263.cell scalarRow12747.grid) (caps repair12747) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12747

theorem covarianceGood12747_payment :
    (retDist (paperDesignP 12747).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12747)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12747_payment



end BstLean.Part269.N12747

namespace BstLean.Part269.N12747
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12747}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12747.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12747) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12747).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12747 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12747) (by norm_num) BstLean.Part268.WorldRow12747.worldPackage rfl
    BstLean.Part268.WorldRow12747.product_lower (BstLean.Part268.WorldRow12747.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12747} (hw : c ∈ Hof BstLean.Part268.WorldRow12747.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12747) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12747) (by norm_num) BstLean.Part268.WorldRow12747.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12747} (hw : c ∈ Hof BstLean.Part268.WorldRow12747.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12747) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12747).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12747) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12747_eq : scalarRow12747.targetFrame = BstLean.Part268.agent12747.frame := by
  norm_num [scalarRow12747,BstLean.Part268.agent12747]

noncomputable def frameData12747 : BstLean.Part264b.FrameData 12747 :=
  BstLean.Part269.frameData_from_numerics (n := 12747) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12747.worldPackage rfl BstLean.Part268.WorldRow12747.product_lower (BstLean.Part268.WorldRow12747.producthi.2.trans (by norm_num))
    scalarRow12747 repair12747 covarianceInputs12747 (fun i hi => sourceNumerics12747 hi)
    BstLean.Part268.agent12747.frame targetFrame12747_eq


end BstLean.Part269.N12747

namespace BstLean.Part269.N12748
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12748 : scalarRow12748.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12748, BstLean.Part268.grid12748, BstLean.Part263.worldGrid]

theorem supplies12748 (j : Fin 43) : Supply 12748 (parameters j)
    (cellLower scalarRow12748.grid (sourceIndex j))
    (cellUpper scalarRow12748.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12748.grid grid_top_bounds12748 j

theorem radii12748 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12748.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12748 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12748 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12748.grid grid_top_bounds12748 j hθ

noncomputable def covarianceInputs12748 :
    BstLean.Part263.CovarianceInputs 12748 scalarRow12748.grid parameters (caps repair12748) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12748 grid_top_bounds12748 repair12748

noncomputable def covarianceEvent12748 : Set (AgFam 12748) :=
  BstLean.Part263.covarianceEvent 12748 scalarRow12748.grid parameters

theorem covarianceEvent12748_measurable : MeasurableSet covarianceEvent12748 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12748_payment :
    (retDist (paperDesignP 12748).toCentres).real
      (agentEv (paperDesignP 12748) covarianceEvent12748)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12748

theorem localCov12748 : BstLean.Part259.LocalCovarianceOn covarianceEvent12748
    (BstLean.Part263.cell scalarRow12748.grid) (caps repair12748) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12748

theorem covarianceGood12748_payment :
    (retDist (paperDesignP 12748).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12748)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12748_payment



end BstLean.Part269.N12748

namespace BstLean.Part269.N12748
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12748}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12748.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12748) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12748).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12748 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12748) (by norm_num) BstLean.Part268.WorldRow12748.worldPackage rfl
    BstLean.Part268.WorldRow12748.product_lower (BstLean.Part268.WorldRow12748.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12748} (hw : c ∈ Hof BstLean.Part268.WorldRow12748.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12748) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12748) (by norm_num) BstLean.Part268.WorldRow12748.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12748} (hw : c ∈ Hof BstLean.Part268.WorldRow12748.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12748) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12748).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12748) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12748_eq : scalarRow12748.targetFrame = BstLean.Part268.agent12748.frame := by
  norm_num [scalarRow12748,BstLean.Part268.agent12748]

noncomputable def frameData12748 : BstLean.Part264b.FrameData 12748 :=
  BstLean.Part269.frameData_from_numerics (n := 12748) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12748.worldPackage rfl BstLean.Part268.WorldRow12748.product_lower (BstLean.Part268.WorldRow12748.producthi.2.trans (by norm_num))
    scalarRow12748 repair12748 covarianceInputs12748 (fun i hi => sourceNumerics12748 hi)
    BstLean.Part268.agent12748.frame targetFrame12748_eq


end BstLean.Part269.N12748

namespace BstLean.Part269.N12749
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12749 : scalarRow12749.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12749, BstLean.Part268.grid12749, BstLean.Part263.worldGrid]

theorem supplies12749 (j : Fin 43) : Supply 12749 (parameters j)
    (cellLower scalarRow12749.grid (sourceIndex j))
    (cellUpper scalarRow12749.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12749.grid grid_top_bounds12749 j

theorem radii12749 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12749.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12749 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12749 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12749.grid grid_top_bounds12749 j hθ

noncomputable def covarianceInputs12749 :
    BstLean.Part263.CovarianceInputs 12749 scalarRow12749.grid parameters (caps repair12749) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12749 grid_top_bounds12749 repair12749

noncomputable def covarianceEvent12749 : Set (AgFam 12749) :=
  BstLean.Part263.covarianceEvent 12749 scalarRow12749.grid parameters

theorem covarianceEvent12749_measurable : MeasurableSet covarianceEvent12749 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12749_payment :
    (retDist (paperDesignP 12749).toCentres).real
      (agentEv (paperDesignP 12749) covarianceEvent12749)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12749

theorem localCov12749 : BstLean.Part259.LocalCovarianceOn covarianceEvent12749
    (BstLean.Part263.cell scalarRow12749.grid) (caps repair12749) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12749

theorem covarianceGood12749_payment :
    (retDist (paperDesignP 12749).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12749)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12749_payment



end BstLean.Part269.N12749

namespace BstLean.Part269.N12749
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12749}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12749.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12749) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12749).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12749 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12749) (by norm_num) BstLean.Part268.WorldRow12749.worldPackage rfl
    BstLean.Part268.WorldRow12749.product_lower (BstLean.Part268.WorldRow12749.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12749} (hw : c ∈ Hof BstLean.Part268.WorldRow12749.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12749) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12749) (by norm_num) BstLean.Part268.WorldRow12749.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12749} (hw : c ∈ Hof BstLean.Part268.WorldRow12749.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12749) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12749).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12749) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12749_eq : scalarRow12749.targetFrame = BstLean.Part268.agent12749.frame := by
  norm_num [scalarRow12749,BstLean.Part268.agent12749]

noncomputable def frameData12749 : BstLean.Part264b.FrameData 12749 :=
  BstLean.Part269.frameData_from_numerics (n := 12749) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12749.worldPackage rfl BstLean.Part268.WorldRow12749.product_lower (BstLean.Part268.WorldRow12749.producthi.2.trans (by norm_num))
    scalarRow12749 repair12749 covarianceInputs12749 (fun i hi => sourceNumerics12749 hi)
    BstLean.Part268.agent12749.frame targetFrame12749_eq


end BstLean.Part269.N12749
