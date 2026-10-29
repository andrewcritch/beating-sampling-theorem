import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World16Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs16
import BstLean.Part269Rows16
import BstLean.Part269Sources16
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12760
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12760 : scalarRow12760.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12760, BstLean.Part268.grid12760, BstLean.Part263.worldGrid]

theorem supplies12760 (j : Fin 43) : Supply 12760 (parameters j)
    (cellLower scalarRow12760.grid (sourceIndex j))
    (cellUpper scalarRow12760.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12760.grid grid_top_bounds12760 j

theorem radii12760 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12760.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12760 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12760 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12760.grid grid_top_bounds12760 j hθ

noncomputable def covarianceInputs12760 :
    BstLean.Part263.CovarianceInputs 12760 scalarRow12760.grid parameters (caps repair12760) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12760 grid_top_bounds12760 repair12760

noncomputable def covarianceEvent12760 : Set (AgFam 12760) :=
  BstLean.Part263.covarianceEvent 12760 scalarRow12760.grid parameters

theorem covarianceEvent12760_measurable : MeasurableSet covarianceEvent12760 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12760_payment :
    (retDist (paperDesignP 12760).toCentres).real
      (agentEv (paperDesignP 12760) covarianceEvent12760)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12760

theorem localCov12760 : BstLean.Part259.LocalCovarianceOn covarianceEvent12760
    (BstLean.Part263.cell scalarRow12760.grid) (caps repair12760) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12760

theorem covarianceGood12760_payment :
    (retDist (paperDesignP 12760).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12760)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12760_payment



end BstLean.Part269.N12760

namespace BstLean.Part269.N12760
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12760}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12760.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12760) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12760).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12760 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12760) (by norm_num) BstLean.Part268.WorldRow12760.worldPackage rfl
    BstLean.Part268.WorldRow12760.product_lower (BstLean.Part268.WorldRow12760.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12760} (hw : c ∈ Hof BstLean.Part268.WorldRow12760.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12760) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12760) (by norm_num) BstLean.Part268.WorldRow12760.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12760} (hw : c ∈ Hof BstLean.Part268.WorldRow12760.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12760) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12760).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12760) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12760_eq : scalarRow12760.targetFrame = BstLean.Part268.agent12760.frame := by
  norm_num [scalarRow12760,BstLean.Part268.agent12760]

noncomputable def frameData12760 : BstLean.Part264b.FrameData 12760 :=
  BstLean.Part269.frameData_from_numerics (n := 12760) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12760.worldPackage rfl BstLean.Part268.WorldRow12760.product_lower (BstLean.Part268.WorldRow12760.producthi.2.trans (by norm_num))
    scalarRow12760 repair12760 covarianceInputs12760 (fun i hi => sourceNumerics12760 hi)
    BstLean.Part268.agent12760.frame targetFrame12760_eq


end BstLean.Part269.N12760

namespace BstLean.Part269.N12761
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12761 : scalarRow12761.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12761, BstLean.Part268.grid12761, BstLean.Part263.worldGrid]

theorem supplies12761 (j : Fin 43) : Supply 12761 (parameters j)
    (cellLower scalarRow12761.grid (sourceIndex j))
    (cellUpper scalarRow12761.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12761.grid grid_top_bounds12761 j

theorem radii12761 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12761.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12761 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12761 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12761.grid grid_top_bounds12761 j hθ

noncomputable def covarianceInputs12761 :
    BstLean.Part263.CovarianceInputs 12761 scalarRow12761.grid parameters (caps repair12761) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12761 grid_top_bounds12761 repair12761

noncomputable def covarianceEvent12761 : Set (AgFam 12761) :=
  BstLean.Part263.covarianceEvent 12761 scalarRow12761.grid parameters

theorem covarianceEvent12761_measurable : MeasurableSet covarianceEvent12761 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12761_payment :
    (retDist (paperDesignP 12761).toCentres).real
      (agentEv (paperDesignP 12761) covarianceEvent12761)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12761

theorem localCov12761 : BstLean.Part259.LocalCovarianceOn covarianceEvent12761
    (BstLean.Part263.cell scalarRow12761.grid) (caps repair12761) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12761

theorem covarianceGood12761_payment :
    (retDist (paperDesignP 12761).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12761)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12761_payment



end BstLean.Part269.N12761

namespace BstLean.Part269.N12761
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12761}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12761.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12761) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12761).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12761 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12761) (by norm_num) BstLean.Part268.WorldRow12761.worldPackage rfl
    BstLean.Part268.WorldRow12761.product_lower (BstLean.Part268.WorldRow12761.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12761} (hw : c ∈ Hof BstLean.Part268.WorldRow12761.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12761) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12761) (by norm_num) BstLean.Part268.WorldRow12761.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12761} (hw : c ∈ Hof BstLean.Part268.WorldRow12761.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12761) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12761).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12761) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12761_eq : scalarRow12761.targetFrame = BstLean.Part268.agent12761.frame := by
  norm_num [scalarRow12761,BstLean.Part268.agent12761]

noncomputable def frameData12761 : BstLean.Part264b.FrameData 12761 :=
  BstLean.Part269.frameData_from_numerics (n := 12761) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12761.worldPackage rfl BstLean.Part268.WorldRow12761.product_lower (BstLean.Part268.WorldRow12761.producthi.2.trans (by norm_num))
    scalarRow12761 repair12761 covarianceInputs12761 (fun i hi => sourceNumerics12761 hi)
    BstLean.Part268.agent12761.frame targetFrame12761_eq


end BstLean.Part269.N12761

namespace BstLean.Part269.N12762
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12762 : scalarRow12762.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12762, BstLean.Part268.grid12762, BstLean.Part263.worldGrid]

theorem supplies12762 (j : Fin 43) : Supply 12762 (parameters j)
    (cellLower scalarRow12762.grid (sourceIndex j))
    (cellUpper scalarRow12762.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12762.grid grid_top_bounds12762 j

theorem radii12762 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12762.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12762 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12762 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12762.grid grid_top_bounds12762 j hθ

noncomputable def covarianceInputs12762 :
    BstLean.Part263.CovarianceInputs 12762 scalarRow12762.grid parameters (caps repair12762) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12762 grid_top_bounds12762 repair12762

noncomputable def covarianceEvent12762 : Set (AgFam 12762) :=
  BstLean.Part263.covarianceEvent 12762 scalarRow12762.grid parameters

theorem covarianceEvent12762_measurable : MeasurableSet covarianceEvent12762 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12762_payment :
    (retDist (paperDesignP 12762).toCentres).real
      (agentEv (paperDesignP 12762) covarianceEvent12762)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12762

theorem localCov12762 : BstLean.Part259.LocalCovarianceOn covarianceEvent12762
    (BstLean.Part263.cell scalarRow12762.grid) (caps repair12762) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12762

theorem covarianceGood12762_payment :
    (retDist (paperDesignP 12762).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12762)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12762_payment



end BstLean.Part269.N12762

namespace BstLean.Part269.N12762
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12762}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12762.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12762) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12762).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12762 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12762) (by norm_num) BstLean.Part268.WorldRow12762.worldPackage rfl
    BstLean.Part268.WorldRow12762.product_lower (BstLean.Part268.WorldRow12762.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12762} (hw : c ∈ Hof BstLean.Part268.WorldRow12762.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12762) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12762) (by norm_num) BstLean.Part268.WorldRow12762.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12762} (hw : c ∈ Hof BstLean.Part268.WorldRow12762.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12762) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12762).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12762) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12762_eq : scalarRow12762.targetFrame = BstLean.Part268.agent12762.frame := by
  norm_num [scalarRow12762,BstLean.Part268.agent12762]

noncomputable def frameData12762 : BstLean.Part264b.FrameData 12762 :=
  BstLean.Part269.frameData_from_numerics (n := 12762) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12762.worldPackage rfl BstLean.Part268.WorldRow12762.product_lower (BstLean.Part268.WorldRow12762.producthi.2.trans (by norm_num))
    scalarRow12762 repair12762 covarianceInputs12762 (fun i hi => sourceNumerics12762 hi)
    BstLean.Part268.agent12762.frame targetFrame12762_eq


end BstLean.Part269.N12762

namespace BstLean.Part269.N12763
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12763 : scalarRow12763.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12763, BstLean.Part268.grid12763, BstLean.Part263.worldGrid]

theorem supplies12763 (j : Fin 43) : Supply 12763 (parameters j)
    (cellLower scalarRow12763.grid (sourceIndex j))
    (cellUpper scalarRow12763.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12763.grid grid_top_bounds12763 j

theorem radii12763 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12763.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12763 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12763 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12763.grid grid_top_bounds12763 j hθ

noncomputable def covarianceInputs12763 :
    BstLean.Part263.CovarianceInputs 12763 scalarRow12763.grid parameters (caps repair12763) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12763 grid_top_bounds12763 repair12763

noncomputable def covarianceEvent12763 : Set (AgFam 12763) :=
  BstLean.Part263.covarianceEvent 12763 scalarRow12763.grid parameters

theorem covarianceEvent12763_measurable : MeasurableSet covarianceEvent12763 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12763_payment :
    (retDist (paperDesignP 12763).toCentres).real
      (agentEv (paperDesignP 12763) covarianceEvent12763)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12763

theorem localCov12763 : BstLean.Part259.LocalCovarianceOn covarianceEvent12763
    (BstLean.Part263.cell scalarRow12763.grid) (caps repair12763) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12763

theorem covarianceGood12763_payment :
    (retDist (paperDesignP 12763).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12763)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12763_payment



end BstLean.Part269.N12763

namespace BstLean.Part269.N12763
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12763}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12763.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12763) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12763).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12763 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12763) (by norm_num) BstLean.Part268.WorldRow12763.worldPackage rfl
    BstLean.Part268.WorldRow12763.product_lower (BstLean.Part268.WorldRow12763.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12763} (hw : c ∈ Hof BstLean.Part268.WorldRow12763.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12763) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12763) (by norm_num) BstLean.Part268.WorldRow12763.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12763} (hw : c ∈ Hof BstLean.Part268.WorldRow12763.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12763) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12763).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12763) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12763_eq : scalarRow12763.targetFrame = BstLean.Part268.agent12763.frame := by
  norm_num [scalarRow12763,BstLean.Part268.agent12763]

noncomputable def frameData12763 : BstLean.Part264b.FrameData 12763 :=
  BstLean.Part269.frameData_from_numerics (n := 12763) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12763.worldPackage rfl BstLean.Part268.WorldRow12763.product_lower (BstLean.Part268.WorldRow12763.producthi.2.trans (by norm_num))
    scalarRow12763 repair12763 covarianceInputs12763 (fun i hi => sourceNumerics12763 hi)
    BstLean.Part268.agent12763.frame targetFrame12763_eq


end BstLean.Part269.N12763

namespace BstLean.Part269.N12764
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12764 : scalarRow12764.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12764, BstLean.Part268.grid12764, BstLean.Part263.worldGrid]

theorem supplies12764 (j : Fin 43) : Supply 12764 (parameters j)
    (cellLower scalarRow12764.grid (sourceIndex j))
    (cellUpper scalarRow12764.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12764.grid grid_top_bounds12764 j

theorem radii12764 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12764.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12764 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12764 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12764.grid grid_top_bounds12764 j hθ

noncomputable def covarianceInputs12764 :
    BstLean.Part263.CovarianceInputs 12764 scalarRow12764.grid parameters (caps repair12764) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12764 grid_top_bounds12764 repair12764

noncomputable def covarianceEvent12764 : Set (AgFam 12764) :=
  BstLean.Part263.covarianceEvent 12764 scalarRow12764.grid parameters

theorem covarianceEvent12764_measurable : MeasurableSet covarianceEvent12764 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12764_payment :
    (retDist (paperDesignP 12764).toCentres).real
      (agentEv (paperDesignP 12764) covarianceEvent12764)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12764

theorem localCov12764 : BstLean.Part259.LocalCovarianceOn covarianceEvent12764
    (BstLean.Part263.cell scalarRow12764.grid) (caps repair12764) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12764

theorem covarianceGood12764_payment :
    (retDist (paperDesignP 12764).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12764)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12764_payment



end BstLean.Part269.N12764

namespace BstLean.Part269.N12764
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12764}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12764.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12764) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12764).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12764 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12764) (by norm_num) BstLean.Part268.WorldRow12764.worldPackage rfl
    BstLean.Part268.WorldRow12764.product_lower (BstLean.Part268.WorldRow12764.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12764} (hw : c ∈ Hof BstLean.Part268.WorldRow12764.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12764) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12764) (by norm_num) BstLean.Part268.WorldRow12764.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12764} (hw : c ∈ Hof BstLean.Part268.WorldRow12764.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12764) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12764).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12764) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12764_eq : scalarRow12764.targetFrame = BstLean.Part268.agent12764.frame := by
  norm_num [scalarRow12764,BstLean.Part268.agent12764]

noncomputable def frameData12764 : BstLean.Part264b.FrameData 12764 :=
  BstLean.Part269.frameData_from_numerics (n := 12764) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12764.worldPackage rfl BstLean.Part268.WorldRow12764.product_lower (BstLean.Part268.WorldRow12764.producthi.2.trans (by norm_num))
    scalarRow12764 repair12764 covarianceInputs12764 (fun i hi => sourceNumerics12764 hi)
    BstLean.Part268.agent12764.frame targetFrame12764_eq


end BstLean.Part269.N12764
