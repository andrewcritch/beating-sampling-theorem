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

namespace BstLean.Part269.N12770
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12770 : scalarRow12770.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12770, BstLean.Part268.grid12770, BstLean.Part263.worldGrid]

theorem supplies12770 (j : Fin 43) : Supply 12770 (parameters j)
    (cellLower scalarRow12770.grid (sourceIndex j))
    (cellUpper scalarRow12770.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12770.grid grid_top_bounds12770 j

theorem radii12770 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12770.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12770 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12770 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12770.grid grid_top_bounds12770 j hθ

noncomputable def covarianceInputs12770 :
    BstLean.Part263.CovarianceInputs 12770 scalarRow12770.grid parameters (caps repair12770) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12770 grid_top_bounds12770 repair12770

noncomputable def covarianceEvent12770 : Set (AgFam 12770) :=
  BstLean.Part263.covarianceEvent 12770 scalarRow12770.grid parameters

theorem covarianceEvent12770_measurable : MeasurableSet covarianceEvent12770 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12770_payment :
    (retDist (paperDesignP 12770).toCentres).real
      (agentEv (paperDesignP 12770) covarianceEvent12770)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12770

theorem localCov12770 : BstLean.Part259.LocalCovarianceOn covarianceEvent12770
    (BstLean.Part263.cell scalarRow12770.grid) (caps repair12770) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12770

theorem covarianceGood12770_payment :
    (retDist (paperDesignP 12770).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12770)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12770_payment



end BstLean.Part269.N12770

namespace BstLean.Part269.N12770
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12770}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12770.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12770) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12770).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12770 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12770) (by norm_num) BstLean.Part268.WorldRow12770.worldPackage rfl
    BstLean.Part268.WorldRow12770.product_lower (BstLean.Part268.WorldRow12770.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12770} (hw : c ∈ Hof BstLean.Part268.WorldRow12770.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12770) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12770) (by norm_num) BstLean.Part268.WorldRow12770.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12770} (hw : c ∈ Hof BstLean.Part268.WorldRow12770.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12770) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12770).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12770) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12770_eq : scalarRow12770.targetFrame = BstLean.Part268.agent12770.frame := by
  norm_num [scalarRow12770,BstLean.Part268.agent12770]

noncomputable def frameData12770 : BstLean.Part264b.FrameData 12770 :=
  BstLean.Part269.frameData_from_numerics (n := 12770) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12770.worldPackage rfl BstLean.Part268.WorldRow12770.product_lower (BstLean.Part268.WorldRow12770.producthi.2.trans (by norm_num))
    scalarRow12770 repair12770 covarianceInputs12770 (fun i hi => sourceNumerics12770 hi)
    BstLean.Part268.agent12770.frame targetFrame12770_eq


end BstLean.Part269.N12770

namespace BstLean.Part269.N12771
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12771 : scalarRow12771.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12771, BstLean.Part268.grid12771, BstLean.Part263.worldGrid]

theorem supplies12771 (j : Fin 43) : Supply 12771 (parameters j)
    (cellLower scalarRow12771.grid (sourceIndex j))
    (cellUpper scalarRow12771.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12771.grid grid_top_bounds12771 j

theorem radii12771 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12771.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12771 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12771 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12771.grid grid_top_bounds12771 j hθ

noncomputable def covarianceInputs12771 :
    BstLean.Part263.CovarianceInputs 12771 scalarRow12771.grid parameters (caps repair12771) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12771 grid_top_bounds12771 repair12771

noncomputable def covarianceEvent12771 : Set (AgFam 12771) :=
  BstLean.Part263.covarianceEvent 12771 scalarRow12771.grid parameters

theorem covarianceEvent12771_measurable : MeasurableSet covarianceEvent12771 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12771_payment :
    (retDist (paperDesignP 12771).toCentres).real
      (agentEv (paperDesignP 12771) covarianceEvent12771)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12771

theorem localCov12771 : BstLean.Part259.LocalCovarianceOn covarianceEvent12771
    (BstLean.Part263.cell scalarRow12771.grid) (caps repair12771) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12771

theorem covarianceGood12771_payment :
    (retDist (paperDesignP 12771).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12771)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12771_payment



end BstLean.Part269.N12771

namespace BstLean.Part269.N12771
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12771}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12771.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12771) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12771).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12771 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12771) (by norm_num) BstLean.Part268.WorldRow12771.worldPackage rfl
    BstLean.Part268.WorldRow12771.product_lower (BstLean.Part268.WorldRow12771.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12771} (hw : c ∈ Hof BstLean.Part268.WorldRow12771.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12771) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12771) (by norm_num) BstLean.Part268.WorldRow12771.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12771} (hw : c ∈ Hof BstLean.Part268.WorldRow12771.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12771) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12771).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12771) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12771_eq : scalarRow12771.targetFrame = BstLean.Part268.agent12771.frame := by
  norm_num [scalarRow12771,BstLean.Part268.agent12771]

noncomputable def frameData12771 : BstLean.Part264b.FrameData 12771 :=
  BstLean.Part269.frameData_from_numerics (n := 12771) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12771.worldPackage rfl BstLean.Part268.WorldRow12771.product_lower (BstLean.Part268.WorldRow12771.producthi.2.trans (by norm_num))
    scalarRow12771 repair12771 covarianceInputs12771 (fun i hi => sourceNumerics12771 hi)
    BstLean.Part268.agent12771.frame targetFrame12771_eq


end BstLean.Part269.N12771

namespace BstLean.Part269.N12772
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12772 : scalarRow12772.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12772, BstLean.Part268.grid12772, BstLean.Part263.worldGrid]

theorem supplies12772 (j : Fin 43) : Supply 12772 (parameters j)
    (cellLower scalarRow12772.grid (sourceIndex j))
    (cellUpper scalarRow12772.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12772.grid grid_top_bounds12772 j

theorem radii12772 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12772.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12772 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12772 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12772.grid grid_top_bounds12772 j hθ

noncomputable def covarianceInputs12772 :
    BstLean.Part263.CovarianceInputs 12772 scalarRow12772.grid parameters (caps repair12772) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12772 grid_top_bounds12772 repair12772

noncomputable def covarianceEvent12772 : Set (AgFam 12772) :=
  BstLean.Part263.covarianceEvent 12772 scalarRow12772.grid parameters

theorem covarianceEvent12772_measurable : MeasurableSet covarianceEvent12772 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12772_payment :
    (retDist (paperDesignP 12772).toCentres).real
      (agentEv (paperDesignP 12772) covarianceEvent12772)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12772

theorem localCov12772 : BstLean.Part259.LocalCovarianceOn covarianceEvent12772
    (BstLean.Part263.cell scalarRow12772.grid) (caps repair12772) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12772

theorem covarianceGood12772_payment :
    (retDist (paperDesignP 12772).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12772)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12772_payment



end BstLean.Part269.N12772

namespace BstLean.Part269.N12772
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12772}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12772.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12772) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12772).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12772 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12772) (by norm_num) BstLean.Part268.WorldRow12772.worldPackage rfl
    BstLean.Part268.WorldRow12772.product_lower (BstLean.Part268.WorldRow12772.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12772} (hw : c ∈ Hof BstLean.Part268.WorldRow12772.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12772) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12772) (by norm_num) BstLean.Part268.WorldRow12772.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12772} (hw : c ∈ Hof BstLean.Part268.WorldRow12772.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12772) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12772).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12772) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12772_eq : scalarRow12772.targetFrame = BstLean.Part268.agent12772.frame := by
  norm_num [scalarRow12772,BstLean.Part268.agent12772]

noncomputable def frameData12772 : BstLean.Part264b.FrameData 12772 :=
  BstLean.Part269.frameData_from_numerics (n := 12772) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12772.worldPackage rfl BstLean.Part268.WorldRow12772.product_lower (BstLean.Part268.WorldRow12772.producthi.2.trans (by norm_num))
    scalarRow12772 repair12772 covarianceInputs12772 (fun i hi => sourceNumerics12772 hi)
    BstLean.Part268.agent12772.frame targetFrame12772_eq


end BstLean.Part269.N12772

namespace BstLean.Part269.N12773
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12773 : scalarRow12773.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12773, BstLean.Part268.grid12773, BstLean.Part263.worldGrid]

theorem supplies12773 (j : Fin 43) : Supply 12773 (parameters j)
    (cellLower scalarRow12773.grid (sourceIndex j))
    (cellUpper scalarRow12773.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12773.grid grid_top_bounds12773 j

theorem radii12773 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12773.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12773 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12773 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12773.grid grid_top_bounds12773 j hθ

noncomputable def covarianceInputs12773 :
    BstLean.Part263.CovarianceInputs 12773 scalarRow12773.grid parameters (caps repair12773) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12773 grid_top_bounds12773 repair12773

noncomputable def covarianceEvent12773 : Set (AgFam 12773) :=
  BstLean.Part263.covarianceEvent 12773 scalarRow12773.grid parameters

theorem covarianceEvent12773_measurable : MeasurableSet covarianceEvent12773 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12773_payment :
    (retDist (paperDesignP 12773).toCentres).real
      (agentEv (paperDesignP 12773) covarianceEvent12773)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12773

theorem localCov12773 : BstLean.Part259.LocalCovarianceOn covarianceEvent12773
    (BstLean.Part263.cell scalarRow12773.grid) (caps repair12773) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12773

theorem covarianceGood12773_payment :
    (retDist (paperDesignP 12773).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12773)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12773_payment



end BstLean.Part269.N12773

namespace BstLean.Part269.N12773
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12773}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12773.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12773) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12773).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12773 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12773) (by norm_num) BstLean.Part268.WorldRow12773.worldPackage rfl
    BstLean.Part268.WorldRow12773.product_lower (BstLean.Part268.WorldRow12773.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12773} (hw : c ∈ Hof BstLean.Part268.WorldRow12773.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12773) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12773) (by norm_num) BstLean.Part268.WorldRow12773.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12773} (hw : c ∈ Hof BstLean.Part268.WorldRow12773.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12773) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12773).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12773) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12773_eq : scalarRow12773.targetFrame = BstLean.Part268.agent12773.frame := by
  norm_num [scalarRow12773,BstLean.Part268.agent12773]

noncomputable def frameData12773 : BstLean.Part264b.FrameData 12773 :=
  BstLean.Part269.frameData_from_numerics (n := 12773) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12773.worldPackage rfl BstLean.Part268.WorldRow12773.product_lower (BstLean.Part268.WorldRow12773.producthi.2.trans (by norm_num))
    scalarRow12773 repair12773 covarianceInputs12773 (fun i hi => sourceNumerics12773 hi)
    BstLean.Part268.agent12773.frame targetFrame12773_eq


end BstLean.Part269.N12773

namespace BstLean.Part269.N12774
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12774 : scalarRow12774.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12774, BstLean.Part268.grid12774, BstLean.Part263.worldGrid]

theorem supplies12774 (j : Fin 43) : Supply 12774 (parameters j)
    (cellLower scalarRow12774.grid (sourceIndex j))
    (cellUpper scalarRow12774.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12774.grid grid_top_bounds12774 j

theorem radii12774 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12774.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12774 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12774 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12774.grid grid_top_bounds12774 j hθ

noncomputable def covarianceInputs12774 :
    BstLean.Part263.CovarianceInputs 12774 scalarRow12774.grid parameters (caps repair12774) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12774 grid_top_bounds12774 repair12774

noncomputable def covarianceEvent12774 : Set (AgFam 12774) :=
  BstLean.Part263.covarianceEvent 12774 scalarRow12774.grid parameters

theorem covarianceEvent12774_measurable : MeasurableSet covarianceEvent12774 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12774_payment :
    (retDist (paperDesignP 12774).toCentres).real
      (agentEv (paperDesignP 12774) covarianceEvent12774)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12774

theorem localCov12774 : BstLean.Part259.LocalCovarianceOn covarianceEvent12774
    (BstLean.Part263.cell scalarRow12774.grid) (caps repair12774) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12774

theorem covarianceGood12774_payment :
    (retDist (paperDesignP 12774).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12774)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12774_payment



end BstLean.Part269.N12774

namespace BstLean.Part269.N12774
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12774}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12774.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12774) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12774).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12774 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12774) (by norm_num) BstLean.Part268.WorldRow12774.worldPackage rfl
    BstLean.Part268.WorldRow12774.product_lower (BstLean.Part268.WorldRow12774.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12774} (hw : c ∈ Hof BstLean.Part268.WorldRow12774.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12774) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12774) (by norm_num) BstLean.Part268.WorldRow12774.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12774} (hw : c ∈ Hof BstLean.Part268.WorldRow12774.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12774) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12774).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12774) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12774_eq : scalarRow12774.targetFrame = BstLean.Part268.agent12774.frame := by
  norm_num [scalarRow12774,BstLean.Part268.agent12774]

noncomputable def frameData12774 : BstLean.Part264b.FrameData 12774 :=
  BstLean.Part269.frameData_from_numerics (n := 12774) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12774.worldPackage rfl BstLean.Part268.WorldRow12774.product_lower (BstLean.Part268.WorldRow12774.producthi.2.trans (by norm_num))
    scalarRow12774 repair12774 covarianceInputs12774 (fun i hi => sourceNumerics12774 hi)
    BstLean.Part268.agent12774.frame targetFrame12774_eq


end BstLean.Part269.N12774
