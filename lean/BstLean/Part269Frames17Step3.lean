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

namespace BstLean.Part269.N12790
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12790 : scalarRow12790.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12790, BstLean.Part268.grid12790, BstLean.Part263.worldGrid]

theorem supplies12790 (j : Fin 43) : Supply 12790 (parameters j)
    (cellLower scalarRow12790.grid (sourceIndex j))
    (cellUpper scalarRow12790.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12790.grid grid_top_bounds12790 j

theorem radii12790 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12790.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12790 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12790 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12790.grid grid_top_bounds12790 j hθ

noncomputable def covarianceInputs12790 :
    BstLean.Part263.CovarianceInputs 12790 scalarRow12790.grid parameters (caps repair12790) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12790 grid_top_bounds12790 repair12790

noncomputable def covarianceEvent12790 : Set (AgFam 12790) :=
  BstLean.Part263.covarianceEvent 12790 scalarRow12790.grid parameters

theorem covarianceEvent12790_measurable : MeasurableSet covarianceEvent12790 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12790_payment :
    (retDist (paperDesignP 12790).toCentres).real
      (agentEv (paperDesignP 12790) covarianceEvent12790)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12790

theorem localCov12790 : BstLean.Part259.LocalCovarianceOn covarianceEvent12790
    (BstLean.Part263.cell scalarRow12790.grid) (caps repair12790) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12790

theorem covarianceGood12790_payment :
    (retDist (paperDesignP 12790).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12790)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12790_payment



end BstLean.Part269.N12790

namespace BstLean.Part269.N12790
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12790}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12790.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12790) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12790).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12790 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12790) (by norm_num) BstLean.Part268.WorldRow12790.worldPackage rfl
    BstLean.Part268.WorldRow12790.product_lower (BstLean.Part268.WorldRow12790.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12790} (hw : c ∈ Hof BstLean.Part268.WorldRow12790.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12790) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12790) (by norm_num) BstLean.Part268.WorldRow12790.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12790} (hw : c ∈ Hof BstLean.Part268.WorldRow12790.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12790) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12790).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12790) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12790_eq : scalarRow12790.targetFrame = BstLean.Part268.agent12790.frame := by
  norm_num [scalarRow12790,BstLean.Part268.agent12790]

noncomputable def frameData12790 : BstLean.Part264b.FrameData 12790 :=
  BstLean.Part269.frameData_from_numerics (n := 12790) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12790.worldPackage rfl BstLean.Part268.WorldRow12790.product_lower (BstLean.Part268.WorldRow12790.producthi.2.trans (by norm_num))
    scalarRow12790 repair12790 covarianceInputs12790 (fun i hi => sourceNumerics12790 hi)
    BstLean.Part268.agent12790.frame targetFrame12790_eq


end BstLean.Part269.N12790

namespace BstLean.Part269.N12791
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12791 : scalarRow12791.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12791, BstLean.Part268.grid12791, BstLean.Part263.worldGrid]

theorem supplies12791 (j : Fin 43) : Supply 12791 (parameters j)
    (cellLower scalarRow12791.grid (sourceIndex j))
    (cellUpper scalarRow12791.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12791.grid grid_top_bounds12791 j

theorem radii12791 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12791.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12791 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12791 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12791.grid grid_top_bounds12791 j hθ

noncomputable def covarianceInputs12791 :
    BstLean.Part263.CovarianceInputs 12791 scalarRow12791.grid parameters (caps repair12791) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12791 grid_top_bounds12791 repair12791

noncomputable def covarianceEvent12791 : Set (AgFam 12791) :=
  BstLean.Part263.covarianceEvent 12791 scalarRow12791.grid parameters

theorem covarianceEvent12791_measurable : MeasurableSet covarianceEvent12791 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12791_payment :
    (retDist (paperDesignP 12791).toCentres).real
      (agentEv (paperDesignP 12791) covarianceEvent12791)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12791

theorem localCov12791 : BstLean.Part259.LocalCovarianceOn covarianceEvent12791
    (BstLean.Part263.cell scalarRow12791.grid) (caps repair12791) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12791

theorem covarianceGood12791_payment :
    (retDist (paperDesignP 12791).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12791)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12791_payment



end BstLean.Part269.N12791

namespace BstLean.Part269.N12791
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12791}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12791.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12791) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12791).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12791 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12791) (by norm_num) BstLean.Part268.WorldRow12791.worldPackage rfl
    BstLean.Part268.WorldRow12791.product_lower (BstLean.Part268.WorldRow12791.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12791} (hw : c ∈ Hof BstLean.Part268.WorldRow12791.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12791) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12791) (by norm_num) BstLean.Part268.WorldRow12791.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12791} (hw : c ∈ Hof BstLean.Part268.WorldRow12791.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12791) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12791).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12791) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12791_eq : scalarRow12791.targetFrame = BstLean.Part268.agent12791.frame := by
  norm_num [scalarRow12791,BstLean.Part268.agent12791]

noncomputable def frameData12791 : BstLean.Part264b.FrameData 12791 :=
  BstLean.Part269.frameData_from_numerics (n := 12791) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12791.worldPackage rfl BstLean.Part268.WorldRow12791.product_lower (BstLean.Part268.WorldRow12791.producthi.2.trans (by norm_num))
    scalarRow12791 repair12791 covarianceInputs12791 (fun i hi => sourceNumerics12791 hi)
    BstLean.Part268.agent12791.frame targetFrame12791_eq


end BstLean.Part269.N12791

namespace BstLean.Part269.N12792
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12792 : scalarRow12792.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12792, BstLean.Part268.grid12792, BstLean.Part263.worldGrid]

theorem supplies12792 (j : Fin 43) : Supply 12792 (parameters j)
    (cellLower scalarRow12792.grid (sourceIndex j))
    (cellUpper scalarRow12792.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12792.grid grid_top_bounds12792 j

theorem radii12792 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12792.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12792 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12792 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12792.grid grid_top_bounds12792 j hθ

noncomputable def covarianceInputs12792 :
    BstLean.Part263.CovarianceInputs 12792 scalarRow12792.grid parameters (caps repair12792) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12792 grid_top_bounds12792 repair12792

noncomputable def covarianceEvent12792 : Set (AgFam 12792) :=
  BstLean.Part263.covarianceEvent 12792 scalarRow12792.grid parameters

theorem covarianceEvent12792_measurable : MeasurableSet covarianceEvent12792 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12792_payment :
    (retDist (paperDesignP 12792).toCentres).real
      (agentEv (paperDesignP 12792) covarianceEvent12792)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12792

theorem localCov12792 : BstLean.Part259.LocalCovarianceOn covarianceEvent12792
    (BstLean.Part263.cell scalarRow12792.grid) (caps repair12792) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12792

theorem covarianceGood12792_payment :
    (retDist (paperDesignP 12792).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12792)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12792_payment



end BstLean.Part269.N12792

namespace BstLean.Part269.N12792
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12792}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12792.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12792) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12792).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12792 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12792) (by norm_num) BstLean.Part268.WorldRow12792.worldPackage rfl
    BstLean.Part268.WorldRow12792.product_lower (BstLean.Part268.WorldRow12792.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12792} (hw : c ∈ Hof BstLean.Part268.WorldRow12792.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12792) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12792) (by norm_num) BstLean.Part268.WorldRow12792.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12792} (hw : c ∈ Hof BstLean.Part268.WorldRow12792.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12792) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12792).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12792) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12792_eq : scalarRow12792.targetFrame = BstLean.Part268.agent12792.frame := by
  norm_num [scalarRow12792,BstLean.Part268.agent12792]

noncomputable def frameData12792 : BstLean.Part264b.FrameData 12792 :=
  BstLean.Part269.frameData_from_numerics (n := 12792) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12792.worldPackage rfl BstLean.Part268.WorldRow12792.product_lower (BstLean.Part268.WorldRow12792.producthi.2.trans (by norm_num))
    scalarRow12792 repair12792 covarianceInputs12792 (fun i hi => sourceNumerics12792 hi)
    BstLean.Part268.agent12792.frame targetFrame12792_eq


end BstLean.Part269.N12792

namespace BstLean.Part269.N12793
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12793 : scalarRow12793.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12793, BstLean.Part268.grid12793, BstLean.Part263.worldGrid]

theorem supplies12793 (j : Fin 43) : Supply 12793 (parameters j)
    (cellLower scalarRow12793.grid (sourceIndex j))
    (cellUpper scalarRow12793.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12793.grid grid_top_bounds12793 j

theorem radii12793 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12793.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12793 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12793 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12793.grid grid_top_bounds12793 j hθ

noncomputable def covarianceInputs12793 :
    BstLean.Part263.CovarianceInputs 12793 scalarRow12793.grid parameters (caps repair12793) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12793 grid_top_bounds12793 repair12793

noncomputable def covarianceEvent12793 : Set (AgFam 12793) :=
  BstLean.Part263.covarianceEvent 12793 scalarRow12793.grid parameters

theorem covarianceEvent12793_measurable : MeasurableSet covarianceEvent12793 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12793_payment :
    (retDist (paperDesignP 12793).toCentres).real
      (agentEv (paperDesignP 12793) covarianceEvent12793)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12793

theorem localCov12793 : BstLean.Part259.LocalCovarianceOn covarianceEvent12793
    (BstLean.Part263.cell scalarRow12793.grid) (caps repair12793) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12793

theorem covarianceGood12793_payment :
    (retDist (paperDesignP 12793).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12793)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12793_payment



end BstLean.Part269.N12793

namespace BstLean.Part269.N12793
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12793}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12793.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12793) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12793).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12793 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12793) (by norm_num) BstLean.Part268.WorldRow12793.worldPackage rfl
    BstLean.Part268.WorldRow12793.product_lower (BstLean.Part268.WorldRow12793.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12793} (hw : c ∈ Hof BstLean.Part268.WorldRow12793.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12793) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12793) (by norm_num) BstLean.Part268.WorldRow12793.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12793} (hw : c ∈ Hof BstLean.Part268.WorldRow12793.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12793) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12793).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12793) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12793_eq : scalarRow12793.targetFrame = BstLean.Part268.agent12793.frame := by
  norm_num [scalarRow12793,BstLean.Part268.agent12793]

noncomputable def frameData12793 : BstLean.Part264b.FrameData 12793 :=
  BstLean.Part269.frameData_from_numerics (n := 12793) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12793.worldPackage rfl BstLean.Part268.WorldRow12793.product_lower (BstLean.Part268.WorldRow12793.producthi.2.trans (by norm_num))
    scalarRow12793 repair12793 covarianceInputs12793 (fun i hi => sourceNumerics12793 hi)
    BstLean.Part268.agent12793.frame targetFrame12793_eq


end BstLean.Part269.N12793

namespace BstLean.Part269.N12794
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12794 : scalarRow12794.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12794, BstLean.Part268.grid12794, BstLean.Part263.worldGrid]

theorem supplies12794 (j : Fin 43) : Supply 12794 (parameters j)
    (cellLower scalarRow12794.grid (sourceIndex j))
    (cellUpper scalarRow12794.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12794.grid grid_top_bounds12794 j

theorem radii12794 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12794.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12794 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12794 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12794.grid grid_top_bounds12794 j hθ

noncomputable def covarianceInputs12794 :
    BstLean.Part263.CovarianceInputs 12794 scalarRow12794.grid parameters (caps repair12794) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12794 grid_top_bounds12794 repair12794

noncomputable def covarianceEvent12794 : Set (AgFam 12794) :=
  BstLean.Part263.covarianceEvent 12794 scalarRow12794.grid parameters

theorem covarianceEvent12794_measurable : MeasurableSet covarianceEvent12794 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12794_payment :
    (retDist (paperDesignP 12794).toCentres).real
      (agentEv (paperDesignP 12794) covarianceEvent12794)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12794

theorem localCov12794 : BstLean.Part259.LocalCovarianceOn covarianceEvent12794
    (BstLean.Part263.cell scalarRow12794.grid) (caps repair12794) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12794

theorem covarianceGood12794_payment :
    (retDist (paperDesignP 12794).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12794)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12794_payment



end BstLean.Part269.N12794

namespace BstLean.Part269.N12794
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12794}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12794.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12794) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12794).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12794 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12794) (by norm_num) BstLean.Part268.WorldRow12794.worldPackage rfl
    BstLean.Part268.WorldRow12794.product_lower (BstLean.Part268.WorldRow12794.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12794} (hw : c ∈ Hof BstLean.Part268.WorldRow12794.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12794) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12794) (by norm_num) BstLean.Part268.WorldRow12794.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12794} (hw : c ∈ Hof BstLean.Part268.WorldRow12794.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12794) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12794).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12794) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12794_eq : scalarRow12794.targetFrame = BstLean.Part268.agent12794.frame := by
  norm_num [scalarRow12794,BstLean.Part268.agent12794]

noncomputable def frameData12794 : BstLean.Part264b.FrameData 12794 :=
  BstLean.Part269.frameData_from_numerics (n := 12794) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12794.worldPackage rfl BstLean.Part268.WorldRow12794.product_lower (BstLean.Part268.WorldRow12794.producthi.2.trans (by norm_num))
    scalarRow12794 repair12794 covarianceInputs12794 (fun i hi => sourceNumerics12794 hi)
    BstLean.Part268.agent12794.frame targetFrame12794_eq


end BstLean.Part269.N12794
