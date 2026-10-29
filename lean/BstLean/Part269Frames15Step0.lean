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

namespace BstLean.Part269.N12725
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12725 : scalarRow12725.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12725, BstLean.Part268.grid12725, BstLean.Part263.worldGrid]

theorem supplies12725 (j : Fin 43) : Supply 12725 (parameters j)
    (cellLower scalarRow12725.grid (sourceIndex j))
    (cellUpper scalarRow12725.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12725.grid grid_top_bounds12725 j

theorem radii12725 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12725.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12725 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12725 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12725.grid grid_top_bounds12725 j hθ

noncomputable def covarianceInputs12725 :
    BstLean.Part263.CovarianceInputs 12725 scalarRow12725.grid parameters (caps repair12725) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12725 grid_top_bounds12725 repair12725

noncomputable def covarianceEvent12725 : Set (AgFam 12725) :=
  BstLean.Part263.covarianceEvent 12725 scalarRow12725.grid parameters

theorem covarianceEvent12725_measurable : MeasurableSet covarianceEvent12725 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12725_payment :
    (retDist (paperDesignP 12725).toCentres).real
      (agentEv (paperDesignP 12725) covarianceEvent12725)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12725

theorem localCov12725 : BstLean.Part259.LocalCovarianceOn covarianceEvent12725
    (BstLean.Part263.cell scalarRow12725.grid) (caps repair12725) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12725

theorem covarianceGood12725_payment :
    (retDist (paperDesignP 12725).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12725)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12725_payment



end BstLean.Part269.N12725

namespace BstLean.Part269.N12725
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12725}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12725.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12725) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12725).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12725 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12725) (by norm_num) BstLean.Part268.WorldRow12725.worldPackage rfl
    BstLean.Part268.WorldRow12725.product_lower (BstLean.Part268.WorldRow12725.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12725} (hw : c ∈ Hof BstLean.Part268.WorldRow12725.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12725) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12725) (by norm_num) BstLean.Part268.WorldRow12725.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12725} (hw : c ∈ Hof BstLean.Part268.WorldRow12725.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12725) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12725).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12725) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12725_eq : scalarRow12725.targetFrame = BstLean.Part268.agent12725.frame := by
  norm_num [scalarRow12725,BstLean.Part268.agent12725]

noncomputable def frameData12725 : BstLean.Part264b.FrameData 12725 :=
  BstLean.Part269.frameData_from_numerics (n := 12725) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12725.worldPackage rfl BstLean.Part268.WorldRow12725.product_lower (BstLean.Part268.WorldRow12725.producthi.2.trans (by norm_num))
    scalarRow12725 repair12725 covarianceInputs12725 (fun i hi => sourceNumerics12725 hi)
    BstLean.Part268.agent12725.frame targetFrame12725_eq


end BstLean.Part269.N12725

namespace BstLean.Part269.N12726
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12726 : scalarRow12726.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12726, BstLean.Part268.grid12726, BstLean.Part263.worldGrid]

theorem supplies12726 (j : Fin 43) : Supply 12726 (parameters j)
    (cellLower scalarRow12726.grid (sourceIndex j))
    (cellUpper scalarRow12726.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12726.grid grid_top_bounds12726 j

theorem radii12726 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12726.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12726 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12726 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12726.grid grid_top_bounds12726 j hθ

noncomputable def covarianceInputs12726 :
    BstLean.Part263.CovarianceInputs 12726 scalarRow12726.grid parameters (caps repair12726) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12726 grid_top_bounds12726 repair12726

noncomputable def covarianceEvent12726 : Set (AgFam 12726) :=
  BstLean.Part263.covarianceEvent 12726 scalarRow12726.grid parameters

theorem covarianceEvent12726_measurable : MeasurableSet covarianceEvent12726 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12726_payment :
    (retDist (paperDesignP 12726).toCentres).real
      (agentEv (paperDesignP 12726) covarianceEvent12726)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12726

theorem localCov12726 : BstLean.Part259.LocalCovarianceOn covarianceEvent12726
    (BstLean.Part263.cell scalarRow12726.grid) (caps repair12726) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12726

theorem covarianceGood12726_payment :
    (retDist (paperDesignP 12726).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12726)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12726_payment



end BstLean.Part269.N12726

namespace BstLean.Part269.N12726
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12726}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12726.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12726) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12726).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12726 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12726) (by norm_num) BstLean.Part268.WorldRow12726.worldPackage rfl
    BstLean.Part268.WorldRow12726.product_lower (BstLean.Part268.WorldRow12726.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12726} (hw : c ∈ Hof BstLean.Part268.WorldRow12726.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12726) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12726) (by norm_num) BstLean.Part268.WorldRow12726.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12726} (hw : c ∈ Hof BstLean.Part268.WorldRow12726.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12726) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12726).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12726) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12726_eq : scalarRow12726.targetFrame = BstLean.Part268.agent12726.frame := by
  norm_num [scalarRow12726,BstLean.Part268.agent12726]

noncomputable def frameData12726 : BstLean.Part264b.FrameData 12726 :=
  BstLean.Part269.frameData_from_numerics (n := 12726) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12726.worldPackage rfl BstLean.Part268.WorldRow12726.product_lower (BstLean.Part268.WorldRow12726.producthi.2.trans (by norm_num))
    scalarRow12726 repair12726 covarianceInputs12726 (fun i hi => sourceNumerics12726 hi)
    BstLean.Part268.agent12726.frame targetFrame12726_eq


end BstLean.Part269.N12726

namespace BstLean.Part269.N12727
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12727 : scalarRow12727.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12727, BstLean.Part268.grid12727, BstLean.Part263.worldGrid]

theorem supplies12727 (j : Fin 43) : Supply 12727 (parameters j)
    (cellLower scalarRow12727.grid (sourceIndex j))
    (cellUpper scalarRow12727.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12727.grid grid_top_bounds12727 j

theorem radii12727 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12727.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12727 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12727 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12727.grid grid_top_bounds12727 j hθ

noncomputable def covarianceInputs12727 :
    BstLean.Part263.CovarianceInputs 12727 scalarRow12727.grid parameters (caps repair12727) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12727 grid_top_bounds12727 repair12727

noncomputable def covarianceEvent12727 : Set (AgFam 12727) :=
  BstLean.Part263.covarianceEvent 12727 scalarRow12727.grid parameters

theorem covarianceEvent12727_measurable : MeasurableSet covarianceEvent12727 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12727_payment :
    (retDist (paperDesignP 12727).toCentres).real
      (agentEv (paperDesignP 12727) covarianceEvent12727)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12727

theorem localCov12727 : BstLean.Part259.LocalCovarianceOn covarianceEvent12727
    (BstLean.Part263.cell scalarRow12727.grid) (caps repair12727) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12727

theorem covarianceGood12727_payment :
    (retDist (paperDesignP 12727).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12727)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12727_payment



end BstLean.Part269.N12727

namespace BstLean.Part269.N12727
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12727}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12727.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12727) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12727).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12727 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12727) (by norm_num) BstLean.Part268.WorldRow12727.worldPackage rfl
    BstLean.Part268.WorldRow12727.product_lower (BstLean.Part268.WorldRow12727.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12727} (hw : c ∈ Hof BstLean.Part268.WorldRow12727.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12727) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12727) (by norm_num) BstLean.Part268.WorldRow12727.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12727} (hw : c ∈ Hof BstLean.Part268.WorldRow12727.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12727) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12727).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12727) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12727_eq : scalarRow12727.targetFrame = BstLean.Part268.agent12727.frame := by
  norm_num [scalarRow12727,BstLean.Part268.agent12727]

noncomputable def frameData12727 : BstLean.Part264b.FrameData 12727 :=
  BstLean.Part269.frameData_from_numerics (n := 12727) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12727.worldPackage rfl BstLean.Part268.WorldRow12727.product_lower (BstLean.Part268.WorldRow12727.producthi.2.trans (by norm_num))
    scalarRow12727 repair12727 covarianceInputs12727 (fun i hi => sourceNumerics12727 hi)
    BstLean.Part268.agent12727.frame targetFrame12727_eq


end BstLean.Part269.N12727

namespace BstLean.Part269.N12728
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12728 : scalarRow12728.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12728, BstLean.Part268.grid12728, BstLean.Part263.worldGrid]

theorem supplies12728 (j : Fin 43) : Supply 12728 (parameters j)
    (cellLower scalarRow12728.grid (sourceIndex j))
    (cellUpper scalarRow12728.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12728.grid grid_top_bounds12728 j

theorem radii12728 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12728.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12728 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12728 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12728.grid grid_top_bounds12728 j hθ

noncomputable def covarianceInputs12728 :
    BstLean.Part263.CovarianceInputs 12728 scalarRow12728.grid parameters (caps repair12728) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12728 grid_top_bounds12728 repair12728

noncomputable def covarianceEvent12728 : Set (AgFam 12728) :=
  BstLean.Part263.covarianceEvent 12728 scalarRow12728.grid parameters

theorem covarianceEvent12728_measurable : MeasurableSet covarianceEvent12728 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12728_payment :
    (retDist (paperDesignP 12728).toCentres).real
      (agentEv (paperDesignP 12728) covarianceEvent12728)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12728

theorem localCov12728 : BstLean.Part259.LocalCovarianceOn covarianceEvent12728
    (BstLean.Part263.cell scalarRow12728.grid) (caps repair12728) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12728

theorem covarianceGood12728_payment :
    (retDist (paperDesignP 12728).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12728)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12728_payment



end BstLean.Part269.N12728

namespace BstLean.Part269.N12728
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12728}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12728.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12728) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12728).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12728 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12728) (by norm_num) BstLean.Part268.WorldRow12728.worldPackage rfl
    BstLean.Part268.WorldRow12728.product_lower (BstLean.Part268.WorldRow12728.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12728} (hw : c ∈ Hof BstLean.Part268.WorldRow12728.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12728) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12728) (by norm_num) BstLean.Part268.WorldRow12728.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12728} (hw : c ∈ Hof BstLean.Part268.WorldRow12728.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12728) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12728).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12728) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12728_eq : scalarRow12728.targetFrame = BstLean.Part268.agent12728.frame := by
  norm_num [scalarRow12728,BstLean.Part268.agent12728]

noncomputable def frameData12728 : BstLean.Part264b.FrameData 12728 :=
  BstLean.Part269.frameData_from_numerics (n := 12728) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12728.worldPackage rfl BstLean.Part268.WorldRow12728.product_lower (BstLean.Part268.WorldRow12728.producthi.2.trans (by norm_num))
    scalarRow12728 repair12728 covarianceInputs12728 (fun i hi => sourceNumerics12728 hi)
    BstLean.Part268.agent12728.frame targetFrame12728_eq


end BstLean.Part269.N12728

namespace BstLean.Part269.N12729
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12729 : scalarRow12729.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12729, BstLean.Part268.grid12729, BstLean.Part263.worldGrid]

theorem supplies12729 (j : Fin 43) : Supply 12729 (parameters j)
    (cellLower scalarRow12729.grid (sourceIndex j))
    (cellUpper scalarRow12729.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12729.grid grid_top_bounds12729 j

theorem radii12729 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12729.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12729 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12729 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12729.grid grid_top_bounds12729 j hθ

noncomputable def covarianceInputs12729 :
    BstLean.Part263.CovarianceInputs 12729 scalarRow12729.grid parameters (caps repair12729) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12729 grid_top_bounds12729 repair12729

noncomputable def covarianceEvent12729 : Set (AgFam 12729) :=
  BstLean.Part263.covarianceEvent 12729 scalarRow12729.grid parameters

theorem covarianceEvent12729_measurable : MeasurableSet covarianceEvent12729 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12729_payment :
    (retDist (paperDesignP 12729).toCentres).real
      (agentEv (paperDesignP 12729) covarianceEvent12729)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12729

theorem localCov12729 : BstLean.Part259.LocalCovarianceOn covarianceEvent12729
    (BstLean.Part263.cell scalarRow12729.grid) (caps repair12729) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12729

theorem covarianceGood12729_payment :
    (retDist (paperDesignP 12729).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12729)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12729_payment



end BstLean.Part269.N12729

namespace BstLean.Part269.N12729
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12729}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12729.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12729) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12729).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12729 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12729) (by norm_num) BstLean.Part268.WorldRow12729.worldPackage rfl
    BstLean.Part268.WorldRow12729.product_lower (BstLean.Part268.WorldRow12729.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12729} (hw : c ∈ Hof BstLean.Part268.WorldRow12729.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12729) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12729) (by norm_num) BstLean.Part268.WorldRow12729.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12729} (hw : c ∈ Hof BstLean.Part268.WorldRow12729.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12729) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12729).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12729) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12729_eq : scalarRow12729.targetFrame = BstLean.Part268.agent12729.frame := by
  norm_num [scalarRow12729,BstLean.Part268.agent12729]

noncomputable def frameData12729 : BstLean.Part264b.FrameData 12729 :=
  BstLean.Part269.frameData_from_numerics (n := 12729) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12729.worldPackage rfl BstLean.Part268.WorldRow12729.product_lower (BstLean.Part268.WorldRow12729.producthi.2.trans (by norm_num))
    scalarRow12729 repair12729 covarianceInputs12729 (fun i hi => sourceNumerics12729 hi)
    BstLean.Part268.agent12729.frame targetFrame12729_eq


end BstLean.Part269.N12729
