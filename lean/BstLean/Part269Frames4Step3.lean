import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World4Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs4
import BstLean.Part269Rows4
import BstLean.Part269Sources4
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12465
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12465 : scalarRow12465.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12465, BstLean.Part268.grid12465, BstLean.Part263.worldGrid]

theorem supplies12465 (j : Fin 43) : Supply 12465 (parameters j)
    (cellLower scalarRow12465.grid (sourceIndex j))
    (cellUpper scalarRow12465.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12465.grid grid_top_bounds12465 j

theorem radii12465 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12465.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12465 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12465 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12465.grid grid_top_bounds12465 j hθ

noncomputable def covarianceInputs12465 :
    BstLean.Part263.CovarianceInputs 12465 scalarRow12465.grid parameters (caps repair12465) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12465 grid_top_bounds12465 repair12465

noncomputable def covarianceEvent12465 : Set (AgFam 12465) :=
  BstLean.Part263.covarianceEvent 12465 scalarRow12465.grid parameters

theorem covarianceEvent12465_measurable : MeasurableSet covarianceEvent12465 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12465_payment :
    (retDist (paperDesignP 12465).toCentres).real
      (agentEv (paperDesignP 12465) covarianceEvent12465)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12465

theorem localCov12465 : BstLean.Part259.LocalCovarianceOn covarianceEvent12465
    (BstLean.Part263.cell scalarRow12465.grid) (caps repair12465) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12465

theorem covarianceGood12465_payment :
    (retDist (paperDesignP 12465).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12465)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12465_payment



end BstLean.Part269.N12465

namespace BstLean.Part269.N12465
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12465}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12465.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12465) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12465).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12465 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12465) (by norm_num) BstLean.Part268.WorldRow12465.worldPackage rfl
    BstLean.Part268.WorldRow12465.product_lower (BstLean.Part268.WorldRow12465.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12465} (hw : c ∈ Hof BstLean.Part268.WorldRow12465.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12465) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12465) (by norm_num) BstLean.Part268.WorldRow12465.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12465} (hw : c ∈ Hof BstLean.Part268.WorldRow12465.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12465) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12465).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12465) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12465_eq : scalarRow12465.targetFrame = BstLean.Part268.agent12465.frame := by
  norm_num [scalarRow12465,BstLean.Part268.agent12465]

noncomputable def frameData12465 : BstLean.Part264b.FrameData 12465 :=
  BstLean.Part269.frameData_from_numerics (n := 12465) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12465.worldPackage rfl BstLean.Part268.WorldRow12465.product_lower (BstLean.Part268.WorldRow12465.producthi.2.trans (by norm_num))
    scalarRow12465 repair12465 covarianceInputs12465 (fun i hi => sourceNumerics12465 hi)
    BstLean.Part268.agent12465.frame targetFrame12465_eq


end BstLean.Part269.N12465

namespace BstLean.Part269.N12466
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12466 : scalarRow12466.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12466, BstLean.Part268.grid12466, BstLean.Part263.worldGrid]

theorem supplies12466 (j : Fin 43) : Supply 12466 (parameters j)
    (cellLower scalarRow12466.grid (sourceIndex j))
    (cellUpper scalarRow12466.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12466.grid grid_top_bounds12466 j

theorem radii12466 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12466.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12466 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12466 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12466.grid grid_top_bounds12466 j hθ

noncomputable def covarianceInputs12466 :
    BstLean.Part263.CovarianceInputs 12466 scalarRow12466.grid parameters (caps repair12466) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12466 grid_top_bounds12466 repair12466

noncomputable def covarianceEvent12466 : Set (AgFam 12466) :=
  BstLean.Part263.covarianceEvent 12466 scalarRow12466.grid parameters

theorem covarianceEvent12466_measurable : MeasurableSet covarianceEvent12466 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12466_payment :
    (retDist (paperDesignP 12466).toCentres).real
      (agentEv (paperDesignP 12466) covarianceEvent12466)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12466

theorem localCov12466 : BstLean.Part259.LocalCovarianceOn covarianceEvent12466
    (BstLean.Part263.cell scalarRow12466.grid) (caps repair12466) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12466

theorem covarianceGood12466_payment :
    (retDist (paperDesignP 12466).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12466)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12466_payment



end BstLean.Part269.N12466

namespace BstLean.Part269.N12466
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12466}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12466.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12466) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12466).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12466 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12466) (by norm_num) BstLean.Part268.WorldRow12466.worldPackage rfl
    BstLean.Part268.WorldRow12466.product_lower (BstLean.Part268.WorldRow12466.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12466} (hw : c ∈ Hof BstLean.Part268.WorldRow12466.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12466) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12466) (by norm_num) BstLean.Part268.WorldRow12466.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12466} (hw : c ∈ Hof BstLean.Part268.WorldRow12466.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12466) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12466).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12466) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12466_eq : scalarRow12466.targetFrame = BstLean.Part268.agent12466.frame := by
  norm_num [scalarRow12466,BstLean.Part268.agent12466]

noncomputable def frameData12466 : BstLean.Part264b.FrameData 12466 :=
  BstLean.Part269.frameData_from_numerics (n := 12466) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12466.worldPackage rfl BstLean.Part268.WorldRow12466.product_lower (BstLean.Part268.WorldRow12466.producthi.2.trans (by norm_num))
    scalarRow12466 repair12466 covarianceInputs12466 (fun i hi => sourceNumerics12466 hi)
    BstLean.Part268.agent12466.frame targetFrame12466_eq


end BstLean.Part269.N12466

namespace BstLean.Part269.N12467
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12467 : scalarRow12467.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12467, BstLean.Part268.grid12467, BstLean.Part263.worldGrid]

theorem supplies12467 (j : Fin 43) : Supply 12467 (parameters j)
    (cellLower scalarRow12467.grid (sourceIndex j))
    (cellUpper scalarRow12467.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12467.grid grid_top_bounds12467 j

theorem radii12467 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12467.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12467 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12467 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12467.grid grid_top_bounds12467 j hθ

noncomputable def covarianceInputs12467 :
    BstLean.Part263.CovarianceInputs 12467 scalarRow12467.grid parameters (caps repair12467) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12467 grid_top_bounds12467 repair12467

noncomputable def covarianceEvent12467 : Set (AgFam 12467) :=
  BstLean.Part263.covarianceEvent 12467 scalarRow12467.grid parameters

theorem covarianceEvent12467_measurable : MeasurableSet covarianceEvent12467 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12467_payment :
    (retDist (paperDesignP 12467).toCentres).real
      (agentEv (paperDesignP 12467) covarianceEvent12467)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12467

theorem localCov12467 : BstLean.Part259.LocalCovarianceOn covarianceEvent12467
    (BstLean.Part263.cell scalarRow12467.grid) (caps repair12467) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12467

theorem covarianceGood12467_payment :
    (retDist (paperDesignP 12467).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12467)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12467_payment



end BstLean.Part269.N12467

namespace BstLean.Part269.N12467
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12467}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12467.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12467) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12467).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12467 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12467) (by norm_num) BstLean.Part268.WorldRow12467.worldPackage rfl
    BstLean.Part268.WorldRow12467.product_lower (BstLean.Part268.WorldRow12467.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12467} (hw : c ∈ Hof BstLean.Part268.WorldRow12467.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12467) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12467) (by norm_num) BstLean.Part268.WorldRow12467.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12467} (hw : c ∈ Hof BstLean.Part268.WorldRow12467.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12467) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12467).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12467) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12467_eq : scalarRow12467.targetFrame = BstLean.Part268.agent12467.frame := by
  norm_num [scalarRow12467,BstLean.Part268.agent12467]

noncomputable def frameData12467 : BstLean.Part264b.FrameData 12467 :=
  BstLean.Part269.frameData_from_numerics (n := 12467) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12467.worldPackage rfl BstLean.Part268.WorldRow12467.product_lower (BstLean.Part268.WorldRow12467.producthi.2.trans (by norm_num))
    scalarRow12467 repair12467 covarianceInputs12467 (fun i hi => sourceNumerics12467 hi)
    BstLean.Part268.agent12467.frame targetFrame12467_eq


end BstLean.Part269.N12467

namespace BstLean.Part269.N12468
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12468 : scalarRow12468.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12468, BstLean.Part268.grid12468, BstLean.Part263.worldGrid]

theorem supplies12468 (j : Fin 43) : Supply 12468 (parameters j)
    (cellLower scalarRow12468.grid (sourceIndex j))
    (cellUpper scalarRow12468.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12468.grid grid_top_bounds12468 j

theorem radii12468 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12468.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12468 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12468 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12468.grid grid_top_bounds12468 j hθ

noncomputable def covarianceInputs12468 :
    BstLean.Part263.CovarianceInputs 12468 scalarRow12468.grid parameters (caps repair12468) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12468 grid_top_bounds12468 repair12468

noncomputable def covarianceEvent12468 : Set (AgFam 12468) :=
  BstLean.Part263.covarianceEvent 12468 scalarRow12468.grid parameters

theorem covarianceEvent12468_measurable : MeasurableSet covarianceEvent12468 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12468_payment :
    (retDist (paperDesignP 12468).toCentres).real
      (agentEv (paperDesignP 12468) covarianceEvent12468)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12468

theorem localCov12468 : BstLean.Part259.LocalCovarianceOn covarianceEvent12468
    (BstLean.Part263.cell scalarRow12468.grid) (caps repair12468) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12468

theorem covarianceGood12468_payment :
    (retDist (paperDesignP 12468).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12468)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12468_payment



end BstLean.Part269.N12468

namespace BstLean.Part269.N12468
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12468}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12468.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12468) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12468).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12468 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12468) (by norm_num) BstLean.Part268.WorldRow12468.worldPackage rfl
    BstLean.Part268.WorldRow12468.product_lower (BstLean.Part268.WorldRow12468.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12468} (hw : c ∈ Hof BstLean.Part268.WorldRow12468.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12468) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12468) (by norm_num) BstLean.Part268.WorldRow12468.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12468} (hw : c ∈ Hof BstLean.Part268.WorldRow12468.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12468) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12468).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12468) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12468_eq : scalarRow12468.targetFrame = BstLean.Part268.agent12468.frame := by
  norm_num [scalarRow12468,BstLean.Part268.agent12468]

noncomputable def frameData12468 : BstLean.Part264b.FrameData 12468 :=
  BstLean.Part269.frameData_from_numerics (n := 12468) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12468.worldPackage rfl BstLean.Part268.WorldRow12468.product_lower (BstLean.Part268.WorldRow12468.producthi.2.trans (by norm_num))
    scalarRow12468 repair12468 covarianceInputs12468 (fun i hi => sourceNumerics12468 hi)
    BstLean.Part268.agent12468.frame targetFrame12468_eq


end BstLean.Part269.N12468

namespace BstLean.Part269.N12469
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12469 : scalarRow12469.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12469, BstLean.Part268.grid12469, BstLean.Part263.worldGrid]

theorem supplies12469 (j : Fin 43) : Supply 12469 (parameters j)
    (cellLower scalarRow12469.grid (sourceIndex j))
    (cellUpper scalarRow12469.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12469.grid grid_top_bounds12469 j

theorem radii12469 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12469.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12469 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12469 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12469.grid grid_top_bounds12469 j hθ

noncomputable def covarianceInputs12469 :
    BstLean.Part263.CovarianceInputs 12469 scalarRow12469.grid parameters (caps repair12469) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12469 grid_top_bounds12469 repair12469

noncomputable def covarianceEvent12469 : Set (AgFam 12469) :=
  BstLean.Part263.covarianceEvent 12469 scalarRow12469.grid parameters

theorem covarianceEvent12469_measurable : MeasurableSet covarianceEvent12469 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12469_payment :
    (retDist (paperDesignP 12469).toCentres).real
      (agentEv (paperDesignP 12469) covarianceEvent12469)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12469

theorem localCov12469 : BstLean.Part259.LocalCovarianceOn covarianceEvent12469
    (BstLean.Part263.cell scalarRow12469.grid) (caps repair12469) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12469

theorem covarianceGood12469_payment :
    (retDist (paperDesignP 12469).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12469)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12469_payment



end BstLean.Part269.N12469

namespace BstLean.Part269.N12469
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12469}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12469.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12469) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12469).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12469 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12469) (by norm_num) BstLean.Part268.WorldRow12469.worldPackage rfl
    BstLean.Part268.WorldRow12469.product_lower (BstLean.Part268.WorldRow12469.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12469} (hw : c ∈ Hof BstLean.Part268.WorldRow12469.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12469) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12469) (by norm_num) BstLean.Part268.WorldRow12469.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12469} (hw : c ∈ Hof BstLean.Part268.WorldRow12469.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12469) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12469).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12469) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12469_eq : scalarRow12469.targetFrame = BstLean.Part268.agent12469.frame := by
  norm_num [scalarRow12469,BstLean.Part268.agent12469]

noncomputable def frameData12469 : BstLean.Part264b.FrameData 12469 :=
  BstLean.Part269.frameData_from_numerics (n := 12469) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12469.worldPackage rfl BstLean.Part268.WorldRow12469.product_lower (BstLean.Part268.WorldRow12469.producthi.2.trans (by norm_num))
    scalarRow12469 repair12469 covarianceInputs12469 (fun i hi => sourceNumerics12469 hi)
    BstLean.Part268.agent12469.frame targetFrame12469_eq


end BstLean.Part269.N12469
