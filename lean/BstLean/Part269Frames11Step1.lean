import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World11Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs11
import BstLean.Part269Rows11
import BstLean.Part269Sources11
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12630
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12630 : scalarRow12630.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12630, BstLean.Part268.grid12630, BstLean.Part263.worldGrid]

theorem supplies12630 (j : Fin 43) : Supply 12630 (parameters j)
    (cellLower scalarRow12630.grid (sourceIndex j))
    (cellUpper scalarRow12630.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12630.grid grid_top_bounds12630 j

theorem radii12630 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12630.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12630 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12630 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12630.grid grid_top_bounds12630 j hθ

noncomputable def covarianceInputs12630 :
    BstLean.Part263.CovarianceInputs 12630 scalarRow12630.grid parameters (caps repair12630) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12630 grid_top_bounds12630 repair12630

noncomputable def covarianceEvent12630 : Set (AgFam 12630) :=
  BstLean.Part263.covarianceEvent 12630 scalarRow12630.grid parameters

theorem covarianceEvent12630_measurable : MeasurableSet covarianceEvent12630 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12630_payment :
    (retDist (paperDesignP 12630).toCentres).real
      (agentEv (paperDesignP 12630) covarianceEvent12630)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12630

theorem localCov12630 : BstLean.Part259.LocalCovarianceOn covarianceEvent12630
    (BstLean.Part263.cell scalarRow12630.grid) (caps repair12630) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12630

theorem covarianceGood12630_payment :
    (retDist (paperDesignP 12630).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12630)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12630_payment



end BstLean.Part269.N12630

namespace BstLean.Part269.N12630
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12630}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12630.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12630) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12630).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12630 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12630) (by norm_num) BstLean.Part268.WorldRow12630.worldPackage rfl
    BstLean.Part268.WorldRow12630.product_lower (BstLean.Part268.WorldRow12630.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12630} (hw : c ∈ Hof BstLean.Part268.WorldRow12630.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12630) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12630) (by norm_num) BstLean.Part268.WorldRow12630.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12630} (hw : c ∈ Hof BstLean.Part268.WorldRow12630.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12630) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12630).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12630) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12630_eq : scalarRow12630.targetFrame = BstLean.Part268.agent12630.frame := by
  norm_num [scalarRow12630,BstLean.Part268.agent12630]

noncomputable def frameData12630 : BstLean.Part264b.FrameData 12630 :=
  BstLean.Part269.frameData_from_numerics (n := 12630) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12630.worldPackage rfl BstLean.Part268.WorldRow12630.product_lower (BstLean.Part268.WorldRow12630.producthi.2.trans (by norm_num))
    scalarRow12630 repair12630 covarianceInputs12630 (fun i hi => sourceNumerics12630 hi)
    BstLean.Part268.agent12630.frame targetFrame12630_eq


end BstLean.Part269.N12630

namespace BstLean.Part269.N12631
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12631 : scalarRow12631.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12631, BstLean.Part268.grid12631, BstLean.Part263.worldGrid]

theorem supplies12631 (j : Fin 43) : Supply 12631 (parameters j)
    (cellLower scalarRow12631.grid (sourceIndex j))
    (cellUpper scalarRow12631.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12631.grid grid_top_bounds12631 j

theorem radii12631 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12631.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12631 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12631 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12631.grid grid_top_bounds12631 j hθ

noncomputable def covarianceInputs12631 :
    BstLean.Part263.CovarianceInputs 12631 scalarRow12631.grid parameters (caps repair12631) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12631 grid_top_bounds12631 repair12631

noncomputable def covarianceEvent12631 : Set (AgFam 12631) :=
  BstLean.Part263.covarianceEvent 12631 scalarRow12631.grid parameters

theorem covarianceEvent12631_measurable : MeasurableSet covarianceEvent12631 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12631_payment :
    (retDist (paperDesignP 12631).toCentres).real
      (agentEv (paperDesignP 12631) covarianceEvent12631)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12631

theorem localCov12631 : BstLean.Part259.LocalCovarianceOn covarianceEvent12631
    (BstLean.Part263.cell scalarRow12631.grid) (caps repair12631) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12631

theorem covarianceGood12631_payment :
    (retDist (paperDesignP 12631).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12631)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12631_payment



end BstLean.Part269.N12631

namespace BstLean.Part269.N12631
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12631}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12631.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12631) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12631).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12631 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12631) (by norm_num) BstLean.Part268.WorldRow12631.worldPackage rfl
    BstLean.Part268.WorldRow12631.product_lower (BstLean.Part268.WorldRow12631.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12631} (hw : c ∈ Hof BstLean.Part268.WorldRow12631.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12631) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12631) (by norm_num) BstLean.Part268.WorldRow12631.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12631} (hw : c ∈ Hof BstLean.Part268.WorldRow12631.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12631) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12631).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12631) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12631_eq : scalarRow12631.targetFrame = BstLean.Part268.agent12631.frame := by
  norm_num [scalarRow12631,BstLean.Part268.agent12631]

noncomputable def frameData12631 : BstLean.Part264b.FrameData 12631 :=
  BstLean.Part269.frameData_from_numerics (n := 12631) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12631.worldPackage rfl BstLean.Part268.WorldRow12631.product_lower (BstLean.Part268.WorldRow12631.producthi.2.trans (by norm_num))
    scalarRow12631 repair12631 covarianceInputs12631 (fun i hi => sourceNumerics12631 hi)
    BstLean.Part268.agent12631.frame targetFrame12631_eq


end BstLean.Part269.N12631

namespace BstLean.Part269.N12632
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12632 : scalarRow12632.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12632, BstLean.Part268.grid12632, BstLean.Part263.worldGrid]

theorem supplies12632 (j : Fin 43) : Supply 12632 (parameters j)
    (cellLower scalarRow12632.grid (sourceIndex j))
    (cellUpper scalarRow12632.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12632.grid grid_top_bounds12632 j

theorem radii12632 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12632.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12632 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12632 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12632.grid grid_top_bounds12632 j hθ

noncomputable def covarianceInputs12632 :
    BstLean.Part263.CovarianceInputs 12632 scalarRow12632.grid parameters (caps repair12632) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12632 grid_top_bounds12632 repair12632

noncomputable def covarianceEvent12632 : Set (AgFam 12632) :=
  BstLean.Part263.covarianceEvent 12632 scalarRow12632.grid parameters

theorem covarianceEvent12632_measurable : MeasurableSet covarianceEvent12632 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12632_payment :
    (retDist (paperDesignP 12632).toCentres).real
      (agentEv (paperDesignP 12632) covarianceEvent12632)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12632

theorem localCov12632 : BstLean.Part259.LocalCovarianceOn covarianceEvent12632
    (BstLean.Part263.cell scalarRow12632.grid) (caps repair12632) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12632

theorem covarianceGood12632_payment :
    (retDist (paperDesignP 12632).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12632)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12632_payment



end BstLean.Part269.N12632

namespace BstLean.Part269.N12632
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12632}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12632.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12632) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12632).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12632 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12632) (by norm_num) BstLean.Part268.WorldRow12632.worldPackage rfl
    BstLean.Part268.WorldRow12632.product_lower (BstLean.Part268.WorldRow12632.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12632} (hw : c ∈ Hof BstLean.Part268.WorldRow12632.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12632) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12632) (by norm_num) BstLean.Part268.WorldRow12632.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12632} (hw : c ∈ Hof BstLean.Part268.WorldRow12632.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12632) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12632).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12632) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12632_eq : scalarRow12632.targetFrame = BstLean.Part268.agent12632.frame := by
  norm_num [scalarRow12632,BstLean.Part268.agent12632]

noncomputable def frameData12632 : BstLean.Part264b.FrameData 12632 :=
  BstLean.Part269.frameData_from_numerics (n := 12632) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12632.worldPackage rfl BstLean.Part268.WorldRow12632.product_lower (BstLean.Part268.WorldRow12632.producthi.2.trans (by norm_num))
    scalarRow12632 repair12632 covarianceInputs12632 (fun i hi => sourceNumerics12632 hi)
    BstLean.Part268.agent12632.frame targetFrame12632_eq


end BstLean.Part269.N12632

namespace BstLean.Part269.N12633
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12633 : scalarRow12633.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12633, BstLean.Part268.grid12633, BstLean.Part263.worldGrid]

theorem supplies12633 (j : Fin 43) : Supply 12633 (parameters j)
    (cellLower scalarRow12633.grid (sourceIndex j))
    (cellUpper scalarRow12633.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12633.grid grid_top_bounds12633 j

theorem radii12633 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12633.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12633 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12633 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12633.grid grid_top_bounds12633 j hθ

noncomputable def covarianceInputs12633 :
    BstLean.Part263.CovarianceInputs 12633 scalarRow12633.grid parameters (caps repair12633) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12633 grid_top_bounds12633 repair12633

noncomputable def covarianceEvent12633 : Set (AgFam 12633) :=
  BstLean.Part263.covarianceEvent 12633 scalarRow12633.grid parameters

theorem covarianceEvent12633_measurable : MeasurableSet covarianceEvent12633 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12633_payment :
    (retDist (paperDesignP 12633).toCentres).real
      (agentEv (paperDesignP 12633) covarianceEvent12633)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12633

theorem localCov12633 : BstLean.Part259.LocalCovarianceOn covarianceEvent12633
    (BstLean.Part263.cell scalarRow12633.grid) (caps repair12633) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12633

theorem covarianceGood12633_payment :
    (retDist (paperDesignP 12633).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12633)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12633_payment



end BstLean.Part269.N12633

namespace BstLean.Part269.N12633
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12633}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12633.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12633) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12633).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12633 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12633) (by norm_num) BstLean.Part268.WorldRow12633.worldPackage rfl
    BstLean.Part268.WorldRow12633.product_lower (BstLean.Part268.WorldRow12633.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12633} (hw : c ∈ Hof BstLean.Part268.WorldRow12633.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12633) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12633) (by norm_num) BstLean.Part268.WorldRow12633.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12633} (hw : c ∈ Hof BstLean.Part268.WorldRow12633.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12633) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12633).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12633) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12633_eq : scalarRow12633.targetFrame = BstLean.Part268.agent12633.frame := by
  norm_num [scalarRow12633,BstLean.Part268.agent12633]

noncomputable def frameData12633 : BstLean.Part264b.FrameData 12633 :=
  BstLean.Part269.frameData_from_numerics (n := 12633) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12633.worldPackage rfl BstLean.Part268.WorldRow12633.product_lower (BstLean.Part268.WorldRow12633.producthi.2.trans (by norm_num))
    scalarRow12633 repair12633 covarianceInputs12633 (fun i hi => sourceNumerics12633 hi)
    BstLean.Part268.agent12633.frame targetFrame12633_eq


end BstLean.Part269.N12633

namespace BstLean.Part269.N12634
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12634 : scalarRow12634.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12634, BstLean.Part268.grid12634, BstLean.Part263.worldGrid]

theorem supplies12634 (j : Fin 43) : Supply 12634 (parameters j)
    (cellLower scalarRow12634.grid (sourceIndex j))
    (cellUpper scalarRow12634.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12634.grid grid_top_bounds12634 j

theorem radii12634 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12634.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12634 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12634 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12634.grid grid_top_bounds12634 j hθ

noncomputable def covarianceInputs12634 :
    BstLean.Part263.CovarianceInputs 12634 scalarRow12634.grid parameters (caps repair12634) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12634 grid_top_bounds12634 repair12634

noncomputable def covarianceEvent12634 : Set (AgFam 12634) :=
  BstLean.Part263.covarianceEvent 12634 scalarRow12634.grid parameters

theorem covarianceEvent12634_measurable : MeasurableSet covarianceEvent12634 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12634_payment :
    (retDist (paperDesignP 12634).toCentres).real
      (agentEv (paperDesignP 12634) covarianceEvent12634)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12634

theorem localCov12634 : BstLean.Part259.LocalCovarianceOn covarianceEvent12634
    (BstLean.Part263.cell scalarRow12634.grid) (caps repair12634) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12634

theorem covarianceGood12634_payment :
    (retDist (paperDesignP 12634).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12634)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12634_payment



end BstLean.Part269.N12634

namespace BstLean.Part269.N12634
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12634}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12634.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12634) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12634).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12634 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12634) (by norm_num) BstLean.Part268.WorldRow12634.worldPackage rfl
    BstLean.Part268.WorldRow12634.product_lower (BstLean.Part268.WorldRow12634.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12634} (hw : c ∈ Hof BstLean.Part268.WorldRow12634.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12634) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12634) (by norm_num) BstLean.Part268.WorldRow12634.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12634} (hw : c ∈ Hof BstLean.Part268.WorldRow12634.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12634) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12634).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12634) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12634_eq : scalarRow12634.targetFrame = BstLean.Part268.agent12634.frame := by
  norm_num [scalarRow12634,BstLean.Part268.agent12634]

noncomputable def frameData12634 : BstLean.Part264b.FrameData 12634 :=
  BstLean.Part269.frameData_from_numerics (n := 12634) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12634.worldPackage rfl BstLean.Part268.WorldRow12634.product_lower (BstLean.Part268.WorldRow12634.producthi.2.trans (by norm_num))
    scalarRow12634 repair12634 covarianceInputs12634 (fun i hi => sourceNumerics12634 hi)
    BstLean.Part268.agent12634.frame targetFrame12634_eq


end BstLean.Part269.N12634
