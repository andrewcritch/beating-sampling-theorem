import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World9Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs9
import BstLean.Part269Rows9
import BstLean.Part269Sources9
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12590
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12590 : scalarRow12590.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12590, BstLean.Part268.grid12590, BstLean.Part263.worldGrid]

theorem supplies12590 (j : Fin 43) : Supply 12590 (parameters j)
    (cellLower scalarRow12590.grid (sourceIndex j))
    (cellUpper scalarRow12590.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12590.grid grid_top_bounds12590 j

theorem radii12590 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12590.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12590 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12590 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12590.grid grid_top_bounds12590 j hθ

noncomputable def covarianceInputs12590 :
    BstLean.Part263.CovarianceInputs 12590 scalarRow12590.grid parameters (caps repair12590) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12590 grid_top_bounds12590 repair12590

noncomputable def covarianceEvent12590 : Set (AgFam 12590) :=
  BstLean.Part263.covarianceEvent 12590 scalarRow12590.grid parameters

theorem covarianceEvent12590_measurable : MeasurableSet covarianceEvent12590 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12590_payment :
    (retDist (paperDesignP 12590).toCentres).real
      (agentEv (paperDesignP 12590) covarianceEvent12590)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12590

theorem localCov12590 : BstLean.Part259.LocalCovarianceOn covarianceEvent12590
    (BstLean.Part263.cell scalarRow12590.grid) (caps repair12590) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12590

theorem covarianceGood12590_payment :
    (retDist (paperDesignP 12590).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12590)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12590_payment



end BstLean.Part269.N12590

namespace BstLean.Part269.N12590
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12590}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12590.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12590) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12590).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12590 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12590) (by norm_num) BstLean.Part268.WorldRow12590.worldPackage rfl
    BstLean.Part268.WorldRow12590.product_lower (BstLean.Part268.WorldRow12590.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12590} (hw : c ∈ Hof BstLean.Part268.WorldRow12590.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12590) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12590) (by norm_num) BstLean.Part268.WorldRow12590.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12590} (hw : c ∈ Hof BstLean.Part268.WorldRow12590.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12590) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12590).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12590) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12590_eq : scalarRow12590.targetFrame = BstLean.Part268.agent12590.frame := by
  norm_num [scalarRow12590,BstLean.Part268.agent12590]

noncomputable def frameData12590 : BstLean.Part264b.FrameData 12590 :=
  BstLean.Part269.frameData_from_numerics (n := 12590) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12590.worldPackage rfl BstLean.Part268.WorldRow12590.product_lower (BstLean.Part268.WorldRow12590.producthi.2.trans (by norm_num))
    scalarRow12590 repair12590 covarianceInputs12590 (fun i hi => sourceNumerics12590 hi)
    BstLean.Part268.agent12590.frame targetFrame12590_eq


end BstLean.Part269.N12590

namespace BstLean.Part269.N12591
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12591 : scalarRow12591.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12591, BstLean.Part268.grid12591, BstLean.Part263.worldGrid]

theorem supplies12591 (j : Fin 43) : Supply 12591 (parameters j)
    (cellLower scalarRow12591.grid (sourceIndex j))
    (cellUpper scalarRow12591.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12591.grid grid_top_bounds12591 j

theorem radii12591 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12591.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12591 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12591 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12591.grid grid_top_bounds12591 j hθ

noncomputable def covarianceInputs12591 :
    BstLean.Part263.CovarianceInputs 12591 scalarRow12591.grid parameters (caps repair12591) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12591 grid_top_bounds12591 repair12591

noncomputable def covarianceEvent12591 : Set (AgFam 12591) :=
  BstLean.Part263.covarianceEvent 12591 scalarRow12591.grid parameters

theorem covarianceEvent12591_measurable : MeasurableSet covarianceEvent12591 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12591_payment :
    (retDist (paperDesignP 12591).toCentres).real
      (agentEv (paperDesignP 12591) covarianceEvent12591)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12591

theorem localCov12591 : BstLean.Part259.LocalCovarianceOn covarianceEvent12591
    (BstLean.Part263.cell scalarRow12591.grid) (caps repair12591) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12591

theorem covarianceGood12591_payment :
    (retDist (paperDesignP 12591).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12591)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12591_payment



end BstLean.Part269.N12591

namespace BstLean.Part269.N12591
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12591}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12591.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12591) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12591).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12591 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12591) (by norm_num) BstLean.Part268.WorldRow12591.worldPackage rfl
    BstLean.Part268.WorldRow12591.product_lower (BstLean.Part268.WorldRow12591.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12591} (hw : c ∈ Hof BstLean.Part268.WorldRow12591.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12591) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12591) (by norm_num) BstLean.Part268.WorldRow12591.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12591} (hw : c ∈ Hof BstLean.Part268.WorldRow12591.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12591) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12591).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12591) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12591_eq : scalarRow12591.targetFrame = BstLean.Part268.agent12591.frame := by
  norm_num [scalarRow12591,BstLean.Part268.agent12591]

noncomputable def frameData12591 : BstLean.Part264b.FrameData 12591 :=
  BstLean.Part269.frameData_from_numerics (n := 12591) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12591.worldPackage rfl BstLean.Part268.WorldRow12591.product_lower (BstLean.Part268.WorldRow12591.producthi.2.trans (by norm_num))
    scalarRow12591 repair12591 covarianceInputs12591 (fun i hi => sourceNumerics12591 hi)
    BstLean.Part268.agent12591.frame targetFrame12591_eq


end BstLean.Part269.N12591

namespace BstLean.Part269.N12592
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12592 : scalarRow12592.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12592, BstLean.Part268.grid12592, BstLean.Part263.worldGrid]

theorem supplies12592 (j : Fin 43) : Supply 12592 (parameters j)
    (cellLower scalarRow12592.grid (sourceIndex j))
    (cellUpper scalarRow12592.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12592.grid grid_top_bounds12592 j

theorem radii12592 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12592.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12592 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12592 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12592.grid grid_top_bounds12592 j hθ

noncomputable def covarianceInputs12592 :
    BstLean.Part263.CovarianceInputs 12592 scalarRow12592.grid parameters (caps repair12592) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12592 grid_top_bounds12592 repair12592

noncomputable def covarianceEvent12592 : Set (AgFam 12592) :=
  BstLean.Part263.covarianceEvent 12592 scalarRow12592.grid parameters

theorem covarianceEvent12592_measurable : MeasurableSet covarianceEvent12592 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12592_payment :
    (retDist (paperDesignP 12592).toCentres).real
      (agentEv (paperDesignP 12592) covarianceEvent12592)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12592

theorem localCov12592 : BstLean.Part259.LocalCovarianceOn covarianceEvent12592
    (BstLean.Part263.cell scalarRow12592.grid) (caps repair12592) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12592

theorem covarianceGood12592_payment :
    (retDist (paperDesignP 12592).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12592)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12592_payment



end BstLean.Part269.N12592

namespace BstLean.Part269.N12592
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12592}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12592.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12592) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12592).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12592 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12592) (by norm_num) BstLean.Part268.WorldRow12592.worldPackage rfl
    BstLean.Part268.WorldRow12592.product_lower (BstLean.Part268.WorldRow12592.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12592} (hw : c ∈ Hof BstLean.Part268.WorldRow12592.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12592) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12592) (by norm_num) BstLean.Part268.WorldRow12592.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12592} (hw : c ∈ Hof BstLean.Part268.WorldRow12592.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12592) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12592).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12592) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12592_eq : scalarRow12592.targetFrame = BstLean.Part268.agent12592.frame := by
  norm_num [scalarRow12592,BstLean.Part268.agent12592]

noncomputable def frameData12592 : BstLean.Part264b.FrameData 12592 :=
  BstLean.Part269.frameData_from_numerics (n := 12592) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12592.worldPackage rfl BstLean.Part268.WorldRow12592.product_lower (BstLean.Part268.WorldRow12592.producthi.2.trans (by norm_num))
    scalarRow12592 repair12592 covarianceInputs12592 (fun i hi => sourceNumerics12592 hi)
    BstLean.Part268.agent12592.frame targetFrame12592_eq


end BstLean.Part269.N12592

namespace BstLean.Part269.N12593
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12593 : scalarRow12593.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12593, BstLean.Part268.grid12593, BstLean.Part263.worldGrid]

theorem supplies12593 (j : Fin 43) : Supply 12593 (parameters j)
    (cellLower scalarRow12593.grid (sourceIndex j))
    (cellUpper scalarRow12593.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12593.grid grid_top_bounds12593 j

theorem radii12593 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12593.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12593 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12593 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12593.grid grid_top_bounds12593 j hθ

noncomputable def covarianceInputs12593 :
    BstLean.Part263.CovarianceInputs 12593 scalarRow12593.grid parameters (caps repair12593) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12593 grid_top_bounds12593 repair12593

noncomputable def covarianceEvent12593 : Set (AgFam 12593) :=
  BstLean.Part263.covarianceEvent 12593 scalarRow12593.grid parameters

theorem covarianceEvent12593_measurable : MeasurableSet covarianceEvent12593 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12593_payment :
    (retDist (paperDesignP 12593).toCentres).real
      (agentEv (paperDesignP 12593) covarianceEvent12593)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12593

theorem localCov12593 : BstLean.Part259.LocalCovarianceOn covarianceEvent12593
    (BstLean.Part263.cell scalarRow12593.grid) (caps repair12593) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12593

theorem covarianceGood12593_payment :
    (retDist (paperDesignP 12593).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12593)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12593_payment



end BstLean.Part269.N12593

namespace BstLean.Part269.N12593
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12593}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12593.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12593) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12593).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12593 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12593) (by norm_num) BstLean.Part268.WorldRow12593.worldPackage rfl
    BstLean.Part268.WorldRow12593.product_lower (BstLean.Part268.WorldRow12593.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12593} (hw : c ∈ Hof BstLean.Part268.WorldRow12593.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12593) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12593) (by norm_num) BstLean.Part268.WorldRow12593.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12593} (hw : c ∈ Hof BstLean.Part268.WorldRow12593.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12593) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12593).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12593) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12593_eq : scalarRow12593.targetFrame = BstLean.Part268.agent12593.frame := by
  norm_num [scalarRow12593,BstLean.Part268.agent12593]

noncomputable def frameData12593 : BstLean.Part264b.FrameData 12593 :=
  BstLean.Part269.frameData_from_numerics (n := 12593) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12593.worldPackage rfl BstLean.Part268.WorldRow12593.product_lower (BstLean.Part268.WorldRow12593.producthi.2.trans (by norm_num))
    scalarRow12593 repair12593 covarianceInputs12593 (fun i hi => sourceNumerics12593 hi)
    BstLean.Part268.agent12593.frame targetFrame12593_eq


end BstLean.Part269.N12593

namespace BstLean.Part269.N12594
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12594 : scalarRow12594.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12594, BstLean.Part268.grid12594, BstLean.Part263.worldGrid]

theorem supplies12594 (j : Fin 43) : Supply 12594 (parameters j)
    (cellLower scalarRow12594.grid (sourceIndex j))
    (cellUpper scalarRow12594.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12594.grid grid_top_bounds12594 j

theorem radii12594 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12594.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12594 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12594 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12594.grid grid_top_bounds12594 j hθ

noncomputable def covarianceInputs12594 :
    BstLean.Part263.CovarianceInputs 12594 scalarRow12594.grid parameters (caps repair12594) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12594 grid_top_bounds12594 repair12594

noncomputable def covarianceEvent12594 : Set (AgFam 12594) :=
  BstLean.Part263.covarianceEvent 12594 scalarRow12594.grid parameters

theorem covarianceEvent12594_measurable : MeasurableSet covarianceEvent12594 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12594_payment :
    (retDist (paperDesignP 12594).toCentres).real
      (agentEv (paperDesignP 12594) covarianceEvent12594)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12594

theorem localCov12594 : BstLean.Part259.LocalCovarianceOn covarianceEvent12594
    (BstLean.Part263.cell scalarRow12594.grid) (caps repair12594) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12594

theorem covarianceGood12594_payment :
    (retDist (paperDesignP 12594).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12594)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12594_payment



end BstLean.Part269.N12594

namespace BstLean.Part269.N12594
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12594}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12594.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12594) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12594).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12594 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12594) (by norm_num) BstLean.Part268.WorldRow12594.worldPackage rfl
    BstLean.Part268.WorldRow12594.product_lower (BstLean.Part268.WorldRow12594.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12594} (hw : c ∈ Hof BstLean.Part268.WorldRow12594.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12594) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12594) (by norm_num) BstLean.Part268.WorldRow12594.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12594} (hw : c ∈ Hof BstLean.Part268.WorldRow12594.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12594) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12594).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12594) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12594_eq : scalarRow12594.targetFrame = BstLean.Part268.agent12594.frame := by
  norm_num [scalarRow12594,BstLean.Part268.agent12594]

noncomputable def frameData12594 : BstLean.Part264b.FrameData 12594 :=
  BstLean.Part269.frameData_from_numerics (n := 12594) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12594.worldPackage rfl BstLean.Part268.WorldRow12594.product_lower (BstLean.Part268.WorldRow12594.producthi.2.trans (by norm_num))
    scalarRow12594 repair12594 covarianceInputs12594 (fun i hi => sourceNumerics12594 hi)
    BstLean.Part268.agent12594.frame targetFrame12594_eq


end BstLean.Part269.N12594
