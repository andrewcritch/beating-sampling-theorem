import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World10Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs10
import BstLean.Part269Rows10
import BstLean.Part269Sources10
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12620
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12620 : scalarRow12620.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12620, BstLean.Part268.grid12620, BstLean.Part263.worldGrid]

theorem supplies12620 (j : Fin 43) : Supply 12620 (parameters j)
    (cellLower scalarRow12620.grid (sourceIndex j))
    (cellUpper scalarRow12620.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12620.grid grid_top_bounds12620 j

theorem radii12620 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12620.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12620 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12620 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12620.grid grid_top_bounds12620 j hθ

noncomputable def covarianceInputs12620 :
    BstLean.Part263.CovarianceInputs 12620 scalarRow12620.grid parameters (caps repair12620) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12620 grid_top_bounds12620 repair12620

noncomputable def covarianceEvent12620 : Set (AgFam 12620) :=
  BstLean.Part263.covarianceEvent 12620 scalarRow12620.grid parameters

theorem covarianceEvent12620_measurable : MeasurableSet covarianceEvent12620 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12620_payment :
    (retDist (paperDesignP 12620).toCentres).real
      (agentEv (paperDesignP 12620) covarianceEvent12620)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12620

theorem localCov12620 : BstLean.Part259.LocalCovarianceOn covarianceEvent12620
    (BstLean.Part263.cell scalarRow12620.grid) (caps repair12620) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12620

theorem covarianceGood12620_payment :
    (retDist (paperDesignP 12620).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12620)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12620_payment



end BstLean.Part269.N12620

namespace BstLean.Part269.N12620
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12620}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12620.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12620) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12620).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12620 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12620) (by norm_num) BstLean.Part268.WorldRow12620.worldPackage rfl
    BstLean.Part268.WorldRow12620.product_lower (BstLean.Part268.WorldRow12620.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12620} (hw : c ∈ Hof BstLean.Part268.WorldRow12620.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12620) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12620) (by norm_num) BstLean.Part268.WorldRow12620.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12620} (hw : c ∈ Hof BstLean.Part268.WorldRow12620.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12620) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12620).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12620) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12620_eq : scalarRow12620.targetFrame = BstLean.Part268.agent12620.frame := by
  norm_num [scalarRow12620,BstLean.Part268.agent12620]

noncomputable def frameData12620 : BstLean.Part264b.FrameData 12620 :=
  BstLean.Part269.frameData_from_numerics (n := 12620) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12620.worldPackage rfl BstLean.Part268.WorldRow12620.product_lower (BstLean.Part268.WorldRow12620.producthi.2.trans (by norm_num))
    scalarRow12620 repair12620 covarianceInputs12620 (fun i hi => sourceNumerics12620 hi)
    BstLean.Part268.agent12620.frame targetFrame12620_eq


end BstLean.Part269.N12620

namespace BstLean.Part269.N12621
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12621 : scalarRow12621.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12621, BstLean.Part268.grid12621, BstLean.Part263.worldGrid]

theorem supplies12621 (j : Fin 43) : Supply 12621 (parameters j)
    (cellLower scalarRow12621.grid (sourceIndex j))
    (cellUpper scalarRow12621.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12621.grid grid_top_bounds12621 j

theorem radii12621 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12621.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12621 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12621 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12621.grid grid_top_bounds12621 j hθ

noncomputable def covarianceInputs12621 :
    BstLean.Part263.CovarianceInputs 12621 scalarRow12621.grid parameters (caps repair12621) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12621 grid_top_bounds12621 repair12621

noncomputable def covarianceEvent12621 : Set (AgFam 12621) :=
  BstLean.Part263.covarianceEvent 12621 scalarRow12621.grid parameters

theorem covarianceEvent12621_measurable : MeasurableSet covarianceEvent12621 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12621_payment :
    (retDist (paperDesignP 12621).toCentres).real
      (agentEv (paperDesignP 12621) covarianceEvent12621)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12621

theorem localCov12621 : BstLean.Part259.LocalCovarianceOn covarianceEvent12621
    (BstLean.Part263.cell scalarRow12621.grid) (caps repair12621) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12621

theorem covarianceGood12621_payment :
    (retDist (paperDesignP 12621).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12621)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12621_payment



end BstLean.Part269.N12621

namespace BstLean.Part269.N12621
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12621}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12621.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12621) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12621).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12621 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12621) (by norm_num) BstLean.Part268.WorldRow12621.worldPackage rfl
    BstLean.Part268.WorldRow12621.product_lower (BstLean.Part268.WorldRow12621.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12621} (hw : c ∈ Hof BstLean.Part268.WorldRow12621.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12621) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12621) (by norm_num) BstLean.Part268.WorldRow12621.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12621} (hw : c ∈ Hof BstLean.Part268.WorldRow12621.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12621) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12621).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12621) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12621_eq : scalarRow12621.targetFrame = BstLean.Part268.agent12621.frame := by
  norm_num [scalarRow12621,BstLean.Part268.agent12621]

noncomputable def frameData12621 : BstLean.Part264b.FrameData 12621 :=
  BstLean.Part269.frameData_from_numerics (n := 12621) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12621.worldPackage rfl BstLean.Part268.WorldRow12621.product_lower (BstLean.Part268.WorldRow12621.producthi.2.trans (by norm_num))
    scalarRow12621 repair12621 covarianceInputs12621 (fun i hi => sourceNumerics12621 hi)
    BstLean.Part268.agent12621.frame targetFrame12621_eq


end BstLean.Part269.N12621

namespace BstLean.Part269.N12622
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12622 : scalarRow12622.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12622, BstLean.Part268.grid12622, BstLean.Part263.worldGrid]

theorem supplies12622 (j : Fin 43) : Supply 12622 (parameters j)
    (cellLower scalarRow12622.grid (sourceIndex j))
    (cellUpper scalarRow12622.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12622.grid grid_top_bounds12622 j

theorem radii12622 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12622.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12622 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12622 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12622.grid grid_top_bounds12622 j hθ

noncomputable def covarianceInputs12622 :
    BstLean.Part263.CovarianceInputs 12622 scalarRow12622.grid parameters (caps repair12622) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12622 grid_top_bounds12622 repair12622

noncomputable def covarianceEvent12622 : Set (AgFam 12622) :=
  BstLean.Part263.covarianceEvent 12622 scalarRow12622.grid parameters

theorem covarianceEvent12622_measurable : MeasurableSet covarianceEvent12622 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12622_payment :
    (retDist (paperDesignP 12622).toCentres).real
      (agentEv (paperDesignP 12622) covarianceEvent12622)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12622

theorem localCov12622 : BstLean.Part259.LocalCovarianceOn covarianceEvent12622
    (BstLean.Part263.cell scalarRow12622.grid) (caps repair12622) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12622

theorem covarianceGood12622_payment :
    (retDist (paperDesignP 12622).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12622)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12622_payment



end BstLean.Part269.N12622

namespace BstLean.Part269.N12622
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12622}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12622.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12622) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12622).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12622 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12622) (by norm_num) BstLean.Part268.WorldRow12622.worldPackage rfl
    BstLean.Part268.WorldRow12622.product_lower (BstLean.Part268.WorldRow12622.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12622} (hw : c ∈ Hof BstLean.Part268.WorldRow12622.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12622) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12622) (by norm_num) BstLean.Part268.WorldRow12622.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12622} (hw : c ∈ Hof BstLean.Part268.WorldRow12622.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12622) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12622).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12622) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12622_eq : scalarRow12622.targetFrame = BstLean.Part268.agent12622.frame := by
  norm_num [scalarRow12622,BstLean.Part268.agent12622]

noncomputable def frameData12622 : BstLean.Part264b.FrameData 12622 :=
  BstLean.Part269.frameData_from_numerics (n := 12622) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12622.worldPackage rfl BstLean.Part268.WorldRow12622.product_lower (BstLean.Part268.WorldRow12622.producthi.2.trans (by norm_num))
    scalarRow12622 repair12622 covarianceInputs12622 (fun i hi => sourceNumerics12622 hi)
    BstLean.Part268.agent12622.frame targetFrame12622_eq


end BstLean.Part269.N12622

namespace BstLean.Part269.N12623
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12623 : scalarRow12623.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12623, BstLean.Part268.grid12623, BstLean.Part263.worldGrid]

theorem supplies12623 (j : Fin 43) : Supply 12623 (parameters j)
    (cellLower scalarRow12623.grid (sourceIndex j))
    (cellUpper scalarRow12623.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12623.grid grid_top_bounds12623 j

theorem radii12623 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12623.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12623 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12623 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12623.grid grid_top_bounds12623 j hθ

noncomputable def covarianceInputs12623 :
    BstLean.Part263.CovarianceInputs 12623 scalarRow12623.grid parameters (caps repair12623) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12623 grid_top_bounds12623 repair12623

noncomputable def covarianceEvent12623 : Set (AgFam 12623) :=
  BstLean.Part263.covarianceEvent 12623 scalarRow12623.grid parameters

theorem covarianceEvent12623_measurable : MeasurableSet covarianceEvent12623 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12623_payment :
    (retDist (paperDesignP 12623).toCentres).real
      (agentEv (paperDesignP 12623) covarianceEvent12623)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12623

theorem localCov12623 : BstLean.Part259.LocalCovarianceOn covarianceEvent12623
    (BstLean.Part263.cell scalarRow12623.grid) (caps repair12623) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12623

theorem covarianceGood12623_payment :
    (retDist (paperDesignP 12623).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12623)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12623_payment



end BstLean.Part269.N12623

namespace BstLean.Part269.N12623
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12623}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12623.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12623) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12623).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12623 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12623) (by norm_num) BstLean.Part268.WorldRow12623.worldPackage rfl
    BstLean.Part268.WorldRow12623.product_lower (BstLean.Part268.WorldRow12623.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12623} (hw : c ∈ Hof BstLean.Part268.WorldRow12623.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12623) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12623) (by norm_num) BstLean.Part268.WorldRow12623.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12623} (hw : c ∈ Hof BstLean.Part268.WorldRow12623.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12623) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12623).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12623) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12623_eq : scalarRow12623.targetFrame = BstLean.Part268.agent12623.frame := by
  norm_num [scalarRow12623,BstLean.Part268.agent12623]

noncomputable def frameData12623 : BstLean.Part264b.FrameData 12623 :=
  BstLean.Part269.frameData_from_numerics (n := 12623) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12623.worldPackage rfl BstLean.Part268.WorldRow12623.product_lower (BstLean.Part268.WorldRow12623.producthi.2.trans (by norm_num))
    scalarRow12623 repair12623 covarianceInputs12623 (fun i hi => sourceNumerics12623 hi)
    BstLean.Part268.agent12623.frame targetFrame12623_eq


end BstLean.Part269.N12623

namespace BstLean.Part269.N12624
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12624 : scalarRow12624.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12624, BstLean.Part268.grid12624, BstLean.Part263.worldGrid]

theorem supplies12624 (j : Fin 43) : Supply 12624 (parameters j)
    (cellLower scalarRow12624.grid (sourceIndex j))
    (cellUpper scalarRow12624.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12624.grid grid_top_bounds12624 j

theorem radii12624 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12624.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12624 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12624 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12624.grid grid_top_bounds12624 j hθ

noncomputable def covarianceInputs12624 :
    BstLean.Part263.CovarianceInputs 12624 scalarRow12624.grid parameters (caps repair12624) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12624 grid_top_bounds12624 repair12624

noncomputable def covarianceEvent12624 : Set (AgFam 12624) :=
  BstLean.Part263.covarianceEvent 12624 scalarRow12624.grid parameters

theorem covarianceEvent12624_measurable : MeasurableSet covarianceEvent12624 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12624_payment :
    (retDist (paperDesignP 12624).toCentres).real
      (agentEv (paperDesignP 12624) covarianceEvent12624)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12624

theorem localCov12624 : BstLean.Part259.LocalCovarianceOn covarianceEvent12624
    (BstLean.Part263.cell scalarRow12624.grid) (caps repair12624) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12624

theorem covarianceGood12624_payment :
    (retDist (paperDesignP 12624).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12624)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12624_payment



end BstLean.Part269.N12624

namespace BstLean.Part269.N12624
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12624}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12624.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12624) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12624).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12624 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12624) (by norm_num) BstLean.Part268.WorldRow12624.worldPackage rfl
    BstLean.Part268.WorldRow12624.product_lower (BstLean.Part268.WorldRow12624.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12624} (hw : c ∈ Hof BstLean.Part268.WorldRow12624.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12624) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12624) (by norm_num) BstLean.Part268.WorldRow12624.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12624} (hw : c ∈ Hof BstLean.Part268.WorldRow12624.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12624) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12624).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12624) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12624_eq : scalarRow12624.targetFrame = BstLean.Part268.agent12624.frame := by
  norm_num [scalarRow12624,BstLean.Part268.agent12624]

noncomputable def frameData12624 : BstLean.Part264b.FrameData 12624 :=
  BstLean.Part269.frameData_from_numerics (n := 12624) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12624.worldPackage rfl BstLean.Part268.WorldRow12624.product_lower (BstLean.Part268.WorldRow12624.producthi.2.trans (by norm_num))
    scalarRow12624 repair12624 covarianceInputs12624 (fun i hi => sourceNumerics12624 hi)
    BstLean.Part268.agent12624.frame targetFrame12624_eq


end BstLean.Part269.N12624
