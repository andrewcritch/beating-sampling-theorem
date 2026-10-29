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

namespace BstLean.Part269.N12755
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12755 : scalarRow12755.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12755, BstLean.Part268.grid12755, BstLean.Part263.worldGrid]

theorem supplies12755 (j : Fin 43) : Supply 12755 (parameters j)
    (cellLower scalarRow12755.grid (sourceIndex j))
    (cellUpper scalarRow12755.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12755.grid grid_top_bounds12755 j

theorem radii12755 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12755.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12755 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12755 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12755.grid grid_top_bounds12755 j hθ

noncomputable def covarianceInputs12755 :
    BstLean.Part263.CovarianceInputs 12755 scalarRow12755.grid parameters (caps repair12755) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12755 grid_top_bounds12755 repair12755

noncomputable def covarianceEvent12755 : Set (AgFam 12755) :=
  BstLean.Part263.covarianceEvent 12755 scalarRow12755.grid parameters

theorem covarianceEvent12755_measurable : MeasurableSet covarianceEvent12755 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12755_payment :
    (retDist (paperDesignP 12755).toCentres).real
      (agentEv (paperDesignP 12755) covarianceEvent12755)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12755

theorem localCov12755 : BstLean.Part259.LocalCovarianceOn covarianceEvent12755
    (BstLean.Part263.cell scalarRow12755.grid) (caps repair12755) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12755

theorem covarianceGood12755_payment :
    (retDist (paperDesignP 12755).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12755)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12755_payment



end BstLean.Part269.N12755

namespace BstLean.Part269.N12755
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12755}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12755.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12755) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12755).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12755 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12755) (by norm_num) BstLean.Part268.WorldRow12755.worldPackage rfl
    BstLean.Part268.WorldRow12755.product_lower (BstLean.Part268.WorldRow12755.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12755} (hw : c ∈ Hof BstLean.Part268.WorldRow12755.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12755) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12755) (by norm_num) BstLean.Part268.WorldRow12755.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12755} (hw : c ∈ Hof BstLean.Part268.WorldRow12755.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12755) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12755).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12755) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12755_eq : scalarRow12755.targetFrame = BstLean.Part268.agent12755.frame := by
  norm_num [scalarRow12755,BstLean.Part268.agent12755]

noncomputable def frameData12755 : BstLean.Part264b.FrameData 12755 :=
  BstLean.Part269.frameData_from_numerics (n := 12755) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12755.worldPackage rfl BstLean.Part268.WorldRow12755.product_lower (BstLean.Part268.WorldRow12755.producthi.2.trans (by norm_num))
    scalarRow12755 repair12755 covarianceInputs12755 (fun i hi => sourceNumerics12755 hi)
    BstLean.Part268.agent12755.frame targetFrame12755_eq


end BstLean.Part269.N12755

namespace BstLean.Part269.N12756
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12756 : scalarRow12756.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12756, BstLean.Part268.grid12756, BstLean.Part263.worldGrid]

theorem supplies12756 (j : Fin 43) : Supply 12756 (parameters j)
    (cellLower scalarRow12756.grid (sourceIndex j))
    (cellUpper scalarRow12756.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12756.grid grid_top_bounds12756 j

theorem radii12756 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12756.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12756 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12756 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12756.grid grid_top_bounds12756 j hθ

noncomputable def covarianceInputs12756 :
    BstLean.Part263.CovarianceInputs 12756 scalarRow12756.grid parameters (caps repair12756) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12756 grid_top_bounds12756 repair12756

noncomputable def covarianceEvent12756 : Set (AgFam 12756) :=
  BstLean.Part263.covarianceEvent 12756 scalarRow12756.grid parameters

theorem covarianceEvent12756_measurable : MeasurableSet covarianceEvent12756 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12756_payment :
    (retDist (paperDesignP 12756).toCentres).real
      (agentEv (paperDesignP 12756) covarianceEvent12756)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12756

theorem localCov12756 : BstLean.Part259.LocalCovarianceOn covarianceEvent12756
    (BstLean.Part263.cell scalarRow12756.grid) (caps repair12756) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12756

theorem covarianceGood12756_payment :
    (retDist (paperDesignP 12756).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12756)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12756_payment



end BstLean.Part269.N12756

namespace BstLean.Part269.N12756
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12756}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12756.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12756) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12756).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12756 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12756) (by norm_num) BstLean.Part268.WorldRow12756.worldPackage rfl
    BstLean.Part268.WorldRow12756.product_lower (BstLean.Part268.WorldRow12756.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12756} (hw : c ∈ Hof BstLean.Part268.WorldRow12756.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12756) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12756) (by norm_num) BstLean.Part268.WorldRow12756.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12756} (hw : c ∈ Hof BstLean.Part268.WorldRow12756.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12756) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12756).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12756) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12756_eq : scalarRow12756.targetFrame = BstLean.Part268.agent12756.frame := by
  norm_num [scalarRow12756,BstLean.Part268.agent12756]

noncomputable def frameData12756 : BstLean.Part264b.FrameData 12756 :=
  BstLean.Part269.frameData_from_numerics (n := 12756) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12756.worldPackage rfl BstLean.Part268.WorldRow12756.product_lower (BstLean.Part268.WorldRow12756.producthi.2.trans (by norm_num))
    scalarRow12756 repair12756 covarianceInputs12756 (fun i hi => sourceNumerics12756 hi)
    BstLean.Part268.agent12756.frame targetFrame12756_eq


end BstLean.Part269.N12756

namespace BstLean.Part269.N12757
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12757 : scalarRow12757.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12757, BstLean.Part268.grid12757, BstLean.Part263.worldGrid]

theorem supplies12757 (j : Fin 43) : Supply 12757 (parameters j)
    (cellLower scalarRow12757.grid (sourceIndex j))
    (cellUpper scalarRow12757.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12757.grid grid_top_bounds12757 j

theorem radii12757 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12757.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12757 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12757 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12757.grid grid_top_bounds12757 j hθ

noncomputable def covarianceInputs12757 :
    BstLean.Part263.CovarianceInputs 12757 scalarRow12757.grid parameters (caps repair12757) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12757 grid_top_bounds12757 repair12757

noncomputable def covarianceEvent12757 : Set (AgFam 12757) :=
  BstLean.Part263.covarianceEvent 12757 scalarRow12757.grid parameters

theorem covarianceEvent12757_measurable : MeasurableSet covarianceEvent12757 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12757_payment :
    (retDist (paperDesignP 12757).toCentres).real
      (agentEv (paperDesignP 12757) covarianceEvent12757)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12757

theorem localCov12757 : BstLean.Part259.LocalCovarianceOn covarianceEvent12757
    (BstLean.Part263.cell scalarRow12757.grid) (caps repair12757) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12757

theorem covarianceGood12757_payment :
    (retDist (paperDesignP 12757).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12757)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12757_payment



end BstLean.Part269.N12757

namespace BstLean.Part269.N12757
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12757}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12757.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12757) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12757).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12757 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12757) (by norm_num) BstLean.Part268.WorldRow12757.worldPackage rfl
    BstLean.Part268.WorldRow12757.product_lower (BstLean.Part268.WorldRow12757.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12757} (hw : c ∈ Hof BstLean.Part268.WorldRow12757.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12757) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12757) (by norm_num) BstLean.Part268.WorldRow12757.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12757} (hw : c ∈ Hof BstLean.Part268.WorldRow12757.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12757) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12757).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12757) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12757_eq : scalarRow12757.targetFrame = BstLean.Part268.agent12757.frame := by
  norm_num [scalarRow12757,BstLean.Part268.agent12757]

noncomputable def frameData12757 : BstLean.Part264b.FrameData 12757 :=
  BstLean.Part269.frameData_from_numerics (n := 12757) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12757.worldPackage rfl BstLean.Part268.WorldRow12757.product_lower (BstLean.Part268.WorldRow12757.producthi.2.trans (by norm_num))
    scalarRow12757 repair12757 covarianceInputs12757 (fun i hi => sourceNumerics12757 hi)
    BstLean.Part268.agent12757.frame targetFrame12757_eq


end BstLean.Part269.N12757

namespace BstLean.Part269.N12758
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12758 : scalarRow12758.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12758, BstLean.Part268.grid12758, BstLean.Part263.worldGrid]

theorem supplies12758 (j : Fin 43) : Supply 12758 (parameters j)
    (cellLower scalarRow12758.grid (sourceIndex j))
    (cellUpper scalarRow12758.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12758.grid grid_top_bounds12758 j

theorem radii12758 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12758.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12758 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12758 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12758.grid grid_top_bounds12758 j hθ

noncomputable def covarianceInputs12758 :
    BstLean.Part263.CovarianceInputs 12758 scalarRow12758.grid parameters (caps repair12758) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12758 grid_top_bounds12758 repair12758

noncomputable def covarianceEvent12758 : Set (AgFam 12758) :=
  BstLean.Part263.covarianceEvent 12758 scalarRow12758.grid parameters

theorem covarianceEvent12758_measurable : MeasurableSet covarianceEvent12758 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12758_payment :
    (retDist (paperDesignP 12758).toCentres).real
      (agentEv (paperDesignP 12758) covarianceEvent12758)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12758

theorem localCov12758 : BstLean.Part259.LocalCovarianceOn covarianceEvent12758
    (BstLean.Part263.cell scalarRow12758.grid) (caps repair12758) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12758

theorem covarianceGood12758_payment :
    (retDist (paperDesignP 12758).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12758)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12758_payment



end BstLean.Part269.N12758

namespace BstLean.Part269.N12758
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12758}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12758.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12758) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12758).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12758 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12758) (by norm_num) BstLean.Part268.WorldRow12758.worldPackage rfl
    BstLean.Part268.WorldRow12758.product_lower (BstLean.Part268.WorldRow12758.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12758} (hw : c ∈ Hof BstLean.Part268.WorldRow12758.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12758) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12758) (by norm_num) BstLean.Part268.WorldRow12758.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12758} (hw : c ∈ Hof BstLean.Part268.WorldRow12758.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12758) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12758).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12758) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12758_eq : scalarRow12758.targetFrame = BstLean.Part268.agent12758.frame := by
  norm_num [scalarRow12758,BstLean.Part268.agent12758]

noncomputable def frameData12758 : BstLean.Part264b.FrameData 12758 :=
  BstLean.Part269.frameData_from_numerics (n := 12758) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12758.worldPackage rfl BstLean.Part268.WorldRow12758.product_lower (BstLean.Part268.WorldRow12758.producthi.2.trans (by norm_num))
    scalarRow12758 repair12758 covarianceInputs12758 (fun i hi => sourceNumerics12758 hi)
    BstLean.Part268.agent12758.frame targetFrame12758_eq


end BstLean.Part269.N12758

namespace BstLean.Part269.N12759
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12759 : scalarRow12759.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12759, BstLean.Part268.grid12759, BstLean.Part263.worldGrid]

theorem supplies12759 (j : Fin 43) : Supply 12759 (parameters j)
    (cellLower scalarRow12759.grid (sourceIndex j))
    (cellUpper scalarRow12759.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12759.grid grid_top_bounds12759 j

theorem radii12759 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12759.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12759 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12759 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12759.grid grid_top_bounds12759 j hθ

noncomputable def covarianceInputs12759 :
    BstLean.Part263.CovarianceInputs 12759 scalarRow12759.grid parameters (caps repair12759) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12759 grid_top_bounds12759 repair12759

noncomputable def covarianceEvent12759 : Set (AgFam 12759) :=
  BstLean.Part263.covarianceEvent 12759 scalarRow12759.grid parameters

theorem covarianceEvent12759_measurable : MeasurableSet covarianceEvent12759 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12759_payment :
    (retDist (paperDesignP 12759).toCentres).real
      (agentEv (paperDesignP 12759) covarianceEvent12759)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12759

theorem localCov12759 : BstLean.Part259.LocalCovarianceOn covarianceEvent12759
    (BstLean.Part263.cell scalarRow12759.grid) (caps repair12759) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12759

theorem covarianceGood12759_payment :
    (retDist (paperDesignP 12759).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12759)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12759_payment



end BstLean.Part269.N12759

namespace BstLean.Part269.N12759
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12759}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12759.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12759) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12759).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12759 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12759) (by norm_num) BstLean.Part268.WorldRow12759.worldPackage rfl
    BstLean.Part268.WorldRow12759.product_lower (BstLean.Part268.WorldRow12759.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12759} (hw : c ∈ Hof BstLean.Part268.WorldRow12759.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12759) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12759) (by norm_num) BstLean.Part268.WorldRow12759.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12759} (hw : c ∈ Hof BstLean.Part268.WorldRow12759.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12759) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12759).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12759) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12759_eq : scalarRow12759.targetFrame = BstLean.Part268.agent12759.frame := by
  norm_num [scalarRow12759,BstLean.Part268.agent12759]

noncomputable def frameData12759 : BstLean.Part264b.FrameData 12759 :=
  BstLean.Part269.frameData_from_numerics (n := 12759) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12759.worldPackage rfl BstLean.Part268.WorldRow12759.product_lower (BstLean.Part268.WorldRow12759.producthi.2.trans (by norm_num))
    scalarRow12759 repair12759 covarianceInputs12759 (fun i hi => sourceNumerics12759 hi)
    BstLean.Part268.agent12759.frame targetFrame12759_eq


end BstLean.Part269.N12759
