import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World12Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs12
import BstLean.Part269Rows12
import BstLean.Part269Sources12
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12655
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12655 : scalarRow12655.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12655, BstLean.Part268.grid12655, BstLean.Part263.worldGrid]

theorem supplies12655 (j : Fin 43) : Supply 12655 (parameters j)
    (cellLower scalarRow12655.grid (sourceIndex j))
    (cellUpper scalarRow12655.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12655.grid grid_top_bounds12655 j

theorem radii12655 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12655.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12655 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12655 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12655.grid grid_top_bounds12655 j hθ

noncomputable def covarianceInputs12655 :
    BstLean.Part263.CovarianceInputs 12655 scalarRow12655.grid parameters (caps repair12655) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12655 grid_top_bounds12655 repair12655

noncomputable def covarianceEvent12655 : Set (AgFam 12655) :=
  BstLean.Part263.covarianceEvent 12655 scalarRow12655.grid parameters

theorem covarianceEvent12655_measurable : MeasurableSet covarianceEvent12655 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12655_payment :
    (retDist (paperDesignP 12655).toCentres).real
      (agentEv (paperDesignP 12655) covarianceEvent12655)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12655

theorem localCov12655 : BstLean.Part259.LocalCovarianceOn covarianceEvent12655
    (BstLean.Part263.cell scalarRow12655.grid) (caps repair12655) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12655

theorem covarianceGood12655_payment :
    (retDist (paperDesignP 12655).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12655)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12655_payment



end BstLean.Part269.N12655

namespace BstLean.Part269.N12655
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12655}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12655.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12655) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12655).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12655 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12655) (by norm_num) BstLean.Part268.WorldRow12655.worldPackage rfl
    BstLean.Part268.WorldRow12655.product_lower (BstLean.Part268.WorldRow12655.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12655} (hw : c ∈ Hof BstLean.Part268.WorldRow12655.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12655) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12655) (by norm_num) BstLean.Part268.WorldRow12655.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12655} (hw : c ∈ Hof BstLean.Part268.WorldRow12655.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12655) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12655).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12655) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12655_eq : scalarRow12655.targetFrame = BstLean.Part268.agent12655.frame := by
  norm_num [scalarRow12655,BstLean.Part268.agent12655]

noncomputable def frameData12655 : BstLean.Part264b.FrameData 12655 :=
  BstLean.Part269.frameData_from_numerics (n := 12655) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12655.worldPackage rfl BstLean.Part268.WorldRow12655.product_lower (BstLean.Part268.WorldRow12655.producthi.2.trans (by norm_num))
    scalarRow12655 repair12655 covarianceInputs12655 (fun i hi => sourceNumerics12655 hi)
    BstLean.Part268.agent12655.frame targetFrame12655_eq


end BstLean.Part269.N12655

namespace BstLean.Part269.N12656
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12656 : scalarRow12656.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12656, BstLean.Part268.grid12656, BstLean.Part263.worldGrid]

theorem supplies12656 (j : Fin 43) : Supply 12656 (parameters j)
    (cellLower scalarRow12656.grid (sourceIndex j))
    (cellUpper scalarRow12656.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12656.grid grid_top_bounds12656 j

theorem radii12656 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12656.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12656 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12656 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12656.grid grid_top_bounds12656 j hθ

noncomputable def covarianceInputs12656 :
    BstLean.Part263.CovarianceInputs 12656 scalarRow12656.grid parameters (caps repair12656) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12656 grid_top_bounds12656 repair12656

noncomputable def covarianceEvent12656 : Set (AgFam 12656) :=
  BstLean.Part263.covarianceEvent 12656 scalarRow12656.grid parameters

theorem covarianceEvent12656_measurable : MeasurableSet covarianceEvent12656 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12656_payment :
    (retDist (paperDesignP 12656).toCentres).real
      (agentEv (paperDesignP 12656) covarianceEvent12656)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12656

theorem localCov12656 : BstLean.Part259.LocalCovarianceOn covarianceEvent12656
    (BstLean.Part263.cell scalarRow12656.grid) (caps repair12656) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12656

theorem covarianceGood12656_payment :
    (retDist (paperDesignP 12656).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12656)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12656_payment



end BstLean.Part269.N12656

namespace BstLean.Part269.N12656
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12656}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12656.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12656) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12656).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12656 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12656) (by norm_num) BstLean.Part268.WorldRow12656.worldPackage rfl
    BstLean.Part268.WorldRow12656.product_lower (BstLean.Part268.WorldRow12656.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12656} (hw : c ∈ Hof BstLean.Part268.WorldRow12656.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12656) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12656) (by norm_num) BstLean.Part268.WorldRow12656.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12656} (hw : c ∈ Hof BstLean.Part268.WorldRow12656.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12656) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12656).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12656) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12656_eq : scalarRow12656.targetFrame = BstLean.Part268.agent12656.frame := by
  norm_num [scalarRow12656,BstLean.Part268.agent12656]

noncomputable def frameData12656 : BstLean.Part264b.FrameData 12656 :=
  BstLean.Part269.frameData_from_numerics (n := 12656) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12656.worldPackage rfl BstLean.Part268.WorldRow12656.product_lower (BstLean.Part268.WorldRow12656.producthi.2.trans (by norm_num))
    scalarRow12656 repair12656 covarianceInputs12656 (fun i hi => sourceNumerics12656 hi)
    BstLean.Part268.agent12656.frame targetFrame12656_eq


end BstLean.Part269.N12656

namespace BstLean.Part269.N12657
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12657 : scalarRow12657.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12657, BstLean.Part268.grid12657, BstLean.Part263.worldGrid]

theorem supplies12657 (j : Fin 43) : Supply 12657 (parameters j)
    (cellLower scalarRow12657.grid (sourceIndex j))
    (cellUpper scalarRow12657.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12657.grid grid_top_bounds12657 j

theorem radii12657 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12657.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12657 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12657 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12657.grid grid_top_bounds12657 j hθ

noncomputable def covarianceInputs12657 :
    BstLean.Part263.CovarianceInputs 12657 scalarRow12657.grid parameters (caps repair12657) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12657 grid_top_bounds12657 repair12657

noncomputable def covarianceEvent12657 : Set (AgFam 12657) :=
  BstLean.Part263.covarianceEvent 12657 scalarRow12657.grid parameters

theorem covarianceEvent12657_measurable : MeasurableSet covarianceEvent12657 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12657_payment :
    (retDist (paperDesignP 12657).toCentres).real
      (agentEv (paperDesignP 12657) covarianceEvent12657)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12657

theorem localCov12657 : BstLean.Part259.LocalCovarianceOn covarianceEvent12657
    (BstLean.Part263.cell scalarRow12657.grid) (caps repair12657) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12657

theorem covarianceGood12657_payment :
    (retDist (paperDesignP 12657).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12657)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12657_payment



end BstLean.Part269.N12657

namespace BstLean.Part269.N12657
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12657}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12657.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12657) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12657).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12657 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12657) (by norm_num) BstLean.Part268.WorldRow12657.worldPackage rfl
    BstLean.Part268.WorldRow12657.product_lower (BstLean.Part268.WorldRow12657.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12657} (hw : c ∈ Hof BstLean.Part268.WorldRow12657.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12657) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12657) (by norm_num) BstLean.Part268.WorldRow12657.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12657} (hw : c ∈ Hof BstLean.Part268.WorldRow12657.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12657) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12657).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12657) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12657_eq : scalarRow12657.targetFrame = BstLean.Part268.agent12657.frame := by
  norm_num [scalarRow12657,BstLean.Part268.agent12657]

noncomputable def frameData12657 : BstLean.Part264b.FrameData 12657 :=
  BstLean.Part269.frameData_from_numerics (n := 12657) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12657.worldPackage rfl BstLean.Part268.WorldRow12657.product_lower (BstLean.Part268.WorldRow12657.producthi.2.trans (by norm_num))
    scalarRow12657 repair12657 covarianceInputs12657 (fun i hi => sourceNumerics12657 hi)
    BstLean.Part268.agent12657.frame targetFrame12657_eq


end BstLean.Part269.N12657

namespace BstLean.Part269.N12658
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12658 : scalarRow12658.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12658, BstLean.Part268.grid12658, BstLean.Part263.worldGrid]

theorem supplies12658 (j : Fin 43) : Supply 12658 (parameters j)
    (cellLower scalarRow12658.grid (sourceIndex j))
    (cellUpper scalarRow12658.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12658.grid grid_top_bounds12658 j

theorem radii12658 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12658.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12658 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12658 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12658.grid grid_top_bounds12658 j hθ

noncomputable def covarianceInputs12658 :
    BstLean.Part263.CovarianceInputs 12658 scalarRow12658.grid parameters (caps repair12658) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12658 grid_top_bounds12658 repair12658

noncomputable def covarianceEvent12658 : Set (AgFam 12658) :=
  BstLean.Part263.covarianceEvent 12658 scalarRow12658.grid parameters

theorem covarianceEvent12658_measurable : MeasurableSet covarianceEvent12658 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12658_payment :
    (retDist (paperDesignP 12658).toCentres).real
      (agentEv (paperDesignP 12658) covarianceEvent12658)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12658

theorem localCov12658 : BstLean.Part259.LocalCovarianceOn covarianceEvent12658
    (BstLean.Part263.cell scalarRow12658.grid) (caps repair12658) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12658

theorem covarianceGood12658_payment :
    (retDist (paperDesignP 12658).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12658)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12658_payment



end BstLean.Part269.N12658

namespace BstLean.Part269.N12658
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12658}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12658.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12658) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12658).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12658 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12658) (by norm_num) BstLean.Part268.WorldRow12658.worldPackage rfl
    BstLean.Part268.WorldRow12658.product_lower (BstLean.Part268.WorldRow12658.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12658} (hw : c ∈ Hof BstLean.Part268.WorldRow12658.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12658) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12658) (by norm_num) BstLean.Part268.WorldRow12658.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12658} (hw : c ∈ Hof BstLean.Part268.WorldRow12658.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12658) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12658).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12658) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12658_eq : scalarRow12658.targetFrame = BstLean.Part268.agent12658.frame := by
  norm_num [scalarRow12658,BstLean.Part268.agent12658]

noncomputable def frameData12658 : BstLean.Part264b.FrameData 12658 :=
  BstLean.Part269.frameData_from_numerics (n := 12658) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12658.worldPackage rfl BstLean.Part268.WorldRow12658.product_lower (BstLean.Part268.WorldRow12658.producthi.2.trans (by norm_num))
    scalarRow12658 repair12658 covarianceInputs12658 (fun i hi => sourceNumerics12658 hi)
    BstLean.Part268.agent12658.frame targetFrame12658_eq


end BstLean.Part269.N12658

namespace BstLean.Part269.N12659
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12659 : scalarRow12659.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12659, BstLean.Part268.grid12659, BstLean.Part263.worldGrid]

theorem supplies12659 (j : Fin 43) : Supply 12659 (parameters j)
    (cellLower scalarRow12659.grid (sourceIndex j))
    (cellUpper scalarRow12659.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12659.grid grid_top_bounds12659 j

theorem radii12659 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12659.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12659 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12659 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12659.grid grid_top_bounds12659 j hθ

noncomputable def covarianceInputs12659 :
    BstLean.Part263.CovarianceInputs 12659 scalarRow12659.grid parameters (caps repair12659) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12659 grid_top_bounds12659 repair12659

noncomputable def covarianceEvent12659 : Set (AgFam 12659) :=
  BstLean.Part263.covarianceEvent 12659 scalarRow12659.grid parameters

theorem covarianceEvent12659_measurable : MeasurableSet covarianceEvent12659 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12659_payment :
    (retDist (paperDesignP 12659).toCentres).real
      (agentEv (paperDesignP 12659) covarianceEvent12659)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12659

theorem localCov12659 : BstLean.Part259.LocalCovarianceOn covarianceEvent12659
    (BstLean.Part263.cell scalarRow12659.grid) (caps repair12659) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12659

theorem covarianceGood12659_payment :
    (retDist (paperDesignP 12659).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12659)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12659_payment



end BstLean.Part269.N12659

namespace BstLean.Part269.N12659
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12659}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12659.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12659) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12659).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12659 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12659) (by norm_num) BstLean.Part268.WorldRow12659.worldPackage rfl
    BstLean.Part268.WorldRow12659.product_lower (BstLean.Part268.WorldRow12659.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12659} (hw : c ∈ Hof BstLean.Part268.WorldRow12659.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12659) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12659) (by norm_num) BstLean.Part268.WorldRow12659.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12659} (hw : c ∈ Hof BstLean.Part268.WorldRow12659.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12659) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12659).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12659) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12659_eq : scalarRow12659.targetFrame = BstLean.Part268.agent12659.frame := by
  norm_num [scalarRow12659,BstLean.Part268.agent12659]

noncomputable def frameData12659 : BstLean.Part264b.FrameData 12659 :=
  BstLean.Part269.frameData_from_numerics (n := 12659) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12659.worldPackage rfl BstLean.Part268.WorldRow12659.product_lower (BstLean.Part268.WorldRow12659.producthi.2.trans (by norm_num))
    scalarRow12659 repair12659 covarianceInputs12659 (fun i hi => sourceNumerics12659 hi)
    BstLean.Part268.agent12659.frame targetFrame12659_eq


end BstLean.Part269.N12659
