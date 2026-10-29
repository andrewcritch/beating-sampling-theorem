import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World14Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs14
import BstLean.Part269Rows14
import BstLean.Part269Sources14
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12720
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12720 : scalarRow12720.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12720, BstLean.Part268.grid12720, BstLean.Part263.worldGrid]

theorem supplies12720 (j : Fin 43) : Supply 12720 (parameters j)
    (cellLower scalarRow12720.grid (sourceIndex j))
    (cellUpper scalarRow12720.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12720.grid grid_top_bounds12720 j

theorem radii12720 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12720.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12720 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12720 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12720.grid grid_top_bounds12720 j hθ

noncomputable def covarianceInputs12720 :
    BstLean.Part263.CovarianceInputs 12720 scalarRow12720.grid parameters (caps repair12720) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12720 grid_top_bounds12720 repair12720

noncomputable def covarianceEvent12720 : Set (AgFam 12720) :=
  BstLean.Part263.covarianceEvent 12720 scalarRow12720.grid parameters

theorem covarianceEvent12720_measurable : MeasurableSet covarianceEvent12720 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12720_payment :
    (retDist (paperDesignP 12720).toCentres).real
      (agentEv (paperDesignP 12720) covarianceEvent12720)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12720

theorem localCov12720 : BstLean.Part259.LocalCovarianceOn covarianceEvent12720
    (BstLean.Part263.cell scalarRow12720.grid) (caps repair12720) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12720

theorem covarianceGood12720_payment :
    (retDist (paperDesignP 12720).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12720)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12720_payment



end BstLean.Part269.N12720

namespace BstLean.Part269.N12720
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12720}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12720.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12720) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12720).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12720 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12720) (by norm_num) BstLean.Part268.WorldRow12720.worldPackage rfl
    BstLean.Part268.WorldRow12720.product_lower (BstLean.Part268.WorldRow12720.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12720} (hw : c ∈ Hof BstLean.Part268.WorldRow12720.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12720) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12720) (by norm_num) BstLean.Part268.WorldRow12720.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12720} (hw : c ∈ Hof BstLean.Part268.WorldRow12720.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12720) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12720).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12720) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12720_eq : scalarRow12720.targetFrame = BstLean.Part268.agent12720.frame := by
  norm_num [scalarRow12720,BstLean.Part268.agent12720]

noncomputable def frameData12720 : BstLean.Part264b.FrameData 12720 :=
  BstLean.Part269.frameData_from_numerics (n := 12720) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12720.worldPackage rfl BstLean.Part268.WorldRow12720.product_lower (BstLean.Part268.WorldRow12720.producthi.2.trans (by norm_num))
    scalarRow12720 repair12720 covarianceInputs12720 (fun i hi => sourceNumerics12720 hi)
    BstLean.Part268.agent12720.frame targetFrame12720_eq


end BstLean.Part269.N12720

namespace BstLean.Part269.N12721
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12721 : scalarRow12721.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12721, BstLean.Part268.grid12721, BstLean.Part263.worldGrid]

theorem supplies12721 (j : Fin 43) : Supply 12721 (parameters j)
    (cellLower scalarRow12721.grid (sourceIndex j))
    (cellUpper scalarRow12721.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12721.grid grid_top_bounds12721 j

theorem radii12721 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12721.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12721 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12721 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12721.grid grid_top_bounds12721 j hθ

noncomputable def covarianceInputs12721 :
    BstLean.Part263.CovarianceInputs 12721 scalarRow12721.grid parameters (caps repair12721) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12721 grid_top_bounds12721 repair12721

noncomputable def covarianceEvent12721 : Set (AgFam 12721) :=
  BstLean.Part263.covarianceEvent 12721 scalarRow12721.grid parameters

theorem covarianceEvent12721_measurable : MeasurableSet covarianceEvent12721 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12721_payment :
    (retDist (paperDesignP 12721).toCentres).real
      (agentEv (paperDesignP 12721) covarianceEvent12721)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12721

theorem localCov12721 : BstLean.Part259.LocalCovarianceOn covarianceEvent12721
    (BstLean.Part263.cell scalarRow12721.grid) (caps repair12721) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12721

theorem covarianceGood12721_payment :
    (retDist (paperDesignP 12721).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12721)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12721_payment



end BstLean.Part269.N12721

namespace BstLean.Part269.N12721
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12721}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12721.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12721) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12721).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12721 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12721) (by norm_num) BstLean.Part268.WorldRow12721.worldPackage rfl
    BstLean.Part268.WorldRow12721.product_lower (BstLean.Part268.WorldRow12721.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12721} (hw : c ∈ Hof BstLean.Part268.WorldRow12721.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12721) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12721) (by norm_num) BstLean.Part268.WorldRow12721.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12721} (hw : c ∈ Hof BstLean.Part268.WorldRow12721.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12721) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12721).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12721) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12721_eq : scalarRow12721.targetFrame = BstLean.Part268.agent12721.frame := by
  norm_num [scalarRow12721,BstLean.Part268.agent12721]

noncomputable def frameData12721 : BstLean.Part264b.FrameData 12721 :=
  BstLean.Part269.frameData_from_numerics (n := 12721) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12721.worldPackage rfl BstLean.Part268.WorldRow12721.product_lower (BstLean.Part268.WorldRow12721.producthi.2.trans (by norm_num))
    scalarRow12721 repair12721 covarianceInputs12721 (fun i hi => sourceNumerics12721 hi)
    BstLean.Part268.agent12721.frame targetFrame12721_eq


end BstLean.Part269.N12721

namespace BstLean.Part269.N12722
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12722 : scalarRow12722.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12722, BstLean.Part268.grid12722, BstLean.Part263.worldGrid]

theorem supplies12722 (j : Fin 43) : Supply 12722 (parameters j)
    (cellLower scalarRow12722.grid (sourceIndex j))
    (cellUpper scalarRow12722.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12722.grid grid_top_bounds12722 j

theorem radii12722 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12722.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12722 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12722 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12722.grid grid_top_bounds12722 j hθ

noncomputable def covarianceInputs12722 :
    BstLean.Part263.CovarianceInputs 12722 scalarRow12722.grid parameters (caps repair12722) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12722 grid_top_bounds12722 repair12722

noncomputable def covarianceEvent12722 : Set (AgFam 12722) :=
  BstLean.Part263.covarianceEvent 12722 scalarRow12722.grid parameters

theorem covarianceEvent12722_measurable : MeasurableSet covarianceEvent12722 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12722_payment :
    (retDist (paperDesignP 12722).toCentres).real
      (agentEv (paperDesignP 12722) covarianceEvent12722)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12722

theorem localCov12722 : BstLean.Part259.LocalCovarianceOn covarianceEvent12722
    (BstLean.Part263.cell scalarRow12722.grid) (caps repair12722) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12722

theorem covarianceGood12722_payment :
    (retDist (paperDesignP 12722).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12722)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12722_payment



end BstLean.Part269.N12722

namespace BstLean.Part269.N12722
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12722}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12722.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12722) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12722).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12722 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12722) (by norm_num) BstLean.Part268.WorldRow12722.worldPackage rfl
    BstLean.Part268.WorldRow12722.product_lower (BstLean.Part268.WorldRow12722.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12722} (hw : c ∈ Hof BstLean.Part268.WorldRow12722.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12722) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12722) (by norm_num) BstLean.Part268.WorldRow12722.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12722} (hw : c ∈ Hof BstLean.Part268.WorldRow12722.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12722) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12722).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12722) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12722_eq : scalarRow12722.targetFrame = BstLean.Part268.agent12722.frame := by
  norm_num [scalarRow12722,BstLean.Part268.agent12722]

noncomputable def frameData12722 : BstLean.Part264b.FrameData 12722 :=
  BstLean.Part269.frameData_from_numerics (n := 12722) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12722.worldPackage rfl BstLean.Part268.WorldRow12722.product_lower (BstLean.Part268.WorldRow12722.producthi.2.trans (by norm_num))
    scalarRow12722 repair12722 covarianceInputs12722 (fun i hi => sourceNumerics12722 hi)
    BstLean.Part268.agent12722.frame targetFrame12722_eq


end BstLean.Part269.N12722

namespace BstLean.Part269.N12723
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12723 : scalarRow12723.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12723, BstLean.Part268.grid12723, BstLean.Part263.worldGrid]

theorem supplies12723 (j : Fin 43) : Supply 12723 (parameters j)
    (cellLower scalarRow12723.grid (sourceIndex j))
    (cellUpper scalarRow12723.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12723.grid grid_top_bounds12723 j

theorem radii12723 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12723.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12723 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12723 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12723.grid grid_top_bounds12723 j hθ

noncomputable def covarianceInputs12723 :
    BstLean.Part263.CovarianceInputs 12723 scalarRow12723.grid parameters (caps repair12723) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12723 grid_top_bounds12723 repair12723

noncomputable def covarianceEvent12723 : Set (AgFam 12723) :=
  BstLean.Part263.covarianceEvent 12723 scalarRow12723.grid parameters

theorem covarianceEvent12723_measurable : MeasurableSet covarianceEvent12723 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12723_payment :
    (retDist (paperDesignP 12723).toCentres).real
      (agentEv (paperDesignP 12723) covarianceEvent12723)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12723

theorem localCov12723 : BstLean.Part259.LocalCovarianceOn covarianceEvent12723
    (BstLean.Part263.cell scalarRow12723.grid) (caps repair12723) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12723

theorem covarianceGood12723_payment :
    (retDist (paperDesignP 12723).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12723)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12723_payment



end BstLean.Part269.N12723

namespace BstLean.Part269.N12723
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12723}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12723.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12723) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12723).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12723 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12723) (by norm_num) BstLean.Part268.WorldRow12723.worldPackage rfl
    BstLean.Part268.WorldRow12723.product_lower (BstLean.Part268.WorldRow12723.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12723} (hw : c ∈ Hof BstLean.Part268.WorldRow12723.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12723) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12723) (by norm_num) BstLean.Part268.WorldRow12723.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12723} (hw : c ∈ Hof BstLean.Part268.WorldRow12723.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12723) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12723).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12723) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12723_eq : scalarRow12723.targetFrame = BstLean.Part268.agent12723.frame := by
  norm_num [scalarRow12723,BstLean.Part268.agent12723]

noncomputable def frameData12723 : BstLean.Part264b.FrameData 12723 :=
  BstLean.Part269.frameData_from_numerics (n := 12723) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12723.worldPackage rfl BstLean.Part268.WorldRow12723.product_lower (BstLean.Part268.WorldRow12723.producthi.2.trans (by norm_num))
    scalarRow12723 repair12723 covarianceInputs12723 (fun i hi => sourceNumerics12723 hi)
    BstLean.Part268.agent12723.frame targetFrame12723_eq


end BstLean.Part269.N12723

namespace BstLean.Part269.N12724
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12724 : scalarRow12724.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12724, BstLean.Part268.grid12724, BstLean.Part263.worldGrid]

theorem supplies12724 (j : Fin 43) : Supply 12724 (parameters j)
    (cellLower scalarRow12724.grid (sourceIndex j))
    (cellUpper scalarRow12724.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12724.grid grid_top_bounds12724 j

theorem radii12724 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12724.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12724 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12724 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12724.grid grid_top_bounds12724 j hθ

noncomputable def covarianceInputs12724 :
    BstLean.Part263.CovarianceInputs 12724 scalarRow12724.grid parameters (caps repair12724) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12724 grid_top_bounds12724 repair12724

noncomputable def covarianceEvent12724 : Set (AgFam 12724) :=
  BstLean.Part263.covarianceEvent 12724 scalarRow12724.grid parameters

theorem covarianceEvent12724_measurable : MeasurableSet covarianceEvent12724 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12724_payment :
    (retDist (paperDesignP 12724).toCentres).real
      (agentEv (paperDesignP 12724) covarianceEvent12724)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12724

theorem localCov12724 : BstLean.Part259.LocalCovarianceOn covarianceEvent12724
    (BstLean.Part263.cell scalarRow12724.grid) (caps repair12724) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12724

theorem covarianceGood12724_payment :
    (retDist (paperDesignP 12724).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12724)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12724_payment



end BstLean.Part269.N12724

namespace BstLean.Part269.N12724
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12724}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12724.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12724) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12724).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12724 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12724) (by norm_num) BstLean.Part268.WorldRow12724.worldPackage rfl
    BstLean.Part268.WorldRow12724.product_lower (BstLean.Part268.WorldRow12724.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12724} (hw : c ∈ Hof BstLean.Part268.WorldRow12724.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12724) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12724) (by norm_num) BstLean.Part268.WorldRow12724.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12724} (hw : c ∈ Hof BstLean.Part268.WorldRow12724.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12724) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12724).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12724) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12724_eq : scalarRow12724.targetFrame = BstLean.Part268.agent12724.frame := by
  norm_num [scalarRow12724,BstLean.Part268.agent12724]

noncomputable def frameData12724 : BstLean.Part264b.FrameData 12724 :=
  BstLean.Part269.frameData_from_numerics (n := 12724) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12724.worldPackage rfl BstLean.Part268.WorldRow12724.product_lower (BstLean.Part268.WorldRow12724.producthi.2.trans (by norm_num))
    scalarRow12724 repair12724 covarianceInputs12724 (fun i hi => sourceNumerics12724 hi)
    BstLean.Part268.agent12724.frame targetFrame12724_eq


end BstLean.Part269.N12724
