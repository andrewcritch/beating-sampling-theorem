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

namespace BstLean.Part269.N12650
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12650 : scalarRow12650.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12650, BstLean.Part268.grid12650, BstLean.Part263.worldGrid]

theorem supplies12650 (j : Fin 43) : Supply 12650 (parameters j)
    (cellLower scalarRow12650.grid (sourceIndex j))
    (cellUpper scalarRow12650.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12650.grid grid_top_bounds12650 j

theorem radii12650 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12650.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12650 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12650 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12650.grid grid_top_bounds12650 j hθ

noncomputable def covarianceInputs12650 :
    BstLean.Part263.CovarianceInputs 12650 scalarRow12650.grid parameters (caps repair12650) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12650 grid_top_bounds12650 repair12650

noncomputable def covarianceEvent12650 : Set (AgFam 12650) :=
  BstLean.Part263.covarianceEvent 12650 scalarRow12650.grid parameters

theorem covarianceEvent12650_measurable : MeasurableSet covarianceEvent12650 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12650_payment :
    (retDist (paperDesignP 12650).toCentres).real
      (agentEv (paperDesignP 12650) covarianceEvent12650)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12650

theorem localCov12650 : BstLean.Part259.LocalCovarianceOn covarianceEvent12650
    (BstLean.Part263.cell scalarRow12650.grid) (caps repair12650) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12650

theorem covarianceGood12650_payment :
    (retDist (paperDesignP 12650).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12650)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12650_payment



end BstLean.Part269.N12650

namespace BstLean.Part269.N12650
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12650}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12650.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12650) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12650).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12650 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12650) (by norm_num) BstLean.Part268.WorldRow12650.worldPackage rfl
    BstLean.Part268.WorldRow12650.product_lower (BstLean.Part268.WorldRow12650.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12650} (hw : c ∈ Hof BstLean.Part268.WorldRow12650.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12650) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12650) (by norm_num) BstLean.Part268.WorldRow12650.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12650} (hw : c ∈ Hof BstLean.Part268.WorldRow12650.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12650) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12650).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12650) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12650_eq : scalarRow12650.targetFrame = BstLean.Part268.agent12650.frame := by
  norm_num [scalarRow12650,BstLean.Part268.agent12650]

noncomputable def frameData12650 : BstLean.Part264b.FrameData 12650 :=
  BstLean.Part269.frameData_from_numerics (n := 12650) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12650.worldPackage rfl BstLean.Part268.WorldRow12650.product_lower (BstLean.Part268.WorldRow12650.producthi.2.trans (by norm_num))
    scalarRow12650 repair12650 covarianceInputs12650 (fun i hi => sourceNumerics12650 hi)
    BstLean.Part268.agent12650.frame targetFrame12650_eq


end BstLean.Part269.N12650

namespace BstLean.Part269.N12651
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12651 : scalarRow12651.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12651, BstLean.Part268.grid12651, BstLean.Part263.worldGrid]

theorem supplies12651 (j : Fin 43) : Supply 12651 (parameters j)
    (cellLower scalarRow12651.grid (sourceIndex j))
    (cellUpper scalarRow12651.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12651.grid grid_top_bounds12651 j

theorem radii12651 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12651.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12651 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12651 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12651.grid grid_top_bounds12651 j hθ

noncomputable def covarianceInputs12651 :
    BstLean.Part263.CovarianceInputs 12651 scalarRow12651.grid parameters (caps repair12651) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12651 grid_top_bounds12651 repair12651

noncomputable def covarianceEvent12651 : Set (AgFam 12651) :=
  BstLean.Part263.covarianceEvent 12651 scalarRow12651.grid parameters

theorem covarianceEvent12651_measurable : MeasurableSet covarianceEvent12651 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12651_payment :
    (retDist (paperDesignP 12651).toCentres).real
      (agentEv (paperDesignP 12651) covarianceEvent12651)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12651

theorem localCov12651 : BstLean.Part259.LocalCovarianceOn covarianceEvent12651
    (BstLean.Part263.cell scalarRow12651.grid) (caps repair12651) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12651

theorem covarianceGood12651_payment :
    (retDist (paperDesignP 12651).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12651)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12651_payment



end BstLean.Part269.N12651

namespace BstLean.Part269.N12651
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12651}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12651.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12651) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12651).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12651 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12651) (by norm_num) BstLean.Part268.WorldRow12651.worldPackage rfl
    BstLean.Part268.WorldRow12651.product_lower (BstLean.Part268.WorldRow12651.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12651} (hw : c ∈ Hof BstLean.Part268.WorldRow12651.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12651) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12651) (by norm_num) BstLean.Part268.WorldRow12651.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12651} (hw : c ∈ Hof BstLean.Part268.WorldRow12651.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12651) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12651).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12651) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12651_eq : scalarRow12651.targetFrame = BstLean.Part268.agent12651.frame := by
  norm_num [scalarRow12651,BstLean.Part268.agent12651]

noncomputable def frameData12651 : BstLean.Part264b.FrameData 12651 :=
  BstLean.Part269.frameData_from_numerics (n := 12651) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12651.worldPackage rfl BstLean.Part268.WorldRow12651.product_lower (BstLean.Part268.WorldRow12651.producthi.2.trans (by norm_num))
    scalarRow12651 repair12651 covarianceInputs12651 (fun i hi => sourceNumerics12651 hi)
    BstLean.Part268.agent12651.frame targetFrame12651_eq


end BstLean.Part269.N12651

namespace BstLean.Part269.N12652
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12652 : scalarRow12652.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12652, BstLean.Part268.grid12652, BstLean.Part263.worldGrid]

theorem supplies12652 (j : Fin 43) : Supply 12652 (parameters j)
    (cellLower scalarRow12652.grid (sourceIndex j))
    (cellUpper scalarRow12652.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12652.grid grid_top_bounds12652 j

theorem radii12652 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12652.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12652 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12652 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12652.grid grid_top_bounds12652 j hθ

noncomputable def covarianceInputs12652 :
    BstLean.Part263.CovarianceInputs 12652 scalarRow12652.grid parameters (caps repair12652) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12652 grid_top_bounds12652 repair12652

noncomputable def covarianceEvent12652 : Set (AgFam 12652) :=
  BstLean.Part263.covarianceEvent 12652 scalarRow12652.grid parameters

theorem covarianceEvent12652_measurable : MeasurableSet covarianceEvent12652 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12652_payment :
    (retDist (paperDesignP 12652).toCentres).real
      (agentEv (paperDesignP 12652) covarianceEvent12652)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12652

theorem localCov12652 : BstLean.Part259.LocalCovarianceOn covarianceEvent12652
    (BstLean.Part263.cell scalarRow12652.grid) (caps repair12652) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12652

theorem covarianceGood12652_payment :
    (retDist (paperDesignP 12652).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12652)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12652_payment



end BstLean.Part269.N12652

namespace BstLean.Part269.N12652
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12652}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12652.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12652) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12652).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12652 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12652) (by norm_num) BstLean.Part268.WorldRow12652.worldPackage rfl
    BstLean.Part268.WorldRow12652.product_lower (BstLean.Part268.WorldRow12652.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12652} (hw : c ∈ Hof BstLean.Part268.WorldRow12652.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12652) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12652) (by norm_num) BstLean.Part268.WorldRow12652.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12652} (hw : c ∈ Hof BstLean.Part268.WorldRow12652.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12652) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12652).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12652) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12652_eq : scalarRow12652.targetFrame = BstLean.Part268.agent12652.frame := by
  norm_num [scalarRow12652,BstLean.Part268.agent12652]

noncomputable def frameData12652 : BstLean.Part264b.FrameData 12652 :=
  BstLean.Part269.frameData_from_numerics (n := 12652) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12652.worldPackage rfl BstLean.Part268.WorldRow12652.product_lower (BstLean.Part268.WorldRow12652.producthi.2.trans (by norm_num))
    scalarRow12652 repair12652 covarianceInputs12652 (fun i hi => sourceNumerics12652 hi)
    BstLean.Part268.agent12652.frame targetFrame12652_eq


end BstLean.Part269.N12652

namespace BstLean.Part269.N12653
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12653 : scalarRow12653.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12653, BstLean.Part268.grid12653, BstLean.Part263.worldGrid]

theorem supplies12653 (j : Fin 43) : Supply 12653 (parameters j)
    (cellLower scalarRow12653.grid (sourceIndex j))
    (cellUpper scalarRow12653.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12653.grid grid_top_bounds12653 j

theorem radii12653 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12653.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12653 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12653 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12653.grid grid_top_bounds12653 j hθ

noncomputable def covarianceInputs12653 :
    BstLean.Part263.CovarianceInputs 12653 scalarRow12653.grid parameters (caps repair12653) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12653 grid_top_bounds12653 repair12653

noncomputable def covarianceEvent12653 : Set (AgFam 12653) :=
  BstLean.Part263.covarianceEvent 12653 scalarRow12653.grid parameters

theorem covarianceEvent12653_measurable : MeasurableSet covarianceEvent12653 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12653_payment :
    (retDist (paperDesignP 12653).toCentres).real
      (agentEv (paperDesignP 12653) covarianceEvent12653)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12653

theorem localCov12653 : BstLean.Part259.LocalCovarianceOn covarianceEvent12653
    (BstLean.Part263.cell scalarRow12653.grid) (caps repair12653) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12653

theorem covarianceGood12653_payment :
    (retDist (paperDesignP 12653).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12653)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12653_payment



end BstLean.Part269.N12653

namespace BstLean.Part269.N12653
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12653}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12653.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12653) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12653).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12653 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12653) (by norm_num) BstLean.Part268.WorldRow12653.worldPackage rfl
    BstLean.Part268.WorldRow12653.product_lower (BstLean.Part268.WorldRow12653.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12653} (hw : c ∈ Hof BstLean.Part268.WorldRow12653.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12653) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12653) (by norm_num) BstLean.Part268.WorldRow12653.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12653} (hw : c ∈ Hof BstLean.Part268.WorldRow12653.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12653) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12653).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12653) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12653_eq : scalarRow12653.targetFrame = BstLean.Part268.agent12653.frame := by
  norm_num [scalarRow12653,BstLean.Part268.agent12653]

noncomputable def frameData12653 : BstLean.Part264b.FrameData 12653 :=
  BstLean.Part269.frameData_from_numerics (n := 12653) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12653.worldPackage rfl BstLean.Part268.WorldRow12653.product_lower (BstLean.Part268.WorldRow12653.producthi.2.trans (by norm_num))
    scalarRow12653 repair12653 covarianceInputs12653 (fun i hi => sourceNumerics12653 hi)
    BstLean.Part268.agent12653.frame targetFrame12653_eq


end BstLean.Part269.N12653

namespace BstLean.Part269.N12654
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12654 : scalarRow12654.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12654, BstLean.Part268.grid12654, BstLean.Part263.worldGrid]

theorem supplies12654 (j : Fin 43) : Supply 12654 (parameters j)
    (cellLower scalarRow12654.grid (sourceIndex j))
    (cellUpper scalarRow12654.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12654.grid grid_top_bounds12654 j

theorem radii12654 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12654.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12654 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12654 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12654.grid grid_top_bounds12654 j hθ

noncomputable def covarianceInputs12654 :
    BstLean.Part263.CovarianceInputs 12654 scalarRow12654.grid parameters (caps repair12654) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12654 grid_top_bounds12654 repair12654

noncomputable def covarianceEvent12654 : Set (AgFam 12654) :=
  BstLean.Part263.covarianceEvent 12654 scalarRow12654.grid parameters

theorem covarianceEvent12654_measurable : MeasurableSet covarianceEvent12654 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12654_payment :
    (retDist (paperDesignP 12654).toCentres).real
      (agentEv (paperDesignP 12654) covarianceEvent12654)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12654

theorem localCov12654 : BstLean.Part259.LocalCovarianceOn covarianceEvent12654
    (BstLean.Part263.cell scalarRow12654.grid) (caps repair12654) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12654

theorem covarianceGood12654_payment :
    (retDist (paperDesignP 12654).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12654)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12654_payment



end BstLean.Part269.N12654

namespace BstLean.Part269.N12654
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12654}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12654.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12654) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12654).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12654 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12654) (by norm_num) BstLean.Part268.WorldRow12654.worldPackage rfl
    BstLean.Part268.WorldRow12654.product_lower (BstLean.Part268.WorldRow12654.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12654} (hw : c ∈ Hof BstLean.Part268.WorldRow12654.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12654) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12654) (by norm_num) BstLean.Part268.WorldRow12654.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12654} (hw : c ∈ Hof BstLean.Part268.WorldRow12654.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12654) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12654).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12654) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12654_eq : scalarRow12654.targetFrame = BstLean.Part268.agent12654.frame := by
  norm_num [scalarRow12654,BstLean.Part268.agent12654]

noncomputable def frameData12654 : BstLean.Part264b.FrameData 12654 :=
  BstLean.Part269.frameData_from_numerics (n := 12654) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12654.worldPackage rfl BstLean.Part268.WorldRow12654.product_lower (BstLean.Part268.WorldRow12654.producthi.2.trans (by norm_num))
    scalarRow12654 repair12654 covarianceInputs12654 (fun i hi => sourceNumerics12654 hi)
    BstLean.Part268.agent12654.frame targetFrame12654_eq


end BstLean.Part269.N12654
