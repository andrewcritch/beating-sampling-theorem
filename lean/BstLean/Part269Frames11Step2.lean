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

namespace BstLean.Part269.N12635
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12635 : scalarRow12635.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12635, BstLean.Part268.grid12635, BstLean.Part263.worldGrid]

theorem supplies12635 (j : Fin 43) : Supply 12635 (parameters j)
    (cellLower scalarRow12635.grid (sourceIndex j))
    (cellUpper scalarRow12635.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12635.grid grid_top_bounds12635 j

theorem radii12635 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12635.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12635 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12635 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12635.grid grid_top_bounds12635 j hθ

noncomputable def covarianceInputs12635 :
    BstLean.Part263.CovarianceInputs 12635 scalarRow12635.grid parameters (caps repair12635) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12635 grid_top_bounds12635 repair12635

noncomputable def covarianceEvent12635 : Set (AgFam 12635) :=
  BstLean.Part263.covarianceEvent 12635 scalarRow12635.grid parameters

theorem covarianceEvent12635_measurable : MeasurableSet covarianceEvent12635 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12635_payment :
    (retDist (paperDesignP 12635).toCentres).real
      (agentEv (paperDesignP 12635) covarianceEvent12635)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12635

theorem localCov12635 : BstLean.Part259.LocalCovarianceOn covarianceEvent12635
    (BstLean.Part263.cell scalarRow12635.grid) (caps repair12635) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12635

theorem covarianceGood12635_payment :
    (retDist (paperDesignP 12635).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12635)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12635_payment



end BstLean.Part269.N12635

namespace BstLean.Part269.N12635
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12635}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12635.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12635) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12635).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12635 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12635) (by norm_num) BstLean.Part268.WorldRow12635.worldPackage rfl
    BstLean.Part268.WorldRow12635.product_lower (BstLean.Part268.WorldRow12635.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12635} (hw : c ∈ Hof BstLean.Part268.WorldRow12635.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12635) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12635) (by norm_num) BstLean.Part268.WorldRow12635.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12635} (hw : c ∈ Hof BstLean.Part268.WorldRow12635.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12635) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12635).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12635) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12635_eq : scalarRow12635.targetFrame = BstLean.Part268.agent12635.frame := by
  norm_num [scalarRow12635,BstLean.Part268.agent12635]

noncomputable def frameData12635 : BstLean.Part264b.FrameData 12635 :=
  BstLean.Part269.frameData_from_numerics (n := 12635) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12635.worldPackage rfl BstLean.Part268.WorldRow12635.product_lower (BstLean.Part268.WorldRow12635.producthi.2.trans (by norm_num))
    scalarRow12635 repair12635 covarianceInputs12635 (fun i hi => sourceNumerics12635 hi)
    BstLean.Part268.agent12635.frame targetFrame12635_eq


end BstLean.Part269.N12635

namespace BstLean.Part269.N12636
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12636 : scalarRow12636.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12636, BstLean.Part268.grid12636, BstLean.Part263.worldGrid]

theorem supplies12636 (j : Fin 43) : Supply 12636 (parameters j)
    (cellLower scalarRow12636.grid (sourceIndex j))
    (cellUpper scalarRow12636.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12636.grid grid_top_bounds12636 j

theorem radii12636 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12636.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12636 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12636 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12636.grid grid_top_bounds12636 j hθ

noncomputable def covarianceInputs12636 :
    BstLean.Part263.CovarianceInputs 12636 scalarRow12636.grid parameters (caps repair12636) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12636 grid_top_bounds12636 repair12636

noncomputable def covarianceEvent12636 : Set (AgFam 12636) :=
  BstLean.Part263.covarianceEvent 12636 scalarRow12636.grid parameters

theorem covarianceEvent12636_measurable : MeasurableSet covarianceEvent12636 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12636_payment :
    (retDist (paperDesignP 12636).toCentres).real
      (agentEv (paperDesignP 12636) covarianceEvent12636)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12636

theorem localCov12636 : BstLean.Part259.LocalCovarianceOn covarianceEvent12636
    (BstLean.Part263.cell scalarRow12636.grid) (caps repair12636) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12636

theorem covarianceGood12636_payment :
    (retDist (paperDesignP 12636).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12636)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12636_payment



end BstLean.Part269.N12636

namespace BstLean.Part269.N12636
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12636}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12636.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12636) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12636).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12636 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12636) (by norm_num) BstLean.Part268.WorldRow12636.worldPackage rfl
    BstLean.Part268.WorldRow12636.product_lower (BstLean.Part268.WorldRow12636.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12636} (hw : c ∈ Hof BstLean.Part268.WorldRow12636.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12636) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12636) (by norm_num) BstLean.Part268.WorldRow12636.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12636} (hw : c ∈ Hof BstLean.Part268.WorldRow12636.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12636) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12636).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12636) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12636_eq : scalarRow12636.targetFrame = BstLean.Part268.agent12636.frame := by
  norm_num [scalarRow12636,BstLean.Part268.agent12636]

noncomputable def frameData12636 : BstLean.Part264b.FrameData 12636 :=
  BstLean.Part269.frameData_from_numerics (n := 12636) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12636.worldPackage rfl BstLean.Part268.WorldRow12636.product_lower (BstLean.Part268.WorldRow12636.producthi.2.trans (by norm_num))
    scalarRow12636 repair12636 covarianceInputs12636 (fun i hi => sourceNumerics12636 hi)
    BstLean.Part268.agent12636.frame targetFrame12636_eq


end BstLean.Part269.N12636

namespace BstLean.Part269.N12637
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12637 : scalarRow12637.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12637, BstLean.Part268.grid12637, BstLean.Part263.worldGrid]

theorem supplies12637 (j : Fin 43) : Supply 12637 (parameters j)
    (cellLower scalarRow12637.grid (sourceIndex j))
    (cellUpper scalarRow12637.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12637.grid grid_top_bounds12637 j

theorem radii12637 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12637.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12637 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12637 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12637.grid grid_top_bounds12637 j hθ

noncomputable def covarianceInputs12637 :
    BstLean.Part263.CovarianceInputs 12637 scalarRow12637.grid parameters (caps repair12637) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12637 grid_top_bounds12637 repair12637

noncomputable def covarianceEvent12637 : Set (AgFam 12637) :=
  BstLean.Part263.covarianceEvent 12637 scalarRow12637.grid parameters

theorem covarianceEvent12637_measurable : MeasurableSet covarianceEvent12637 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12637_payment :
    (retDist (paperDesignP 12637).toCentres).real
      (agentEv (paperDesignP 12637) covarianceEvent12637)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12637

theorem localCov12637 : BstLean.Part259.LocalCovarianceOn covarianceEvent12637
    (BstLean.Part263.cell scalarRow12637.grid) (caps repair12637) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12637

theorem covarianceGood12637_payment :
    (retDist (paperDesignP 12637).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12637)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12637_payment



end BstLean.Part269.N12637

namespace BstLean.Part269.N12637
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12637}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12637.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12637) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12637).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12637 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12637) (by norm_num) BstLean.Part268.WorldRow12637.worldPackage rfl
    BstLean.Part268.WorldRow12637.product_lower (BstLean.Part268.WorldRow12637.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12637} (hw : c ∈ Hof BstLean.Part268.WorldRow12637.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12637) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12637) (by norm_num) BstLean.Part268.WorldRow12637.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12637} (hw : c ∈ Hof BstLean.Part268.WorldRow12637.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12637) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12637).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12637) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12637_eq : scalarRow12637.targetFrame = BstLean.Part268.agent12637.frame := by
  norm_num [scalarRow12637,BstLean.Part268.agent12637]

noncomputable def frameData12637 : BstLean.Part264b.FrameData 12637 :=
  BstLean.Part269.frameData_from_numerics (n := 12637) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12637.worldPackage rfl BstLean.Part268.WorldRow12637.product_lower (BstLean.Part268.WorldRow12637.producthi.2.trans (by norm_num))
    scalarRow12637 repair12637 covarianceInputs12637 (fun i hi => sourceNumerics12637 hi)
    BstLean.Part268.agent12637.frame targetFrame12637_eq


end BstLean.Part269.N12637

namespace BstLean.Part269.N12638
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12638 : scalarRow12638.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12638, BstLean.Part268.grid12638, BstLean.Part263.worldGrid]

theorem supplies12638 (j : Fin 43) : Supply 12638 (parameters j)
    (cellLower scalarRow12638.grid (sourceIndex j))
    (cellUpper scalarRow12638.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12638.grid grid_top_bounds12638 j

theorem radii12638 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12638.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12638 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12638 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12638.grid grid_top_bounds12638 j hθ

noncomputable def covarianceInputs12638 :
    BstLean.Part263.CovarianceInputs 12638 scalarRow12638.grid parameters (caps repair12638) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12638 grid_top_bounds12638 repair12638

noncomputable def covarianceEvent12638 : Set (AgFam 12638) :=
  BstLean.Part263.covarianceEvent 12638 scalarRow12638.grid parameters

theorem covarianceEvent12638_measurable : MeasurableSet covarianceEvent12638 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12638_payment :
    (retDist (paperDesignP 12638).toCentres).real
      (agentEv (paperDesignP 12638) covarianceEvent12638)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12638

theorem localCov12638 : BstLean.Part259.LocalCovarianceOn covarianceEvent12638
    (BstLean.Part263.cell scalarRow12638.grid) (caps repair12638) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12638

theorem covarianceGood12638_payment :
    (retDist (paperDesignP 12638).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12638)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12638_payment



end BstLean.Part269.N12638

namespace BstLean.Part269.N12638
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12638}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12638.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12638) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12638).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12638 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12638) (by norm_num) BstLean.Part268.WorldRow12638.worldPackage rfl
    BstLean.Part268.WorldRow12638.product_lower (BstLean.Part268.WorldRow12638.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12638} (hw : c ∈ Hof BstLean.Part268.WorldRow12638.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12638) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12638) (by norm_num) BstLean.Part268.WorldRow12638.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12638} (hw : c ∈ Hof BstLean.Part268.WorldRow12638.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12638) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12638).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12638) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12638_eq : scalarRow12638.targetFrame = BstLean.Part268.agent12638.frame := by
  norm_num [scalarRow12638,BstLean.Part268.agent12638]

noncomputable def frameData12638 : BstLean.Part264b.FrameData 12638 :=
  BstLean.Part269.frameData_from_numerics (n := 12638) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12638.worldPackage rfl BstLean.Part268.WorldRow12638.product_lower (BstLean.Part268.WorldRow12638.producthi.2.trans (by norm_num))
    scalarRow12638 repair12638 covarianceInputs12638 (fun i hi => sourceNumerics12638 hi)
    BstLean.Part268.agent12638.frame targetFrame12638_eq


end BstLean.Part269.N12638

namespace BstLean.Part269.N12639
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12639 : scalarRow12639.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12639, BstLean.Part268.grid12639, BstLean.Part263.worldGrid]

theorem supplies12639 (j : Fin 43) : Supply 12639 (parameters j)
    (cellLower scalarRow12639.grid (sourceIndex j))
    (cellUpper scalarRow12639.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12639.grid grid_top_bounds12639 j

theorem radii12639 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12639.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12639 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12639 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12639.grid grid_top_bounds12639 j hθ

noncomputable def covarianceInputs12639 :
    BstLean.Part263.CovarianceInputs 12639 scalarRow12639.grid parameters (caps repair12639) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12639 grid_top_bounds12639 repair12639

noncomputable def covarianceEvent12639 : Set (AgFam 12639) :=
  BstLean.Part263.covarianceEvent 12639 scalarRow12639.grid parameters

theorem covarianceEvent12639_measurable : MeasurableSet covarianceEvent12639 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12639_payment :
    (retDist (paperDesignP 12639).toCentres).real
      (agentEv (paperDesignP 12639) covarianceEvent12639)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12639

theorem localCov12639 : BstLean.Part259.LocalCovarianceOn covarianceEvent12639
    (BstLean.Part263.cell scalarRow12639.grid) (caps repair12639) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12639

theorem covarianceGood12639_payment :
    (retDist (paperDesignP 12639).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12639)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12639_payment



end BstLean.Part269.N12639

namespace BstLean.Part269.N12639
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12639}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12639.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12639) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12639).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12639 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12639) (by norm_num) BstLean.Part268.WorldRow12639.worldPackage rfl
    BstLean.Part268.WorldRow12639.product_lower (BstLean.Part268.WorldRow12639.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12639} (hw : c ∈ Hof BstLean.Part268.WorldRow12639.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12639) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12639) (by norm_num) BstLean.Part268.WorldRow12639.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12639} (hw : c ∈ Hof BstLean.Part268.WorldRow12639.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12639) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12639).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12639) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12639_eq : scalarRow12639.targetFrame = BstLean.Part268.agent12639.frame := by
  norm_num [scalarRow12639,BstLean.Part268.agent12639]

noncomputable def frameData12639 : BstLean.Part264b.FrameData 12639 :=
  BstLean.Part269.frameData_from_numerics (n := 12639) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12639.worldPackage rfl BstLean.Part268.WorldRow12639.product_lower (BstLean.Part268.WorldRow12639.producthi.2.trans (by norm_num))
    scalarRow12639 repair12639 covarianceInputs12639 (fun i hi => sourceNumerics12639 hi)
    BstLean.Part268.agent12639.frame targetFrame12639_eq


end BstLean.Part269.N12639
