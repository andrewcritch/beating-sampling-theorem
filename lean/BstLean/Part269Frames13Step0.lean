import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World13Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs13
import BstLean.Part269Rows13
import BstLean.Part269Sources13
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12675
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12675 : scalarRow12675.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12675, BstLean.Part268.grid12675, BstLean.Part263.worldGrid]

theorem supplies12675 (j : Fin 43) : Supply 12675 (parameters j)
    (cellLower scalarRow12675.grid (sourceIndex j))
    (cellUpper scalarRow12675.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12675.grid grid_top_bounds12675 j

theorem radii12675 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12675.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12675 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12675 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12675.grid grid_top_bounds12675 j hθ

noncomputable def covarianceInputs12675 :
    BstLean.Part263.CovarianceInputs 12675 scalarRow12675.grid parameters (caps repair12675) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12675 grid_top_bounds12675 repair12675

noncomputable def covarianceEvent12675 : Set (AgFam 12675) :=
  BstLean.Part263.covarianceEvent 12675 scalarRow12675.grid parameters

theorem covarianceEvent12675_measurable : MeasurableSet covarianceEvent12675 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12675_payment :
    (retDist (paperDesignP 12675).toCentres).real
      (agentEv (paperDesignP 12675) covarianceEvent12675)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12675

theorem localCov12675 : BstLean.Part259.LocalCovarianceOn covarianceEvent12675
    (BstLean.Part263.cell scalarRow12675.grid) (caps repair12675) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12675

theorem covarianceGood12675_payment :
    (retDist (paperDesignP 12675).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12675)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12675_payment



end BstLean.Part269.N12675

namespace BstLean.Part269.N12675
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12675}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12675.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12675) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12675).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12675 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12675) (by norm_num) BstLean.Part268.WorldRow12675.worldPackage rfl
    BstLean.Part268.WorldRow12675.product_lower (BstLean.Part268.WorldRow12675.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12675} (hw : c ∈ Hof BstLean.Part268.WorldRow12675.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12675) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12675) (by norm_num) BstLean.Part268.WorldRow12675.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12675} (hw : c ∈ Hof BstLean.Part268.WorldRow12675.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12675) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12675).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12675) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12675_eq : scalarRow12675.targetFrame = BstLean.Part268.agent12675.frame := by
  norm_num [scalarRow12675,BstLean.Part268.agent12675]

noncomputable def frameData12675 : BstLean.Part264b.FrameData 12675 :=
  BstLean.Part269.frameData_from_numerics (n := 12675) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12675.worldPackage rfl BstLean.Part268.WorldRow12675.product_lower (BstLean.Part268.WorldRow12675.producthi.2.trans (by norm_num))
    scalarRow12675 repair12675 covarianceInputs12675 (fun i hi => sourceNumerics12675 hi)
    BstLean.Part268.agent12675.frame targetFrame12675_eq


end BstLean.Part269.N12675

namespace BstLean.Part269.N12676
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12676 : scalarRow12676.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12676, BstLean.Part268.grid12676, BstLean.Part263.worldGrid]

theorem supplies12676 (j : Fin 43) : Supply 12676 (parameters j)
    (cellLower scalarRow12676.grid (sourceIndex j))
    (cellUpper scalarRow12676.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12676.grid grid_top_bounds12676 j

theorem radii12676 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12676.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12676 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12676 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12676.grid grid_top_bounds12676 j hθ

noncomputable def covarianceInputs12676 :
    BstLean.Part263.CovarianceInputs 12676 scalarRow12676.grid parameters (caps repair12676) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12676 grid_top_bounds12676 repair12676

noncomputable def covarianceEvent12676 : Set (AgFam 12676) :=
  BstLean.Part263.covarianceEvent 12676 scalarRow12676.grid parameters

theorem covarianceEvent12676_measurable : MeasurableSet covarianceEvent12676 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12676_payment :
    (retDist (paperDesignP 12676).toCentres).real
      (agentEv (paperDesignP 12676) covarianceEvent12676)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12676

theorem localCov12676 : BstLean.Part259.LocalCovarianceOn covarianceEvent12676
    (BstLean.Part263.cell scalarRow12676.grid) (caps repair12676) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12676

theorem covarianceGood12676_payment :
    (retDist (paperDesignP 12676).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12676)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12676_payment



end BstLean.Part269.N12676

namespace BstLean.Part269.N12676
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12676}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12676.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12676) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12676).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12676 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12676) (by norm_num) BstLean.Part268.WorldRow12676.worldPackage rfl
    BstLean.Part268.WorldRow12676.product_lower (BstLean.Part268.WorldRow12676.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12676} (hw : c ∈ Hof BstLean.Part268.WorldRow12676.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12676) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12676) (by norm_num) BstLean.Part268.WorldRow12676.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12676} (hw : c ∈ Hof BstLean.Part268.WorldRow12676.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12676) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12676).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12676) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12676_eq : scalarRow12676.targetFrame = BstLean.Part268.agent12676.frame := by
  norm_num [scalarRow12676,BstLean.Part268.agent12676]

noncomputable def frameData12676 : BstLean.Part264b.FrameData 12676 :=
  BstLean.Part269.frameData_from_numerics (n := 12676) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12676.worldPackage rfl BstLean.Part268.WorldRow12676.product_lower (BstLean.Part268.WorldRow12676.producthi.2.trans (by norm_num))
    scalarRow12676 repair12676 covarianceInputs12676 (fun i hi => sourceNumerics12676 hi)
    BstLean.Part268.agent12676.frame targetFrame12676_eq


end BstLean.Part269.N12676

namespace BstLean.Part269.N12677
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12677 : scalarRow12677.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12677, BstLean.Part268.grid12677, BstLean.Part263.worldGrid]

theorem supplies12677 (j : Fin 43) : Supply 12677 (parameters j)
    (cellLower scalarRow12677.grid (sourceIndex j))
    (cellUpper scalarRow12677.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12677.grid grid_top_bounds12677 j

theorem radii12677 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12677.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12677 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12677 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12677.grid grid_top_bounds12677 j hθ

noncomputable def covarianceInputs12677 :
    BstLean.Part263.CovarianceInputs 12677 scalarRow12677.grid parameters (caps repair12677) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12677 grid_top_bounds12677 repair12677

noncomputable def covarianceEvent12677 : Set (AgFam 12677) :=
  BstLean.Part263.covarianceEvent 12677 scalarRow12677.grid parameters

theorem covarianceEvent12677_measurable : MeasurableSet covarianceEvent12677 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12677_payment :
    (retDist (paperDesignP 12677).toCentres).real
      (agentEv (paperDesignP 12677) covarianceEvent12677)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12677

theorem localCov12677 : BstLean.Part259.LocalCovarianceOn covarianceEvent12677
    (BstLean.Part263.cell scalarRow12677.grid) (caps repair12677) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12677

theorem covarianceGood12677_payment :
    (retDist (paperDesignP 12677).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12677)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12677_payment



end BstLean.Part269.N12677

namespace BstLean.Part269.N12677
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12677}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12677.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12677) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12677).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12677 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12677) (by norm_num) BstLean.Part268.WorldRow12677.worldPackage rfl
    BstLean.Part268.WorldRow12677.product_lower (BstLean.Part268.WorldRow12677.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12677} (hw : c ∈ Hof BstLean.Part268.WorldRow12677.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12677) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12677) (by norm_num) BstLean.Part268.WorldRow12677.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12677} (hw : c ∈ Hof BstLean.Part268.WorldRow12677.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12677) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12677).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12677) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12677_eq : scalarRow12677.targetFrame = BstLean.Part268.agent12677.frame := by
  norm_num [scalarRow12677,BstLean.Part268.agent12677]

noncomputable def frameData12677 : BstLean.Part264b.FrameData 12677 :=
  BstLean.Part269.frameData_from_numerics (n := 12677) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12677.worldPackage rfl BstLean.Part268.WorldRow12677.product_lower (BstLean.Part268.WorldRow12677.producthi.2.trans (by norm_num))
    scalarRow12677 repair12677 covarianceInputs12677 (fun i hi => sourceNumerics12677 hi)
    BstLean.Part268.agent12677.frame targetFrame12677_eq


end BstLean.Part269.N12677

namespace BstLean.Part269.N12678
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12678 : scalarRow12678.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12678, BstLean.Part268.grid12678, BstLean.Part263.worldGrid]

theorem supplies12678 (j : Fin 43) : Supply 12678 (parameters j)
    (cellLower scalarRow12678.grid (sourceIndex j))
    (cellUpper scalarRow12678.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12678.grid grid_top_bounds12678 j

theorem radii12678 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12678.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12678 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12678 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12678.grid grid_top_bounds12678 j hθ

noncomputable def covarianceInputs12678 :
    BstLean.Part263.CovarianceInputs 12678 scalarRow12678.grid parameters (caps repair12678) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12678 grid_top_bounds12678 repair12678

noncomputable def covarianceEvent12678 : Set (AgFam 12678) :=
  BstLean.Part263.covarianceEvent 12678 scalarRow12678.grid parameters

theorem covarianceEvent12678_measurable : MeasurableSet covarianceEvent12678 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12678_payment :
    (retDist (paperDesignP 12678).toCentres).real
      (agentEv (paperDesignP 12678) covarianceEvent12678)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12678

theorem localCov12678 : BstLean.Part259.LocalCovarianceOn covarianceEvent12678
    (BstLean.Part263.cell scalarRow12678.grid) (caps repair12678) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12678

theorem covarianceGood12678_payment :
    (retDist (paperDesignP 12678).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12678)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12678_payment



end BstLean.Part269.N12678

namespace BstLean.Part269.N12678
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12678}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12678.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12678) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12678).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12678 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12678) (by norm_num) BstLean.Part268.WorldRow12678.worldPackage rfl
    BstLean.Part268.WorldRow12678.product_lower (BstLean.Part268.WorldRow12678.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12678} (hw : c ∈ Hof BstLean.Part268.WorldRow12678.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12678) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12678) (by norm_num) BstLean.Part268.WorldRow12678.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12678} (hw : c ∈ Hof BstLean.Part268.WorldRow12678.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12678) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12678).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12678) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12678_eq : scalarRow12678.targetFrame = BstLean.Part268.agent12678.frame := by
  norm_num [scalarRow12678,BstLean.Part268.agent12678]

noncomputable def frameData12678 : BstLean.Part264b.FrameData 12678 :=
  BstLean.Part269.frameData_from_numerics (n := 12678) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12678.worldPackage rfl BstLean.Part268.WorldRow12678.product_lower (BstLean.Part268.WorldRow12678.producthi.2.trans (by norm_num))
    scalarRow12678 repair12678 covarianceInputs12678 (fun i hi => sourceNumerics12678 hi)
    BstLean.Part268.agent12678.frame targetFrame12678_eq


end BstLean.Part269.N12678

namespace BstLean.Part269.N12679
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12679 : scalarRow12679.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12679, BstLean.Part268.grid12679, BstLean.Part263.worldGrid]

theorem supplies12679 (j : Fin 43) : Supply 12679 (parameters j)
    (cellLower scalarRow12679.grid (sourceIndex j))
    (cellUpper scalarRow12679.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12679.grid grid_top_bounds12679 j

theorem radii12679 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12679.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12679 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12679 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12679.grid grid_top_bounds12679 j hθ

noncomputable def covarianceInputs12679 :
    BstLean.Part263.CovarianceInputs 12679 scalarRow12679.grid parameters (caps repair12679) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12679 grid_top_bounds12679 repair12679

noncomputable def covarianceEvent12679 : Set (AgFam 12679) :=
  BstLean.Part263.covarianceEvent 12679 scalarRow12679.grid parameters

theorem covarianceEvent12679_measurable : MeasurableSet covarianceEvent12679 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12679_payment :
    (retDist (paperDesignP 12679).toCentres).real
      (agentEv (paperDesignP 12679) covarianceEvent12679)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12679

theorem localCov12679 : BstLean.Part259.LocalCovarianceOn covarianceEvent12679
    (BstLean.Part263.cell scalarRow12679.grid) (caps repair12679) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12679

theorem covarianceGood12679_payment :
    (retDist (paperDesignP 12679).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12679)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12679_payment



end BstLean.Part269.N12679

namespace BstLean.Part269.N12679
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12679}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12679.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12679) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12679).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12679 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12679) (by norm_num) BstLean.Part268.WorldRow12679.worldPackage rfl
    BstLean.Part268.WorldRow12679.product_lower (BstLean.Part268.WorldRow12679.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12679} (hw : c ∈ Hof BstLean.Part268.WorldRow12679.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12679) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12679) (by norm_num) BstLean.Part268.WorldRow12679.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12679} (hw : c ∈ Hof BstLean.Part268.WorldRow12679.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12679) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12679).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12679) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12679_eq : scalarRow12679.targetFrame = BstLean.Part268.agent12679.frame := by
  norm_num [scalarRow12679,BstLean.Part268.agent12679]

noncomputable def frameData12679 : BstLean.Part264b.FrameData 12679 :=
  BstLean.Part269.frameData_from_numerics (n := 12679) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12679.worldPackage rfl BstLean.Part268.WorldRow12679.product_lower (BstLean.Part268.WorldRow12679.producthi.2.trans (by norm_num))
    scalarRow12679 repair12679 covarianceInputs12679 (fun i hi => sourceNumerics12679 hi)
    BstLean.Part268.agent12679.frame targetFrame12679_eq


end BstLean.Part269.N12679
