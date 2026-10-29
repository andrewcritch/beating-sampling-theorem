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

namespace BstLean.Part269.N12450
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12450 : scalarRow12450.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12450, BstLean.Part268.grid12450, BstLean.Part263.worldGrid]

theorem supplies12450 (j : Fin 43) : Supply 12450 (parameters j)
    (cellLower scalarRow12450.grid (sourceIndex j))
    (cellUpper scalarRow12450.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12450.grid grid_top_bounds12450 j

theorem radii12450 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12450.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12450 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12450 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12450.grid grid_top_bounds12450 j hθ

noncomputable def covarianceInputs12450 :
    BstLean.Part263.CovarianceInputs 12450 scalarRow12450.grid parameters (caps repair12450) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12450 grid_top_bounds12450 repair12450

noncomputable def covarianceEvent12450 : Set (AgFam 12450) :=
  BstLean.Part263.covarianceEvent 12450 scalarRow12450.grid parameters

theorem covarianceEvent12450_measurable : MeasurableSet covarianceEvent12450 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12450_payment :
    (retDist (paperDesignP 12450).toCentres).real
      (agentEv (paperDesignP 12450) covarianceEvent12450)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12450

theorem localCov12450 : BstLean.Part259.LocalCovarianceOn covarianceEvent12450
    (BstLean.Part263.cell scalarRow12450.grid) (caps repair12450) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12450

theorem covarianceGood12450_payment :
    (retDist (paperDesignP 12450).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12450)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12450_payment



end BstLean.Part269.N12450

namespace BstLean.Part269.N12450
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12450}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12450.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12450) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12450).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12450 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12450) (by norm_num) BstLean.Part268.WorldRow12450.worldPackage rfl
    BstLean.Part268.WorldRow12450.product_lower (BstLean.Part268.WorldRow12450.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12450} (hw : c ∈ Hof BstLean.Part268.WorldRow12450.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12450) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12450) (by norm_num) BstLean.Part268.WorldRow12450.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12450} (hw : c ∈ Hof BstLean.Part268.WorldRow12450.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12450) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12450).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12450) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12450_eq : scalarRow12450.targetFrame = BstLean.Part268.agent12450.frame := by
  norm_num [scalarRow12450,BstLean.Part268.agent12450]

noncomputable def frameData12450 : BstLean.Part264b.FrameData 12450 :=
  BstLean.Part269.frameData_from_numerics (n := 12450) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12450.worldPackage rfl BstLean.Part268.WorldRow12450.product_lower (BstLean.Part268.WorldRow12450.producthi.2.trans (by norm_num))
    scalarRow12450 repair12450 covarianceInputs12450 (fun i hi => sourceNumerics12450 hi)
    BstLean.Part268.agent12450.frame targetFrame12450_eq


end BstLean.Part269.N12450

namespace BstLean.Part269.N12451
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12451 : scalarRow12451.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12451, BstLean.Part268.grid12451, BstLean.Part263.worldGrid]

theorem supplies12451 (j : Fin 43) : Supply 12451 (parameters j)
    (cellLower scalarRow12451.grid (sourceIndex j))
    (cellUpper scalarRow12451.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12451.grid grid_top_bounds12451 j

theorem radii12451 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12451.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12451 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12451 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12451.grid grid_top_bounds12451 j hθ

noncomputable def covarianceInputs12451 :
    BstLean.Part263.CovarianceInputs 12451 scalarRow12451.grid parameters (caps repair12451) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12451 grid_top_bounds12451 repair12451

noncomputable def covarianceEvent12451 : Set (AgFam 12451) :=
  BstLean.Part263.covarianceEvent 12451 scalarRow12451.grid parameters

theorem covarianceEvent12451_measurable : MeasurableSet covarianceEvent12451 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12451_payment :
    (retDist (paperDesignP 12451).toCentres).real
      (agentEv (paperDesignP 12451) covarianceEvent12451)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12451

theorem localCov12451 : BstLean.Part259.LocalCovarianceOn covarianceEvent12451
    (BstLean.Part263.cell scalarRow12451.grid) (caps repair12451) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12451

theorem covarianceGood12451_payment :
    (retDist (paperDesignP 12451).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12451)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12451_payment



end BstLean.Part269.N12451

namespace BstLean.Part269.N12451
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12451}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12451.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12451) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12451).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12451 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12451) (by norm_num) BstLean.Part268.WorldRow12451.worldPackage rfl
    BstLean.Part268.WorldRow12451.product_lower (BstLean.Part268.WorldRow12451.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12451} (hw : c ∈ Hof BstLean.Part268.WorldRow12451.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12451) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12451) (by norm_num) BstLean.Part268.WorldRow12451.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12451} (hw : c ∈ Hof BstLean.Part268.WorldRow12451.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12451) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12451).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12451) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12451_eq : scalarRow12451.targetFrame = BstLean.Part268.agent12451.frame := by
  norm_num [scalarRow12451,BstLean.Part268.agent12451]

noncomputable def frameData12451 : BstLean.Part264b.FrameData 12451 :=
  BstLean.Part269.frameData_from_numerics (n := 12451) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12451.worldPackage rfl BstLean.Part268.WorldRow12451.product_lower (BstLean.Part268.WorldRow12451.producthi.2.trans (by norm_num))
    scalarRow12451 repair12451 covarianceInputs12451 (fun i hi => sourceNumerics12451 hi)
    BstLean.Part268.agent12451.frame targetFrame12451_eq


end BstLean.Part269.N12451

namespace BstLean.Part269.N12452
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12452 : scalarRow12452.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12452, BstLean.Part268.grid12452, BstLean.Part263.worldGrid]

theorem supplies12452 (j : Fin 43) : Supply 12452 (parameters j)
    (cellLower scalarRow12452.grid (sourceIndex j))
    (cellUpper scalarRow12452.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12452.grid grid_top_bounds12452 j

theorem radii12452 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12452.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12452 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12452 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12452.grid grid_top_bounds12452 j hθ

noncomputable def covarianceInputs12452 :
    BstLean.Part263.CovarianceInputs 12452 scalarRow12452.grid parameters (caps repair12452) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12452 grid_top_bounds12452 repair12452

noncomputable def covarianceEvent12452 : Set (AgFam 12452) :=
  BstLean.Part263.covarianceEvent 12452 scalarRow12452.grid parameters

theorem covarianceEvent12452_measurable : MeasurableSet covarianceEvent12452 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12452_payment :
    (retDist (paperDesignP 12452).toCentres).real
      (agentEv (paperDesignP 12452) covarianceEvent12452)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12452

theorem localCov12452 : BstLean.Part259.LocalCovarianceOn covarianceEvent12452
    (BstLean.Part263.cell scalarRow12452.grid) (caps repair12452) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12452

theorem covarianceGood12452_payment :
    (retDist (paperDesignP 12452).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12452)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12452_payment



end BstLean.Part269.N12452

namespace BstLean.Part269.N12452
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12452}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12452.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12452) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12452).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12452 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12452) (by norm_num) BstLean.Part268.WorldRow12452.worldPackage rfl
    BstLean.Part268.WorldRow12452.product_lower (BstLean.Part268.WorldRow12452.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12452} (hw : c ∈ Hof BstLean.Part268.WorldRow12452.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12452) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12452) (by norm_num) BstLean.Part268.WorldRow12452.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12452} (hw : c ∈ Hof BstLean.Part268.WorldRow12452.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12452) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12452).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12452) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12452_eq : scalarRow12452.targetFrame = BstLean.Part268.agent12452.frame := by
  norm_num [scalarRow12452,BstLean.Part268.agent12452]

noncomputable def frameData12452 : BstLean.Part264b.FrameData 12452 :=
  BstLean.Part269.frameData_from_numerics (n := 12452) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12452.worldPackage rfl BstLean.Part268.WorldRow12452.product_lower (BstLean.Part268.WorldRow12452.producthi.2.trans (by norm_num))
    scalarRow12452 repair12452 covarianceInputs12452 (fun i hi => sourceNumerics12452 hi)
    BstLean.Part268.agent12452.frame targetFrame12452_eq


end BstLean.Part269.N12452

namespace BstLean.Part269.N12453
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12453 : scalarRow12453.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12453, BstLean.Part268.grid12453, BstLean.Part263.worldGrid]

theorem supplies12453 (j : Fin 43) : Supply 12453 (parameters j)
    (cellLower scalarRow12453.grid (sourceIndex j))
    (cellUpper scalarRow12453.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12453.grid grid_top_bounds12453 j

theorem radii12453 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12453.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12453 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12453 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12453.grid grid_top_bounds12453 j hθ

noncomputable def covarianceInputs12453 :
    BstLean.Part263.CovarianceInputs 12453 scalarRow12453.grid parameters (caps repair12453) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12453 grid_top_bounds12453 repair12453

noncomputable def covarianceEvent12453 : Set (AgFam 12453) :=
  BstLean.Part263.covarianceEvent 12453 scalarRow12453.grid parameters

theorem covarianceEvent12453_measurable : MeasurableSet covarianceEvent12453 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12453_payment :
    (retDist (paperDesignP 12453).toCentres).real
      (agentEv (paperDesignP 12453) covarianceEvent12453)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12453

theorem localCov12453 : BstLean.Part259.LocalCovarianceOn covarianceEvent12453
    (BstLean.Part263.cell scalarRow12453.grid) (caps repair12453) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12453

theorem covarianceGood12453_payment :
    (retDist (paperDesignP 12453).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12453)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12453_payment



end BstLean.Part269.N12453

namespace BstLean.Part269.N12453
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12453}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12453.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12453) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12453).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12453 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12453) (by norm_num) BstLean.Part268.WorldRow12453.worldPackage rfl
    BstLean.Part268.WorldRow12453.product_lower (BstLean.Part268.WorldRow12453.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12453} (hw : c ∈ Hof BstLean.Part268.WorldRow12453.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12453) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12453) (by norm_num) BstLean.Part268.WorldRow12453.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12453} (hw : c ∈ Hof BstLean.Part268.WorldRow12453.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12453) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12453).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12453) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12453_eq : scalarRow12453.targetFrame = BstLean.Part268.agent12453.frame := by
  norm_num [scalarRow12453,BstLean.Part268.agent12453]

noncomputable def frameData12453 : BstLean.Part264b.FrameData 12453 :=
  BstLean.Part269.frameData_from_numerics (n := 12453) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12453.worldPackage rfl BstLean.Part268.WorldRow12453.product_lower (BstLean.Part268.WorldRow12453.producthi.2.trans (by norm_num))
    scalarRow12453 repair12453 covarianceInputs12453 (fun i hi => sourceNumerics12453 hi)
    BstLean.Part268.agent12453.frame targetFrame12453_eq


end BstLean.Part269.N12453

namespace BstLean.Part269.N12454
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12454 : scalarRow12454.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12454, BstLean.Part268.grid12454, BstLean.Part263.worldGrid]

theorem supplies12454 (j : Fin 43) : Supply 12454 (parameters j)
    (cellLower scalarRow12454.grid (sourceIndex j))
    (cellUpper scalarRow12454.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12454.grid grid_top_bounds12454 j

theorem radii12454 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12454.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12454 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12454 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12454.grid grid_top_bounds12454 j hθ

noncomputable def covarianceInputs12454 :
    BstLean.Part263.CovarianceInputs 12454 scalarRow12454.grid parameters (caps repair12454) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12454 grid_top_bounds12454 repair12454

noncomputable def covarianceEvent12454 : Set (AgFam 12454) :=
  BstLean.Part263.covarianceEvent 12454 scalarRow12454.grid parameters

theorem covarianceEvent12454_measurable : MeasurableSet covarianceEvent12454 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12454_payment :
    (retDist (paperDesignP 12454).toCentres).real
      (agentEv (paperDesignP 12454) covarianceEvent12454)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12454

theorem localCov12454 : BstLean.Part259.LocalCovarianceOn covarianceEvent12454
    (BstLean.Part263.cell scalarRow12454.grid) (caps repair12454) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12454

theorem covarianceGood12454_payment :
    (retDist (paperDesignP 12454).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12454)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12454_payment



end BstLean.Part269.N12454

namespace BstLean.Part269.N12454
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12454}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12454.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12454) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12454).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12454 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12454) (by norm_num) BstLean.Part268.WorldRow12454.worldPackage rfl
    BstLean.Part268.WorldRow12454.product_lower (BstLean.Part268.WorldRow12454.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12454} (hw : c ∈ Hof BstLean.Part268.WorldRow12454.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12454) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12454) (by norm_num) BstLean.Part268.WorldRow12454.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12454} (hw : c ∈ Hof BstLean.Part268.WorldRow12454.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12454) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12454).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12454) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12454_eq : scalarRow12454.targetFrame = BstLean.Part268.agent12454.frame := by
  norm_num [scalarRow12454,BstLean.Part268.agent12454]

noncomputable def frameData12454 : BstLean.Part264b.FrameData 12454 :=
  BstLean.Part269.frameData_from_numerics (n := 12454) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12454.worldPackage rfl BstLean.Part268.WorldRow12454.product_lower (BstLean.Part268.WorldRow12454.producthi.2.trans (by norm_num))
    scalarRow12454 repair12454 covarianceInputs12454 (fun i hi => sourceNumerics12454 hi)
    BstLean.Part268.agent12454.frame targetFrame12454_eq


end BstLean.Part269.N12454
