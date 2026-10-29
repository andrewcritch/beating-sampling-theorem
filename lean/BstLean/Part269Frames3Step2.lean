import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World3Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs3
import BstLean.Part269Rows3
import BstLean.Part269Sources3
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12435
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12435 : scalarRow12435.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12435, BstLean.Part268.grid12435, BstLean.Part263.worldGrid]

theorem supplies12435 (j : Fin 43) : Supply 12435 (parameters j)
    (cellLower scalarRow12435.grid (sourceIndex j))
    (cellUpper scalarRow12435.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12435.grid grid_top_bounds12435 j

theorem radii12435 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12435.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12435 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12435 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12435.grid grid_top_bounds12435 j hθ

noncomputable def covarianceInputs12435 :
    BstLean.Part263.CovarianceInputs 12435 scalarRow12435.grid parameters (caps repair12435) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12435 grid_top_bounds12435 repair12435

noncomputable def covarianceEvent12435 : Set (AgFam 12435) :=
  BstLean.Part263.covarianceEvent 12435 scalarRow12435.grid parameters

theorem covarianceEvent12435_measurable : MeasurableSet covarianceEvent12435 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12435_payment :
    (retDist (paperDesignP 12435).toCentres).real
      (agentEv (paperDesignP 12435) covarianceEvent12435)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12435

theorem localCov12435 : BstLean.Part259.LocalCovarianceOn covarianceEvent12435
    (BstLean.Part263.cell scalarRow12435.grid) (caps repair12435) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12435

theorem covarianceGood12435_payment :
    (retDist (paperDesignP 12435).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12435)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12435_payment



end BstLean.Part269.N12435

namespace BstLean.Part269.N12435
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12435}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12435.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12435) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12435).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12435 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12435) (by norm_num) BstLean.Part268.WorldRow12435.worldPackage rfl
    BstLean.Part268.WorldRow12435.product_lower (BstLean.Part268.WorldRow12435.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12435} (hw : c ∈ Hof BstLean.Part268.WorldRow12435.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12435) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12435) (by norm_num) BstLean.Part268.WorldRow12435.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12435} (hw : c ∈ Hof BstLean.Part268.WorldRow12435.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12435) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12435).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12435) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12435_eq : scalarRow12435.targetFrame = BstLean.Part268.agent12435.frame := by
  norm_num [scalarRow12435,BstLean.Part268.agent12435]

noncomputable def frameData12435 : BstLean.Part264b.FrameData 12435 :=
  BstLean.Part269.frameData_from_numerics (n := 12435) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12435.worldPackage rfl BstLean.Part268.WorldRow12435.product_lower (BstLean.Part268.WorldRow12435.producthi.2.trans (by norm_num))
    scalarRow12435 repair12435 covarianceInputs12435 (fun i hi => sourceNumerics12435 hi)
    BstLean.Part268.agent12435.frame targetFrame12435_eq


end BstLean.Part269.N12435

namespace BstLean.Part269.N12436
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12436 : scalarRow12436.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12436, BstLean.Part268.grid12436, BstLean.Part263.worldGrid]

theorem supplies12436 (j : Fin 43) : Supply 12436 (parameters j)
    (cellLower scalarRow12436.grid (sourceIndex j))
    (cellUpper scalarRow12436.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12436.grid grid_top_bounds12436 j

theorem radii12436 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12436.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12436 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12436 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12436.grid grid_top_bounds12436 j hθ

noncomputable def covarianceInputs12436 :
    BstLean.Part263.CovarianceInputs 12436 scalarRow12436.grid parameters (caps repair12436) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12436 grid_top_bounds12436 repair12436

noncomputable def covarianceEvent12436 : Set (AgFam 12436) :=
  BstLean.Part263.covarianceEvent 12436 scalarRow12436.grid parameters

theorem covarianceEvent12436_measurable : MeasurableSet covarianceEvent12436 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12436_payment :
    (retDist (paperDesignP 12436).toCentres).real
      (agentEv (paperDesignP 12436) covarianceEvent12436)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12436

theorem localCov12436 : BstLean.Part259.LocalCovarianceOn covarianceEvent12436
    (BstLean.Part263.cell scalarRow12436.grid) (caps repair12436) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12436

theorem covarianceGood12436_payment :
    (retDist (paperDesignP 12436).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12436)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12436_payment



end BstLean.Part269.N12436

namespace BstLean.Part269.N12436
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12436}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12436.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12436) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12436).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12436 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12436) (by norm_num) BstLean.Part268.WorldRow12436.worldPackage rfl
    BstLean.Part268.WorldRow12436.product_lower (BstLean.Part268.WorldRow12436.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12436} (hw : c ∈ Hof BstLean.Part268.WorldRow12436.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12436) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12436) (by norm_num) BstLean.Part268.WorldRow12436.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12436} (hw : c ∈ Hof BstLean.Part268.WorldRow12436.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12436) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12436).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12436) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12436_eq : scalarRow12436.targetFrame = BstLean.Part268.agent12436.frame := by
  norm_num [scalarRow12436,BstLean.Part268.agent12436]

noncomputable def frameData12436 : BstLean.Part264b.FrameData 12436 :=
  BstLean.Part269.frameData_from_numerics (n := 12436) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12436.worldPackage rfl BstLean.Part268.WorldRow12436.product_lower (BstLean.Part268.WorldRow12436.producthi.2.trans (by norm_num))
    scalarRow12436 repair12436 covarianceInputs12436 (fun i hi => sourceNumerics12436 hi)
    BstLean.Part268.agent12436.frame targetFrame12436_eq


end BstLean.Part269.N12436

namespace BstLean.Part269.N12437
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12437 : scalarRow12437.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12437, BstLean.Part268.grid12437, BstLean.Part263.worldGrid]

theorem supplies12437 (j : Fin 43) : Supply 12437 (parameters j)
    (cellLower scalarRow12437.grid (sourceIndex j))
    (cellUpper scalarRow12437.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12437.grid grid_top_bounds12437 j

theorem radii12437 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12437.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12437 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12437 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12437.grid grid_top_bounds12437 j hθ

noncomputable def covarianceInputs12437 :
    BstLean.Part263.CovarianceInputs 12437 scalarRow12437.grid parameters (caps repair12437) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12437 grid_top_bounds12437 repair12437

noncomputable def covarianceEvent12437 : Set (AgFam 12437) :=
  BstLean.Part263.covarianceEvent 12437 scalarRow12437.grid parameters

theorem covarianceEvent12437_measurable : MeasurableSet covarianceEvent12437 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12437_payment :
    (retDist (paperDesignP 12437).toCentres).real
      (agentEv (paperDesignP 12437) covarianceEvent12437)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12437

theorem localCov12437 : BstLean.Part259.LocalCovarianceOn covarianceEvent12437
    (BstLean.Part263.cell scalarRow12437.grid) (caps repair12437) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12437

theorem covarianceGood12437_payment :
    (retDist (paperDesignP 12437).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12437)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12437_payment



end BstLean.Part269.N12437

namespace BstLean.Part269.N12437
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12437}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12437.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12437) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12437).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12437 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12437) (by norm_num) BstLean.Part268.WorldRow12437.worldPackage rfl
    BstLean.Part268.WorldRow12437.product_lower (BstLean.Part268.WorldRow12437.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12437} (hw : c ∈ Hof BstLean.Part268.WorldRow12437.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12437) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12437) (by norm_num) BstLean.Part268.WorldRow12437.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12437} (hw : c ∈ Hof BstLean.Part268.WorldRow12437.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12437) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12437).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12437) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12437_eq : scalarRow12437.targetFrame = BstLean.Part268.agent12437.frame := by
  norm_num [scalarRow12437,BstLean.Part268.agent12437]

noncomputable def frameData12437 : BstLean.Part264b.FrameData 12437 :=
  BstLean.Part269.frameData_from_numerics (n := 12437) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12437.worldPackage rfl BstLean.Part268.WorldRow12437.product_lower (BstLean.Part268.WorldRow12437.producthi.2.trans (by norm_num))
    scalarRow12437 repair12437 covarianceInputs12437 (fun i hi => sourceNumerics12437 hi)
    BstLean.Part268.agent12437.frame targetFrame12437_eq


end BstLean.Part269.N12437

namespace BstLean.Part269.N12438
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12438 : scalarRow12438.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12438, BstLean.Part268.grid12438, BstLean.Part263.worldGrid]

theorem supplies12438 (j : Fin 43) : Supply 12438 (parameters j)
    (cellLower scalarRow12438.grid (sourceIndex j))
    (cellUpper scalarRow12438.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12438.grid grid_top_bounds12438 j

theorem radii12438 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12438.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12438 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12438 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12438.grid grid_top_bounds12438 j hθ

noncomputable def covarianceInputs12438 :
    BstLean.Part263.CovarianceInputs 12438 scalarRow12438.grid parameters (caps repair12438) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12438 grid_top_bounds12438 repair12438

noncomputable def covarianceEvent12438 : Set (AgFam 12438) :=
  BstLean.Part263.covarianceEvent 12438 scalarRow12438.grid parameters

theorem covarianceEvent12438_measurable : MeasurableSet covarianceEvent12438 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12438_payment :
    (retDist (paperDesignP 12438).toCentres).real
      (agentEv (paperDesignP 12438) covarianceEvent12438)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12438

theorem localCov12438 : BstLean.Part259.LocalCovarianceOn covarianceEvent12438
    (BstLean.Part263.cell scalarRow12438.grid) (caps repair12438) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12438

theorem covarianceGood12438_payment :
    (retDist (paperDesignP 12438).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12438)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12438_payment



end BstLean.Part269.N12438

namespace BstLean.Part269.N12438
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12438}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12438.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12438) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12438).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12438 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12438) (by norm_num) BstLean.Part268.WorldRow12438.worldPackage rfl
    BstLean.Part268.WorldRow12438.product_lower (BstLean.Part268.WorldRow12438.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12438} (hw : c ∈ Hof BstLean.Part268.WorldRow12438.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12438) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12438) (by norm_num) BstLean.Part268.WorldRow12438.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12438} (hw : c ∈ Hof BstLean.Part268.WorldRow12438.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12438) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12438).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12438) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12438_eq : scalarRow12438.targetFrame = BstLean.Part268.agent12438.frame := by
  norm_num [scalarRow12438,BstLean.Part268.agent12438]

noncomputable def frameData12438 : BstLean.Part264b.FrameData 12438 :=
  BstLean.Part269.frameData_from_numerics (n := 12438) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12438.worldPackage rfl BstLean.Part268.WorldRow12438.product_lower (BstLean.Part268.WorldRow12438.producthi.2.trans (by norm_num))
    scalarRow12438 repair12438 covarianceInputs12438 (fun i hi => sourceNumerics12438 hi)
    BstLean.Part268.agent12438.frame targetFrame12438_eq


end BstLean.Part269.N12438

namespace BstLean.Part269.N12439
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12439 : scalarRow12439.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12439, BstLean.Part268.grid12439, BstLean.Part263.worldGrid]

theorem supplies12439 (j : Fin 43) : Supply 12439 (parameters j)
    (cellLower scalarRow12439.grid (sourceIndex j))
    (cellUpper scalarRow12439.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12439.grid grid_top_bounds12439 j

theorem radii12439 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12439.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12439 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12439 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12439.grid grid_top_bounds12439 j hθ

noncomputable def covarianceInputs12439 :
    BstLean.Part263.CovarianceInputs 12439 scalarRow12439.grid parameters (caps repair12439) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12439 grid_top_bounds12439 repair12439

noncomputable def covarianceEvent12439 : Set (AgFam 12439) :=
  BstLean.Part263.covarianceEvent 12439 scalarRow12439.grid parameters

theorem covarianceEvent12439_measurable : MeasurableSet covarianceEvent12439 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12439_payment :
    (retDist (paperDesignP 12439).toCentres).real
      (agentEv (paperDesignP 12439) covarianceEvent12439)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12439

theorem localCov12439 : BstLean.Part259.LocalCovarianceOn covarianceEvent12439
    (BstLean.Part263.cell scalarRow12439.grid) (caps repair12439) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12439

theorem covarianceGood12439_payment :
    (retDist (paperDesignP 12439).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12439)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12439_payment



end BstLean.Part269.N12439

namespace BstLean.Part269.N12439
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12439}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12439.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12439) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12439).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12439 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12439) (by norm_num) BstLean.Part268.WorldRow12439.worldPackage rfl
    BstLean.Part268.WorldRow12439.product_lower (BstLean.Part268.WorldRow12439.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12439} (hw : c ∈ Hof BstLean.Part268.WorldRow12439.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12439) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12439) (by norm_num) BstLean.Part268.WorldRow12439.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12439} (hw : c ∈ Hof BstLean.Part268.WorldRow12439.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12439) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12439).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12439) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12439_eq : scalarRow12439.targetFrame = BstLean.Part268.agent12439.frame := by
  norm_num [scalarRow12439,BstLean.Part268.agent12439]

noncomputable def frameData12439 : BstLean.Part264b.FrameData 12439 :=
  BstLean.Part269.frameData_from_numerics (n := 12439) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12439.worldPackage rfl BstLean.Part268.WorldRow12439.product_lower (BstLean.Part268.WorldRow12439.producthi.2.trans (by norm_num))
    scalarRow12439 repair12439 covarianceInputs12439 (fun i hi => sourceNumerics12439 hi)
    BstLean.Part268.agent12439.frame targetFrame12439_eq


end BstLean.Part269.N12439
