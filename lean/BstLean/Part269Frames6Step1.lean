import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World6Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs6
import BstLean.Part269Rows6
import BstLean.Part269Sources6
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12505
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12505 : scalarRow12505.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12505, BstLean.Part268.grid12505, BstLean.Part263.worldGrid]

theorem supplies12505 (j : Fin 43) : Supply 12505 (parameters j)
    (cellLower scalarRow12505.grid (sourceIndex j))
    (cellUpper scalarRow12505.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12505.grid grid_top_bounds12505 j

theorem radii12505 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12505.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12505 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12505 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12505.grid grid_top_bounds12505 j hθ

noncomputable def covarianceInputs12505 :
    BstLean.Part263.CovarianceInputs 12505 scalarRow12505.grid parameters (caps repair12505) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12505 grid_top_bounds12505 repair12505

noncomputable def covarianceEvent12505 : Set (AgFam 12505) :=
  BstLean.Part263.covarianceEvent 12505 scalarRow12505.grid parameters

theorem covarianceEvent12505_measurable : MeasurableSet covarianceEvent12505 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12505_payment :
    (retDist (paperDesignP 12505).toCentres).real
      (agentEv (paperDesignP 12505) covarianceEvent12505)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12505

theorem localCov12505 : BstLean.Part259.LocalCovarianceOn covarianceEvent12505
    (BstLean.Part263.cell scalarRow12505.grid) (caps repair12505) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12505

theorem covarianceGood12505_payment :
    (retDist (paperDesignP 12505).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12505)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12505_payment



end BstLean.Part269.N12505

namespace BstLean.Part269.N12505
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12505}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12505.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12505) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12505).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12505 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12505) (by norm_num) BstLean.Part268.WorldRow12505.worldPackage rfl
    BstLean.Part268.WorldRow12505.product_lower (BstLean.Part268.WorldRow12505.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12505} (hw : c ∈ Hof BstLean.Part268.WorldRow12505.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12505) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12505) (by norm_num) BstLean.Part268.WorldRow12505.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12505} (hw : c ∈ Hof BstLean.Part268.WorldRow12505.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12505) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12505).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12505) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12505_eq : scalarRow12505.targetFrame = BstLean.Part268.agent12505.frame := by
  norm_num [scalarRow12505,BstLean.Part268.agent12505]

noncomputable def frameData12505 : BstLean.Part264b.FrameData 12505 :=
  BstLean.Part269.frameData_from_numerics (n := 12505) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12505.worldPackage rfl BstLean.Part268.WorldRow12505.product_lower (BstLean.Part268.WorldRow12505.producthi.2.trans (by norm_num))
    scalarRow12505 repair12505 covarianceInputs12505 (fun i hi => sourceNumerics12505 hi)
    BstLean.Part268.agent12505.frame targetFrame12505_eq


end BstLean.Part269.N12505

namespace BstLean.Part269.N12506
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12506 : scalarRow12506.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12506, BstLean.Part268.grid12506, BstLean.Part263.worldGrid]

theorem supplies12506 (j : Fin 43) : Supply 12506 (parameters j)
    (cellLower scalarRow12506.grid (sourceIndex j))
    (cellUpper scalarRow12506.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12506.grid grid_top_bounds12506 j

theorem radii12506 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12506.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12506 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12506 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12506.grid grid_top_bounds12506 j hθ

noncomputable def covarianceInputs12506 :
    BstLean.Part263.CovarianceInputs 12506 scalarRow12506.grid parameters (caps repair12506) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12506 grid_top_bounds12506 repair12506

noncomputable def covarianceEvent12506 : Set (AgFam 12506) :=
  BstLean.Part263.covarianceEvent 12506 scalarRow12506.grid parameters

theorem covarianceEvent12506_measurable : MeasurableSet covarianceEvent12506 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12506_payment :
    (retDist (paperDesignP 12506).toCentres).real
      (agentEv (paperDesignP 12506) covarianceEvent12506)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12506

theorem localCov12506 : BstLean.Part259.LocalCovarianceOn covarianceEvent12506
    (BstLean.Part263.cell scalarRow12506.grid) (caps repair12506) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12506

theorem covarianceGood12506_payment :
    (retDist (paperDesignP 12506).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12506)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12506_payment



end BstLean.Part269.N12506

namespace BstLean.Part269.N12506
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12506}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12506.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12506) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12506).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12506 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12506) (by norm_num) BstLean.Part268.WorldRow12506.worldPackage rfl
    BstLean.Part268.WorldRow12506.product_lower (BstLean.Part268.WorldRow12506.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12506} (hw : c ∈ Hof BstLean.Part268.WorldRow12506.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12506) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12506) (by norm_num) BstLean.Part268.WorldRow12506.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12506} (hw : c ∈ Hof BstLean.Part268.WorldRow12506.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12506) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12506).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12506) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12506_eq : scalarRow12506.targetFrame = BstLean.Part268.agent12506.frame := by
  norm_num [scalarRow12506,BstLean.Part268.agent12506]

noncomputable def frameData12506 : BstLean.Part264b.FrameData 12506 :=
  BstLean.Part269.frameData_from_numerics (n := 12506) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12506.worldPackage rfl BstLean.Part268.WorldRow12506.product_lower (BstLean.Part268.WorldRow12506.producthi.2.trans (by norm_num))
    scalarRow12506 repair12506 covarianceInputs12506 (fun i hi => sourceNumerics12506 hi)
    BstLean.Part268.agent12506.frame targetFrame12506_eq


end BstLean.Part269.N12506

namespace BstLean.Part269.N12507
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12507 : scalarRow12507.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12507, BstLean.Part268.grid12507, BstLean.Part263.worldGrid]

theorem supplies12507 (j : Fin 43) : Supply 12507 (parameters j)
    (cellLower scalarRow12507.grid (sourceIndex j))
    (cellUpper scalarRow12507.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12507.grid grid_top_bounds12507 j

theorem radii12507 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12507.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12507 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12507 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12507.grid grid_top_bounds12507 j hθ

noncomputable def covarianceInputs12507 :
    BstLean.Part263.CovarianceInputs 12507 scalarRow12507.grid parameters (caps repair12507) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12507 grid_top_bounds12507 repair12507

noncomputable def covarianceEvent12507 : Set (AgFam 12507) :=
  BstLean.Part263.covarianceEvent 12507 scalarRow12507.grid parameters

theorem covarianceEvent12507_measurable : MeasurableSet covarianceEvent12507 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12507_payment :
    (retDist (paperDesignP 12507).toCentres).real
      (agentEv (paperDesignP 12507) covarianceEvent12507)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12507

theorem localCov12507 : BstLean.Part259.LocalCovarianceOn covarianceEvent12507
    (BstLean.Part263.cell scalarRow12507.grid) (caps repair12507) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12507

theorem covarianceGood12507_payment :
    (retDist (paperDesignP 12507).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12507)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12507_payment



end BstLean.Part269.N12507

namespace BstLean.Part269.N12507
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12507}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12507.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12507) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12507).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12507 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12507) (by norm_num) BstLean.Part268.WorldRow12507.worldPackage rfl
    BstLean.Part268.WorldRow12507.product_lower (BstLean.Part268.WorldRow12507.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12507} (hw : c ∈ Hof BstLean.Part268.WorldRow12507.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12507) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12507) (by norm_num) BstLean.Part268.WorldRow12507.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12507} (hw : c ∈ Hof BstLean.Part268.WorldRow12507.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12507) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12507).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12507) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12507_eq : scalarRow12507.targetFrame = BstLean.Part268.agent12507.frame := by
  norm_num [scalarRow12507,BstLean.Part268.agent12507]

noncomputable def frameData12507 : BstLean.Part264b.FrameData 12507 :=
  BstLean.Part269.frameData_from_numerics (n := 12507) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12507.worldPackage rfl BstLean.Part268.WorldRow12507.product_lower (BstLean.Part268.WorldRow12507.producthi.2.trans (by norm_num))
    scalarRow12507 repair12507 covarianceInputs12507 (fun i hi => sourceNumerics12507 hi)
    BstLean.Part268.agent12507.frame targetFrame12507_eq


end BstLean.Part269.N12507

namespace BstLean.Part269.N12508
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12508 : scalarRow12508.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12508, BstLean.Part268.grid12508, BstLean.Part263.worldGrid]

theorem supplies12508 (j : Fin 43) : Supply 12508 (parameters j)
    (cellLower scalarRow12508.grid (sourceIndex j))
    (cellUpper scalarRow12508.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12508.grid grid_top_bounds12508 j

theorem radii12508 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12508.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12508 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12508 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12508.grid grid_top_bounds12508 j hθ

noncomputable def covarianceInputs12508 :
    BstLean.Part263.CovarianceInputs 12508 scalarRow12508.grid parameters (caps repair12508) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12508 grid_top_bounds12508 repair12508

noncomputable def covarianceEvent12508 : Set (AgFam 12508) :=
  BstLean.Part263.covarianceEvent 12508 scalarRow12508.grid parameters

theorem covarianceEvent12508_measurable : MeasurableSet covarianceEvent12508 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12508_payment :
    (retDist (paperDesignP 12508).toCentres).real
      (agentEv (paperDesignP 12508) covarianceEvent12508)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12508

theorem localCov12508 : BstLean.Part259.LocalCovarianceOn covarianceEvent12508
    (BstLean.Part263.cell scalarRow12508.grid) (caps repair12508) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12508

theorem covarianceGood12508_payment :
    (retDist (paperDesignP 12508).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12508)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12508_payment



end BstLean.Part269.N12508

namespace BstLean.Part269.N12508
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12508}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12508.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12508) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12508).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12508 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12508) (by norm_num) BstLean.Part268.WorldRow12508.worldPackage rfl
    BstLean.Part268.WorldRow12508.product_lower (BstLean.Part268.WorldRow12508.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12508} (hw : c ∈ Hof BstLean.Part268.WorldRow12508.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12508) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12508) (by norm_num) BstLean.Part268.WorldRow12508.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12508} (hw : c ∈ Hof BstLean.Part268.WorldRow12508.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12508) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12508).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12508) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12508_eq : scalarRow12508.targetFrame = BstLean.Part268.agent12508.frame := by
  norm_num [scalarRow12508,BstLean.Part268.agent12508]

noncomputable def frameData12508 : BstLean.Part264b.FrameData 12508 :=
  BstLean.Part269.frameData_from_numerics (n := 12508) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12508.worldPackage rfl BstLean.Part268.WorldRow12508.product_lower (BstLean.Part268.WorldRow12508.producthi.2.trans (by norm_num))
    scalarRow12508 repair12508 covarianceInputs12508 (fun i hi => sourceNumerics12508 hi)
    BstLean.Part268.agent12508.frame targetFrame12508_eq


end BstLean.Part269.N12508

namespace BstLean.Part269.N12509
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12509 : scalarRow12509.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12509, BstLean.Part268.grid12509, BstLean.Part263.worldGrid]

theorem supplies12509 (j : Fin 43) : Supply 12509 (parameters j)
    (cellLower scalarRow12509.grid (sourceIndex j))
    (cellUpper scalarRow12509.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12509.grid grid_top_bounds12509 j

theorem radii12509 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12509.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12509 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12509 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12509.grid grid_top_bounds12509 j hθ

noncomputable def covarianceInputs12509 :
    BstLean.Part263.CovarianceInputs 12509 scalarRow12509.grid parameters (caps repair12509) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12509 grid_top_bounds12509 repair12509

noncomputable def covarianceEvent12509 : Set (AgFam 12509) :=
  BstLean.Part263.covarianceEvent 12509 scalarRow12509.grid parameters

theorem covarianceEvent12509_measurable : MeasurableSet covarianceEvent12509 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12509_payment :
    (retDist (paperDesignP 12509).toCentres).real
      (agentEv (paperDesignP 12509) covarianceEvent12509)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12509

theorem localCov12509 : BstLean.Part259.LocalCovarianceOn covarianceEvent12509
    (BstLean.Part263.cell scalarRow12509.grid) (caps repair12509) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12509

theorem covarianceGood12509_payment :
    (retDist (paperDesignP 12509).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12509)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12509_payment



end BstLean.Part269.N12509

namespace BstLean.Part269.N12509
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12509}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12509.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12509) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12509).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12509 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12509) (by norm_num) BstLean.Part268.WorldRow12509.worldPackage rfl
    BstLean.Part268.WorldRow12509.product_lower (BstLean.Part268.WorldRow12509.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12509} (hw : c ∈ Hof BstLean.Part268.WorldRow12509.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12509) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12509) (by norm_num) BstLean.Part268.WorldRow12509.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12509} (hw : c ∈ Hof BstLean.Part268.WorldRow12509.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12509) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12509).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12509) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12509_eq : scalarRow12509.targetFrame = BstLean.Part268.agent12509.frame := by
  norm_num [scalarRow12509,BstLean.Part268.agent12509]

noncomputable def frameData12509 : BstLean.Part264b.FrameData 12509 :=
  BstLean.Part269.frameData_from_numerics (n := 12509) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12509.worldPackage rfl BstLean.Part268.WorldRow12509.product_lower (BstLean.Part268.WorldRow12509.producthi.2.trans (by norm_num))
    scalarRow12509 repair12509 covarianceInputs12509 (fun i hi => sourceNumerics12509 hi)
    BstLean.Part268.agent12509.frame targetFrame12509_eq


end BstLean.Part269.N12509
