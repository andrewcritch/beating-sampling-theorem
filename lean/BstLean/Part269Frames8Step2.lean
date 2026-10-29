import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World8Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs8
import BstLean.Part269Rows8
import BstLean.Part269Sources8
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12560
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12560 : scalarRow12560.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12560, BstLean.Part268.grid12560, BstLean.Part263.worldGrid]

theorem supplies12560 (j : Fin 43) : Supply 12560 (parameters j)
    (cellLower scalarRow12560.grid (sourceIndex j))
    (cellUpper scalarRow12560.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12560.grid grid_top_bounds12560 j

theorem radii12560 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12560.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12560 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12560 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12560.grid grid_top_bounds12560 j hθ

noncomputable def covarianceInputs12560 :
    BstLean.Part263.CovarianceInputs 12560 scalarRow12560.grid parameters (caps repair12560) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12560 grid_top_bounds12560 repair12560

noncomputable def covarianceEvent12560 : Set (AgFam 12560) :=
  BstLean.Part263.covarianceEvent 12560 scalarRow12560.grid parameters

theorem covarianceEvent12560_measurable : MeasurableSet covarianceEvent12560 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12560_payment :
    (retDist (paperDesignP 12560).toCentres).real
      (agentEv (paperDesignP 12560) covarianceEvent12560)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12560

theorem localCov12560 : BstLean.Part259.LocalCovarianceOn covarianceEvent12560
    (BstLean.Part263.cell scalarRow12560.grid) (caps repair12560) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12560

theorem covarianceGood12560_payment :
    (retDist (paperDesignP 12560).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12560)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12560_payment



end BstLean.Part269.N12560

namespace BstLean.Part269.N12560
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12560}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12560.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12560) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12560).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12560 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12560) (by norm_num) BstLean.Part268.WorldRow12560.worldPackage rfl
    BstLean.Part268.WorldRow12560.product_lower (BstLean.Part268.WorldRow12560.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12560} (hw : c ∈ Hof BstLean.Part268.WorldRow12560.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12560) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12560) (by norm_num) BstLean.Part268.WorldRow12560.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12560} (hw : c ∈ Hof BstLean.Part268.WorldRow12560.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12560) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12560).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12560) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12560_eq : scalarRow12560.targetFrame = BstLean.Part268.agent12560.frame := by
  norm_num [scalarRow12560,BstLean.Part268.agent12560]

noncomputable def frameData12560 : BstLean.Part264b.FrameData 12560 :=
  BstLean.Part269.frameData_from_numerics (n := 12560) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12560.worldPackage rfl BstLean.Part268.WorldRow12560.product_lower (BstLean.Part268.WorldRow12560.producthi.2.trans (by norm_num))
    scalarRow12560 repair12560 covarianceInputs12560 (fun i hi => sourceNumerics12560 hi)
    BstLean.Part268.agent12560.frame targetFrame12560_eq


end BstLean.Part269.N12560

namespace BstLean.Part269.N12561
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12561 : scalarRow12561.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12561, BstLean.Part268.grid12561, BstLean.Part263.worldGrid]

theorem supplies12561 (j : Fin 43) : Supply 12561 (parameters j)
    (cellLower scalarRow12561.grid (sourceIndex j))
    (cellUpper scalarRow12561.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12561.grid grid_top_bounds12561 j

theorem radii12561 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12561.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12561 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12561 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12561.grid grid_top_bounds12561 j hθ

noncomputable def covarianceInputs12561 :
    BstLean.Part263.CovarianceInputs 12561 scalarRow12561.grid parameters (caps repair12561) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12561 grid_top_bounds12561 repair12561

noncomputable def covarianceEvent12561 : Set (AgFam 12561) :=
  BstLean.Part263.covarianceEvent 12561 scalarRow12561.grid parameters

theorem covarianceEvent12561_measurable : MeasurableSet covarianceEvent12561 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12561_payment :
    (retDist (paperDesignP 12561).toCentres).real
      (agentEv (paperDesignP 12561) covarianceEvent12561)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12561

theorem localCov12561 : BstLean.Part259.LocalCovarianceOn covarianceEvent12561
    (BstLean.Part263.cell scalarRow12561.grid) (caps repair12561) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12561

theorem covarianceGood12561_payment :
    (retDist (paperDesignP 12561).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12561)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12561_payment



end BstLean.Part269.N12561

namespace BstLean.Part269.N12561
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12561}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12561.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12561) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12561).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12561 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12561) (by norm_num) BstLean.Part268.WorldRow12561.worldPackage rfl
    BstLean.Part268.WorldRow12561.product_lower (BstLean.Part268.WorldRow12561.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12561} (hw : c ∈ Hof BstLean.Part268.WorldRow12561.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12561) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12561) (by norm_num) BstLean.Part268.WorldRow12561.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12561} (hw : c ∈ Hof BstLean.Part268.WorldRow12561.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12561) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12561).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12561) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12561_eq : scalarRow12561.targetFrame = BstLean.Part268.agent12561.frame := by
  norm_num [scalarRow12561,BstLean.Part268.agent12561]

noncomputable def frameData12561 : BstLean.Part264b.FrameData 12561 :=
  BstLean.Part269.frameData_from_numerics (n := 12561) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12561.worldPackage rfl BstLean.Part268.WorldRow12561.product_lower (BstLean.Part268.WorldRow12561.producthi.2.trans (by norm_num))
    scalarRow12561 repair12561 covarianceInputs12561 (fun i hi => sourceNumerics12561 hi)
    BstLean.Part268.agent12561.frame targetFrame12561_eq


end BstLean.Part269.N12561

namespace BstLean.Part269.N12562
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12562 : scalarRow12562.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12562, BstLean.Part268.grid12562, BstLean.Part263.worldGrid]

theorem supplies12562 (j : Fin 43) : Supply 12562 (parameters j)
    (cellLower scalarRow12562.grid (sourceIndex j))
    (cellUpper scalarRow12562.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12562.grid grid_top_bounds12562 j

theorem radii12562 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12562.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12562 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12562 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12562.grid grid_top_bounds12562 j hθ

noncomputable def covarianceInputs12562 :
    BstLean.Part263.CovarianceInputs 12562 scalarRow12562.grid parameters (caps repair12562) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12562 grid_top_bounds12562 repair12562

noncomputable def covarianceEvent12562 : Set (AgFam 12562) :=
  BstLean.Part263.covarianceEvent 12562 scalarRow12562.grid parameters

theorem covarianceEvent12562_measurable : MeasurableSet covarianceEvent12562 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12562_payment :
    (retDist (paperDesignP 12562).toCentres).real
      (agentEv (paperDesignP 12562) covarianceEvent12562)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12562

theorem localCov12562 : BstLean.Part259.LocalCovarianceOn covarianceEvent12562
    (BstLean.Part263.cell scalarRow12562.grid) (caps repair12562) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12562

theorem covarianceGood12562_payment :
    (retDist (paperDesignP 12562).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12562)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12562_payment



end BstLean.Part269.N12562

namespace BstLean.Part269.N12562
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12562}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12562.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12562) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12562).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12562 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12562) (by norm_num) BstLean.Part268.WorldRow12562.worldPackage rfl
    BstLean.Part268.WorldRow12562.product_lower (BstLean.Part268.WorldRow12562.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12562} (hw : c ∈ Hof BstLean.Part268.WorldRow12562.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12562) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12562) (by norm_num) BstLean.Part268.WorldRow12562.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12562} (hw : c ∈ Hof BstLean.Part268.WorldRow12562.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12562) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12562).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12562) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12562_eq : scalarRow12562.targetFrame = BstLean.Part268.agent12562.frame := by
  norm_num [scalarRow12562,BstLean.Part268.agent12562]

noncomputable def frameData12562 : BstLean.Part264b.FrameData 12562 :=
  BstLean.Part269.frameData_from_numerics (n := 12562) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12562.worldPackage rfl BstLean.Part268.WorldRow12562.product_lower (BstLean.Part268.WorldRow12562.producthi.2.trans (by norm_num))
    scalarRow12562 repair12562 covarianceInputs12562 (fun i hi => sourceNumerics12562 hi)
    BstLean.Part268.agent12562.frame targetFrame12562_eq


end BstLean.Part269.N12562

namespace BstLean.Part269.N12563
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12563 : scalarRow12563.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12563, BstLean.Part268.grid12563, BstLean.Part263.worldGrid]

theorem supplies12563 (j : Fin 43) : Supply 12563 (parameters j)
    (cellLower scalarRow12563.grid (sourceIndex j))
    (cellUpper scalarRow12563.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12563.grid grid_top_bounds12563 j

theorem radii12563 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12563.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12563 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12563 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12563.grid grid_top_bounds12563 j hθ

noncomputable def covarianceInputs12563 :
    BstLean.Part263.CovarianceInputs 12563 scalarRow12563.grid parameters (caps repair12563) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12563 grid_top_bounds12563 repair12563

noncomputable def covarianceEvent12563 : Set (AgFam 12563) :=
  BstLean.Part263.covarianceEvent 12563 scalarRow12563.grid parameters

theorem covarianceEvent12563_measurable : MeasurableSet covarianceEvent12563 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12563_payment :
    (retDist (paperDesignP 12563).toCentres).real
      (agentEv (paperDesignP 12563) covarianceEvent12563)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12563

theorem localCov12563 : BstLean.Part259.LocalCovarianceOn covarianceEvent12563
    (BstLean.Part263.cell scalarRow12563.grid) (caps repair12563) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12563

theorem covarianceGood12563_payment :
    (retDist (paperDesignP 12563).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12563)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12563_payment



end BstLean.Part269.N12563

namespace BstLean.Part269.N12563
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12563}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12563.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12563) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12563).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12563 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12563) (by norm_num) BstLean.Part268.WorldRow12563.worldPackage rfl
    BstLean.Part268.WorldRow12563.product_lower (BstLean.Part268.WorldRow12563.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12563} (hw : c ∈ Hof BstLean.Part268.WorldRow12563.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12563) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12563) (by norm_num) BstLean.Part268.WorldRow12563.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12563} (hw : c ∈ Hof BstLean.Part268.WorldRow12563.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12563) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12563).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12563) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12563_eq : scalarRow12563.targetFrame = BstLean.Part268.agent12563.frame := by
  norm_num [scalarRow12563,BstLean.Part268.agent12563]

noncomputable def frameData12563 : BstLean.Part264b.FrameData 12563 :=
  BstLean.Part269.frameData_from_numerics (n := 12563) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12563.worldPackage rfl BstLean.Part268.WorldRow12563.product_lower (BstLean.Part268.WorldRow12563.producthi.2.trans (by norm_num))
    scalarRow12563 repair12563 covarianceInputs12563 (fun i hi => sourceNumerics12563 hi)
    BstLean.Part268.agent12563.frame targetFrame12563_eq


end BstLean.Part269.N12563

namespace BstLean.Part269.N12564
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12564 : scalarRow12564.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12564, BstLean.Part268.grid12564, BstLean.Part263.worldGrid]

theorem supplies12564 (j : Fin 43) : Supply 12564 (parameters j)
    (cellLower scalarRow12564.grid (sourceIndex j))
    (cellUpper scalarRow12564.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12564.grid grid_top_bounds12564 j

theorem radii12564 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12564.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12564 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12564 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12564.grid grid_top_bounds12564 j hθ

noncomputable def covarianceInputs12564 :
    BstLean.Part263.CovarianceInputs 12564 scalarRow12564.grid parameters (caps repair12564) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12564 grid_top_bounds12564 repair12564

noncomputable def covarianceEvent12564 : Set (AgFam 12564) :=
  BstLean.Part263.covarianceEvent 12564 scalarRow12564.grid parameters

theorem covarianceEvent12564_measurable : MeasurableSet covarianceEvent12564 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12564_payment :
    (retDist (paperDesignP 12564).toCentres).real
      (agentEv (paperDesignP 12564) covarianceEvent12564)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12564

theorem localCov12564 : BstLean.Part259.LocalCovarianceOn covarianceEvent12564
    (BstLean.Part263.cell scalarRow12564.grid) (caps repair12564) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12564

theorem covarianceGood12564_payment :
    (retDist (paperDesignP 12564).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12564)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12564_payment



end BstLean.Part269.N12564

namespace BstLean.Part269.N12564
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12564}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12564.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12564) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12564).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12564 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12564) (by norm_num) BstLean.Part268.WorldRow12564.worldPackage rfl
    BstLean.Part268.WorldRow12564.product_lower (BstLean.Part268.WorldRow12564.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12564} (hw : c ∈ Hof BstLean.Part268.WorldRow12564.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12564) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12564) (by norm_num) BstLean.Part268.WorldRow12564.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12564} (hw : c ∈ Hof BstLean.Part268.WorldRow12564.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12564) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12564).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12564) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12564_eq : scalarRow12564.targetFrame = BstLean.Part268.agent12564.frame := by
  norm_num [scalarRow12564,BstLean.Part268.agent12564]

noncomputable def frameData12564 : BstLean.Part264b.FrameData 12564 :=
  BstLean.Part269.frameData_from_numerics (n := 12564) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12564.worldPackage rfl BstLean.Part268.WorldRow12564.product_lower (BstLean.Part268.WorldRow12564.producthi.2.trans (by norm_num))
    scalarRow12564 repair12564 covarianceInputs12564 (fun i hi => sourceNumerics12564 hi)
    BstLean.Part268.agent12564.frame targetFrame12564_eq


end BstLean.Part269.N12564
