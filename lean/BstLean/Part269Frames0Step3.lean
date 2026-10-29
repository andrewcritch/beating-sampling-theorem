import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World0Step6
import BstLean.Part269BlockSupplies0
import BstLean.Part269Frame12350
import BstLean.Part269FrameAdapter
import BstLean.Part269Geometry0_0
import BstLean.Part269Geometry0_1
import BstLean.Part269Repairs0
import BstLean.Part269Rows0
import BstLean.Part269Sources0

namespace BstLean.Part269.N12366
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12366 : scalarRow12366.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12366, BstLean.Part268.grid12366, BstLean.Part263.worldGrid]

theorem supplies12366 (j : Fin 43) : Supply 12366 (parameters j)
    (cellLower scalarRow12366.grid (sourceIndex j))
    (cellUpper scalarRow12366.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12366.grid grid_top_bounds12366 j

theorem radii12366 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12366.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12366 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12366 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12366.grid grid_top_bounds12366 j hθ

noncomputable def covarianceInputs12366 :
    BstLean.Part263.CovarianceInputs 12366 scalarRow12366.grid parameters (caps repair12366) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12366 grid_top_bounds12366 repair12366

noncomputable def covarianceEvent12366 : Set (AgFam 12366) :=
  BstLean.Part263.covarianceEvent 12366 scalarRow12366.grid parameters

theorem covarianceEvent12366_measurable : MeasurableSet covarianceEvent12366 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12366_payment :
    (retDist (paperDesignP 12366).toCentres).real
      (agentEv (paperDesignP 12366) covarianceEvent12366)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12366

theorem localCov12366 : BstLean.Part259.LocalCovarianceOn covarianceEvent12366
    (BstLean.Part263.cell scalarRow12366.grid) (caps repair12366) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12366

theorem covarianceGood12366_payment :
    (retDist (paperDesignP 12366).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12366)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12366_payment



end BstLean.Part269.N12366

namespace BstLean.Part269.N12366
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12366}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12366.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12366) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12366).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12366 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12366) (by norm_num) BstLean.Part268.WorldRow12366.worldPackage rfl
    BstLean.Part268.WorldRow12366.product_lower (BstLean.Part268.WorldRow12366.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12366} (hw : c ∈ Hof BstLean.Part268.WorldRow12366.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12366) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12366) (by norm_num) BstLean.Part268.WorldRow12366.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12366} (hw : c ∈ Hof BstLean.Part268.WorldRow12366.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12366) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12366).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12366) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12366_eq : scalarRow12366.targetFrame = BstLean.Part268.agent12366.frame := by
  norm_num [scalarRow12366,BstLean.Part268.agent12366]

noncomputable def frameData12366 : BstLean.Part264b.FrameData 12366 :=
  BstLean.Part269.frameData_from_numerics (n := 12366) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12366.worldPackage rfl BstLean.Part268.WorldRow12366.product_lower (BstLean.Part268.WorldRow12366.producthi.2.trans (by norm_num))
    scalarRow12366 repair12366 covarianceInputs12366 (fun i hi => sourceNumerics12366 hi)
    BstLean.Part268.agent12366.frame targetFrame12366_eq


end BstLean.Part269.N12366

namespace BstLean.Part269.N12367
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12367 : scalarRow12367.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12367, BstLean.Part268.grid12367, BstLean.Part263.worldGrid]

theorem supplies12367 (j : Fin 43) : Supply 12367 (parameters j)
    (cellLower scalarRow12367.grid (sourceIndex j))
    (cellUpper scalarRow12367.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12367.grid grid_top_bounds12367 j

theorem radii12367 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12367.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12367 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12367 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12367.grid grid_top_bounds12367 j hθ

noncomputable def covarianceInputs12367 :
    BstLean.Part263.CovarianceInputs 12367 scalarRow12367.grid parameters (caps repair12367) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12367 grid_top_bounds12367 repair12367

noncomputable def covarianceEvent12367 : Set (AgFam 12367) :=
  BstLean.Part263.covarianceEvent 12367 scalarRow12367.grid parameters

theorem covarianceEvent12367_measurable : MeasurableSet covarianceEvent12367 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12367_payment :
    (retDist (paperDesignP 12367).toCentres).real
      (agentEv (paperDesignP 12367) covarianceEvent12367)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12367

theorem localCov12367 : BstLean.Part259.LocalCovarianceOn covarianceEvent12367
    (BstLean.Part263.cell scalarRow12367.grid) (caps repair12367) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12367

theorem covarianceGood12367_payment :
    (retDist (paperDesignP 12367).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12367)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12367_payment



end BstLean.Part269.N12367

namespace BstLean.Part269.N12367
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12367}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12367.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12367) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12367).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12367 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12367) (by norm_num) BstLean.Part268.WorldRow12367.worldPackage rfl
    BstLean.Part268.WorldRow12367.product_lower (BstLean.Part268.WorldRow12367.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12367} (hw : c ∈ Hof BstLean.Part268.WorldRow12367.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12367) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12367) (by norm_num) BstLean.Part268.WorldRow12367.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12367} (hw : c ∈ Hof BstLean.Part268.WorldRow12367.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12367) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12367).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12367) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12367_eq : scalarRow12367.targetFrame = BstLean.Part268.agent12367.frame := by
  norm_num [scalarRow12367,BstLean.Part268.agent12367]

noncomputable def frameData12367 : BstLean.Part264b.FrameData 12367 :=
  BstLean.Part269.frameData_from_numerics (n := 12367) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12367.worldPackage rfl BstLean.Part268.WorldRow12367.product_lower (BstLean.Part268.WorldRow12367.producthi.2.trans (by norm_num))
    scalarRow12367 repair12367 covarianceInputs12367 (fun i hi => sourceNumerics12367 hi)
    BstLean.Part268.agent12367.frame targetFrame12367_eq


end BstLean.Part269.N12367

namespace BstLean.Part269.N12368
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12368 : scalarRow12368.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12368, BstLean.Part268.grid12368, BstLean.Part263.worldGrid]

theorem supplies12368 (j : Fin 43) : Supply 12368 (parameters j)
    (cellLower scalarRow12368.grid (sourceIndex j))
    (cellUpper scalarRow12368.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12368.grid grid_top_bounds12368 j

theorem radii12368 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12368.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12368 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12368 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12368.grid grid_top_bounds12368 j hθ

noncomputable def covarianceInputs12368 :
    BstLean.Part263.CovarianceInputs 12368 scalarRow12368.grid parameters (caps repair12368) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12368 grid_top_bounds12368 repair12368

noncomputable def covarianceEvent12368 : Set (AgFam 12368) :=
  BstLean.Part263.covarianceEvent 12368 scalarRow12368.grid parameters

theorem covarianceEvent12368_measurable : MeasurableSet covarianceEvent12368 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12368_payment :
    (retDist (paperDesignP 12368).toCentres).real
      (agentEv (paperDesignP 12368) covarianceEvent12368)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12368

theorem localCov12368 : BstLean.Part259.LocalCovarianceOn covarianceEvent12368
    (BstLean.Part263.cell scalarRow12368.grid) (caps repair12368) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12368

theorem covarianceGood12368_payment :
    (retDist (paperDesignP 12368).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12368)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12368_payment



end BstLean.Part269.N12368

namespace BstLean.Part269.N12368
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12368}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12368.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12368) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12368).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12368 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12368) (by norm_num) BstLean.Part268.WorldRow12368.worldPackage rfl
    BstLean.Part268.WorldRow12368.product_lower (BstLean.Part268.WorldRow12368.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12368} (hw : c ∈ Hof BstLean.Part268.WorldRow12368.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12368) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12368) (by norm_num) BstLean.Part268.WorldRow12368.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12368} (hw : c ∈ Hof BstLean.Part268.WorldRow12368.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12368) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12368).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12368) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12368_eq : scalarRow12368.targetFrame = BstLean.Part268.agent12368.frame := by
  norm_num [scalarRow12368,BstLean.Part268.agent12368]

noncomputable def frameData12368 : BstLean.Part264b.FrameData 12368 :=
  BstLean.Part269.frameData_from_numerics (n := 12368) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12368.worldPackage rfl BstLean.Part268.WorldRow12368.product_lower (BstLean.Part268.WorldRow12368.producthi.2.trans (by norm_num))
    scalarRow12368 repair12368 covarianceInputs12368 (fun i hi => sourceNumerics12368 hi)
    BstLean.Part268.agent12368.frame targetFrame12368_eq


end BstLean.Part269.N12368

namespace BstLean.Part269.N12369
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12369 : scalarRow12369.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12369, BstLean.Part268.grid12369, BstLean.Part263.worldGrid]

theorem supplies12369 (j : Fin 43) : Supply 12369 (parameters j)
    (cellLower scalarRow12369.grid (sourceIndex j))
    (cellUpper scalarRow12369.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12369.grid grid_top_bounds12369 j

theorem radii12369 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12369.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12369 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12369 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12369.grid grid_top_bounds12369 j hθ

noncomputable def covarianceInputs12369 :
    BstLean.Part263.CovarianceInputs 12369 scalarRow12369.grid parameters (caps repair12369) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12369 grid_top_bounds12369 repair12369

noncomputable def covarianceEvent12369 : Set (AgFam 12369) :=
  BstLean.Part263.covarianceEvent 12369 scalarRow12369.grid parameters

theorem covarianceEvent12369_measurable : MeasurableSet covarianceEvent12369 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12369_payment :
    (retDist (paperDesignP 12369).toCentres).real
      (agentEv (paperDesignP 12369) covarianceEvent12369)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12369

theorem localCov12369 : BstLean.Part259.LocalCovarianceOn covarianceEvent12369
    (BstLean.Part263.cell scalarRow12369.grid) (caps repair12369) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12369

theorem covarianceGood12369_payment :
    (retDist (paperDesignP 12369).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12369)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12369_payment



end BstLean.Part269.N12369

namespace BstLean.Part269.N12369
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12369}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12369.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12369) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12369).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12369 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12369) (by norm_num) BstLean.Part268.WorldRow12369.worldPackage rfl
    BstLean.Part268.WorldRow12369.product_lower (BstLean.Part268.WorldRow12369.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12369} (hw : c ∈ Hof BstLean.Part268.WorldRow12369.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12369) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12369) (by norm_num) BstLean.Part268.WorldRow12369.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12369} (hw : c ∈ Hof BstLean.Part268.WorldRow12369.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12369) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12369).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12369) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12369_eq : scalarRow12369.targetFrame = BstLean.Part268.agent12369.frame := by
  norm_num [scalarRow12369,BstLean.Part268.agent12369]

noncomputable def frameData12369 : BstLean.Part264b.FrameData 12369 :=
  BstLean.Part269.frameData_from_numerics (n := 12369) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12369.worldPackage rfl BstLean.Part268.WorldRow12369.product_lower (BstLean.Part268.WorldRow12369.producthi.2.trans (by norm_num))
    scalarRow12369 repair12369 covarianceInputs12369 (fun i hi => sourceNumerics12369 hi)
    BstLean.Part268.agent12369.frame targetFrame12369_eq


end BstLean.Part269.N12369

namespace BstLean.Part269.N12370
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12370 : scalarRow12370.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12370, BstLean.Part268.grid12370, BstLean.Part263.worldGrid]

theorem supplies12370 (j : Fin 43) : Supply 12370 (parameters j)
    (cellLower scalarRow12370.grid (sourceIndex j))
    (cellUpper scalarRow12370.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12370.grid grid_top_bounds12370 j

theorem radii12370 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12370.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12370 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12370 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12370.grid grid_top_bounds12370 j hθ

noncomputable def covarianceInputs12370 :
    BstLean.Part263.CovarianceInputs 12370 scalarRow12370.grid parameters (caps repair12370) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12370 grid_top_bounds12370 repair12370

noncomputable def covarianceEvent12370 : Set (AgFam 12370) :=
  BstLean.Part263.covarianceEvent 12370 scalarRow12370.grid parameters

theorem covarianceEvent12370_measurable : MeasurableSet covarianceEvent12370 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12370_payment :
    (retDist (paperDesignP 12370).toCentres).real
      (agentEv (paperDesignP 12370) covarianceEvent12370)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12370

theorem localCov12370 : BstLean.Part259.LocalCovarianceOn covarianceEvent12370
    (BstLean.Part263.cell scalarRow12370.grid) (caps repair12370) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12370

theorem covarianceGood12370_payment :
    (retDist (paperDesignP 12370).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12370)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12370_payment



end BstLean.Part269.N12370

namespace BstLean.Part269.N12370
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12370}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12370.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12370) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12370).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12370 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12370) (by norm_num) BstLean.Part268.WorldRow12370.worldPackage rfl
    BstLean.Part268.WorldRow12370.product_lower (BstLean.Part268.WorldRow12370.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12370} (hw : c ∈ Hof BstLean.Part268.WorldRow12370.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12370) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12370) (by norm_num) BstLean.Part268.WorldRow12370.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12370} (hw : c ∈ Hof BstLean.Part268.WorldRow12370.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12370) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12370).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12370) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12370_eq : scalarRow12370.targetFrame = BstLean.Part268.agent12370.frame := by
  norm_num [scalarRow12370,BstLean.Part268.agent12370]

noncomputable def frameData12370 : BstLean.Part264b.FrameData 12370 :=
  BstLean.Part269.frameData_from_numerics (n := 12370) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12370.worldPackage rfl BstLean.Part268.WorldRow12370.product_lower (BstLean.Part268.WorldRow12370.producthi.2.trans (by norm_num))
    scalarRow12370 repair12370 covarianceInputs12370 (fun i hi => sourceNumerics12370 hi)
    BstLean.Part268.agent12370.frame targetFrame12370_eq


end BstLean.Part269.N12370
