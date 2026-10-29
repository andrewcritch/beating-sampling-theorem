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

namespace BstLean.Part269.N12356
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12356 : scalarRow12356.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12356, BstLean.Part268.grid12356, BstLean.Part263.worldGrid]

theorem supplies12356 (j : Fin 43) : Supply 12356 (parameters j)
    (cellLower scalarRow12356.grid (sourceIndex j))
    (cellUpper scalarRow12356.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12356.grid grid_top_bounds12356 j

theorem radii12356 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12356.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12356 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12356 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12356.grid grid_top_bounds12356 j hθ

noncomputable def covarianceInputs12356 :
    BstLean.Part263.CovarianceInputs 12356 scalarRow12356.grid parameters (caps repair12356) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12356 grid_top_bounds12356 repair12356

noncomputable def covarianceEvent12356 : Set (AgFam 12356) :=
  BstLean.Part263.covarianceEvent 12356 scalarRow12356.grid parameters

theorem covarianceEvent12356_measurable : MeasurableSet covarianceEvent12356 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12356_payment :
    (retDist (paperDesignP 12356).toCentres).real
      (agentEv (paperDesignP 12356) covarianceEvent12356)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12356

theorem localCov12356 : BstLean.Part259.LocalCovarianceOn covarianceEvent12356
    (BstLean.Part263.cell scalarRow12356.grid) (caps repair12356) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12356

theorem covarianceGood12356_payment :
    (retDist (paperDesignP 12356).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12356)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12356_payment



end BstLean.Part269.N12356

namespace BstLean.Part269.N12356
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12356}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12356.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12356) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12356).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12356 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12356) (by norm_num) BstLean.Part268.WorldRow12356.worldPackage rfl
    BstLean.Part268.WorldRow12356.product_lower (BstLean.Part268.WorldRow12356.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12356} (hw : c ∈ Hof BstLean.Part268.WorldRow12356.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12356) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12356) (by norm_num) BstLean.Part268.WorldRow12356.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12356} (hw : c ∈ Hof BstLean.Part268.WorldRow12356.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12356) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12356).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12356) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12356_eq : scalarRow12356.targetFrame = BstLean.Part268.agent12356.frame := by
  norm_num [scalarRow12356,BstLean.Part268.agent12356]

noncomputable def frameData12356 : BstLean.Part264b.FrameData 12356 :=
  BstLean.Part269.frameData_from_numerics (n := 12356) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12356.worldPackage rfl BstLean.Part268.WorldRow12356.product_lower (BstLean.Part268.WorldRow12356.producthi.2.trans (by norm_num))
    scalarRow12356 repair12356 covarianceInputs12356 (fun i hi => sourceNumerics12356 hi)
    BstLean.Part268.agent12356.frame targetFrame12356_eq


end BstLean.Part269.N12356

namespace BstLean.Part269.N12357
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12357 : scalarRow12357.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12357, BstLean.Part268.grid12357, BstLean.Part263.worldGrid]

theorem supplies12357 (j : Fin 43) : Supply 12357 (parameters j)
    (cellLower scalarRow12357.grid (sourceIndex j))
    (cellUpper scalarRow12357.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12357.grid grid_top_bounds12357 j

theorem radii12357 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12357.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12357 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12357 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12357.grid grid_top_bounds12357 j hθ

noncomputable def covarianceInputs12357 :
    BstLean.Part263.CovarianceInputs 12357 scalarRow12357.grid parameters (caps repair12357) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12357 grid_top_bounds12357 repair12357

noncomputable def covarianceEvent12357 : Set (AgFam 12357) :=
  BstLean.Part263.covarianceEvent 12357 scalarRow12357.grid parameters

theorem covarianceEvent12357_measurable : MeasurableSet covarianceEvent12357 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12357_payment :
    (retDist (paperDesignP 12357).toCentres).real
      (agentEv (paperDesignP 12357) covarianceEvent12357)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12357

theorem localCov12357 : BstLean.Part259.LocalCovarianceOn covarianceEvent12357
    (BstLean.Part263.cell scalarRow12357.grid) (caps repair12357) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12357

theorem covarianceGood12357_payment :
    (retDist (paperDesignP 12357).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12357)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12357_payment



end BstLean.Part269.N12357

namespace BstLean.Part269.N12357
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12357}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12357.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12357) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12357).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12357 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12357) (by norm_num) BstLean.Part268.WorldRow12357.worldPackage rfl
    BstLean.Part268.WorldRow12357.product_lower (BstLean.Part268.WorldRow12357.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12357} (hw : c ∈ Hof BstLean.Part268.WorldRow12357.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12357) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12357) (by norm_num) BstLean.Part268.WorldRow12357.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12357} (hw : c ∈ Hof BstLean.Part268.WorldRow12357.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12357) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12357).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12357) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12357_eq : scalarRow12357.targetFrame = BstLean.Part268.agent12357.frame := by
  norm_num [scalarRow12357,BstLean.Part268.agent12357]

noncomputable def frameData12357 : BstLean.Part264b.FrameData 12357 :=
  BstLean.Part269.frameData_from_numerics (n := 12357) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12357.worldPackage rfl BstLean.Part268.WorldRow12357.product_lower (BstLean.Part268.WorldRow12357.producthi.2.trans (by norm_num))
    scalarRow12357 repair12357 covarianceInputs12357 (fun i hi => sourceNumerics12357 hi)
    BstLean.Part268.agent12357.frame targetFrame12357_eq


end BstLean.Part269.N12357

namespace BstLean.Part269.N12358
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12358 : scalarRow12358.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12358, BstLean.Part268.grid12358, BstLean.Part263.worldGrid]

theorem supplies12358 (j : Fin 43) : Supply 12358 (parameters j)
    (cellLower scalarRow12358.grid (sourceIndex j))
    (cellUpper scalarRow12358.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12358.grid grid_top_bounds12358 j

theorem radii12358 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12358.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12358 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12358 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12358.grid grid_top_bounds12358 j hθ

noncomputable def covarianceInputs12358 :
    BstLean.Part263.CovarianceInputs 12358 scalarRow12358.grid parameters (caps repair12358) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12358 grid_top_bounds12358 repair12358

noncomputable def covarianceEvent12358 : Set (AgFam 12358) :=
  BstLean.Part263.covarianceEvent 12358 scalarRow12358.grid parameters

theorem covarianceEvent12358_measurable : MeasurableSet covarianceEvent12358 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12358_payment :
    (retDist (paperDesignP 12358).toCentres).real
      (agentEv (paperDesignP 12358) covarianceEvent12358)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12358

theorem localCov12358 : BstLean.Part259.LocalCovarianceOn covarianceEvent12358
    (BstLean.Part263.cell scalarRow12358.grid) (caps repair12358) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12358

theorem covarianceGood12358_payment :
    (retDist (paperDesignP 12358).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12358)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12358_payment



end BstLean.Part269.N12358

namespace BstLean.Part269.N12358
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12358}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12358.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12358) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12358).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12358 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12358) (by norm_num) BstLean.Part268.WorldRow12358.worldPackage rfl
    BstLean.Part268.WorldRow12358.product_lower (BstLean.Part268.WorldRow12358.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12358} (hw : c ∈ Hof BstLean.Part268.WorldRow12358.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12358) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12358) (by norm_num) BstLean.Part268.WorldRow12358.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12358} (hw : c ∈ Hof BstLean.Part268.WorldRow12358.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12358) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12358).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12358) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12358_eq : scalarRow12358.targetFrame = BstLean.Part268.agent12358.frame := by
  norm_num [scalarRow12358,BstLean.Part268.agent12358]

noncomputable def frameData12358 : BstLean.Part264b.FrameData 12358 :=
  BstLean.Part269.frameData_from_numerics (n := 12358) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12358.worldPackage rfl BstLean.Part268.WorldRow12358.product_lower (BstLean.Part268.WorldRow12358.producthi.2.trans (by norm_num))
    scalarRow12358 repair12358 covarianceInputs12358 (fun i hi => sourceNumerics12358 hi)
    BstLean.Part268.agent12358.frame targetFrame12358_eq


end BstLean.Part269.N12358

namespace BstLean.Part269.N12359
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12359 : scalarRow12359.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12359, BstLean.Part268.grid12359, BstLean.Part263.worldGrid]

theorem supplies12359 (j : Fin 43) : Supply 12359 (parameters j)
    (cellLower scalarRow12359.grid (sourceIndex j))
    (cellUpper scalarRow12359.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12359.grid grid_top_bounds12359 j

theorem radii12359 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12359.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12359 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12359 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12359.grid grid_top_bounds12359 j hθ

noncomputable def covarianceInputs12359 :
    BstLean.Part263.CovarianceInputs 12359 scalarRow12359.grid parameters (caps repair12359) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12359 grid_top_bounds12359 repair12359

noncomputable def covarianceEvent12359 : Set (AgFam 12359) :=
  BstLean.Part263.covarianceEvent 12359 scalarRow12359.grid parameters

theorem covarianceEvent12359_measurable : MeasurableSet covarianceEvent12359 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12359_payment :
    (retDist (paperDesignP 12359).toCentres).real
      (agentEv (paperDesignP 12359) covarianceEvent12359)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12359

theorem localCov12359 : BstLean.Part259.LocalCovarianceOn covarianceEvent12359
    (BstLean.Part263.cell scalarRow12359.grid) (caps repair12359) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12359

theorem covarianceGood12359_payment :
    (retDist (paperDesignP 12359).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12359)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12359_payment



end BstLean.Part269.N12359

namespace BstLean.Part269.N12359
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12359}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12359.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12359) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12359).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12359 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12359) (by norm_num) BstLean.Part268.WorldRow12359.worldPackage rfl
    BstLean.Part268.WorldRow12359.product_lower (BstLean.Part268.WorldRow12359.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12359} (hw : c ∈ Hof BstLean.Part268.WorldRow12359.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12359) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12359) (by norm_num) BstLean.Part268.WorldRow12359.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12359} (hw : c ∈ Hof BstLean.Part268.WorldRow12359.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12359) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12359).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12359) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12359_eq : scalarRow12359.targetFrame = BstLean.Part268.agent12359.frame := by
  norm_num [scalarRow12359,BstLean.Part268.agent12359]

noncomputable def frameData12359 : BstLean.Part264b.FrameData 12359 :=
  BstLean.Part269.frameData_from_numerics (n := 12359) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12359.worldPackage rfl BstLean.Part268.WorldRow12359.product_lower (BstLean.Part268.WorldRow12359.producthi.2.trans (by norm_num))
    scalarRow12359 repair12359 covarianceInputs12359 (fun i hi => sourceNumerics12359 hi)
    BstLean.Part268.agent12359.frame targetFrame12359_eq


end BstLean.Part269.N12359

namespace BstLean.Part269.N12360
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12360 : scalarRow12360.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12360, BstLean.Part268.grid12360, BstLean.Part263.worldGrid]

theorem supplies12360 (j : Fin 43) : Supply 12360 (parameters j)
    (cellLower scalarRow12360.grid (sourceIndex j))
    (cellUpper scalarRow12360.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12360.grid grid_top_bounds12360 j

theorem radii12360 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12360.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12360 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12360 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12360.grid grid_top_bounds12360 j hθ

noncomputable def covarianceInputs12360 :
    BstLean.Part263.CovarianceInputs 12360 scalarRow12360.grid parameters (caps repair12360) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12360 grid_top_bounds12360 repair12360

noncomputable def covarianceEvent12360 : Set (AgFam 12360) :=
  BstLean.Part263.covarianceEvent 12360 scalarRow12360.grid parameters

theorem covarianceEvent12360_measurable : MeasurableSet covarianceEvent12360 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12360_payment :
    (retDist (paperDesignP 12360).toCentres).real
      (agentEv (paperDesignP 12360) covarianceEvent12360)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12360

theorem localCov12360 : BstLean.Part259.LocalCovarianceOn covarianceEvent12360
    (BstLean.Part263.cell scalarRow12360.grid) (caps repair12360) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12360

theorem covarianceGood12360_payment :
    (retDist (paperDesignP 12360).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12360)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12360_payment



end BstLean.Part269.N12360

namespace BstLean.Part269.N12360
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12360}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12360.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12360) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12360).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12360 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12360) (by norm_num) BstLean.Part268.WorldRow12360.worldPackage rfl
    BstLean.Part268.WorldRow12360.product_lower (BstLean.Part268.WorldRow12360.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12360} (hw : c ∈ Hof BstLean.Part268.WorldRow12360.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12360) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12360) (by norm_num) BstLean.Part268.WorldRow12360.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12360} (hw : c ∈ Hof BstLean.Part268.WorldRow12360.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12360) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12360).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12360) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12360_eq : scalarRow12360.targetFrame = BstLean.Part268.agent12360.frame := by
  norm_num [scalarRow12360,BstLean.Part268.agent12360]

noncomputable def frameData12360 : BstLean.Part264b.FrameData 12360 :=
  BstLean.Part269.frameData_from_numerics (n := 12360) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12360.worldPackage rfl BstLean.Part268.WorldRow12360.product_lower (BstLean.Part268.WorldRow12360.producthi.2.trans (by norm_num))
    scalarRow12360 repair12360 covarianceInputs12360 (fun i hi => sourceNumerics12360 hi)
    BstLean.Part268.agent12360.frame targetFrame12360_eq


end BstLean.Part269.N12360
