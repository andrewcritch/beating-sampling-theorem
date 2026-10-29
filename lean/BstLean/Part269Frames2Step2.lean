import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World2Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs2
import BstLean.Part269Rows2
import BstLean.Part269Sources2
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12410
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12410 : scalarRow12410.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12410, BstLean.Part268.grid12410, BstLean.Part263.worldGrid]

theorem supplies12410 (j : Fin 43) : Supply 12410 (parameters j)
    (cellLower scalarRow12410.grid (sourceIndex j))
    (cellUpper scalarRow12410.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12410.grid grid_top_bounds12410 j

theorem radii12410 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12410.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12410 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12410 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12410.grid grid_top_bounds12410 j hθ

noncomputable def covarianceInputs12410 :
    BstLean.Part263.CovarianceInputs 12410 scalarRow12410.grid parameters (caps repair12410) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12410 grid_top_bounds12410 repair12410

noncomputable def covarianceEvent12410 : Set (AgFam 12410) :=
  BstLean.Part263.covarianceEvent 12410 scalarRow12410.grid parameters

theorem covarianceEvent12410_measurable : MeasurableSet covarianceEvent12410 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12410_payment :
    (retDist (paperDesignP 12410).toCentres).real
      (agentEv (paperDesignP 12410) covarianceEvent12410)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12410

theorem localCov12410 : BstLean.Part259.LocalCovarianceOn covarianceEvent12410
    (BstLean.Part263.cell scalarRow12410.grid) (caps repair12410) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12410

theorem covarianceGood12410_payment :
    (retDist (paperDesignP 12410).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12410)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12410_payment



end BstLean.Part269.N12410

namespace BstLean.Part269.N12410
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12410}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12410.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12410) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12410).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12410 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12410) (by norm_num) BstLean.Part268.WorldRow12410.worldPackage rfl
    BstLean.Part268.WorldRow12410.product_lower (BstLean.Part268.WorldRow12410.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12410} (hw : c ∈ Hof BstLean.Part268.WorldRow12410.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12410) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12410) (by norm_num) BstLean.Part268.WorldRow12410.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12410} (hw : c ∈ Hof BstLean.Part268.WorldRow12410.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12410) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12410).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12410) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12410_eq : scalarRow12410.targetFrame = BstLean.Part268.agent12410.frame := by
  norm_num [scalarRow12410,BstLean.Part268.agent12410]

noncomputable def frameData12410 : BstLean.Part264b.FrameData 12410 :=
  BstLean.Part269.frameData_from_numerics (n := 12410) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12410.worldPackage rfl BstLean.Part268.WorldRow12410.product_lower (BstLean.Part268.WorldRow12410.producthi.2.trans (by norm_num))
    scalarRow12410 repair12410 covarianceInputs12410 (fun i hi => sourceNumerics12410 hi)
    BstLean.Part268.agent12410.frame targetFrame12410_eq


end BstLean.Part269.N12410

namespace BstLean.Part269.N12411
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12411 : scalarRow12411.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12411, BstLean.Part268.grid12411, BstLean.Part263.worldGrid]

theorem supplies12411 (j : Fin 43) : Supply 12411 (parameters j)
    (cellLower scalarRow12411.grid (sourceIndex j))
    (cellUpper scalarRow12411.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12411.grid grid_top_bounds12411 j

theorem radii12411 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12411.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12411 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12411 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12411.grid grid_top_bounds12411 j hθ

noncomputable def covarianceInputs12411 :
    BstLean.Part263.CovarianceInputs 12411 scalarRow12411.grid parameters (caps repair12411) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12411 grid_top_bounds12411 repair12411

noncomputable def covarianceEvent12411 : Set (AgFam 12411) :=
  BstLean.Part263.covarianceEvent 12411 scalarRow12411.grid parameters

theorem covarianceEvent12411_measurable : MeasurableSet covarianceEvent12411 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12411_payment :
    (retDist (paperDesignP 12411).toCentres).real
      (agentEv (paperDesignP 12411) covarianceEvent12411)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12411

theorem localCov12411 : BstLean.Part259.LocalCovarianceOn covarianceEvent12411
    (BstLean.Part263.cell scalarRow12411.grid) (caps repair12411) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12411

theorem covarianceGood12411_payment :
    (retDist (paperDesignP 12411).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12411)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12411_payment



end BstLean.Part269.N12411

namespace BstLean.Part269.N12411
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12411}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12411.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12411) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12411).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12411 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12411) (by norm_num) BstLean.Part268.WorldRow12411.worldPackage rfl
    BstLean.Part268.WorldRow12411.product_lower (BstLean.Part268.WorldRow12411.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12411} (hw : c ∈ Hof BstLean.Part268.WorldRow12411.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12411) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12411) (by norm_num) BstLean.Part268.WorldRow12411.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12411} (hw : c ∈ Hof BstLean.Part268.WorldRow12411.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12411) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12411).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12411) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12411_eq : scalarRow12411.targetFrame = BstLean.Part268.agent12411.frame := by
  norm_num [scalarRow12411,BstLean.Part268.agent12411]

noncomputable def frameData12411 : BstLean.Part264b.FrameData 12411 :=
  BstLean.Part269.frameData_from_numerics (n := 12411) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12411.worldPackage rfl BstLean.Part268.WorldRow12411.product_lower (BstLean.Part268.WorldRow12411.producthi.2.trans (by norm_num))
    scalarRow12411 repair12411 covarianceInputs12411 (fun i hi => sourceNumerics12411 hi)
    BstLean.Part268.agent12411.frame targetFrame12411_eq


end BstLean.Part269.N12411

namespace BstLean.Part269.N12412
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12412 : scalarRow12412.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12412, BstLean.Part268.grid12412, BstLean.Part263.worldGrid]

theorem supplies12412 (j : Fin 43) : Supply 12412 (parameters j)
    (cellLower scalarRow12412.grid (sourceIndex j))
    (cellUpper scalarRow12412.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12412.grid grid_top_bounds12412 j

theorem radii12412 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12412.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12412 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12412 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12412.grid grid_top_bounds12412 j hθ

noncomputable def covarianceInputs12412 :
    BstLean.Part263.CovarianceInputs 12412 scalarRow12412.grid parameters (caps repair12412) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12412 grid_top_bounds12412 repair12412

noncomputable def covarianceEvent12412 : Set (AgFam 12412) :=
  BstLean.Part263.covarianceEvent 12412 scalarRow12412.grid parameters

theorem covarianceEvent12412_measurable : MeasurableSet covarianceEvent12412 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12412_payment :
    (retDist (paperDesignP 12412).toCentres).real
      (agentEv (paperDesignP 12412) covarianceEvent12412)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12412

theorem localCov12412 : BstLean.Part259.LocalCovarianceOn covarianceEvent12412
    (BstLean.Part263.cell scalarRow12412.grid) (caps repair12412) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12412

theorem covarianceGood12412_payment :
    (retDist (paperDesignP 12412).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12412)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12412_payment



end BstLean.Part269.N12412

namespace BstLean.Part269.N12412
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12412}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12412.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12412) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12412).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12412 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12412) (by norm_num) BstLean.Part268.WorldRow12412.worldPackage rfl
    BstLean.Part268.WorldRow12412.product_lower (BstLean.Part268.WorldRow12412.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12412} (hw : c ∈ Hof BstLean.Part268.WorldRow12412.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12412) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12412) (by norm_num) BstLean.Part268.WorldRow12412.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12412} (hw : c ∈ Hof BstLean.Part268.WorldRow12412.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12412) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12412).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12412) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12412_eq : scalarRow12412.targetFrame = BstLean.Part268.agent12412.frame := by
  norm_num [scalarRow12412,BstLean.Part268.agent12412]

noncomputable def frameData12412 : BstLean.Part264b.FrameData 12412 :=
  BstLean.Part269.frameData_from_numerics (n := 12412) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12412.worldPackage rfl BstLean.Part268.WorldRow12412.product_lower (BstLean.Part268.WorldRow12412.producthi.2.trans (by norm_num))
    scalarRow12412 repair12412 covarianceInputs12412 (fun i hi => sourceNumerics12412 hi)
    BstLean.Part268.agent12412.frame targetFrame12412_eq


end BstLean.Part269.N12412

namespace BstLean.Part269.N12413
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12413 : scalarRow12413.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12413, BstLean.Part268.grid12413, BstLean.Part263.worldGrid]

theorem supplies12413 (j : Fin 43) : Supply 12413 (parameters j)
    (cellLower scalarRow12413.grid (sourceIndex j))
    (cellUpper scalarRow12413.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12413.grid grid_top_bounds12413 j

theorem radii12413 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12413.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12413 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12413 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12413.grid grid_top_bounds12413 j hθ

noncomputable def covarianceInputs12413 :
    BstLean.Part263.CovarianceInputs 12413 scalarRow12413.grid parameters (caps repair12413) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12413 grid_top_bounds12413 repair12413

noncomputable def covarianceEvent12413 : Set (AgFam 12413) :=
  BstLean.Part263.covarianceEvent 12413 scalarRow12413.grid parameters

theorem covarianceEvent12413_measurable : MeasurableSet covarianceEvent12413 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12413_payment :
    (retDist (paperDesignP 12413).toCentres).real
      (agentEv (paperDesignP 12413) covarianceEvent12413)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12413

theorem localCov12413 : BstLean.Part259.LocalCovarianceOn covarianceEvent12413
    (BstLean.Part263.cell scalarRow12413.grid) (caps repair12413) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12413

theorem covarianceGood12413_payment :
    (retDist (paperDesignP 12413).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12413)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12413_payment



end BstLean.Part269.N12413

namespace BstLean.Part269.N12413
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12413}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12413.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12413) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12413).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12413 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12413) (by norm_num) BstLean.Part268.WorldRow12413.worldPackage rfl
    BstLean.Part268.WorldRow12413.product_lower (BstLean.Part268.WorldRow12413.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12413} (hw : c ∈ Hof BstLean.Part268.WorldRow12413.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12413) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12413) (by norm_num) BstLean.Part268.WorldRow12413.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12413} (hw : c ∈ Hof BstLean.Part268.WorldRow12413.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12413) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12413).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12413) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12413_eq : scalarRow12413.targetFrame = BstLean.Part268.agent12413.frame := by
  norm_num [scalarRow12413,BstLean.Part268.agent12413]

noncomputable def frameData12413 : BstLean.Part264b.FrameData 12413 :=
  BstLean.Part269.frameData_from_numerics (n := 12413) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12413.worldPackage rfl BstLean.Part268.WorldRow12413.product_lower (BstLean.Part268.WorldRow12413.producthi.2.trans (by norm_num))
    scalarRow12413 repair12413 covarianceInputs12413 (fun i hi => sourceNumerics12413 hi)
    BstLean.Part268.agent12413.frame targetFrame12413_eq


end BstLean.Part269.N12413

namespace BstLean.Part269.N12414
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12414 : scalarRow12414.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12414, BstLean.Part268.grid12414, BstLean.Part263.worldGrid]

theorem supplies12414 (j : Fin 43) : Supply 12414 (parameters j)
    (cellLower scalarRow12414.grid (sourceIndex j))
    (cellUpper scalarRow12414.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12414.grid grid_top_bounds12414 j

theorem radii12414 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12414.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12414 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12414 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12414.grid grid_top_bounds12414 j hθ

noncomputable def covarianceInputs12414 :
    BstLean.Part263.CovarianceInputs 12414 scalarRow12414.grid parameters (caps repair12414) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12414 grid_top_bounds12414 repair12414

noncomputable def covarianceEvent12414 : Set (AgFam 12414) :=
  BstLean.Part263.covarianceEvent 12414 scalarRow12414.grid parameters

theorem covarianceEvent12414_measurable : MeasurableSet covarianceEvent12414 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12414_payment :
    (retDist (paperDesignP 12414).toCentres).real
      (agentEv (paperDesignP 12414) covarianceEvent12414)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12414

theorem localCov12414 : BstLean.Part259.LocalCovarianceOn covarianceEvent12414
    (BstLean.Part263.cell scalarRow12414.grid) (caps repair12414) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12414

theorem covarianceGood12414_payment :
    (retDist (paperDesignP 12414).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12414)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12414_payment



end BstLean.Part269.N12414

namespace BstLean.Part269.N12414
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12414}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12414.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12414) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12414).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12414 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12414) (by norm_num) BstLean.Part268.WorldRow12414.worldPackage rfl
    BstLean.Part268.WorldRow12414.product_lower (BstLean.Part268.WorldRow12414.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12414} (hw : c ∈ Hof BstLean.Part268.WorldRow12414.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12414) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12414) (by norm_num) BstLean.Part268.WorldRow12414.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12414} (hw : c ∈ Hof BstLean.Part268.WorldRow12414.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12414) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12414).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12414) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12414_eq : scalarRow12414.targetFrame = BstLean.Part268.agent12414.frame := by
  norm_num [scalarRow12414,BstLean.Part268.agent12414]

noncomputable def frameData12414 : BstLean.Part264b.FrameData 12414 :=
  BstLean.Part269.frameData_from_numerics (n := 12414) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12414.worldPackage rfl BstLean.Part268.WorldRow12414.product_lower (BstLean.Part268.WorldRow12414.producthi.2.trans (by norm_num))
    scalarRow12414 repair12414 covarianceInputs12414 (fun i hi => sourceNumerics12414 hi)
    BstLean.Part268.agent12414.frame targetFrame12414_eq


end BstLean.Part269.N12414
