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

namespace BstLean.Part269.N12430
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12430 : scalarRow12430.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12430, BstLean.Part268.grid12430, BstLean.Part263.worldGrid]

theorem supplies12430 (j : Fin 43) : Supply 12430 (parameters j)
    (cellLower scalarRow12430.grid (sourceIndex j))
    (cellUpper scalarRow12430.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12430.grid grid_top_bounds12430 j

theorem radii12430 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12430.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12430 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12430 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12430.grid grid_top_bounds12430 j hθ

noncomputable def covarianceInputs12430 :
    BstLean.Part263.CovarianceInputs 12430 scalarRow12430.grid parameters (caps repair12430) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12430 grid_top_bounds12430 repair12430

noncomputable def covarianceEvent12430 : Set (AgFam 12430) :=
  BstLean.Part263.covarianceEvent 12430 scalarRow12430.grid parameters

theorem covarianceEvent12430_measurable : MeasurableSet covarianceEvent12430 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12430_payment :
    (retDist (paperDesignP 12430).toCentres).real
      (agentEv (paperDesignP 12430) covarianceEvent12430)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12430

theorem localCov12430 : BstLean.Part259.LocalCovarianceOn covarianceEvent12430
    (BstLean.Part263.cell scalarRow12430.grid) (caps repair12430) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12430

theorem covarianceGood12430_payment :
    (retDist (paperDesignP 12430).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12430)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12430_payment



end BstLean.Part269.N12430

namespace BstLean.Part269.N12430
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12430}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12430.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12430) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12430).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12430 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12430) (by norm_num) BstLean.Part268.WorldRow12430.worldPackage rfl
    BstLean.Part268.WorldRow12430.product_lower (BstLean.Part268.WorldRow12430.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12430} (hw : c ∈ Hof BstLean.Part268.WorldRow12430.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12430) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12430) (by norm_num) BstLean.Part268.WorldRow12430.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12430} (hw : c ∈ Hof BstLean.Part268.WorldRow12430.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12430) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12430).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12430) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12430_eq : scalarRow12430.targetFrame = BstLean.Part268.agent12430.frame := by
  norm_num [scalarRow12430,BstLean.Part268.agent12430]

noncomputable def frameData12430 : BstLean.Part264b.FrameData 12430 :=
  BstLean.Part269.frameData_from_numerics (n := 12430) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12430.worldPackage rfl BstLean.Part268.WorldRow12430.product_lower (BstLean.Part268.WorldRow12430.producthi.2.trans (by norm_num))
    scalarRow12430 repair12430 covarianceInputs12430 (fun i hi => sourceNumerics12430 hi)
    BstLean.Part268.agent12430.frame targetFrame12430_eq


end BstLean.Part269.N12430

namespace BstLean.Part269.N12431
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12431 : scalarRow12431.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12431, BstLean.Part268.grid12431, BstLean.Part263.worldGrid]

theorem supplies12431 (j : Fin 43) : Supply 12431 (parameters j)
    (cellLower scalarRow12431.grid (sourceIndex j))
    (cellUpper scalarRow12431.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12431.grid grid_top_bounds12431 j

theorem radii12431 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12431.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12431 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12431 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12431.grid grid_top_bounds12431 j hθ

noncomputable def covarianceInputs12431 :
    BstLean.Part263.CovarianceInputs 12431 scalarRow12431.grid parameters (caps repair12431) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12431 grid_top_bounds12431 repair12431

noncomputable def covarianceEvent12431 : Set (AgFam 12431) :=
  BstLean.Part263.covarianceEvent 12431 scalarRow12431.grid parameters

theorem covarianceEvent12431_measurable : MeasurableSet covarianceEvent12431 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12431_payment :
    (retDist (paperDesignP 12431).toCentres).real
      (agentEv (paperDesignP 12431) covarianceEvent12431)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12431

theorem localCov12431 : BstLean.Part259.LocalCovarianceOn covarianceEvent12431
    (BstLean.Part263.cell scalarRow12431.grid) (caps repair12431) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12431

theorem covarianceGood12431_payment :
    (retDist (paperDesignP 12431).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12431)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12431_payment



end BstLean.Part269.N12431

namespace BstLean.Part269.N12431
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12431}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12431.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12431) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12431).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12431 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12431) (by norm_num) BstLean.Part268.WorldRow12431.worldPackage rfl
    BstLean.Part268.WorldRow12431.product_lower (BstLean.Part268.WorldRow12431.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12431} (hw : c ∈ Hof BstLean.Part268.WorldRow12431.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12431) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12431) (by norm_num) BstLean.Part268.WorldRow12431.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12431} (hw : c ∈ Hof BstLean.Part268.WorldRow12431.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12431) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12431).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12431) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12431_eq : scalarRow12431.targetFrame = BstLean.Part268.agent12431.frame := by
  norm_num [scalarRow12431,BstLean.Part268.agent12431]

noncomputable def frameData12431 : BstLean.Part264b.FrameData 12431 :=
  BstLean.Part269.frameData_from_numerics (n := 12431) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12431.worldPackage rfl BstLean.Part268.WorldRow12431.product_lower (BstLean.Part268.WorldRow12431.producthi.2.trans (by norm_num))
    scalarRow12431 repair12431 covarianceInputs12431 (fun i hi => sourceNumerics12431 hi)
    BstLean.Part268.agent12431.frame targetFrame12431_eq


end BstLean.Part269.N12431

namespace BstLean.Part269.N12432
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12432 : scalarRow12432.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12432, BstLean.Part268.grid12432, BstLean.Part263.worldGrid]

theorem supplies12432 (j : Fin 43) : Supply 12432 (parameters j)
    (cellLower scalarRow12432.grid (sourceIndex j))
    (cellUpper scalarRow12432.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12432.grid grid_top_bounds12432 j

theorem radii12432 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12432.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12432 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12432 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12432.grid grid_top_bounds12432 j hθ

noncomputable def covarianceInputs12432 :
    BstLean.Part263.CovarianceInputs 12432 scalarRow12432.grid parameters (caps repair12432) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12432 grid_top_bounds12432 repair12432

noncomputable def covarianceEvent12432 : Set (AgFam 12432) :=
  BstLean.Part263.covarianceEvent 12432 scalarRow12432.grid parameters

theorem covarianceEvent12432_measurable : MeasurableSet covarianceEvent12432 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12432_payment :
    (retDist (paperDesignP 12432).toCentres).real
      (agentEv (paperDesignP 12432) covarianceEvent12432)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12432

theorem localCov12432 : BstLean.Part259.LocalCovarianceOn covarianceEvent12432
    (BstLean.Part263.cell scalarRow12432.grid) (caps repair12432) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12432

theorem covarianceGood12432_payment :
    (retDist (paperDesignP 12432).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12432)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12432_payment



end BstLean.Part269.N12432

namespace BstLean.Part269.N12432
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12432}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12432.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12432) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12432).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12432 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12432) (by norm_num) BstLean.Part268.WorldRow12432.worldPackage rfl
    BstLean.Part268.WorldRow12432.product_lower (BstLean.Part268.WorldRow12432.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12432} (hw : c ∈ Hof BstLean.Part268.WorldRow12432.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12432) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12432) (by norm_num) BstLean.Part268.WorldRow12432.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12432} (hw : c ∈ Hof BstLean.Part268.WorldRow12432.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12432) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12432).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12432) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12432_eq : scalarRow12432.targetFrame = BstLean.Part268.agent12432.frame := by
  norm_num [scalarRow12432,BstLean.Part268.agent12432]

noncomputable def frameData12432 : BstLean.Part264b.FrameData 12432 :=
  BstLean.Part269.frameData_from_numerics (n := 12432) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12432.worldPackage rfl BstLean.Part268.WorldRow12432.product_lower (BstLean.Part268.WorldRow12432.producthi.2.trans (by norm_num))
    scalarRow12432 repair12432 covarianceInputs12432 (fun i hi => sourceNumerics12432 hi)
    BstLean.Part268.agent12432.frame targetFrame12432_eq


end BstLean.Part269.N12432

namespace BstLean.Part269.N12433
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12433 : scalarRow12433.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12433, BstLean.Part268.grid12433, BstLean.Part263.worldGrid]

theorem supplies12433 (j : Fin 43) : Supply 12433 (parameters j)
    (cellLower scalarRow12433.grid (sourceIndex j))
    (cellUpper scalarRow12433.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12433.grid grid_top_bounds12433 j

theorem radii12433 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12433.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12433 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12433 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12433.grid grid_top_bounds12433 j hθ

noncomputable def covarianceInputs12433 :
    BstLean.Part263.CovarianceInputs 12433 scalarRow12433.grid parameters (caps repair12433) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12433 grid_top_bounds12433 repair12433

noncomputable def covarianceEvent12433 : Set (AgFam 12433) :=
  BstLean.Part263.covarianceEvent 12433 scalarRow12433.grid parameters

theorem covarianceEvent12433_measurable : MeasurableSet covarianceEvent12433 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12433_payment :
    (retDist (paperDesignP 12433).toCentres).real
      (agentEv (paperDesignP 12433) covarianceEvent12433)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12433

theorem localCov12433 : BstLean.Part259.LocalCovarianceOn covarianceEvent12433
    (BstLean.Part263.cell scalarRow12433.grid) (caps repair12433) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12433

theorem covarianceGood12433_payment :
    (retDist (paperDesignP 12433).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12433)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12433_payment



end BstLean.Part269.N12433

namespace BstLean.Part269.N12433
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12433}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12433.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12433) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12433).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12433 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12433) (by norm_num) BstLean.Part268.WorldRow12433.worldPackage rfl
    BstLean.Part268.WorldRow12433.product_lower (BstLean.Part268.WorldRow12433.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12433} (hw : c ∈ Hof BstLean.Part268.WorldRow12433.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12433) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12433) (by norm_num) BstLean.Part268.WorldRow12433.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12433} (hw : c ∈ Hof BstLean.Part268.WorldRow12433.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12433) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12433).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12433) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12433_eq : scalarRow12433.targetFrame = BstLean.Part268.agent12433.frame := by
  norm_num [scalarRow12433,BstLean.Part268.agent12433]

noncomputable def frameData12433 : BstLean.Part264b.FrameData 12433 :=
  BstLean.Part269.frameData_from_numerics (n := 12433) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12433.worldPackage rfl BstLean.Part268.WorldRow12433.product_lower (BstLean.Part268.WorldRow12433.producthi.2.trans (by norm_num))
    scalarRow12433 repair12433 covarianceInputs12433 (fun i hi => sourceNumerics12433 hi)
    BstLean.Part268.agent12433.frame targetFrame12433_eq


end BstLean.Part269.N12433

namespace BstLean.Part269.N12434
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12434 : scalarRow12434.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12434, BstLean.Part268.grid12434, BstLean.Part263.worldGrid]

theorem supplies12434 (j : Fin 43) : Supply 12434 (parameters j)
    (cellLower scalarRow12434.grid (sourceIndex j))
    (cellUpper scalarRow12434.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12434.grid grid_top_bounds12434 j

theorem radii12434 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12434.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12434 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12434 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12434.grid grid_top_bounds12434 j hθ

noncomputable def covarianceInputs12434 :
    BstLean.Part263.CovarianceInputs 12434 scalarRow12434.grid parameters (caps repair12434) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12434 grid_top_bounds12434 repair12434

noncomputable def covarianceEvent12434 : Set (AgFam 12434) :=
  BstLean.Part263.covarianceEvent 12434 scalarRow12434.grid parameters

theorem covarianceEvent12434_measurable : MeasurableSet covarianceEvent12434 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12434_payment :
    (retDist (paperDesignP 12434).toCentres).real
      (agentEv (paperDesignP 12434) covarianceEvent12434)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12434

theorem localCov12434 : BstLean.Part259.LocalCovarianceOn covarianceEvent12434
    (BstLean.Part263.cell scalarRow12434.grid) (caps repair12434) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12434

theorem covarianceGood12434_payment :
    (retDist (paperDesignP 12434).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12434)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12434_payment



end BstLean.Part269.N12434

namespace BstLean.Part269.N12434
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12434}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12434.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12434) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12434).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12434 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12434) (by norm_num) BstLean.Part268.WorldRow12434.worldPackage rfl
    BstLean.Part268.WorldRow12434.product_lower (BstLean.Part268.WorldRow12434.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12434} (hw : c ∈ Hof BstLean.Part268.WorldRow12434.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12434) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12434) (by norm_num) BstLean.Part268.WorldRow12434.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12434} (hw : c ∈ Hof BstLean.Part268.WorldRow12434.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12434) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12434).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12434) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12434_eq : scalarRow12434.targetFrame = BstLean.Part268.agent12434.frame := by
  norm_num [scalarRow12434,BstLean.Part268.agent12434]

noncomputable def frameData12434 : BstLean.Part264b.FrameData 12434 :=
  BstLean.Part269.frameData_from_numerics (n := 12434) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12434.worldPackage rfl BstLean.Part268.WorldRow12434.product_lower (BstLean.Part268.WorldRow12434.producthi.2.trans (by norm_num))
    scalarRow12434 repair12434 covarianceInputs12434 (fun i hi => sourceNumerics12434 hi)
    BstLean.Part268.agent12434.frame targetFrame12434_eq


end BstLean.Part269.N12434
