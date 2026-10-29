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

namespace BstLean.Part269.N12520
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12520 : scalarRow12520.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12520, BstLean.Part268.grid12520, BstLean.Part263.worldGrid]

theorem supplies12520 (j : Fin 43) : Supply 12520 (parameters j)
    (cellLower scalarRow12520.grid (sourceIndex j))
    (cellUpper scalarRow12520.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12520.grid grid_top_bounds12520 j

theorem radii12520 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12520.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12520 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12520 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12520.grid grid_top_bounds12520 j hθ

noncomputable def covarianceInputs12520 :
    BstLean.Part263.CovarianceInputs 12520 scalarRow12520.grid parameters (caps repair12520) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12520 grid_top_bounds12520 repair12520

noncomputable def covarianceEvent12520 : Set (AgFam 12520) :=
  BstLean.Part263.covarianceEvent 12520 scalarRow12520.grid parameters

theorem covarianceEvent12520_measurable : MeasurableSet covarianceEvent12520 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12520_payment :
    (retDist (paperDesignP 12520).toCentres).real
      (agentEv (paperDesignP 12520) covarianceEvent12520)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12520

theorem localCov12520 : BstLean.Part259.LocalCovarianceOn covarianceEvent12520
    (BstLean.Part263.cell scalarRow12520.grid) (caps repair12520) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12520

theorem covarianceGood12520_payment :
    (retDist (paperDesignP 12520).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12520)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12520_payment



end BstLean.Part269.N12520

namespace BstLean.Part269.N12520
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12520}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12520.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12520) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12520).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12520 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12520) (by norm_num) BstLean.Part268.WorldRow12520.worldPackage rfl
    BstLean.Part268.WorldRow12520.product_lower (BstLean.Part268.WorldRow12520.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12520} (hw : c ∈ Hof BstLean.Part268.WorldRow12520.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12520) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12520) (by norm_num) BstLean.Part268.WorldRow12520.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12520} (hw : c ∈ Hof BstLean.Part268.WorldRow12520.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12520) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12520).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12520) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12520_eq : scalarRow12520.targetFrame = BstLean.Part268.agent12520.frame := by
  norm_num [scalarRow12520,BstLean.Part268.agent12520]

noncomputable def frameData12520 : BstLean.Part264b.FrameData 12520 :=
  BstLean.Part269.frameData_from_numerics (n := 12520) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12520.worldPackage rfl BstLean.Part268.WorldRow12520.product_lower (BstLean.Part268.WorldRow12520.producthi.2.trans (by norm_num))
    scalarRow12520 repair12520 covarianceInputs12520 (fun i hi => sourceNumerics12520 hi)
    BstLean.Part268.agent12520.frame targetFrame12520_eq


end BstLean.Part269.N12520

namespace BstLean.Part269.N12521
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12521 : scalarRow12521.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12521, BstLean.Part268.grid12521, BstLean.Part263.worldGrid]

theorem supplies12521 (j : Fin 43) : Supply 12521 (parameters j)
    (cellLower scalarRow12521.grid (sourceIndex j))
    (cellUpper scalarRow12521.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12521.grid grid_top_bounds12521 j

theorem radii12521 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12521.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12521 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12521 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12521.grid grid_top_bounds12521 j hθ

noncomputable def covarianceInputs12521 :
    BstLean.Part263.CovarianceInputs 12521 scalarRow12521.grid parameters (caps repair12521) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12521 grid_top_bounds12521 repair12521

noncomputable def covarianceEvent12521 : Set (AgFam 12521) :=
  BstLean.Part263.covarianceEvent 12521 scalarRow12521.grid parameters

theorem covarianceEvent12521_measurable : MeasurableSet covarianceEvent12521 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12521_payment :
    (retDist (paperDesignP 12521).toCentres).real
      (agentEv (paperDesignP 12521) covarianceEvent12521)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12521

theorem localCov12521 : BstLean.Part259.LocalCovarianceOn covarianceEvent12521
    (BstLean.Part263.cell scalarRow12521.grid) (caps repair12521) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12521

theorem covarianceGood12521_payment :
    (retDist (paperDesignP 12521).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12521)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12521_payment



end BstLean.Part269.N12521

namespace BstLean.Part269.N12521
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12521}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12521.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12521) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12521).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12521 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12521) (by norm_num) BstLean.Part268.WorldRow12521.worldPackage rfl
    BstLean.Part268.WorldRow12521.product_lower (BstLean.Part268.WorldRow12521.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12521} (hw : c ∈ Hof BstLean.Part268.WorldRow12521.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12521) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12521) (by norm_num) BstLean.Part268.WorldRow12521.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12521} (hw : c ∈ Hof BstLean.Part268.WorldRow12521.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12521) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12521).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12521) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12521_eq : scalarRow12521.targetFrame = BstLean.Part268.agent12521.frame := by
  norm_num [scalarRow12521,BstLean.Part268.agent12521]

noncomputable def frameData12521 : BstLean.Part264b.FrameData 12521 :=
  BstLean.Part269.frameData_from_numerics (n := 12521) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12521.worldPackage rfl BstLean.Part268.WorldRow12521.product_lower (BstLean.Part268.WorldRow12521.producthi.2.trans (by norm_num))
    scalarRow12521 repair12521 covarianceInputs12521 (fun i hi => sourceNumerics12521 hi)
    BstLean.Part268.agent12521.frame targetFrame12521_eq


end BstLean.Part269.N12521

namespace BstLean.Part269.N12522
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12522 : scalarRow12522.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12522, BstLean.Part268.grid12522, BstLean.Part263.worldGrid]

theorem supplies12522 (j : Fin 43) : Supply 12522 (parameters j)
    (cellLower scalarRow12522.grid (sourceIndex j))
    (cellUpper scalarRow12522.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12522.grid grid_top_bounds12522 j

theorem radii12522 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12522.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12522 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12522 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12522.grid grid_top_bounds12522 j hθ

noncomputable def covarianceInputs12522 :
    BstLean.Part263.CovarianceInputs 12522 scalarRow12522.grid parameters (caps repair12522) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12522 grid_top_bounds12522 repair12522

noncomputable def covarianceEvent12522 : Set (AgFam 12522) :=
  BstLean.Part263.covarianceEvent 12522 scalarRow12522.grid parameters

theorem covarianceEvent12522_measurable : MeasurableSet covarianceEvent12522 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12522_payment :
    (retDist (paperDesignP 12522).toCentres).real
      (agentEv (paperDesignP 12522) covarianceEvent12522)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12522

theorem localCov12522 : BstLean.Part259.LocalCovarianceOn covarianceEvent12522
    (BstLean.Part263.cell scalarRow12522.grid) (caps repair12522) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12522

theorem covarianceGood12522_payment :
    (retDist (paperDesignP 12522).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12522)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12522_payment



end BstLean.Part269.N12522

namespace BstLean.Part269.N12522
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12522}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12522.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12522) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12522).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12522 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12522) (by norm_num) BstLean.Part268.WorldRow12522.worldPackage rfl
    BstLean.Part268.WorldRow12522.product_lower (BstLean.Part268.WorldRow12522.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12522} (hw : c ∈ Hof BstLean.Part268.WorldRow12522.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12522) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12522) (by norm_num) BstLean.Part268.WorldRow12522.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12522} (hw : c ∈ Hof BstLean.Part268.WorldRow12522.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12522) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12522).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12522) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12522_eq : scalarRow12522.targetFrame = BstLean.Part268.agent12522.frame := by
  norm_num [scalarRow12522,BstLean.Part268.agent12522]

noncomputable def frameData12522 : BstLean.Part264b.FrameData 12522 :=
  BstLean.Part269.frameData_from_numerics (n := 12522) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12522.worldPackage rfl BstLean.Part268.WorldRow12522.product_lower (BstLean.Part268.WorldRow12522.producthi.2.trans (by norm_num))
    scalarRow12522 repair12522 covarianceInputs12522 (fun i hi => sourceNumerics12522 hi)
    BstLean.Part268.agent12522.frame targetFrame12522_eq


end BstLean.Part269.N12522

namespace BstLean.Part269.N12523
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12523 : scalarRow12523.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12523, BstLean.Part268.grid12523, BstLean.Part263.worldGrid]

theorem supplies12523 (j : Fin 43) : Supply 12523 (parameters j)
    (cellLower scalarRow12523.grid (sourceIndex j))
    (cellUpper scalarRow12523.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12523.grid grid_top_bounds12523 j

theorem radii12523 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12523.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12523 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12523 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12523.grid grid_top_bounds12523 j hθ

noncomputable def covarianceInputs12523 :
    BstLean.Part263.CovarianceInputs 12523 scalarRow12523.grid parameters (caps repair12523) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12523 grid_top_bounds12523 repair12523

noncomputable def covarianceEvent12523 : Set (AgFam 12523) :=
  BstLean.Part263.covarianceEvent 12523 scalarRow12523.grid parameters

theorem covarianceEvent12523_measurable : MeasurableSet covarianceEvent12523 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12523_payment :
    (retDist (paperDesignP 12523).toCentres).real
      (agentEv (paperDesignP 12523) covarianceEvent12523)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12523

theorem localCov12523 : BstLean.Part259.LocalCovarianceOn covarianceEvent12523
    (BstLean.Part263.cell scalarRow12523.grid) (caps repair12523) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12523

theorem covarianceGood12523_payment :
    (retDist (paperDesignP 12523).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12523)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12523_payment



end BstLean.Part269.N12523

namespace BstLean.Part269.N12523
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12523}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12523.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12523) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12523).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12523 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12523) (by norm_num) BstLean.Part268.WorldRow12523.worldPackage rfl
    BstLean.Part268.WorldRow12523.product_lower (BstLean.Part268.WorldRow12523.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12523} (hw : c ∈ Hof BstLean.Part268.WorldRow12523.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12523) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12523) (by norm_num) BstLean.Part268.WorldRow12523.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12523} (hw : c ∈ Hof BstLean.Part268.WorldRow12523.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12523) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12523).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12523) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12523_eq : scalarRow12523.targetFrame = BstLean.Part268.agent12523.frame := by
  norm_num [scalarRow12523,BstLean.Part268.agent12523]

noncomputable def frameData12523 : BstLean.Part264b.FrameData 12523 :=
  BstLean.Part269.frameData_from_numerics (n := 12523) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12523.worldPackage rfl BstLean.Part268.WorldRow12523.product_lower (BstLean.Part268.WorldRow12523.producthi.2.trans (by norm_num))
    scalarRow12523 repair12523 covarianceInputs12523 (fun i hi => sourceNumerics12523 hi)
    BstLean.Part268.agent12523.frame targetFrame12523_eq


end BstLean.Part269.N12523

namespace BstLean.Part269.N12524
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12524 : scalarRow12524.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12524, BstLean.Part268.grid12524, BstLean.Part263.worldGrid]

theorem supplies12524 (j : Fin 43) : Supply 12524 (parameters j)
    (cellLower scalarRow12524.grid (sourceIndex j))
    (cellUpper scalarRow12524.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12524.grid grid_top_bounds12524 j

theorem radii12524 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12524.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12524 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12524 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12524.grid grid_top_bounds12524 j hθ

noncomputable def covarianceInputs12524 :
    BstLean.Part263.CovarianceInputs 12524 scalarRow12524.grid parameters (caps repair12524) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12524 grid_top_bounds12524 repair12524

noncomputable def covarianceEvent12524 : Set (AgFam 12524) :=
  BstLean.Part263.covarianceEvent 12524 scalarRow12524.grid parameters

theorem covarianceEvent12524_measurable : MeasurableSet covarianceEvent12524 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12524_payment :
    (retDist (paperDesignP 12524).toCentres).real
      (agentEv (paperDesignP 12524) covarianceEvent12524)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12524

theorem localCov12524 : BstLean.Part259.LocalCovarianceOn covarianceEvent12524
    (BstLean.Part263.cell scalarRow12524.grid) (caps repair12524) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12524

theorem covarianceGood12524_payment :
    (retDist (paperDesignP 12524).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12524)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12524_payment



end BstLean.Part269.N12524

namespace BstLean.Part269.N12524
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12524}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12524.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12524) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12524).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12524 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12524) (by norm_num) BstLean.Part268.WorldRow12524.worldPackage rfl
    BstLean.Part268.WorldRow12524.product_lower (BstLean.Part268.WorldRow12524.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12524} (hw : c ∈ Hof BstLean.Part268.WorldRow12524.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12524) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12524) (by norm_num) BstLean.Part268.WorldRow12524.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12524} (hw : c ∈ Hof BstLean.Part268.WorldRow12524.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12524) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12524).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12524) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12524_eq : scalarRow12524.targetFrame = BstLean.Part268.agent12524.frame := by
  norm_num [scalarRow12524,BstLean.Part268.agent12524]

noncomputable def frameData12524 : BstLean.Part264b.FrameData 12524 :=
  BstLean.Part269.frameData_from_numerics (n := 12524) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12524.worldPackage rfl BstLean.Part268.WorldRow12524.product_lower (BstLean.Part268.WorldRow12524.producthi.2.trans (by norm_num))
    scalarRow12524 repair12524 covarianceInputs12524 (fun i hi => sourceNumerics12524 hi)
    BstLean.Part268.agent12524.frame targetFrame12524_eq


end BstLean.Part269.N12524
