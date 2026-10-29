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

namespace BstLean.Part269.N12445
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12445 : scalarRow12445.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12445, BstLean.Part268.grid12445, BstLean.Part263.worldGrid]

theorem supplies12445 (j : Fin 43) : Supply 12445 (parameters j)
    (cellLower scalarRow12445.grid (sourceIndex j))
    (cellUpper scalarRow12445.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12445.grid grid_top_bounds12445 j

theorem radii12445 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12445.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12445 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12445 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12445.grid grid_top_bounds12445 j hθ

noncomputable def covarianceInputs12445 :
    BstLean.Part263.CovarianceInputs 12445 scalarRow12445.grid parameters (caps repair12445) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12445 grid_top_bounds12445 repair12445

noncomputable def covarianceEvent12445 : Set (AgFam 12445) :=
  BstLean.Part263.covarianceEvent 12445 scalarRow12445.grid parameters

theorem covarianceEvent12445_measurable : MeasurableSet covarianceEvent12445 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12445_payment :
    (retDist (paperDesignP 12445).toCentres).real
      (agentEv (paperDesignP 12445) covarianceEvent12445)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12445

theorem localCov12445 : BstLean.Part259.LocalCovarianceOn covarianceEvent12445
    (BstLean.Part263.cell scalarRow12445.grid) (caps repair12445) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12445

theorem covarianceGood12445_payment :
    (retDist (paperDesignP 12445).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12445)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12445_payment



end BstLean.Part269.N12445

namespace BstLean.Part269.N12445
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12445}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12445.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12445) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12445).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12445 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12445) (by norm_num) BstLean.Part268.WorldRow12445.worldPackage rfl
    BstLean.Part268.WorldRow12445.product_lower (BstLean.Part268.WorldRow12445.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12445} (hw : c ∈ Hof BstLean.Part268.WorldRow12445.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12445) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12445) (by norm_num) BstLean.Part268.WorldRow12445.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12445} (hw : c ∈ Hof BstLean.Part268.WorldRow12445.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12445) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12445).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12445) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12445_eq : scalarRow12445.targetFrame = BstLean.Part268.agent12445.frame := by
  norm_num [scalarRow12445,BstLean.Part268.agent12445]

noncomputable def frameData12445 : BstLean.Part264b.FrameData 12445 :=
  BstLean.Part269.frameData_from_numerics (n := 12445) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12445.worldPackage rfl BstLean.Part268.WorldRow12445.product_lower (BstLean.Part268.WorldRow12445.producthi.2.trans (by norm_num))
    scalarRow12445 repair12445 covarianceInputs12445 (fun i hi => sourceNumerics12445 hi)
    BstLean.Part268.agent12445.frame targetFrame12445_eq


end BstLean.Part269.N12445

namespace BstLean.Part269.N12446
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12446 : scalarRow12446.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12446, BstLean.Part268.grid12446, BstLean.Part263.worldGrid]

theorem supplies12446 (j : Fin 43) : Supply 12446 (parameters j)
    (cellLower scalarRow12446.grid (sourceIndex j))
    (cellUpper scalarRow12446.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12446.grid grid_top_bounds12446 j

theorem radii12446 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12446.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12446 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12446 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12446.grid grid_top_bounds12446 j hθ

noncomputable def covarianceInputs12446 :
    BstLean.Part263.CovarianceInputs 12446 scalarRow12446.grid parameters (caps repair12446) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12446 grid_top_bounds12446 repair12446

noncomputable def covarianceEvent12446 : Set (AgFam 12446) :=
  BstLean.Part263.covarianceEvent 12446 scalarRow12446.grid parameters

theorem covarianceEvent12446_measurable : MeasurableSet covarianceEvent12446 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12446_payment :
    (retDist (paperDesignP 12446).toCentres).real
      (agentEv (paperDesignP 12446) covarianceEvent12446)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12446

theorem localCov12446 : BstLean.Part259.LocalCovarianceOn covarianceEvent12446
    (BstLean.Part263.cell scalarRow12446.grid) (caps repair12446) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12446

theorem covarianceGood12446_payment :
    (retDist (paperDesignP 12446).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12446)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12446_payment



end BstLean.Part269.N12446

namespace BstLean.Part269.N12446
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12446}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12446.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12446) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12446).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12446 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12446) (by norm_num) BstLean.Part268.WorldRow12446.worldPackage rfl
    BstLean.Part268.WorldRow12446.product_lower (BstLean.Part268.WorldRow12446.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12446} (hw : c ∈ Hof BstLean.Part268.WorldRow12446.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12446) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12446) (by norm_num) BstLean.Part268.WorldRow12446.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12446} (hw : c ∈ Hof BstLean.Part268.WorldRow12446.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12446) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12446).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12446) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12446_eq : scalarRow12446.targetFrame = BstLean.Part268.agent12446.frame := by
  norm_num [scalarRow12446,BstLean.Part268.agent12446]

noncomputable def frameData12446 : BstLean.Part264b.FrameData 12446 :=
  BstLean.Part269.frameData_from_numerics (n := 12446) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12446.worldPackage rfl BstLean.Part268.WorldRow12446.product_lower (BstLean.Part268.WorldRow12446.producthi.2.trans (by norm_num))
    scalarRow12446 repair12446 covarianceInputs12446 (fun i hi => sourceNumerics12446 hi)
    BstLean.Part268.agent12446.frame targetFrame12446_eq


end BstLean.Part269.N12446

namespace BstLean.Part269.N12447
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12447 : scalarRow12447.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12447, BstLean.Part268.grid12447, BstLean.Part263.worldGrid]

theorem supplies12447 (j : Fin 43) : Supply 12447 (parameters j)
    (cellLower scalarRow12447.grid (sourceIndex j))
    (cellUpper scalarRow12447.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12447.grid grid_top_bounds12447 j

theorem radii12447 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12447.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12447 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12447 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12447.grid grid_top_bounds12447 j hθ

noncomputable def covarianceInputs12447 :
    BstLean.Part263.CovarianceInputs 12447 scalarRow12447.grid parameters (caps repair12447) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12447 grid_top_bounds12447 repair12447

noncomputable def covarianceEvent12447 : Set (AgFam 12447) :=
  BstLean.Part263.covarianceEvent 12447 scalarRow12447.grid parameters

theorem covarianceEvent12447_measurable : MeasurableSet covarianceEvent12447 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12447_payment :
    (retDist (paperDesignP 12447).toCentres).real
      (agentEv (paperDesignP 12447) covarianceEvent12447)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12447

theorem localCov12447 : BstLean.Part259.LocalCovarianceOn covarianceEvent12447
    (BstLean.Part263.cell scalarRow12447.grid) (caps repair12447) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12447

theorem covarianceGood12447_payment :
    (retDist (paperDesignP 12447).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12447)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12447_payment



end BstLean.Part269.N12447

namespace BstLean.Part269.N12447
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12447}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12447.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12447) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12447).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12447 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12447) (by norm_num) BstLean.Part268.WorldRow12447.worldPackage rfl
    BstLean.Part268.WorldRow12447.product_lower (BstLean.Part268.WorldRow12447.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12447} (hw : c ∈ Hof BstLean.Part268.WorldRow12447.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12447) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12447) (by norm_num) BstLean.Part268.WorldRow12447.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12447} (hw : c ∈ Hof BstLean.Part268.WorldRow12447.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12447) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12447).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12447) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12447_eq : scalarRow12447.targetFrame = BstLean.Part268.agent12447.frame := by
  norm_num [scalarRow12447,BstLean.Part268.agent12447]

noncomputable def frameData12447 : BstLean.Part264b.FrameData 12447 :=
  BstLean.Part269.frameData_from_numerics (n := 12447) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12447.worldPackage rfl BstLean.Part268.WorldRow12447.product_lower (BstLean.Part268.WorldRow12447.producthi.2.trans (by norm_num))
    scalarRow12447 repair12447 covarianceInputs12447 (fun i hi => sourceNumerics12447 hi)
    BstLean.Part268.agent12447.frame targetFrame12447_eq


end BstLean.Part269.N12447

namespace BstLean.Part269.N12448
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12448 : scalarRow12448.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12448, BstLean.Part268.grid12448, BstLean.Part263.worldGrid]

theorem supplies12448 (j : Fin 43) : Supply 12448 (parameters j)
    (cellLower scalarRow12448.grid (sourceIndex j))
    (cellUpper scalarRow12448.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12448.grid grid_top_bounds12448 j

theorem radii12448 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12448.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12448 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12448 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12448.grid grid_top_bounds12448 j hθ

noncomputable def covarianceInputs12448 :
    BstLean.Part263.CovarianceInputs 12448 scalarRow12448.grid parameters (caps repair12448) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12448 grid_top_bounds12448 repair12448

noncomputable def covarianceEvent12448 : Set (AgFam 12448) :=
  BstLean.Part263.covarianceEvent 12448 scalarRow12448.grid parameters

theorem covarianceEvent12448_measurable : MeasurableSet covarianceEvent12448 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12448_payment :
    (retDist (paperDesignP 12448).toCentres).real
      (agentEv (paperDesignP 12448) covarianceEvent12448)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12448

theorem localCov12448 : BstLean.Part259.LocalCovarianceOn covarianceEvent12448
    (BstLean.Part263.cell scalarRow12448.grid) (caps repair12448) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12448

theorem covarianceGood12448_payment :
    (retDist (paperDesignP 12448).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12448)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12448_payment



end BstLean.Part269.N12448

namespace BstLean.Part269.N12448
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12448}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12448.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12448) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12448).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12448 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12448) (by norm_num) BstLean.Part268.WorldRow12448.worldPackage rfl
    BstLean.Part268.WorldRow12448.product_lower (BstLean.Part268.WorldRow12448.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12448} (hw : c ∈ Hof BstLean.Part268.WorldRow12448.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12448) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12448) (by norm_num) BstLean.Part268.WorldRow12448.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12448} (hw : c ∈ Hof BstLean.Part268.WorldRow12448.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12448) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12448).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12448) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12448_eq : scalarRow12448.targetFrame = BstLean.Part268.agent12448.frame := by
  norm_num [scalarRow12448,BstLean.Part268.agent12448]

noncomputable def frameData12448 : BstLean.Part264b.FrameData 12448 :=
  BstLean.Part269.frameData_from_numerics (n := 12448) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12448.worldPackage rfl BstLean.Part268.WorldRow12448.product_lower (BstLean.Part268.WorldRow12448.producthi.2.trans (by norm_num))
    scalarRow12448 repair12448 covarianceInputs12448 (fun i hi => sourceNumerics12448 hi)
    BstLean.Part268.agent12448.frame targetFrame12448_eq


end BstLean.Part269.N12448

namespace BstLean.Part269.N12449
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12449 : scalarRow12449.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12449, BstLean.Part268.grid12449, BstLean.Part263.worldGrid]

theorem supplies12449 (j : Fin 43) : Supply 12449 (parameters j)
    (cellLower scalarRow12449.grid (sourceIndex j))
    (cellUpper scalarRow12449.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12449.grid grid_top_bounds12449 j

theorem radii12449 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12449.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12449 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12449 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12449.grid grid_top_bounds12449 j hθ

noncomputable def covarianceInputs12449 :
    BstLean.Part263.CovarianceInputs 12449 scalarRow12449.grid parameters (caps repair12449) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12449 grid_top_bounds12449 repair12449

noncomputable def covarianceEvent12449 : Set (AgFam 12449) :=
  BstLean.Part263.covarianceEvent 12449 scalarRow12449.grid parameters

theorem covarianceEvent12449_measurable : MeasurableSet covarianceEvent12449 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12449_payment :
    (retDist (paperDesignP 12449).toCentres).real
      (agentEv (paperDesignP 12449) covarianceEvent12449)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12449

theorem localCov12449 : BstLean.Part259.LocalCovarianceOn covarianceEvent12449
    (BstLean.Part263.cell scalarRow12449.grid) (caps repair12449) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12449

theorem covarianceGood12449_payment :
    (retDist (paperDesignP 12449).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12449)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12449_payment



end BstLean.Part269.N12449

namespace BstLean.Part269.N12449
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12449}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12449.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12449) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12449).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12449 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12449) (by norm_num) BstLean.Part268.WorldRow12449.worldPackage rfl
    BstLean.Part268.WorldRow12449.product_lower (BstLean.Part268.WorldRow12449.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12449} (hw : c ∈ Hof BstLean.Part268.WorldRow12449.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12449) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12449) (by norm_num) BstLean.Part268.WorldRow12449.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12449} (hw : c ∈ Hof BstLean.Part268.WorldRow12449.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12449) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12449).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12449) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12449_eq : scalarRow12449.targetFrame = BstLean.Part268.agent12449.frame := by
  norm_num [scalarRow12449,BstLean.Part268.agent12449]

noncomputable def frameData12449 : BstLean.Part264b.FrameData 12449 :=
  BstLean.Part269.frameData_from_numerics (n := 12449) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12449.worldPackage rfl BstLean.Part268.WorldRow12449.product_lower (BstLean.Part268.WorldRow12449.producthi.2.trans (by norm_num))
    scalarRow12449 repair12449 covarianceInputs12449 (fun i hi => sourceNumerics12449 hi)
    BstLean.Part268.agent12449.frame targetFrame12449_eq


end BstLean.Part269.N12449
