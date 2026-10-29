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

namespace BstLean.Part269.N12405
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12405 : scalarRow12405.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12405, BstLean.Part268.grid12405, BstLean.Part263.worldGrid]

theorem supplies12405 (j : Fin 43) : Supply 12405 (parameters j)
    (cellLower scalarRow12405.grid (sourceIndex j))
    (cellUpper scalarRow12405.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12405.grid grid_top_bounds12405 j

theorem radii12405 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12405.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12405 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12405 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12405.grid grid_top_bounds12405 j hθ

noncomputable def covarianceInputs12405 :
    BstLean.Part263.CovarianceInputs 12405 scalarRow12405.grid parameters (caps repair12405) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12405 grid_top_bounds12405 repair12405

noncomputable def covarianceEvent12405 : Set (AgFam 12405) :=
  BstLean.Part263.covarianceEvent 12405 scalarRow12405.grid parameters

theorem covarianceEvent12405_measurable : MeasurableSet covarianceEvent12405 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12405_payment :
    (retDist (paperDesignP 12405).toCentres).real
      (agentEv (paperDesignP 12405) covarianceEvent12405)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12405

theorem localCov12405 : BstLean.Part259.LocalCovarianceOn covarianceEvent12405
    (BstLean.Part263.cell scalarRow12405.grid) (caps repair12405) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12405

theorem covarianceGood12405_payment :
    (retDist (paperDesignP 12405).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12405)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12405_payment



end BstLean.Part269.N12405

namespace BstLean.Part269.N12405
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12405}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12405.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12405) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12405).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12405 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12405) (by norm_num) BstLean.Part268.WorldRow12405.worldPackage rfl
    BstLean.Part268.WorldRow12405.product_lower (BstLean.Part268.WorldRow12405.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12405} (hw : c ∈ Hof BstLean.Part268.WorldRow12405.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12405) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12405) (by norm_num) BstLean.Part268.WorldRow12405.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12405} (hw : c ∈ Hof BstLean.Part268.WorldRow12405.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12405) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12405).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12405) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12405_eq : scalarRow12405.targetFrame = BstLean.Part268.agent12405.frame := by
  norm_num [scalarRow12405,BstLean.Part268.agent12405]

noncomputable def frameData12405 : BstLean.Part264b.FrameData 12405 :=
  BstLean.Part269.frameData_from_numerics (n := 12405) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12405.worldPackage rfl BstLean.Part268.WorldRow12405.product_lower (BstLean.Part268.WorldRow12405.producthi.2.trans (by norm_num))
    scalarRow12405 repair12405 covarianceInputs12405 (fun i hi => sourceNumerics12405 hi)
    BstLean.Part268.agent12405.frame targetFrame12405_eq


end BstLean.Part269.N12405

namespace BstLean.Part269.N12406
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12406 : scalarRow12406.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12406, BstLean.Part268.grid12406, BstLean.Part263.worldGrid]

theorem supplies12406 (j : Fin 43) : Supply 12406 (parameters j)
    (cellLower scalarRow12406.grid (sourceIndex j))
    (cellUpper scalarRow12406.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12406.grid grid_top_bounds12406 j

theorem radii12406 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12406.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12406 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12406 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12406.grid grid_top_bounds12406 j hθ

noncomputable def covarianceInputs12406 :
    BstLean.Part263.CovarianceInputs 12406 scalarRow12406.grid parameters (caps repair12406) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12406 grid_top_bounds12406 repair12406

noncomputable def covarianceEvent12406 : Set (AgFam 12406) :=
  BstLean.Part263.covarianceEvent 12406 scalarRow12406.grid parameters

theorem covarianceEvent12406_measurable : MeasurableSet covarianceEvent12406 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12406_payment :
    (retDist (paperDesignP 12406).toCentres).real
      (agentEv (paperDesignP 12406) covarianceEvent12406)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12406

theorem localCov12406 : BstLean.Part259.LocalCovarianceOn covarianceEvent12406
    (BstLean.Part263.cell scalarRow12406.grid) (caps repair12406) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12406

theorem covarianceGood12406_payment :
    (retDist (paperDesignP 12406).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12406)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12406_payment



end BstLean.Part269.N12406

namespace BstLean.Part269.N12406
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12406}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12406.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12406) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12406).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12406 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12406) (by norm_num) BstLean.Part268.WorldRow12406.worldPackage rfl
    BstLean.Part268.WorldRow12406.product_lower (BstLean.Part268.WorldRow12406.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12406} (hw : c ∈ Hof BstLean.Part268.WorldRow12406.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12406) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12406) (by norm_num) BstLean.Part268.WorldRow12406.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12406} (hw : c ∈ Hof BstLean.Part268.WorldRow12406.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12406) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12406).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12406) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12406_eq : scalarRow12406.targetFrame = BstLean.Part268.agent12406.frame := by
  norm_num [scalarRow12406,BstLean.Part268.agent12406]

noncomputable def frameData12406 : BstLean.Part264b.FrameData 12406 :=
  BstLean.Part269.frameData_from_numerics (n := 12406) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12406.worldPackage rfl BstLean.Part268.WorldRow12406.product_lower (BstLean.Part268.WorldRow12406.producthi.2.trans (by norm_num))
    scalarRow12406 repair12406 covarianceInputs12406 (fun i hi => sourceNumerics12406 hi)
    BstLean.Part268.agent12406.frame targetFrame12406_eq


end BstLean.Part269.N12406

namespace BstLean.Part269.N12407
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12407 : scalarRow12407.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12407, BstLean.Part268.grid12407, BstLean.Part263.worldGrid]

theorem supplies12407 (j : Fin 43) : Supply 12407 (parameters j)
    (cellLower scalarRow12407.grid (sourceIndex j))
    (cellUpper scalarRow12407.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12407.grid grid_top_bounds12407 j

theorem radii12407 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12407.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12407 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12407 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12407.grid grid_top_bounds12407 j hθ

noncomputable def covarianceInputs12407 :
    BstLean.Part263.CovarianceInputs 12407 scalarRow12407.grid parameters (caps repair12407) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12407 grid_top_bounds12407 repair12407

noncomputable def covarianceEvent12407 : Set (AgFam 12407) :=
  BstLean.Part263.covarianceEvent 12407 scalarRow12407.grid parameters

theorem covarianceEvent12407_measurable : MeasurableSet covarianceEvent12407 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12407_payment :
    (retDist (paperDesignP 12407).toCentres).real
      (agentEv (paperDesignP 12407) covarianceEvent12407)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12407

theorem localCov12407 : BstLean.Part259.LocalCovarianceOn covarianceEvent12407
    (BstLean.Part263.cell scalarRow12407.grid) (caps repair12407) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12407

theorem covarianceGood12407_payment :
    (retDist (paperDesignP 12407).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12407)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12407_payment



end BstLean.Part269.N12407

namespace BstLean.Part269.N12407
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12407}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12407.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12407) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12407).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12407 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12407) (by norm_num) BstLean.Part268.WorldRow12407.worldPackage rfl
    BstLean.Part268.WorldRow12407.product_lower (BstLean.Part268.WorldRow12407.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12407} (hw : c ∈ Hof BstLean.Part268.WorldRow12407.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12407) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12407) (by norm_num) BstLean.Part268.WorldRow12407.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12407} (hw : c ∈ Hof BstLean.Part268.WorldRow12407.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12407) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12407).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12407) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12407_eq : scalarRow12407.targetFrame = BstLean.Part268.agent12407.frame := by
  norm_num [scalarRow12407,BstLean.Part268.agent12407]

noncomputable def frameData12407 : BstLean.Part264b.FrameData 12407 :=
  BstLean.Part269.frameData_from_numerics (n := 12407) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12407.worldPackage rfl BstLean.Part268.WorldRow12407.product_lower (BstLean.Part268.WorldRow12407.producthi.2.trans (by norm_num))
    scalarRow12407 repair12407 covarianceInputs12407 (fun i hi => sourceNumerics12407 hi)
    BstLean.Part268.agent12407.frame targetFrame12407_eq


end BstLean.Part269.N12407

namespace BstLean.Part269.N12408
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12408 : scalarRow12408.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12408, BstLean.Part268.grid12408, BstLean.Part263.worldGrid]

theorem supplies12408 (j : Fin 43) : Supply 12408 (parameters j)
    (cellLower scalarRow12408.grid (sourceIndex j))
    (cellUpper scalarRow12408.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12408.grid grid_top_bounds12408 j

theorem radii12408 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12408.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12408 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12408 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12408.grid grid_top_bounds12408 j hθ

noncomputable def covarianceInputs12408 :
    BstLean.Part263.CovarianceInputs 12408 scalarRow12408.grid parameters (caps repair12408) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12408 grid_top_bounds12408 repair12408

noncomputable def covarianceEvent12408 : Set (AgFam 12408) :=
  BstLean.Part263.covarianceEvent 12408 scalarRow12408.grid parameters

theorem covarianceEvent12408_measurable : MeasurableSet covarianceEvent12408 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12408_payment :
    (retDist (paperDesignP 12408).toCentres).real
      (agentEv (paperDesignP 12408) covarianceEvent12408)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12408

theorem localCov12408 : BstLean.Part259.LocalCovarianceOn covarianceEvent12408
    (BstLean.Part263.cell scalarRow12408.grid) (caps repair12408) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12408

theorem covarianceGood12408_payment :
    (retDist (paperDesignP 12408).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12408)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12408_payment



end BstLean.Part269.N12408

namespace BstLean.Part269.N12408
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12408}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12408.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12408) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12408).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12408 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12408) (by norm_num) BstLean.Part268.WorldRow12408.worldPackage rfl
    BstLean.Part268.WorldRow12408.product_lower (BstLean.Part268.WorldRow12408.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12408} (hw : c ∈ Hof BstLean.Part268.WorldRow12408.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12408) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12408) (by norm_num) BstLean.Part268.WorldRow12408.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12408} (hw : c ∈ Hof BstLean.Part268.WorldRow12408.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12408) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12408).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12408) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12408_eq : scalarRow12408.targetFrame = BstLean.Part268.agent12408.frame := by
  norm_num [scalarRow12408,BstLean.Part268.agent12408]

noncomputable def frameData12408 : BstLean.Part264b.FrameData 12408 :=
  BstLean.Part269.frameData_from_numerics (n := 12408) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12408.worldPackage rfl BstLean.Part268.WorldRow12408.product_lower (BstLean.Part268.WorldRow12408.producthi.2.trans (by norm_num))
    scalarRow12408 repair12408 covarianceInputs12408 (fun i hi => sourceNumerics12408 hi)
    BstLean.Part268.agent12408.frame targetFrame12408_eq


end BstLean.Part269.N12408

namespace BstLean.Part269.N12409
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12409 : scalarRow12409.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12409, BstLean.Part268.grid12409, BstLean.Part263.worldGrid]

theorem supplies12409 (j : Fin 43) : Supply 12409 (parameters j)
    (cellLower scalarRow12409.grid (sourceIndex j))
    (cellUpper scalarRow12409.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12409.grid grid_top_bounds12409 j

theorem radii12409 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12409.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12409 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12409 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12409.grid grid_top_bounds12409 j hθ

noncomputable def covarianceInputs12409 :
    BstLean.Part263.CovarianceInputs 12409 scalarRow12409.grid parameters (caps repair12409) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12409 grid_top_bounds12409 repair12409

noncomputable def covarianceEvent12409 : Set (AgFam 12409) :=
  BstLean.Part263.covarianceEvent 12409 scalarRow12409.grid parameters

theorem covarianceEvent12409_measurable : MeasurableSet covarianceEvent12409 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12409_payment :
    (retDist (paperDesignP 12409).toCentres).real
      (agentEv (paperDesignP 12409) covarianceEvent12409)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12409

theorem localCov12409 : BstLean.Part259.LocalCovarianceOn covarianceEvent12409
    (BstLean.Part263.cell scalarRow12409.grid) (caps repair12409) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12409

theorem covarianceGood12409_payment :
    (retDist (paperDesignP 12409).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12409)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12409_payment



end BstLean.Part269.N12409

namespace BstLean.Part269.N12409
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12409}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12409.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12409) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12409).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12409 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12409) (by norm_num) BstLean.Part268.WorldRow12409.worldPackage rfl
    BstLean.Part268.WorldRow12409.product_lower (BstLean.Part268.WorldRow12409.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12409} (hw : c ∈ Hof BstLean.Part268.WorldRow12409.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12409) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12409) (by norm_num) BstLean.Part268.WorldRow12409.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12409} (hw : c ∈ Hof BstLean.Part268.WorldRow12409.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12409) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12409).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12409) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12409_eq : scalarRow12409.targetFrame = BstLean.Part268.agent12409.frame := by
  norm_num [scalarRow12409,BstLean.Part268.agent12409]

noncomputable def frameData12409 : BstLean.Part264b.FrameData 12409 :=
  BstLean.Part269.frameData_from_numerics (n := 12409) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12409.worldPackage rfl BstLean.Part268.WorldRow12409.product_lower (BstLean.Part268.WorldRow12409.producthi.2.trans (by norm_num))
    scalarRow12409 repair12409 covarianceInputs12409 (fun i hi => sourceNumerics12409 hi)
    BstLean.Part268.agent12409.frame targetFrame12409_eq


end BstLean.Part269.N12409
