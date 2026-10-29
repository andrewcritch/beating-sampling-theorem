import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World5Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs5
import BstLean.Part269Rows5
import BstLean.Part269Sources5
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12485
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12485 : scalarRow12485.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12485, BstLean.Part268.grid12485, BstLean.Part263.worldGrid]

theorem supplies12485 (j : Fin 43) : Supply 12485 (parameters j)
    (cellLower scalarRow12485.grid (sourceIndex j))
    (cellUpper scalarRow12485.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12485.grid grid_top_bounds12485 j

theorem radii12485 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12485.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12485 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12485 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12485.grid grid_top_bounds12485 j hθ

noncomputable def covarianceInputs12485 :
    BstLean.Part263.CovarianceInputs 12485 scalarRow12485.grid parameters (caps repair12485) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12485 grid_top_bounds12485 repair12485

noncomputable def covarianceEvent12485 : Set (AgFam 12485) :=
  BstLean.Part263.covarianceEvent 12485 scalarRow12485.grid parameters

theorem covarianceEvent12485_measurable : MeasurableSet covarianceEvent12485 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12485_payment :
    (retDist (paperDesignP 12485).toCentres).real
      (agentEv (paperDesignP 12485) covarianceEvent12485)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12485

theorem localCov12485 : BstLean.Part259.LocalCovarianceOn covarianceEvent12485
    (BstLean.Part263.cell scalarRow12485.grid) (caps repair12485) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12485

theorem covarianceGood12485_payment :
    (retDist (paperDesignP 12485).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12485)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12485_payment



end BstLean.Part269.N12485

namespace BstLean.Part269.N12485
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12485}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12485.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12485) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12485).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12485 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12485) (by norm_num) BstLean.Part268.WorldRow12485.worldPackage rfl
    BstLean.Part268.WorldRow12485.product_lower (BstLean.Part268.WorldRow12485.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12485} (hw : c ∈ Hof BstLean.Part268.WorldRow12485.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12485) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12485) (by norm_num) BstLean.Part268.WorldRow12485.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12485} (hw : c ∈ Hof BstLean.Part268.WorldRow12485.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12485) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12485).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12485) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12485_eq : scalarRow12485.targetFrame = BstLean.Part268.agent12485.frame := by
  norm_num [scalarRow12485,BstLean.Part268.agent12485]

noncomputable def frameData12485 : BstLean.Part264b.FrameData 12485 :=
  BstLean.Part269.frameData_from_numerics (n := 12485) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12485.worldPackage rfl BstLean.Part268.WorldRow12485.product_lower (BstLean.Part268.WorldRow12485.producthi.2.trans (by norm_num))
    scalarRow12485 repair12485 covarianceInputs12485 (fun i hi => sourceNumerics12485 hi)
    BstLean.Part268.agent12485.frame targetFrame12485_eq


end BstLean.Part269.N12485

namespace BstLean.Part269.N12486
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12486 : scalarRow12486.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12486, BstLean.Part268.grid12486, BstLean.Part263.worldGrid]

theorem supplies12486 (j : Fin 43) : Supply 12486 (parameters j)
    (cellLower scalarRow12486.grid (sourceIndex j))
    (cellUpper scalarRow12486.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12486.grid grid_top_bounds12486 j

theorem radii12486 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12486.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12486 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12486 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12486.grid grid_top_bounds12486 j hθ

noncomputable def covarianceInputs12486 :
    BstLean.Part263.CovarianceInputs 12486 scalarRow12486.grid parameters (caps repair12486) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12486 grid_top_bounds12486 repair12486

noncomputable def covarianceEvent12486 : Set (AgFam 12486) :=
  BstLean.Part263.covarianceEvent 12486 scalarRow12486.grid parameters

theorem covarianceEvent12486_measurable : MeasurableSet covarianceEvent12486 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12486_payment :
    (retDist (paperDesignP 12486).toCentres).real
      (agentEv (paperDesignP 12486) covarianceEvent12486)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12486

theorem localCov12486 : BstLean.Part259.LocalCovarianceOn covarianceEvent12486
    (BstLean.Part263.cell scalarRow12486.grid) (caps repair12486) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12486

theorem covarianceGood12486_payment :
    (retDist (paperDesignP 12486).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12486)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12486_payment



end BstLean.Part269.N12486

namespace BstLean.Part269.N12486
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12486}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12486.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12486) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12486).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12486 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12486) (by norm_num) BstLean.Part268.WorldRow12486.worldPackage rfl
    BstLean.Part268.WorldRow12486.product_lower (BstLean.Part268.WorldRow12486.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12486} (hw : c ∈ Hof BstLean.Part268.WorldRow12486.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12486) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12486) (by norm_num) BstLean.Part268.WorldRow12486.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12486} (hw : c ∈ Hof BstLean.Part268.WorldRow12486.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12486) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12486).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12486) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12486_eq : scalarRow12486.targetFrame = BstLean.Part268.agent12486.frame := by
  norm_num [scalarRow12486,BstLean.Part268.agent12486]

noncomputable def frameData12486 : BstLean.Part264b.FrameData 12486 :=
  BstLean.Part269.frameData_from_numerics (n := 12486) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12486.worldPackage rfl BstLean.Part268.WorldRow12486.product_lower (BstLean.Part268.WorldRow12486.producthi.2.trans (by norm_num))
    scalarRow12486 repair12486 covarianceInputs12486 (fun i hi => sourceNumerics12486 hi)
    BstLean.Part268.agent12486.frame targetFrame12486_eq


end BstLean.Part269.N12486

namespace BstLean.Part269.N12487
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12487 : scalarRow12487.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12487, BstLean.Part268.grid12487, BstLean.Part263.worldGrid]

theorem supplies12487 (j : Fin 43) : Supply 12487 (parameters j)
    (cellLower scalarRow12487.grid (sourceIndex j))
    (cellUpper scalarRow12487.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12487.grid grid_top_bounds12487 j

theorem radii12487 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12487.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12487 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12487 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12487.grid grid_top_bounds12487 j hθ

noncomputable def covarianceInputs12487 :
    BstLean.Part263.CovarianceInputs 12487 scalarRow12487.grid parameters (caps repair12487) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12487 grid_top_bounds12487 repair12487

noncomputable def covarianceEvent12487 : Set (AgFam 12487) :=
  BstLean.Part263.covarianceEvent 12487 scalarRow12487.grid parameters

theorem covarianceEvent12487_measurable : MeasurableSet covarianceEvent12487 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12487_payment :
    (retDist (paperDesignP 12487).toCentres).real
      (agentEv (paperDesignP 12487) covarianceEvent12487)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12487

theorem localCov12487 : BstLean.Part259.LocalCovarianceOn covarianceEvent12487
    (BstLean.Part263.cell scalarRow12487.grid) (caps repair12487) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12487

theorem covarianceGood12487_payment :
    (retDist (paperDesignP 12487).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12487)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12487_payment



end BstLean.Part269.N12487

namespace BstLean.Part269.N12487
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12487}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12487.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12487) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12487).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12487 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12487) (by norm_num) BstLean.Part268.WorldRow12487.worldPackage rfl
    BstLean.Part268.WorldRow12487.product_lower (BstLean.Part268.WorldRow12487.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12487} (hw : c ∈ Hof BstLean.Part268.WorldRow12487.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12487) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12487) (by norm_num) BstLean.Part268.WorldRow12487.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12487} (hw : c ∈ Hof BstLean.Part268.WorldRow12487.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12487) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12487).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12487) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12487_eq : scalarRow12487.targetFrame = BstLean.Part268.agent12487.frame := by
  norm_num [scalarRow12487,BstLean.Part268.agent12487]

noncomputable def frameData12487 : BstLean.Part264b.FrameData 12487 :=
  BstLean.Part269.frameData_from_numerics (n := 12487) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12487.worldPackage rfl BstLean.Part268.WorldRow12487.product_lower (BstLean.Part268.WorldRow12487.producthi.2.trans (by norm_num))
    scalarRow12487 repair12487 covarianceInputs12487 (fun i hi => sourceNumerics12487 hi)
    BstLean.Part268.agent12487.frame targetFrame12487_eq


end BstLean.Part269.N12487

namespace BstLean.Part269.N12488
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12488 : scalarRow12488.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12488, BstLean.Part268.grid12488, BstLean.Part263.worldGrid]

theorem supplies12488 (j : Fin 43) : Supply 12488 (parameters j)
    (cellLower scalarRow12488.grid (sourceIndex j))
    (cellUpper scalarRow12488.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12488.grid grid_top_bounds12488 j

theorem radii12488 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12488.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12488 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12488 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12488.grid grid_top_bounds12488 j hθ

noncomputable def covarianceInputs12488 :
    BstLean.Part263.CovarianceInputs 12488 scalarRow12488.grid parameters (caps repair12488) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12488 grid_top_bounds12488 repair12488

noncomputable def covarianceEvent12488 : Set (AgFam 12488) :=
  BstLean.Part263.covarianceEvent 12488 scalarRow12488.grid parameters

theorem covarianceEvent12488_measurable : MeasurableSet covarianceEvent12488 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12488_payment :
    (retDist (paperDesignP 12488).toCentres).real
      (agentEv (paperDesignP 12488) covarianceEvent12488)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12488

theorem localCov12488 : BstLean.Part259.LocalCovarianceOn covarianceEvent12488
    (BstLean.Part263.cell scalarRow12488.grid) (caps repair12488) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12488

theorem covarianceGood12488_payment :
    (retDist (paperDesignP 12488).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12488)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12488_payment



end BstLean.Part269.N12488

namespace BstLean.Part269.N12488
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12488}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12488.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12488) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12488).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12488 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12488) (by norm_num) BstLean.Part268.WorldRow12488.worldPackage rfl
    BstLean.Part268.WorldRow12488.product_lower (BstLean.Part268.WorldRow12488.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12488} (hw : c ∈ Hof BstLean.Part268.WorldRow12488.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12488) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12488) (by norm_num) BstLean.Part268.WorldRow12488.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12488} (hw : c ∈ Hof BstLean.Part268.WorldRow12488.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12488) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12488).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12488) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12488_eq : scalarRow12488.targetFrame = BstLean.Part268.agent12488.frame := by
  norm_num [scalarRow12488,BstLean.Part268.agent12488]

noncomputable def frameData12488 : BstLean.Part264b.FrameData 12488 :=
  BstLean.Part269.frameData_from_numerics (n := 12488) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12488.worldPackage rfl BstLean.Part268.WorldRow12488.product_lower (BstLean.Part268.WorldRow12488.producthi.2.trans (by norm_num))
    scalarRow12488 repair12488 covarianceInputs12488 (fun i hi => sourceNumerics12488 hi)
    BstLean.Part268.agent12488.frame targetFrame12488_eq


end BstLean.Part269.N12488

namespace BstLean.Part269.N12489
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12489 : scalarRow12489.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12489, BstLean.Part268.grid12489, BstLean.Part263.worldGrid]

theorem supplies12489 (j : Fin 43) : Supply 12489 (parameters j)
    (cellLower scalarRow12489.grid (sourceIndex j))
    (cellUpper scalarRow12489.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12489.grid grid_top_bounds12489 j

theorem radii12489 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12489.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12489 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12489 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12489.grid grid_top_bounds12489 j hθ

noncomputable def covarianceInputs12489 :
    BstLean.Part263.CovarianceInputs 12489 scalarRow12489.grid parameters (caps repair12489) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12489 grid_top_bounds12489 repair12489

noncomputable def covarianceEvent12489 : Set (AgFam 12489) :=
  BstLean.Part263.covarianceEvent 12489 scalarRow12489.grid parameters

theorem covarianceEvent12489_measurable : MeasurableSet covarianceEvent12489 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12489_payment :
    (retDist (paperDesignP 12489).toCentres).real
      (agentEv (paperDesignP 12489) covarianceEvent12489)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12489

theorem localCov12489 : BstLean.Part259.LocalCovarianceOn covarianceEvent12489
    (BstLean.Part263.cell scalarRow12489.grid) (caps repair12489) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12489

theorem covarianceGood12489_payment :
    (retDist (paperDesignP 12489).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12489)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12489_payment



end BstLean.Part269.N12489

namespace BstLean.Part269.N12489
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12489}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12489.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12489) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12489).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12489 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12489) (by norm_num) BstLean.Part268.WorldRow12489.worldPackage rfl
    BstLean.Part268.WorldRow12489.product_lower (BstLean.Part268.WorldRow12489.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12489} (hw : c ∈ Hof BstLean.Part268.WorldRow12489.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12489) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12489) (by norm_num) BstLean.Part268.WorldRow12489.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12489} (hw : c ∈ Hof BstLean.Part268.WorldRow12489.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12489) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12489).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12489) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12489_eq : scalarRow12489.targetFrame = BstLean.Part268.agent12489.frame := by
  norm_num [scalarRow12489,BstLean.Part268.agent12489]

noncomputable def frameData12489 : BstLean.Part264b.FrameData 12489 :=
  BstLean.Part269.frameData_from_numerics (n := 12489) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12489.worldPackage rfl BstLean.Part268.WorldRow12489.product_lower (BstLean.Part268.WorldRow12489.producthi.2.trans (by norm_num))
    scalarRow12489 repair12489 covarianceInputs12489 (fun i hi => sourceNumerics12489 hi)
    BstLean.Part268.agent12489.frame targetFrame12489_eq


end BstLean.Part269.N12489
