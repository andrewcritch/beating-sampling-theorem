import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World4Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs4
import BstLean.Part269Rows4
import BstLean.Part269Sources4
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12460
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12460 : scalarRow12460.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12460, BstLean.Part268.grid12460, BstLean.Part263.worldGrid]

theorem supplies12460 (j : Fin 43) : Supply 12460 (parameters j)
    (cellLower scalarRow12460.grid (sourceIndex j))
    (cellUpper scalarRow12460.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12460.grid grid_top_bounds12460 j

theorem radii12460 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12460.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12460 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12460 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12460.grid grid_top_bounds12460 j hθ

noncomputable def covarianceInputs12460 :
    BstLean.Part263.CovarianceInputs 12460 scalarRow12460.grid parameters (caps repair12460) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12460 grid_top_bounds12460 repair12460

noncomputable def covarianceEvent12460 : Set (AgFam 12460) :=
  BstLean.Part263.covarianceEvent 12460 scalarRow12460.grid parameters

theorem covarianceEvent12460_measurable : MeasurableSet covarianceEvent12460 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12460_payment :
    (retDist (paperDesignP 12460).toCentres).real
      (agentEv (paperDesignP 12460) covarianceEvent12460)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12460

theorem localCov12460 : BstLean.Part259.LocalCovarianceOn covarianceEvent12460
    (BstLean.Part263.cell scalarRow12460.grid) (caps repair12460) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12460

theorem covarianceGood12460_payment :
    (retDist (paperDesignP 12460).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12460)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12460_payment



end BstLean.Part269.N12460

namespace BstLean.Part269.N12460
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12460}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12460.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12460) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12460).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12460 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12460) (by norm_num) BstLean.Part268.WorldRow12460.worldPackage rfl
    BstLean.Part268.WorldRow12460.product_lower (BstLean.Part268.WorldRow12460.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12460} (hw : c ∈ Hof BstLean.Part268.WorldRow12460.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12460) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12460) (by norm_num) BstLean.Part268.WorldRow12460.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12460} (hw : c ∈ Hof BstLean.Part268.WorldRow12460.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12460) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12460).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12460) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12460_eq : scalarRow12460.targetFrame = BstLean.Part268.agent12460.frame := by
  norm_num [scalarRow12460,BstLean.Part268.agent12460]

noncomputable def frameData12460 : BstLean.Part264b.FrameData 12460 :=
  BstLean.Part269.frameData_from_numerics (n := 12460) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12460.worldPackage rfl BstLean.Part268.WorldRow12460.product_lower (BstLean.Part268.WorldRow12460.producthi.2.trans (by norm_num))
    scalarRow12460 repair12460 covarianceInputs12460 (fun i hi => sourceNumerics12460 hi)
    BstLean.Part268.agent12460.frame targetFrame12460_eq


end BstLean.Part269.N12460

namespace BstLean.Part269.N12461
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12461 : scalarRow12461.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12461, BstLean.Part268.grid12461, BstLean.Part263.worldGrid]

theorem supplies12461 (j : Fin 43) : Supply 12461 (parameters j)
    (cellLower scalarRow12461.grid (sourceIndex j))
    (cellUpper scalarRow12461.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12461.grid grid_top_bounds12461 j

theorem radii12461 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12461.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12461 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12461 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12461.grid grid_top_bounds12461 j hθ

noncomputable def covarianceInputs12461 :
    BstLean.Part263.CovarianceInputs 12461 scalarRow12461.grid parameters (caps repair12461) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12461 grid_top_bounds12461 repair12461

noncomputable def covarianceEvent12461 : Set (AgFam 12461) :=
  BstLean.Part263.covarianceEvent 12461 scalarRow12461.grid parameters

theorem covarianceEvent12461_measurable : MeasurableSet covarianceEvent12461 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12461_payment :
    (retDist (paperDesignP 12461).toCentres).real
      (agentEv (paperDesignP 12461) covarianceEvent12461)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12461

theorem localCov12461 : BstLean.Part259.LocalCovarianceOn covarianceEvent12461
    (BstLean.Part263.cell scalarRow12461.grid) (caps repair12461) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12461

theorem covarianceGood12461_payment :
    (retDist (paperDesignP 12461).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12461)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12461_payment



end BstLean.Part269.N12461

namespace BstLean.Part269.N12461
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12461}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12461.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12461) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12461).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12461 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12461) (by norm_num) BstLean.Part268.WorldRow12461.worldPackage rfl
    BstLean.Part268.WorldRow12461.product_lower (BstLean.Part268.WorldRow12461.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12461} (hw : c ∈ Hof BstLean.Part268.WorldRow12461.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12461) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12461) (by norm_num) BstLean.Part268.WorldRow12461.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12461} (hw : c ∈ Hof BstLean.Part268.WorldRow12461.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12461) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12461).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12461) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12461_eq : scalarRow12461.targetFrame = BstLean.Part268.agent12461.frame := by
  norm_num [scalarRow12461,BstLean.Part268.agent12461]

noncomputable def frameData12461 : BstLean.Part264b.FrameData 12461 :=
  BstLean.Part269.frameData_from_numerics (n := 12461) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12461.worldPackage rfl BstLean.Part268.WorldRow12461.product_lower (BstLean.Part268.WorldRow12461.producthi.2.trans (by norm_num))
    scalarRow12461 repair12461 covarianceInputs12461 (fun i hi => sourceNumerics12461 hi)
    BstLean.Part268.agent12461.frame targetFrame12461_eq


end BstLean.Part269.N12461

namespace BstLean.Part269.N12462
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12462 : scalarRow12462.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12462, BstLean.Part268.grid12462, BstLean.Part263.worldGrid]

theorem supplies12462 (j : Fin 43) : Supply 12462 (parameters j)
    (cellLower scalarRow12462.grid (sourceIndex j))
    (cellUpper scalarRow12462.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12462.grid grid_top_bounds12462 j

theorem radii12462 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12462.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12462 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12462 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12462.grid grid_top_bounds12462 j hθ

noncomputable def covarianceInputs12462 :
    BstLean.Part263.CovarianceInputs 12462 scalarRow12462.grid parameters (caps repair12462) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12462 grid_top_bounds12462 repair12462

noncomputable def covarianceEvent12462 : Set (AgFam 12462) :=
  BstLean.Part263.covarianceEvent 12462 scalarRow12462.grid parameters

theorem covarianceEvent12462_measurable : MeasurableSet covarianceEvent12462 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12462_payment :
    (retDist (paperDesignP 12462).toCentres).real
      (agentEv (paperDesignP 12462) covarianceEvent12462)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12462

theorem localCov12462 : BstLean.Part259.LocalCovarianceOn covarianceEvent12462
    (BstLean.Part263.cell scalarRow12462.grid) (caps repair12462) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12462

theorem covarianceGood12462_payment :
    (retDist (paperDesignP 12462).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12462)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12462_payment



end BstLean.Part269.N12462

namespace BstLean.Part269.N12462
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12462}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12462.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12462) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12462).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12462 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12462) (by norm_num) BstLean.Part268.WorldRow12462.worldPackage rfl
    BstLean.Part268.WorldRow12462.product_lower (BstLean.Part268.WorldRow12462.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12462} (hw : c ∈ Hof BstLean.Part268.WorldRow12462.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12462) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12462) (by norm_num) BstLean.Part268.WorldRow12462.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12462} (hw : c ∈ Hof BstLean.Part268.WorldRow12462.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12462) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12462).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12462) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12462_eq : scalarRow12462.targetFrame = BstLean.Part268.agent12462.frame := by
  norm_num [scalarRow12462,BstLean.Part268.agent12462]

noncomputable def frameData12462 : BstLean.Part264b.FrameData 12462 :=
  BstLean.Part269.frameData_from_numerics (n := 12462) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12462.worldPackage rfl BstLean.Part268.WorldRow12462.product_lower (BstLean.Part268.WorldRow12462.producthi.2.trans (by norm_num))
    scalarRow12462 repair12462 covarianceInputs12462 (fun i hi => sourceNumerics12462 hi)
    BstLean.Part268.agent12462.frame targetFrame12462_eq


end BstLean.Part269.N12462

namespace BstLean.Part269.N12463
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12463 : scalarRow12463.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12463, BstLean.Part268.grid12463, BstLean.Part263.worldGrid]

theorem supplies12463 (j : Fin 43) : Supply 12463 (parameters j)
    (cellLower scalarRow12463.grid (sourceIndex j))
    (cellUpper scalarRow12463.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12463.grid grid_top_bounds12463 j

theorem radii12463 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12463.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12463 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12463 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12463.grid grid_top_bounds12463 j hθ

noncomputable def covarianceInputs12463 :
    BstLean.Part263.CovarianceInputs 12463 scalarRow12463.grid parameters (caps repair12463) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12463 grid_top_bounds12463 repair12463

noncomputable def covarianceEvent12463 : Set (AgFam 12463) :=
  BstLean.Part263.covarianceEvent 12463 scalarRow12463.grid parameters

theorem covarianceEvent12463_measurable : MeasurableSet covarianceEvent12463 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12463_payment :
    (retDist (paperDesignP 12463).toCentres).real
      (agentEv (paperDesignP 12463) covarianceEvent12463)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12463

theorem localCov12463 : BstLean.Part259.LocalCovarianceOn covarianceEvent12463
    (BstLean.Part263.cell scalarRow12463.grid) (caps repair12463) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12463

theorem covarianceGood12463_payment :
    (retDist (paperDesignP 12463).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12463)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12463_payment



end BstLean.Part269.N12463

namespace BstLean.Part269.N12463
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12463}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12463.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12463) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12463).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12463 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12463) (by norm_num) BstLean.Part268.WorldRow12463.worldPackage rfl
    BstLean.Part268.WorldRow12463.product_lower (BstLean.Part268.WorldRow12463.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12463} (hw : c ∈ Hof BstLean.Part268.WorldRow12463.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12463) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12463) (by norm_num) BstLean.Part268.WorldRow12463.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12463} (hw : c ∈ Hof BstLean.Part268.WorldRow12463.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12463) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12463).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12463) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12463_eq : scalarRow12463.targetFrame = BstLean.Part268.agent12463.frame := by
  norm_num [scalarRow12463,BstLean.Part268.agent12463]

noncomputable def frameData12463 : BstLean.Part264b.FrameData 12463 :=
  BstLean.Part269.frameData_from_numerics (n := 12463) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12463.worldPackage rfl BstLean.Part268.WorldRow12463.product_lower (BstLean.Part268.WorldRow12463.producthi.2.trans (by norm_num))
    scalarRow12463 repair12463 covarianceInputs12463 (fun i hi => sourceNumerics12463 hi)
    BstLean.Part268.agent12463.frame targetFrame12463_eq


end BstLean.Part269.N12463

namespace BstLean.Part269.N12464
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12464 : scalarRow12464.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12464, BstLean.Part268.grid12464, BstLean.Part263.worldGrid]

theorem supplies12464 (j : Fin 43) : Supply 12464 (parameters j)
    (cellLower scalarRow12464.grid (sourceIndex j))
    (cellUpper scalarRow12464.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12464.grid grid_top_bounds12464 j

theorem radii12464 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12464.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12464 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12464 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12464.grid grid_top_bounds12464 j hθ

noncomputable def covarianceInputs12464 :
    BstLean.Part263.CovarianceInputs 12464 scalarRow12464.grid parameters (caps repair12464) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12464 grid_top_bounds12464 repair12464

noncomputable def covarianceEvent12464 : Set (AgFam 12464) :=
  BstLean.Part263.covarianceEvent 12464 scalarRow12464.grid parameters

theorem covarianceEvent12464_measurable : MeasurableSet covarianceEvent12464 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12464_payment :
    (retDist (paperDesignP 12464).toCentres).real
      (agentEv (paperDesignP 12464) covarianceEvent12464)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12464

theorem localCov12464 : BstLean.Part259.LocalCovarianceOn covarianceEvent12464
    (BstLean.Part263.cell scalarRow12464.grid) (caps repair12464) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12464

theorem covarianceGood12464_payment :
    (retDist (paperDesignP 12464).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12464)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12464_payment



end BstLean.Part269.N12464

namespace BstLean.Part269.N12464
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12464}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12464.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12464) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12464).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12464 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12464) (by norm_num) BstLean.Part268.WorldRow12464.worldPackage rfl
    BstLean.Part268.WorldRow12464.product_lower (BstLean.Part268.WorldRow12464.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12464} (hw : c ∈ Hof BstLean.Part268.WorldRow12464.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12464) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12464) (by norm_num) BstLean.Part268.WorldRow12464.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12464} (hw : c ∈ Hof BstLean.Part268.WorldRow12464.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12464) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12464).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12464) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12464_eq : scalarRow12464.targetFrame = BstLean.Part268.agent12464.frame := by
  norm_num [scalarRow12464,BstLean.Part268.agent12464]

noncomputable def frameData12464 : BstLean.Part264b.FrameData 12464 :=
  BstLean.Part269.frameData_from_numerics (n := 12464) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12464.worldPackage rfl BstLean.Part268.WorldRow12464.product_lower (BstLean.Part268.WorldRow12464.producthi.2.trans (by norm_num))
    scalarRow12464 repair12464 covarianceInputs12464 (fun i hi => sourceNumerics12464 hi)
    BstLean.Part268.agent12464.frame targetFrame12464_eq


end BstLean.Part269.N12464
