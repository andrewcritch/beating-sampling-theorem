import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World1Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs1
import BstLean.Part269Rows1
import BstLean.Part269Sources1
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12380
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12380 : scalarRow12380.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12380, BstLean.Part268.grid12380, BstLean.Part263.worldGrid]

theorem supplies12380 (j : Fin 43) : Supply 12380 (parameters j)
    (cellLower scalarRow12380.grid (sourceIndex j))
    (cellUpper scalarRow12380.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12380.grid grid_top_bounds12380 j

theorem radii12380 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12380.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12380 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12380 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12380.grid grid_top_bounds12380 j hθ

noncomputable def covarianceInputs12380 :
    BstLean.Part263.CovarianceInputs 12380 scalarRow12380.grid parameters (caps repair12380) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12380 grid_top_bounds12380 repair12380

noncomputable def covarianceEvent12380 : Set (AgFam 12380) :=
  BstLean.Part263.covarianceEvent 12380 scalarRow12380.grid parameters

theorem covarianceEvent12380_measurable : MeasurableSet covarianceEvent12380 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12380_payment :
    (retDist (paperDesignP 12380).toCentres).real
      (agentEv (paperDesignP 12380) covarianceEvent12380)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12380

theorem localCov12380 : BstLean.Part259.LocalCovarianceOn covarianceEvent12380
    (BstLean.Part263.cell scalarRow12380.grid) (caps repair12380) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12380

theorem covarianceGood12380_payment :
    (retDist (paperDesignP 12380).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12380)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12380_payment



end BstLean.Part269.N12380

namespace BstLean.Part269.N12380
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12380}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12380.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12380) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12380).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12380 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12380) (by norm_num) BstLean.Part268.WorldRow12380.worldPackage rfl
    BstLean.Part268.WorldRow12380.product_lower (BstLean.Part268.WorldRow12380.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12380} (hw : c ∈ Hof BstLean.Part268.WorldRow12380.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12380) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12380) (by norm_num) BstLean.Part268.WorldRow12380.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12380} (hw : c ∈ Hof BstLean.Part268.WorldRow12380.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12380) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12380).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12380) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12380_eq : scalarRow12380.targetFrame = BstLean.Part268.agent12380.frame := by
  norm_num [scalarRow12380,BstLean.Part268.agent12380]

noncomputable def frameData12380 : BstLean.Part264b.FrameData 12380 :=
  BstLean.Part269.frameData_from_numerics (n := 12380) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12380.worldPackage rfl BstLean.Part268.WorldRow12380.product_lower (BstLean.Part268.WorldRow12380.producthi.2.trans (by norm_num))
    scalarRow12380 repair12380 covarianceInputs12380 (fun i hi => sourceNumerics12380 hi)
    BstLean.Part268.agent12380.frame targetFrame12380_eq


end BstLean.Part269.N12380

namespace BstLean.Part269.N12381
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12381 : scalarRow12381.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12381, BstLean.Part268.grid12381, BstLean.Part263.worldGrid]

theorem supplies12381 (j : Fin 43) : Supply 12381 (parameters j)
    (cellLower scalarRow12381.grid (sourceIndex j))
    (cellUpper scalarRow12381.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12381.grid grid_top_bounds12381 j

theorem radii12381 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12381.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12381 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12381 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12381.grid grid_top_bounds12381 j hθ

noncomputable def covarianceInputs12381 :
    BstLean.Part263.CovarianceInputs 12381 scalarRow12381.grid parameters (caps repair12381) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12381 grid_top_bounds12381 repair12381

noncomputable def covarianceEvent12381 : Set (AgFam 12381) :=
  BstLean.Part263.covarianceEvent 12381 scalarRow12381.grid parameters

theorem covarianceEvent12381_measurable : MeasurableSet covarianceEvent12381 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12381_payment :
    (retDist (paperDesignP 12381).toCentres).real
      (agentEv (paperDesignP 12381) covarianceEvent12381)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12381

theorem localCov12381 : BstLean.Part259.LocalCovarianceOn covarianceEvent12381
    (BstLean.Part263.cell scalarRow12381.grid) (caps repair12381) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12381

theorem covarianceGood12381_payment :
    (retDist (paperDesignP 12381).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12381)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12381_payment



end BstLean.Part269.N12381

namespace BstLean.Part269.N12381
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12381}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12381.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12381) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12381).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12381 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12381) (by norm_num) BstLean.Part268.WorldRow12381.worldPackage rfl
    BstLean.Part268.WorldRow12381.product_lower (BstLean.Part268.WorldRow12381.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12381} (hw : c ∈ Hof BstLean.Part268.WorldRow12381.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12381) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12381) (by norm_num) BstLean.Part268.WorldRow12381.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12381} (hw : c ∈ Hof BstLean.Part268.WorldRow12381.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12381) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12381).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12381) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12381_eq : scalarRow12381.targetFrame = BstLean.Part268.agent12381.frame := by
  norm_num [scalarRow12381,BstLean.Part268.agent12381]

noncomputable def frameData12381 : BstLean.Part264b.FrameData 12381 :=
  BstLean.Part269.frameData_from_numerics (n := 12381) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12381.worldPackage rfl BstLean.Part268.WorldRow12381.product_lower (BstLean.Part268.WorldRow12381.producthi.2.trans (by norm_num))
    scalarRow12381 repair12381 covarianceInputs12381 (fun i hi => sourceNumerics12381 hi)
    BstLean.Part268.agent12381.frame targetFrame12381_eq


end BstLean.Part269.N12381

namespace BstLean.Part269.N12382
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12382 : scalarRow12382.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12382, BstLean.Part268.grid12382, BstLean.Part263.worldGrid]

theorem supplies12382 (j : Fin 43) : Supply 12382 (parameters j)
    (cellLower scalarRow12382.grid (sourceIndex j))
    (cellUpper scalarRow12382.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12382.grid grid_top_bounds12382 j

theorem radii12382 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12382.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12382 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12382 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12382.grid grid_top_bounds12382 j hθ

noncomputable def covarianceInputs12382 :
    BstLean.Part263.CovarianceInputs 12382 scalarRow12382.grid parameters (caps repair12382) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12382 grid_top_bounds12382 repair12382

noncomputable def covarianceEvent12382 : Set (AgFam 12382) :=
  BstLean.Part263.covarianceEvent 12382 scalarRow12382.grid parameters

theorem covarianceEvent12382_measurable : MeasurableSet covarianceEvent12382 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12382_payment :
    (retDist (paperDesignP 12382).toCentres).real
      (agentEv (paperDesignP 12382) covarianceEvent12382)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12382

theorem localCov12382 : BstLean.Part259.LocalCovarianceOn covarianceEvent12382
    (BstLean.Part263.cell scalarRow12382.grid) (caps repair12382) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12382

theorem covarianceGood12382_payment :
    (retDist (paperDesignP 12382).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12382)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12382_payment



end BstLean.Part269.N12382

namespace BstLean.Part269.N12382
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12382}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12382.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12382) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12382).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12382 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12382) (by norm_num) BstLean.Part268.WorldRow12382.worldPackage rfl
    BstLean.Part268.WorldRow12382.product_lower (BstLean.Part268.WorldRow12382.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12382} (hw : c ∈ Hof BstLean.Part268.WorldRow12382.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12382) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12382) (by norm_num) BstLean.Part268.WorldRow12382.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12382} (hw : c ∈ Hof BstLean.Part268.WorldRow12382.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12382) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12382).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12382) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12382_eq : scalarRow12382.targetFrame = BstLean.Part268.agent12382.frame := by
  norm_num [scalarRow12382,BstLean.Part268.agent12382]

noncomputable def frameData12382 : BstLean.Part264b.FrameData 12382 :=
  BstLean.Part269.frameData_from_numerics (n := 12382) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12382.worldPackage rfl BstLean.Part268.WorldRow12382.product_lower (BstLean.Part268.WorldRow12382.producthi.2.trans (by norm_num))
    scalarRow12382 repair12382 covarianceInputs12382 (fun i hi => sourceNumerics12382 hi)
    BstLean.Part268.agent12382.frame targetFrame12382_eq


end BstLean.Part269.N12382

namespace BstLean.Part269.N12383
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12383 : scalarRow12383.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12383, BstLean.Part268.grid12383, BstLean.Part263.worldGrid]

theorem supplies12383 (j : Fin 43) : Supply 12383 (parameters j)
    (cellLower scalarRow12383.grid (sourceIndex j))
    (cellUpper scalarRow12383.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12383.grid grid_top_bounds12383 j

theorem radii12383 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12383.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12383 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12383 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12383.grid grid_top_bounds12383 j hθ

noncomputable def covarianceInputs12383 :
    BstLean.Part263.CovarianceInputs 12383 scalarRow12383.grid parameters (caps repair12383) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12383 grid_top_bounds12383 repair12383

noncomputable def covarianceEvent12383 : Set (AgFam 12383) :=
  BstLean.Part263.covarianceEvent 12383 scalarRow12383.grid parameters

theorem covarianceEvent12383_measurable : MeasurableSet covarianceEvent12383 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12383_payment :
    (retDist (paperDesignP 12383).toCentres).real
      (agentEv (paperDesignP 12383) covarianceEvent12383)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12383

theorem localCov12383 : BstLean.Part259.LocalCovarianceOn covarianceEvent12383
    (BstLean.Part263.cell scalarRow12383.grid) (caps repair12383) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12383

theorem covarianceGood12383_payment :
    (retDist (paperDesignP 12383).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12383)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12383_payment



end BstLean.Part269.N12383

namespace BstLean.Part269.N12383
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12383}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12383.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12383) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12383).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12383 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12383) (by norm_num) BstLean.Part268.WorldRow12383.worldPackage rfl
    BstLean.Part268.WorldRow12383.product_lower (BstLean.Part268.WorldRow12383.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12383} (hw : c ∈ Hof BstLean.Part268.WorldRow12383.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12383) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12383) (by norm_num) BstLean.Part268.WorldRow12383.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12383} (hw : c ∈ Hof BstLean.Part268.WorldRow12383.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12383) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12383).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12383) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12383_eq : scalarRow12383.targetFrame = BstLean.Part268.agent12383.frame := by
  norm_num [scalarRow12383,BstLean.Part268.agent12383]

noncomputable def frameData12383 : BstLean.Part264b.FrameData 12383 :=
  BstLean.Part269.frameData_from_numerics (n := 12383) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12383.worldPackage rfl BstLean.Part268.WorldRow12383.product_lower (BstLean.Part268.WorldRow12383.producthi.2.trans (by norm_num))
    scalarRow12383 repair12383 covarianceInputs12383 (fun i hi => sourceNumerics12383 hi)
    BstLean.Part268.agent12383.frame targetFrame12383_eq


end BstLean.Part269.N12383

namespace BstLean.Part269.N12384
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12384 : scalarRow12384.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12384, BstLean.Part268.grid12384, BstLean.Part263.worldGrid]

theorem supplies12384 (j : Fin 43) : Supply 12384 (parameters j)
    (cellLower scalarRow12384.grid (sourceIndex j))
    (cellUpper scalarRow12384.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12384.grid grid_top_bounds12384 j

theorem radii12384 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12384.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12384 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12384 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12384.grid grid_top_bounds12384 j hθ

noncomputable def covarianceInputs12384 :
    BstLean.Part263.CovarianceInputs 12384 scalarRow12384.grid parameters (caps repair12384) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12384 grid_top_bounds12384 repair12384

noncomputable def covarianceEvent12384 : Set (AgFam 12384) :=
  BstLean.Part263.covarianceEvent 12384 scalarRow12384.grid parameters

theorem covarianceEvent12384_measurable : MeasurableSet covarianceEvent12384 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12384_payment :
    (retDist (paperDesignP 12384).toCentres).real
      (agentEv (paperDesignP 12384) covarianceEvent12384)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12384

theorem localCov12384 : BstLean.Part259.LocalCovarianceOn covarianceEvent12384
    (BstLean.Part263.cell scalarRow12384.grid) (caps repair12384) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12384

theorem covarianceGood12384_payment :
    (retDist (paperDesignP 12384).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12384)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12384_payment



end BstLean.Part269.N12384

namespace BstLean.Part269.N12384
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12384}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12384.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12384) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12384).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12384 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12384) (by norm_num) BstLean.Part268.WorldRow12384.worldPackage rfl
    BstLean.Part268.WorldRow12384.product_lower (BstLean.Part268.WorldRow12384.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12384} (hw : c ∈ Hof BstLean.Part268.WorldRow12384.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12384) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12384) (by norm_num) BstLean.Part268.WorldRow12384.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12384} (hw : c ∈ Hof BstLean.Part268.WorldRow12384.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12384) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12384).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12384) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12384_eq : scalarRow12384.targetFrame = BstLean.Part268.agent12384.frame := by
  norm_num [scalarRow12384,BstLean.Part268.agent12384]

noncomputable def frameData12384 : BstLean.Part264b.FrameData 12384 :=
  BstLean.Part269.frameData_from_numerics (n := 12384) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12384.worldPackage rfl BstLean.Part268.WorldRow12384.product_lower (BstLean.Part268.WorldRow12384.producthi.2.trans (by norm_num))
    scalarRow12384 repair12384 covarianceInputs12384 (fun i hi => sourceNumerics12384 hi)
    BstLean.Part268.agent12384.frame targetFrame12384_eq


end BstLean.Part269.N12384
