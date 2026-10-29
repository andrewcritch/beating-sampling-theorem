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

namespace BstLean.Part269.N12395
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12395 : scalarRow12395.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12395, BstLean.Part268.grid12395, BstLean.Part263.worldGrid]

theorem supplies12395 (j : Fin 43) : Supply 12395 (parameters j)
    (cellLower scalarRow12395.grid (sourceIndex j))
    (cellUpper scalarRow12395.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12395.grid grid_top_bounds12395 j

theorem radii12395 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12395.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12395 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12395 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12395.grid grid_top_bounds12395 j hθ

noncomputable def covarianceInputs12395 :
    BstLean.Part263.CovarianceInputs 12395 scalarRow12395.grid parameters (caps repair12395) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12395 grid_top_bounds12395 repair12395

noncomputable def covarianceEvent12395 : Set (AgFam 12395) :=
  BstLean.Part263.covarianceEvent 12395 scalarRow12395.grid parameters

theorem covarianceEvent12395_measurable : MeasurableSet covarianceEvent12395 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12395_payment :
    (retDist (paperDesignP 12395).toCentres).real
      (agentEv (paperDesignP 12395) covarianceEvent12395)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12395

theorem localCov12395 : BstLean.Part259.LocalCovarianceOn covarianceEvent12395
    (BstLean.Part263.cell scalarRow12395.grid) (caps repair12395) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12395

theorem covarianceGood12395_payment :
    (retDist (paperDesignP 12395).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12395)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12395_payment



end BstLean.Part269.N12395

namespace BstLean.Part269.N12395
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12395}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12395.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12395) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12395).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12395 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12395) (by norm_num) BstLean.Part268.WorldRow12395.worldPackage rfl
    BstLean.Part268.WorldRow12395.product_lower (BstLean.Part268.WorldRow12395.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12395} (hw : c ∈ Hof BstLean.Part268.WorldRow12395.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12395) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12395) (by norm_num) BstLean.Part268.WorldRow12395.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12395} (hw : c ∈ Hof BstLean.Part268.WorldRow12395.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12395) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12395).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12395) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12395_eq : scalarRow12395.targetFrame = BstLean.Part268.agent12395.frame := by
  norm_num [scalarRow12395,BstLean.Part268.agent12395]

noncomputable def frameData12395 : BstLean.Part264b.FrameData 12395 :=
  BstLean.Part269.frameData_from_numerics (n := 12395) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12395.worldPackage rfl BstLean.Part268.WorldRow12395.product_lower (BstLean.Part268.WorldRow12395.producthi.2.trans (by norm_num))
    scalarRow12395 repair12395 covarianceInputs12395 (fun i hi => sourceNumerics12395 hi)
    BstLean.Part268.agent12395.frame targetFrame12395_eq


end BstLean.Part269.N12395

namespace BstLean.Part269.N12396
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12396 : scalarRow12396.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12396, BstLean.Part268.grid12396, BstLean.Part263.worldGrid]

theorem supplies12396 (j : Fin 43) : Supply 12396 (parameters j)
    (cellLower scalarRow12396.grid (sourceIndex j))
    (cellUpper scalarRow12396.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12396.grid grid_top_bounds12396 j

theorem radii12396 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12396.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12396 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12396 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12396.grid grid_top_bounds12396 j hθ

noncomputable def covarianceInputs12396 :
    BstLean.Part263.CovarianceInputs 12396 scalarRow12396.grid parameters (caps repair12396) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12396 grid_top_bounds12396 repair12396

noncomputable def covarianceEvent12396 : Set (AgFam 12396) :=
  BstLean.Part263.covarianceEvent 12396 scalarRow12396.grid parameters

theorem covarianceEvent12396_measurable : MeasurableSet covarianceEvent12396 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12396_payment :
    (retDist (paperDesignP 12396).toCentres).real
      (agentEv (paperDesignP 12396) covarianceEvent12396)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12396

theorem localCov12396 : BstLean.Part259.LocalCovarianceOn covarianceEvent12396
    (BstLean.Part263.cell scalarRow12396.grid) (caps repair12396) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12396

theorem covarianceGood12396_payment :
    (retDist (paperDesignP 12396).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12396)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12396_payment



end BstLean.Part269.N12396

namespace BstLean.Part269.N12396
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12396}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12396.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12396) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12396).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12396 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12396) (by norm_num) BstLean.Part268.WorldRow12396.worldPackage rfl
    BstLean.Part268.WorldRow12396.product_lower (BstLean.Part268.WorldRow12396.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12396} (hw : c ∈ Hof BstLean.Part268.WorldRow12396.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12396) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12396) (by norm_num) BstLean.Part268.WorldRow12396.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12396} (hw : c ∈ Hof BstLean.Part268.WorldRow12396.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12396) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12396).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12396) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12396_eq : scalarRow12396.targetFrame = BstLean.Part268.agent12396.frame := by
  norm_num [scalarRow12396,BstLean.Part268.agent12396]

noncomputable def frameData12396 : BstLean.Part264b.FrameData 12396 :=
  BstLean.Part269.frameData_from_numerics (n := 12396) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12396.worldPackage rfl BstLean.Part268.WorldRow12396.product_lower (BstLean.Part268.WorldRow12396.producthi.2.trans (by norm_num))
    scalarRow12396 repair12396 covarianceInputs12396 (fun i hi => sourceNumerics12396 hi)
    BstLean.Part268.agent12396.frame targetFrame12396_eq


end BstLean.Part269.N12396

namespace BstLean.Part269.N12397
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12397 : scalarRow12397.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12397, BstLean.Part268.grid12397, BstLean.Part263.worldGrid]

theorem supplies12397 (j : Fin 43) : Supply 12397 (parameters j)
    (cellLower scalarRow12397.grid (sourceIndex j))
    (cellUpper scalarRow12397.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12397.grid grid_top_bounds12397 j

theorem radii12397 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12397.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12397 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12397 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12397.grid grid_top_bounds12397 j hθ

noncomputable def covarianceInputs12397 :
    BstLean.Part263.CovarianceInputs 12397 scalarRow12397.grid parameters (caps repair12397) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12397 grid_top_bounds12397 repair12397

noncomputable def covarianceEvent12397 : Set (AgFam 12397) :=
  BstLean.Part263.covarianceEvent 12397 scalarRow12397.grid parameters

theorem covarianceEvent12397_measurable : MeasurableSet covarianceEvent12397 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12397_payment :
    (retDist (paperDesignP 12397).toCentres).real
      (agentEv (paperDesignP 12397) covarianceEvent12397)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12397

theorem localCov12397 : BstLean.Part259.LocalCovarianceOn covarianceEvent12397
    (BstLean.Part263.cell scalarRow12397.grid) (caps repair12397) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12397

theorem covarianceGood12397_payment :
    (retDist (paperDesignP 12397).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12397)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12397_payment



end BstLean.Part269.N12397

namespace BstLean.Part269.N12397
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12397}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12397.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12397) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12397).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12397 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12397) (by norm_num) BstLean.Part268.WorldRow12397.worldPackage rfl
    BstLean.Part268.WorldRow12397.product_lower (BstLean.Part268.WorldRow12397.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12397} (hw : c ∈ Hof BstLean.Part268.WorldRow12397.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12397) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12397) (by norm_num) BstLean.Part268.WorldRow12397.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12397} (hw : c ∈ Hof BstLean.Part268.WorldRow12397.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12397) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12397).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12397) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12397_eq : scalarRow12397.targetFrame = BstLean.Part268.agent12397.frame := by
  norm_num [scalarRow12397,BstLean.Part268.agent12397]

noncomputable def frameData12397 : BstLean.Part264b.FrameData 12397 :=
  BstLean.Part269.frameData_from_numerics (n := 12397) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12397.worldPackage rfl BstLean.Part268.WorldRow12397.product_lower (BstLean.Part268.WorldRow12397.producthi.2.trans (by norm_num))
    scalarRow12397 repair12397 covarianceInputs12397 (fun i hi => sourceNumerics12397 hi)
    BstLean.Part268.agent12397.frame targetFrame12397_eq


end BstLean.Part269.N12397

namespace BstLean.Part269.N12398
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12398 : scalarRow12398.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12398, BstLean.Part268.grid12398, BstLean.Part263.worldGrid]

theorem supplies12398 (j : Fin 43) : Supply 12398 (parameters j)
    (cellLower scalarRow12398.grid (sourceIndex j))
    (cellUpper scalarRow12398.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12398.grid grid_top_bounds12398 j

theorem radii12398 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12398.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12398 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12398 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12398.grid grid_top_bounds12398 j hθ

noncomputable def covarianceInputs12398 :
    BstLean.Part263.CovarianceInputs 12398 scalarRow12398.grid parameters (caps repair12398) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12398 grid_top_bounds12398 repair12398

noncomputable def covarianceEvent12398 : Set (AgFam 12398) :=
  BstLean.Part263.covarianceEvent 12398 scalarRow12398.grid parameters

theorem covarianceEvent12398_measurable : MeasurableSet covarianceEvent12398 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12398_payment :
    (retDist (paperDesignP 12398).toCentres).real
      (agentEv (paperDesignP 12398) covarianceEvent12398)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12398

theorem localCov12398 : BstLean.Part259.LocalCovarianceOn covarianceEvent12398
    (BstLean.Part263.cell scalarRow12398.grid) (caps repair12398) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12398

theorem covarianceGood12398_payment :
    (retDist (paperDesignP 12398).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12398)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12398_payment



end BstLean.Part269.N12398

namespace BstLean.Part269.N12398
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12398}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12398.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12398) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12398).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12398 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12398) (by norm_num) BstLean.Part268.WorldRow12398.worldPackage rfl
    BstLean.Part268.WorldRow12398.product_lower (BstLean.Part268.WorldRow12398.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12398} (hw : c ∈ Hof BstLean.Part268.WorldRow12398.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12398) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12398) (by norm_num) BstLean.Part268.WorldRow12398.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12398} (hw : c ∈ Hof BstLean.Part268.WorldRow12398.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12398) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12398).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12398) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12398_eq : scalarRow12398.targetFrame = BstLean.Part268.agent12398.frame := by
  norm_num [scalarRow12398,BstLean.Part268.agent12398]

noncomputable def frameData12398 : BstLean.Part264b.FrameData 12398 :=
  BstLean.Part269.frameData_from_numerics (n := 12398) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12398.worldPackage rfl BstLean.Part268.WorldRow12398.product_lower (BstLean.Part268.WorldRow12398.producthi.2.trans (by norm_num))
    scalarRow12398 repair12398 covarianceInputs12398 (fun i hi => sourceNumerics12398 hi)
    BstLean.Part268.agent12398.frame targetFrame12398_eq


end BstLean.Part269.N12398

namespace BstLean.Part269.N12399
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12399 : scalarRow12399.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12399, BstLean.Part268.grid12399, BstLean.Part263.worldGrid]

theorem supplies12399 (j : Fin 43) : Supply 12399 (parameters j)
    (cellLower scalarRow12399.grid (sourceIndex j))
    (cellUpper scalarRow12399.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12399.grid grid_top_bounds12399 j

theorem radii12399 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12399.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12399 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12399 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12399.grid grid_top_bounds12399 j hθ

noncomputable def covarianceInputs12399 :
    BstLean.Part263.CovarianceInputs 12399 scalarRow12399.grid parameters (caps repair12399) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12399 grid_top_bounds12399 repair12399

noncomputable def covarianceEvent12399 : Set (AgFam 12399) :=
  BstLean.Part263.covarianceEvent 12399 scalarRow12399.grid parameters

theorem covarianceEvent12399_measurable : MeasurableSet covarianceEvent12399 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12399_payment :
    (retDist (paperDesignP 12399).toCentres).real
      (agentEv (paperDesignP 12399) covarianceEvent12399)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12399

theorem localCov12399 : BstLean.Part259.LocalCovarianceOn covarianceEvent12399
    (BstLean.Part263.cell scalarRow12399.grid) (caps repair12399) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12399

theorem covarianceGood12399_payment :
    (retDist (paperDesignP 12399).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12399)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12399_payment



end BstLean.Part269.N12399

namespace BstLean.Part269.N12399
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12399}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12399.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12399) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12399).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12399 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12399) (by norm_num) BstLean.Part268.WorldRow12399.worldPackage rfl
    BstLean.Part268.WorldRow12399.product_lower (BstLean.Part268.WorldRow12399.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12399} (hw : c ∈ Hof BstLean.Part268.WorldRow12399.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12399) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12399) (by norm_num) BstLean.Part268.WorldRow12399.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12399} (hw : c ∈ Hof BstLean.Part268.WorldRow12399.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12399) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12399).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12399) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12399_eq : scalarRow12399.targetFrame = BstLean.Part268.agent12399.frame := by
  norm_num [scalarRow12399,BstLean.Part268.agent12399]

noncomputable def frameData12399 : BstLean.Part264b.FrameData 12399 :=
  BstLean.Part269.frameData_from_numerics (n := 12399) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12399.worldPackage rfl BstLean.Part268.WorldRow12399.product_lower (BstLean.Part268.WorldRow12399.producthi.2.trans (by norm_num))
    scalarRow12399 repair12399 covarianceInputs12399 (fun i hi => sourceNumerics12399 hi)
    BstLean.Part268.agent12399.frame targetFrame12399_eq


end BstLean.Part269.N12399
