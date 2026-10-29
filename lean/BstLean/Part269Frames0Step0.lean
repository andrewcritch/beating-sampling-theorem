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

namespace BstLean.Part269.N12351
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12351 : scalarRow12351.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12351, BstLean.Part268.grid12351, BstLean.Part263.worldGrid]

theorem supplies12351 (j : Fin 43) : Supply 12351 (parameters j)
    (cellLower scalarRow12351.grid (sourceIndex j))
    (cellUpper scalarRow12351.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12351.grid grid_top_bounds12351 j

theorem radii12351 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12351.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12351 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12351 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12351.grid grid_top_bounds12351 j hθ

noncomputable def covarianceInputs12351 :
    BstLean.Part263.CovarianceInputs 12351 scalarRow12351.grid parameters (caps repair12351) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12351 grid_top_bounds12351 repair12351

noncomputable def covarianceEvent12351 : Set (AgFam 12351) :=
  BstLean.Part263.covarianceEvent 12351 scalarRow12351.grid parameters

theorem covarianceEvent12351_measurable : MeasurableSet covarianceEvent12351 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12351_payment :
    (retDist (paperDesignP 12351).toCentres).real
      (agentEv (paperDesignP 12351) covarianceEvent12351)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12351

theorem localCov12351 : BstLean.Part259.LocalCovarianceOn covarianceEvent12351
    (BstLean.Part263.cell scalarRow12351.grid) (caps repair12351) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12351

theorem covarianceGood12351_payment :
    (retDist (paperDesignP 12351).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12351)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12351_payment



end BstLean.Part269.N12351

namespace BstLean.Part269.N12351
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12351}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12351.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12351) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12351).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12351 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12351) (by norm_num) BstLean.Part268.WorldRow12351.worldPackage rfl
    BstLean.Part268.WorldRow12351.product_lower (BstLean.Part268.WorldRow12351.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12351} (hw : c ∈ Hof BstLean.Part268.WorldRow12351.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12351) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12351) (by norm_num) BstLean.Part268.WorldRow12351.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12351} (hw : c ∈ Hof BstLean.Part268.WorldRow12351.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12351) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12351).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12351) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12351_eq : scalarRow12351.targetFrame = BstLean.Part268.agent12351.frame := by
  norm_num [scalarRow12351,BstLean.Part268.agent12351]

noncomputable def frameData12351 : BstLean.Part264b.FrameData 12351 :=
  BstLean.Part269.frameData_from_numerics (n := 12351) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12351.worldPackage rfl BstLean.Part268.WorldRow12351.product_lower (BstLean.Part268.WorldRow12351.producthi.2.trans (by norm_num))
    scalarRow12351 repair12351 covarianceInputs12351 (fun i hi => sourceNumerics12351 hi)
    BstLean.Part268.agent12351.frame targetFrame12351_eq


end BstLean.Part269.N12351

namespace BstLean.Part269.N12352
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12352 : scalarRow12352.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12352, BstLean.Part268.grid12352, BstLean.Part263.worldGrid]

theorem supplies12352 (j : Fin 43) : Supply 12352 (parameters j)
    (cellLower scalarRow12352.grid (sourceIndex j))
    (cellUpper scalarRow12352.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12352.grid grid_top_bounds12352 j

theorem radii12352 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12352.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12352 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12352 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12352.grid grid_top_bounds12352 j hθ

noncomputable def covarianceInputs12352 :
    BstLean.Part263.CovarianceInputs 12352 scalarRow12352.grid parameters (caps repair12352) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12352 grid_top_bounds12352 repair12352

noncomputable def covarianceEvent12352 : Set (AgFam 12352) :=
  BstLean.Part263.covarianceEvent 12352 scalarRow12352.grid parameters

theorem covarianceEvent12352_measurable : MeasurableSet covarianceEvent12352 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12352_payment :
    (retDist (paperDesignP 12352).toCentres).real
      (agentEv (paperDesignP 12352) covarianceEvent12352)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12352

theorem localCov12352 : BstLean.Part259.LocalCovarianceOn covarianceEvent12352
    (BstLean.Part263.cell scalarRow12352.grid) (caps repair12352) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12352

theorem covarianceGood12352_payment :
    (retDist (paperDesignP 12352).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12352)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12352_payment



end BstLean.Part269.N12352

namespace BstLean.Part269.N12352
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12352}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12352.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12352) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12352).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12352 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12352) (by norm_num) BstLean.Part268.WorldRow12352.worldPackage rfl
    BstLean.Part268.WorldRow12352.product_lower (BstLean.Part268.WorldRow12352.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12352} (hw : c ∈ Hof BstLean.Part268.WorldRow12352.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12352) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12352) (by norm_num) BstLean.Part268.WorldRow12352.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12352} (hw : c ∈ Hof BstLean.Part268.WorldRow12352.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12352) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12352).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12352) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12352_eq : scalarRow12352.targetFrame = BstLean.Part268.agent12352.frame := by
  norm_num [scalarRow12352,BstLean.Part268.agent12352]

noncomputable def frameData12352 : BstLean.Part264b.FrameData 12352 :=
  BstLean.Part269.frameData_from_numerics (n := 12352) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12352.worldPackage rfl BstLean.Part268.WorldRow12352.product_lower (BstLean.Part268.WorldRow12352.producthi.2.trans (by norm_num))
    scalarRow12352 repair12352 covarianceInputs12352 (fun i hi => sourceNumerics12352 hi)
    BstLean.Part268.agent12352.frame targetFrame12352_eq


end BstLean.Part269.N12352

namespace BstLean.Part269.N12353
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12353 : scalarRow12353.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12353, BstLean.Part268.grid12353, BstLean.Part263.worldGrid]

theorem supplies12353 (j : Fin 43) : Supply 12353 (parameters j)
    (cellLower scalarRow12353.grid (sourceIndex j))
    (cellUpper scalarRow12353.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12353.grid grid_top_bounds12353 j

theorem radii12353 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12353.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12353 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12353 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12353.grid grid_top_bounds12353 j hθ

noncomputable def covarianceInputs12353 :
    BstLean.Part263.CovarianceInputs 12353 scalarRow12353.grid parameters (caps repair12353) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12353 grid_top_bounds12353 repair12353

noncomputable def covarianceEvent12353 : Set (AgFam 12353) :=
  BstLean.Part263.covarianceEvent 12353 scalarRow12353.grid parameters

theorem covarianceEvent12353_measurable : MeasurableSet covarianceEvent12353 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12353_payment :
    (retDist (paperDesignP 12353).toCentres).real
      (agentEv (paperDesignP 12353) covarianceEvent12353)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12353

theorem localCov12353 : BstLean.Part259.LocalCovarianceOn covarianceEvent12353
    (BstLean.Part263.cell scalarRow12353.grid) (caps repair12353) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12353

theorem covarianceGood12353_payment :
    (retDist (paperDesignP 12353).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12353)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12353_payment



end BstLean.Part269.N12353

namespace BstLean.Part269.N12353
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12353}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12353.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12353) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12353).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12353 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12353) (by norm_num) BstLean.Part268.WorldRow12353.worldPackage rfl
    BstLean.Part268.WorldRow12353.product_lower (BstLean.Part268.WorldRow12353.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12353} (hw : c ∈ Hof BstLean.Part268.WorldRow12353.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12353) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12353) (by norm_num) BstLean.Part268.WorldRow12353.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12353} (hw : c ∈ Hof BstLean.Part268.WorldRow12353.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12353) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12353).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12353) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12353_eq : scalarRow12353.targetFrame = BstLean.Part268.agent12353.frame := by
  norm_num [scalarRow12353,BstLean.Part268.agent12353]

noncomputable def frameData12353 : BstLean.Part264b.FrameData 12353 :=
  BstLean.Part269.frameData_from_numerics (n := 12353) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12353.worldPackage rfl BstLean.Part268.WorldRow12353.product_lower (BstLean.Part268.WorldRow12353.producthi.2.trans (by norm_num))
    scalarRow12353 repair12353 covarianceInputs12353 (fun i hi => sourceNumerics12353 hi)
    BstLean.Part268.agent12353.frame targetFrame12353_eq


end BstLean.Part269.N12353

namespace BstLean.Part269.N12354
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12354 : scalarRow12354.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12354, BstLean.Part268.grid12354, BstLean.Part263.worldGrid]

theorem supplies12354 (j : Fin 43) : Supply 12354 (parameters j)
    (cellLower scalarRow12354.grid (sourceIndex j))
    (cellUpper scalarRow12354.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12354.grid grid_top_bounds12354 j

theorem radii12354 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12354.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12354 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12354 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12354.grid grid_top_bounds12354 j hθ

noncomputable def covarianceInputs12354 :
    BstLean.Part263.CovarianceInputs 12354 scalarRow12354.grid parameters (caps repair12354) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12354 grid_top_bounds12354 repair12354

noncomputable def covarianceEvent12354 : Set (AgFam 12354) :=
  BstLean.Part263.covarianceEvent 12354 scalarRow12354.grid parameters

theorem covarianceEvent12354_measurable : MeasurableSet covarianceEvent12354 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12354_payment :
    (retDist (paperDesignP 12354).toCentres).real
      (agentEv (paperDesignP 12354) covarianceEvent12354)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12354

theorem localCov12354 : BstLean.Part259.LocalCovarianceOn covarianceEvent12354
    (BstLean.Part263.cell scalarRow12354.grid) (caps repair12354) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12354

theorem covarianceGood12354_payment :
    (retDist (paperDesignP 12354).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12354)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12354_payment



end BstLean.Part269.N12354

namespace BstLean.Part269.N12354
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12354}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12354.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12354) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12354).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12354 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12354) (by norm_num) BstLean.Part268.WorldRow12354.worldPackage rfl
    BstLean.Part268.WorldRow12354.product_lower (BstLean.Part268.WorldRow12354.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12354} (hw : c ∈ Hof BstLean.Part268.WorldRow12354.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12354) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12354) (by norm_num) BstLean.Part268.WorldRow12354.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12354} (hw : c ∈ Hof BstLean.Part268.WorldRow12354.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12354) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12354).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12354) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12354_eq : scalarRow12354.targetFrame = BstLean.Part268.agent12354.frame := by
  norm_num [scalarRow12354,BstLean.Part268.agent12354]

noncomputable def frameData12354 : BstLean.Part264b.FrameData 12354 :=
  BstLean.Part269.frameData_from_numerics (n := 12354) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12354.worldPackage rfl BstLean.Part268.WorldRow12354.product_lower (BstLean.Part268.WorldRow12354.producthi.2.trans (by norm_num))
    scalarRow12354 repair12354 covarianceInputs12354 (fun i hi => sourceNumerics12354 hi)
    BstLean.Part268.agent12354.frame targetFrame12354_eq


end BstLean.Part269.N12354

namespace BstLean.Part269.N12355
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12355 : scalarRow12355.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12355, BstLean.Part268.grid12355, BstLean.Part263.worldGrid]

theorem supplies12355 (j : Fin 43) : Supply 12355 (parameters j)
    (cellLower scalarRow12355.grid (sourceIndex j))
    (cellUpper scalarRow12355.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12355.grid grid_top_bounds12355 j

theorem radii12355 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12355.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12355 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12355 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12355.grid grid_top_bounds12355 j hθ

noncomputable def covarianceInputs12355 :
    BstLean.Part263.CovarianceInputs 12355 scalarRow12355.grid parameters (caps repair12355) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12355 grid_top_bounds12355 repair12355

noncomputable def covarianceEvent12355 : Set (AgFam 12355) :=
  BstLean.Part263.covarianceEvent 12355 scalarRow12355.grid parameters

theorem covarianceEvent12355_measurable : MeasurableSet covarianceEvent12355 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12355_payment :
    (retDist (paperDesignP 12355).toCentres).real
      (agentEv (paperDesignP 12355) covarianceEvent12355)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12355

theorem localCov12355 : BstLean.Part259.LocalCovarianceOn covarianceEvent12355
    (BstLean.Part263.cell scalarRow12355.grid) (caps repair12355) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12355

theorem covarianceGood12355_payment :
    (retDist (paperDesignP 12355).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12355)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12355_payment



end BstLean.Part269.N12355

namespace BstLean.Part269.N12355
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12355}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12355.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12355) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12355).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12355 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12355) (by norm_num) BstLean.Part268.WorldRow12355.worldPackage rfl
    BstLean.Part268.WorldRow12355.product_lower (BstLean.Part268.WorldRow12355.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12355} (hw : c ∈ Hof BstLean.Part268.WorldRow12355.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12355) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12355) (by norm_num) BstLean.Part268.WorldRow12355.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12355} (hw : c ∈ Hof BstLean.Part268.WorldRow12355.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12355) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12355).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12355) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12355_eq : scalarRow12355.targetFrame = BstLean.Part268.agent12355.frame := by
  norm_num [scalarRow12355,BstLean.Part268.agent12355]

noncomputable def frameData12355 : BstLean.Part264b.FrameData 12355 :=
  BstLean.Part269.frameData_from_numerics (n := 12355) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12355.worldPackage rfl BstLean.Part268.WorldRow12355.product_lower (BstLean.Part268.WorldRow12355.producthi.2.trans (by norm_num))
    scalarRow12355 repair12355 covarianceInputs12355 (fun i hi => sourceNumerics12355 hi)
    BstLean.Part268.agent12355.frame targetFrame12355_eq


end BstLean.Part269.N12355
