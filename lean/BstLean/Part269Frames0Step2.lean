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

namespace BstLean.Part269.N12361
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12361 : scalarRow12361.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12361, BstLean.Part268.grid12361, BstLean.Part263.worldGrid]

theorem supplies12361 (j : Fin 43) : Supply 12361 (parameters j)
    (cellLower scalarRow12361.grid (sourceIndex j))
    (cellUpper scalarRow12361.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12361.grid grid_top_bounds12361 j

theorem radii12361 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12361.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12361 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12361 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12361.grid grid_top_bounds12361 j hθ

noncomputable def covarianceInputs12361 :
    BstLean.Part263.CovarianceInputs 12361 scalarRow12361.grid parameters (caps repair12361) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12361 grid_top_bounds12361 repair12361

noncomputable def covarianceEvent12361 : Set (AgFam 12361) :=
  BstLean.Part263.covarianceEvent 12361 scalarRow12361.grid parameters

theorem covarianceEvent12361_measurable : MeasurableSet covarianceEvent12361 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12361_payment :
    (retDist (paperDesignP 12361).toCentres).real
      (agentEv (paperDesignP 12361) covarianceEvent12361)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12361

theorem localCov12361 : BstLean.Part259.LocalCovarianceOn covarianceEvent12361
    (BstLean.Part263.cell scalarRow12361.grid) (caps repair12361) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12361

theorem covarianceGood12361_payment :
    (retDist (paperDesignP 12361).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12361)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12361_payment



end BstLean.Part269.N12361

namespace BstLean.Part269.N12361
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12361}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12361.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12361) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12361).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12361 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12361) (by norm_num) BstLean.Part268.WorldRow12361.worldPackage rfl
    BstLean.Part268.WorldRow12361.product_lower (BstLean.Part268.WorldRow12361.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12361} (hw : c ∈ Hof BstLean.Part268.WorldRow12361.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12361) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12361) (by norm_num) BstLean.Part268.WorldRow12361.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12361} (hw : c ∈ Hof BstLean.Part268.WorldRow12361.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12361) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12361).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12361) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12361_eq : scalarRow12361.targetFrame = BstLean.Part268.agent12361.frame := by
  norm_num [scalarRow12361,BstLean.Part268.agent12361]

noncomputable def frameData12361 : BstLean.Part264b.FrameData 12361 :=
  BstLean.Part269.frameData_from_numerics (n := 12361) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12361.worldPackage rfl BstLean.Part268.WorldRow12361.product_lower (BstLean.Part268.WorldRow12361.producthi.2.trans (by norm_num))
    scalarRow12361 repair12361 covarianceInputs12361 (fun i hi => sourceNumerics12361 hi)
    BstLean.Part268.agent12361.frame targetFrame12361_eq


end BstLean.Part269.N12361

namespace BstLean.Part269.N12362
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12362 : scalarRow12362.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12362, BstLean.Part268.grid12362, BstLean.Part263.worldGrid]

theorem supplies12362 (j : Fin 43) : Supply 12362 (parameters j)
    (cellLower scalarRow12362.grid (sourceIndex j))
    (cellUpper scalarRow12362.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12362.grid grid_top_bounds12362 j

theorem radii12362 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12362.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12362 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12362 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12362.grid grid_top_bounds12362 j hθ

noncomputable def covarianceInputs12362 :
    BstLean.Part263.CovarianceInputs 12362 scalarRow12362.grid parameters (caps repair12362) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12362 grid_top_bounds12362 repair12362

noncomputable def covarianceEvent12362 : Set (AgFam 12362) :=
  BstLean.Part263.covarianceEvent 12362 scalarRow12362.grid parameters

theorem covarianceEvent12362_measurable : MeasurableSet covarianceEvent12362 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12362_payment :
    (retDist (paperDesignP 12362).toCentres).real
      (agentEv (paperDesignP 12362) covarianceEvent12362)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12362

theorem localCov12362 : BstLean.Part259.LocalCovarianceOn covarianceEvent12362
    (BstLean.Part263.cell scalarRow12362.grid) (caps repair12362) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12362

theorem covarianceGood12362_payment :
    (retDist (paperDesignP 12362).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12362)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12362_payment



end BstLean.Part269.N12362

namespace BstLean.Part269.N12362
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12362}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12362.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12362) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12362).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12362 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12362) (by norm_num) BstLean.Part268.WorldRow12362.worldPackage rfl
    BstLean.Part268.WorldRow12362.product_lower (BstLean.Part268.WorldRow12362.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12362} (hw : c ∈ Hof BstLean.Part268.WorldRow12362.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12362) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12362) (by norm_num) BstLean.Part268.WorldRow12362.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12362} (hw : c ∈ Hof BstLean.Part268.WorldRow12362.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12362) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12362).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12362) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12362_eq : scalarRow12362.targetFrame = BstLean.Part268.agent12362.frame := by
  norm_num [scalarRow12362,BstLean.Part268.agent12362]

noncomputable def frameData12362 : BstLean.Part264b.FrameData 12362 :=
  BstLean.Part269.frameData_from_numerics (n := 12362) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12362.worldPackage rfl BstLean.Part268.WorldRow12362.product_lower (BstLean.Part268.WorldRow12362.producthi.2.trans (by norm_num))
    scalarRow12362 repair12362 covarianceInputs12362 (fun i hi => sourceNumerics12362 hi)
    BstLean.Part268.agent12362.frame targetFrame12362_eq


end BstLean.Part269.N12362

namespace BstLean.Part269.N12363
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12363 : scalarRow12363.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12363, BstLean.Part268.grid12363, BstLean.Part263.worldGrid]

theorem supplies12363 (j : Fin 43) : Supply 12363 (parameters j)
    (cellLower scalarRow12363.grid (sourceIndex j))
    (cellUpper scalarRow12363.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12363.grid grid_top_bounds12363 j

theorem radii12363 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12363.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12363 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12363 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12363.grid grid_top_bounds12363 j hθ

noncomputable def covarianceInputs12363 :
    BstLean.Part263.CovarianceInputs 12363 scalarRow12363.grid parameters (caps repair12363) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12363 grid_top_bounds12363 repair12363

noncomputable def covarianceEvent12363 : Set (AgFam 12363) :=
  BstLean.Part263.covarianceEvent 12363 scalarRow12363.grid parameters

theorem covarianceEvent12363_measurable : MeasurableSet covarianceEvent12363 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12363_payment :
    (retDist (paperDesignP 12363).toCentres).real
      (agentEv (paperDesignP 12363) covarianceEvent12363)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12363

theorem localCov12363 : BstLean.Part259.LocalCovarianceOn covarianceEvent12363
    (BstLean.Part263.cell scalarRow12363.grid) (caps repair12363) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12363

theorem covarianceGood12363_payment :
    (retDist (paperDesignP 12363).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12363)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12363_payment



end BstLean.Part269.N12363

namespace BstLean.Part269.N12363
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12363}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12363.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12363) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12363).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12363 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12363) (by norm_num) BstLean.Part268.WorldRow12363.worldPackage rfl
    BstLean.Part268.WorldRow12363.product_lower (BstLean.Part268.WorldRow12363.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12363} (hw : c ∈ Hof BstLean.Part268.WorldRow12363.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12363) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12363) (by norm_num) BstLean.Part268.WorldRow12363.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12363} (hw : c ∈ Hof BstLean.Part268.WorldRow12363.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12363) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12363).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12363) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12363_eq : scalarRow12363.targetFrame = BstLean.Part268.agent12363.frame := by
  norm_num [scalarRow12363,BstLean.Part268.agent12363]

noncomputable def frameData12363 : BstLean.Part264b.FrameData 12363 :=
  BstLean.Part269.frameData_from_numerics (n := 12363) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12363.worldPackage rfl BstLean.Part268.WorldRow12363.product_lower (BstLean.Part268.WorldRow12363.producthi.2.trans (by norm_num))
    scalarRow12363 repair12363 covarianceInputs12363 (fun i hi => sourceNumerics12363 hi)
    BstLean.Part268.agent12363.frame targetFrame12363_eq


end BstLean.Part269.N12363

namespace BstLean.Part269.N12364
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12364 : scalarRow12364.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12364, BstLean.Part268.grid12364, BstLean.Part263.worldGrid]

theorem supplies12364 (j : Fin 43) : Supply 12364 (parameters j)
    (cellLower scalarRow12364.grid (sourceIndex j))
    (cellUpper scalarRow12364.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12364.grid grid_top_bounds12364 j

theorem radii12364 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12364.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12364 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12364 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12364.grid grid_top_bounds12364 j hθ

noncomputable def covarianceInputs12364 :
    BstLean.Part263.CovarianceInputs 12364 scalarRow12364.grid parameters (caps repair12364) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12364 grid_top_bounds12364 repair12364

noncomputable def covarianceEvent12364 : Set (AgFam 12364) :=
  BstLean.Part263.covarianceEvent 12364 scalarRow12364.grid parameters

theorem covarianceEvent12364_measurable : MeasurableSet covarianceEvent12364 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12364_payment :
    (retDist (paperDesignP 12364).toCentres).real
      (agentEv (paperDesignP 12364) covarianceEvent12364)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12364

theorem localCov12364 : BstLean.Part259.LocalCovarianceOn covarianceEvent12364
    (BstLean.Part263.cell scalarRow12364.grid) (caps repair12364) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12364

theorem covarianceGood12364_payment :
    (retDist (paperDesignP 12364).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12364)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12364_payment



end BstLean.Part269.N12364

namespace BstLean.Part269.N12364
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12364}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12364.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12364) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12364).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12364 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12364) (by norm_num) BstLean.Part268.WorldRow12364.worldPackage rfl
    BstLean.Part268.WorldRow12364.product_lower (BstLean.Part268.WorldRow12364.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12364} (hw : c ∈ Hof BstLean.Part268.WorldRow12364.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12364) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12364) (by norm_num) BstLean.Part268.WorldRow12364.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12364} (hw : c ∈ Hof BstLean.Part268.WorldRow12364.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12364) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12364).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12364) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12364_eq : scalarRow12364.targetFrame = BstLean.Part268.agent12364.frame := by
  norm_num [scalarRow12364,BstLean.Part268.agent12364]

noncomputable def frameData12364 : BstLean.Part264b.FrameData 12364 :=
  BstLean.Part269.frameData_from_numerics (n := 12364) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12364.worldPackage rfl BstLean.Part268.WorldRow12364.product_lower (BstLean.Part268.WorldRow12364.producthi.2.trans (by norm_num))
    scalarRow12364 repair12364 covarianceInputs12364 (fun i hi => sourceNumerics12364 hi)
    BstLean.Part268.agent12364.frame targetFrame12364_eq


end BstLean.Part269.N12364

namespace BstLean.Part269.N12365
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12365 : scalarRow12365.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12365, BstLean.Part268.grid12365, BstLean.Part263.worldGrid]

theorem supplies12365 (j : Fin 43) : Supply 12365 (parameters j)
    (cellLower scalarRow12365.grid (sourceIndex j))
    (cellUpper scalarRow12365.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12365.grid grid_top_bounds12365 j

theorem radii12365 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12365.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12365 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12365 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12365.grid grid_top_bounds12365 j hθ

noncomputable def covarianceInputs12365 :
    BstLean.Part263.CovarianceInputs 12365 scalarRow12365.grid parameters (caps repair12365) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12365 grid_top_bounds12365 repair12365

noncomputable def covarianceEvent12365 : Set (AgFam 12365) :=
  BstLean.Part263.covarianceEvent 12365 scalarRow12365.grid parameters

theorem covarianceEvent12365_measurable : MeasurableSet covarianceEvent12365 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12365_payment :
    (retDist (paperDesignP 12365).toCentres).real
      (agentEv (paperDesignP 12365) covarianceEvent12365)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12365

theorem localCov12365 : BstLean.Part259.LocalCovarianceOn covarianceEvent12365
    (BstLean.Part263.cell scalarRow12365.grid) (caps repair12365) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12365

theorem covarianceGood12365_payment :
    (retDist (paperDesignP 12365).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12365)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12365_payment



end BstLean.Part269.N12365

namespace BstLean.Part269.N12365
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12365}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12365.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12365) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12365).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12365 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12365) (by norm_num) BstLean.Part268.WorldRow12365.worldPackage rfl
    BstLean.Part268.WorldRow12365.product_lower (BstLean.Part268.WorldRow12365.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12365} (hw : c ∈ Hof BstLean.Part268.WorldRow12365.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12365) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12365) (by norm_num) BstLean.Part268.WorldRow12365.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12365} (hw : c ∈ Hof BstLean.Part268.WorldRow12365.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12365) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12365).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12365) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12365_eq : scalarRow12365.targetFrame = BstLean.Part268.agent12365.frame := by
  norm_num [scalarRow12365,BstLean.Part268.agent12365]

noncomputable def frameData12365 : BstLean.Part264b.FrameData 12365 :=
  BstLean.Part269.frameData_from_numerics (n := 12365) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12365.worldPackage rfl BstLean.Part268.WorldRow12365.product_lower (BstLean.Part268.WorldRow12365.producthi.2.trans (by norm_num))
    scalarRow12365 repair12365 covarianceInputs12365 (fun i hi => sourceNumerics12365 hi)
    BstLean.Part268.agent12365.frame targetFrame12365_eq


end BstLean.Part269.N12365
