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

namespace BstLean.Part269.N12371
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12371 : scalarRow12371.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12371, BstLean.Part268.grid12371, BstLean.Part263.worldGrid]

theorem supplies12371 (j : Fin 43) : Supply 12371 (parameters j)
    (cellLower scalarRow12371.grid (sourceIndex j))
    (cellUpper scalarRow12371.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12371.grid grid_top_bounds12371 j

theorem radii12371 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12371.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12371 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12371 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12371.grid grid_top_bounds12371 j hθ

noncomputable def covarianceInputs12371 :
    BstLean.Part263.CovarianceInputs 12371 scalarRow12371.grid parameters (caps repair12371) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12371 grid_top_bounds12371 repair12371

noncomputable def covarianceEvent12371 : Set (AgFam 12371) :=
  BstLean.Part263.covarianceEvent 12371 scalarRow12371.grid parameters

theorem covarianceEvent12371_measurable : MeasurableSet covarianceEvent12371 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12371_payment :
    (retDist (paperDesignP 12371).toCentres).real
      (agentEv (paperDesignP 12371) covarianceEvent12371)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12371

theorem localCov12371 : BstLean.Part259.LocalCovarianceOn covarianceEvent12371
    (BstLean.Part263.cell scalarRow12371.grid) (caps repair12371) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12371

theorem covarianceGood12371_payment :
    (retDist (paperDesignP 12371).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12371)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12371_payment



end BstLean.Part269.N12371

namespace BstLean.Part269.N12371
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12371}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12371.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12371) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12371).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12371 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12371) (by norm_num) BstLean.Part268.WorldRow12371.worldPackage rfl
    BstLean.Part268.WorldRow12371.product_lower (BstLean.Part268.WorldRow12371.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12371} (hw : c ∈ Hof BstLean.Part268.WorldRow12371.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12371) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12371) (by norm_num) BstLean.Part268.WorldRow12371.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12371} (hw : c ∈ Hof BstLean.Part268.WorldRow12371.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12371) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12371).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12371) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12371_eq : scalarRow12371.targetFrame = BstLean.Part268.agent12371.frame := by
  norm_num [scalarRow12371,BstLean.Part268.agent12371]

noncomputable def frameData12371 : BstLean.Part264b.FrameData 12371 :=
  BstLean.Part269.frameData_from_numerics (n := 12371) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12371.worldPackage rfl BstLean.Part268.WorldRow12371.product_lower (BstLean.Part268.WorldRow12371.producthi.2.trans (by norm_num))
    scalarRow12371 repair12371 covarianceInputs12371 (fun i hi => sourceNumerics12371 hi)
    BstLean.Part268.agent12371.frame targetFrame12371_eq


end BstLean.Part269.N12371

namespace BstLean.Part269.N12372
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12372 : scalarRow12372.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12372, BstLean.Part268.grid12372, BstLean.Part263.worldGrid]

theorem supplies12372 (j : Fin 43) : Supply 12372 (parameters j)
    (cellLower scalarRow12372.grid (sourceIndex j))
    (cellUpper scalarRow12372.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12372.grid grid_top_bounds12372 j

theorem radii12372 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12372.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12372 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12372 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12372.grid grid_top_bounds12372 j hθ

noncomputable def covarianceInputs12372 :
    BstLean.Part263.CovarianceInputs 12372 scalarRow12372.grid parameters (caps repair12372) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12372 grid_top_bounds12372 repair12372

noncomputable def covarianceEvent12372 : Set (AgFam 12372) :=
  BstLean.Part263.covarianceEvent 12372 scalarRow12372.grid parameters

theorem covarianceEvent12372_measurable : MeasurableSet covarianceEvent12372 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12372_payment :
    (retDist (paperDesignP 12372).toCentres).real
      (agentEv (paperDesignP 12372) covarianceEvent12372)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12372

theorem localCov12372 : BstLean.Part259.LocalCovarianceOn covarianceEvent12372
    (BstLean.Part263.cell scalarRow12372.grid) (caps repair12372) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12372

theorem covarianceGood12372_payment :
    (retDist (paperDesignP 12372).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12372)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12372_payment



end BstLean.Part269.N12372

namespace BstLean.Part269.N12372
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12372}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12372.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12372) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12372).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12372 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12372) (by norm_num) BstLean.Part268.WorldRow12372.worldPackage rfl
    BstLean.Part268.WorldRow12372.product_lower (BstLean.Part268.WorldRow12372.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12372} (hw : c ∈ Hof BstLean.Part268.WorldRow12372.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12372) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12372) (by norm_num) BstLean.Part268.WorldRow12372.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12372} (hw : c ∈ Hof BstLean.Part268.WorldRow12372.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12372) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12372).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12372) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12372_eq : scalarRow12372.targetFrame = BstLean.Part268.agent12372.frame := by
  norm_num [scalarRow12372,BstLean.Part268.agent12372]

noncomputable def frameData12372 : BstLean.Part264b.FrameData 12372 :=
  BstLean.Part269.frameData_from_numerics (n := 12372) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12372.worldPackage rfl BstLean.Part268.WorldRow12372.product_lower (BstLean.Part268.WorldRow12372.producthi.2.trans (by norm_num))
    scalarRow12372 repair12372 covarianceInputs12372 (fun i hi => sourceNumerics12372 hi)
    BstLean.Part268.agent12372.frame targetFrame12372_eq


end BstLean.Part269.N12372

namespace BstLean.Part269.N12373
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12373 : scalarRow12373.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12373, BstLean.Part268.grid12373, BstLean.Part263.worldGrid]

theorem supplies12373 (j : Fin 43) : Supply 12373 (parameters j)
    (cellLower scalarRow12373.grid (sourceIndex j))
    (cellUpper scalarRow12373.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12373.grid grid_top_bounds12373 j

theorem radii12373 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12373.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12373 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12373 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12373.grid grid_top_bounds12373 j hθ

noncomputable def covarianceInputs12373 :
    BstLean.Part263.CovarianceInputs 12373 scalarRow12373.grid parameters (caps repair12373) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12373 grid_top_bounds12373 repair12373

noncomputable def covarianceEvent12373 : Set (AgFam 12373) :=
  BstLean.Part263.covarianceEvent 12373 scalarRow12373.grid parameters

theorem covarianceEvent12373_measurable : MeasurableSet covarianceEvent12373 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12373_payment :
    (retDist (paperDesignP 12373).toCentres).real
      (agentEv (paperDesignP 12373) covarianceEvent12373)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12373

theorem localCov12373 : BstLean.Part259.LocalCovarianceOn covarianceEvent12373
    (BstLean.Part263.cell scalarRow12373.grid) (caps repair12373) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12373

theorem covarianceGood12373_payment :
    (retDist (paperDesignP 12373).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12373)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12373_payment



end BstLean.Part269.N12373

namespace BstLean.Part269.N12373
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12373}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12373.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12373) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12373).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12373 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12373) (by norm_num) BstLean.Part268.WorldRow12373.worldPackage rfl
    BstLean.Part268.WorldRow12373.product_lower (BstLean.Part268.WorldRow12373.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12373} (hw : c ∈ Hof BstLean.Part268.WorldRow12373.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12373) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12373) (by norm_num) BstLean.Part268.WorldRow12373.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12373} (hw : c ∈ Hof BstLean.Part268.WorldRow12373.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12373) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12373).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12373) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12373_eq : scalarRow12373.targetFrame = BstLean.Part268.agent12373.frame := by
  norm_num [scalarRow12373,BstLean.Part268.agent12373]

noncomputable def frameData12373 : BstLean.Part264b.FrameData 12373 :=
  BstLean.Part269.frameData_from_numerics (n := 12373) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12373.worldPackage rfl BstLean.Part268.WorldRow12373.product_lower (BstLean.Part268.WorldRow12373.producthi.2.trans (by norm_num))
    scalarRow12373 repair12373 covarianceInputs12373 (fun i hi => sourceNumerics12373 hi)
    BstLean.Part268.agent12373.frame targetFrame12373_eq


end BstLean.Part269.N12373

namespace BstLean.Part269.N12374
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12374 : scalarRow12374.grid.top ∈
    Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12374, BstLean.Part268.grid12374, BstLean.Part263.worldGrid]

theorem supplies12374 (j : Fin 43) : Supply 12374 (parameters j)
    (cellLower scalarRow12374.grid (sourceIndex j))
    (cellUpper scalarRow12374.grid (sourceIndex j)) :=
  BstLean.Part269.BG0.supplies (by constructor <;> norm_num)
    scalarRow12374.grid grid_top_bounds12374 j

theorem radii12374 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12374.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12374 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12374 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG0.radii (by constructor <;> norm_num)
    scalarRow12374.grid grid_top_bounds12374 j hθ

noncomputable def covarianceInputs12374 :
    BstLean.Part263.CovarianceInputs 12374 scalarRow12374.grid parameters (caps repair12374) :=
  BstLean.Part269.BG0.covarianceInputs (by constructor <;> norm_num)
    scalarRow12374 grid_top_bounds12374 repair12374

noncomputable def covarianceEvent12374 : Set (AgFam 12374) :=
  BstLean.Part263.covarianceEvent 12374 scalarRow12374.grid parameters

theorem covarianceEvent12374_measurable : MeasurableSet covarianceEvent12374 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12374_payment :
    (retDist (paperDesignP 12374).toCentres).real
      (agentEv (paperDesignP 12374) covarianceEvent12374)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12374

theorem localCov12374 : BstLean.Part259.LocalCovarianceOn covarianceEvent12374
    (BstLean.Part263.cell scalarRow12374.grid) (caps repair12374) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12374

theorem covarianceGood12374_payment :
    (retDist (paperDesignP 12374).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12374)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12374_payment



end BstLean.Part269.N12374

namespace BstLean.Part269.N12374
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12374}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12374.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12374) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12374).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12374 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12374) (by norm_num) BstLean.Part268.WorldRow12374.worldPackage rfl
    BstLean.Part268.WorldRow12374.product_lower (BstLean.Part268.WorldRow12374.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12374} (hw : c ∈ Hof BstLean.Part268.WorldRow12374.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12374) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12374) (by norm_num) BstLean.Part268.WorldRow12374.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12374} (hw : c ∈ Hof BstLean.Part268.WorldRow12374.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12374) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12374).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12374) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12374_eq : scalarRow12374.targetFrame = BstLean.Part268.agent12374.frame := by
  norm_num [scalarRow12374,BstLean.Part268.agent12374]

noncomputable def frameData12374 : BstLean.Part264b.FrameData 12374 :=
  BstLean.Part269.frameData_from_numerics (n := 12374) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12374.worldPackage rfl BstLean.Part268.WorldRow12374.product_lower (BstLean.Part268.WorldRow12374.producthi.2.trans (by norm_num))
    scalarRow12374 repair12374 covarianceInputs12374 (fun i hi => sourceNumerics12374 hi)
    BstLean.Part268.agent12374.frame targetFrame12374_eq


end BstLean.Part269.N12374
