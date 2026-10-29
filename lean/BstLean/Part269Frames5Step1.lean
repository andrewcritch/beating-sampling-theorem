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

namespace BstLean.Part269.N12480
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12480 : scalarRow12480.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12480, BstLean.Part268.grid12480, BstLean.Part263.worldGrid]

theorem supplies12480 (j : Fin 43) : Supply 12480 (parameters j)
    (cellLower scalarRow12480.grid (sourceIndex j))
    (cellUpper scalarRow12480.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12480.grid grid_top_bounds12480 j

theorem radii12480 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12480.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12480 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12480 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12480.grid grid_top_bounds12480 j hθ

noncomputable def covarianceInputs12480 :
    BstLean.Part263.CovarianceInputs 12480 scalarRow12480.grid parameters (caps repair12480) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12480 grid_top_bounds12480 repair12480

noncomputable def covarianceEvent12480 : Set (AgFam 12480) :=
  BstLean.Part263.covarianceEvent 12480 scalarRow12480.grid parameters

theorem covarianceEvent12480_measurable : MeasurableSet covarianceEvent12480 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12480_payment :
    (retDist (paperDesignP 12480).toCentres).real
      (agentEv (paperDesignP 12480) covarianceEvent12480)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12480

theorem localCov12480 : BstLean.Part259.LocalCovarianceOn covarianceEvent12480
    (BstLean.Part263.cell scalarRow12480.grid) (caps repair12480) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12480

theorem covarianceGood12480_payment :
    (retDist (paperDesignP 12480).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12480)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12480_payment



end BstLean.Part269.N12480

namespace BstLean.Part269.N12480
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12480}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12480.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12480) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12480).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12480 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12480) (by norm_num) BstLean.Part268.WorldRow12480.worldPackage rfl
    BstLean.Part268.WorldRow12480.product_lower (BstLean.Part268.WorldRow12480.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12480} (hw : c ∈ Hof BstLean.Part268.WorldRow12480.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12480) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12480) (by norm_num) BstLean.Part268.WorldRow12480.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12480} (hw : c ∈ Hof BstLean.Part268.WorldRow12480.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12480) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12480).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12480) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12480_eq : scalarRow12480.targetFrame = BstLean.Part268.agent12480.frame := by
  norm_num [scalarRow12480,BstLean.Part268.agent12480]

noncomputable def frameData12480 : BstLean.Part264b.FrameData 12480 :=
  BstLean.Part269.frameData_from_numerics (n := 12480) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12480.worldPackage rfl BstLean.Part268.WorldRow12480.product_lower (BstLean.Part268.WorldRow12480.producthi.2.trans (by norm_num))
    scalarRow12480 repair12480 covarianceInputs12480 (fun i hi => sourceNumerics12480 hi)
    BstLean.Part268.agent12480.frame targetFrame12480_eq


end BstLean.Part269.N12480

namespace BstLean.Part269.N12481
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12481 : scalarRow12481.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12481, BstLean.Part268.grid12481, BstLean.Part263.worldGrid]

theorem supplies12481 (j : Fin 43) : Supply 12481 (parameters j)
    (cellLower scalarRow12481.grid (sourceIndex j))
    (cellUpper scalarRow12481.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12481.grid grid_top_bounds12481 j

theorem radii12481 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12481.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12481 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12481 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12481.grid grid_top_bounds12481 j hθ

noncomputable def covarianceInputs12481 :
    BstLean.Part263.CovarianceInputs 12481 scalarRow12481.grid parameters (caps repair12481) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12481 grid_top_bounds12481 repair12481

noncomputable def covarianceEvent12481 : Set (AgFam 12481) :=
  BstLean.Part263.covarianceEvent 12481 scalarRow12481.grid parameters

theorem covarianceEvent12481_measurable : MeasurableSet covarianceEvent12481 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12481_payment :
    (retDist (paperDesignP 12481).toCentres).real
      (agentEv (paperDesignP 12481) covarianceEvent12481)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12481

theorem localCov12481 : BstLean.Part259.LocalCovarianceOn covarianceEvent12481
    (BstLean.Part263.cell scalarRow12481.grid) (caps repair12481) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12481

theorem covarianceGood12481_payment :
    (retDist (paperDesignP 12481).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12481)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12481_payment



end BstLean.Part269.N12481

namespace BstLean.Part269.N12481
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12481}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12481.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12481) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12481).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12481 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12481) (by norm_num) BstLean.Part268.WorldRow12481.worldPackage rfl
    BstLean.Part268.WorldRow12481.product_lower (BstLean.Part268.WorldRow12481.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12481} (hw : c ∈ Hof BstLean.Part268.WorldRow12481.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12481) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12481) (by norm_num) BstLean.Part268.WorldRow12481.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12481} (hw : c ∈ Hof BstLean.Part268.WorldRow12481.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12481) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12481).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12481) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12481_eq : scalarRow12481.targetFrame = BstLean.Part268.agent12481.frame := by
  norm_num [scalarRow12481,BstLean.Part268.agent12481]

noncomputable def frameData12481 : BstLean.Part264b.FrameData 12481 :=
  BstLean.Part269.frameData_from_numerics (n := 12481) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12481.worldPackage rfl BstLean.Part268.WorldRow12481.product_lower (BstLean.Part268.WorldRow12481.producthi.2.trans (by norm_num))
    scalarRow12481 repair12481 covarianceInputs12481 (fun i hi => sourceNumerics12481 hi)
    BstLean.Part268.agent12481.frame targetFrame12481_eq


end BstLean.Part269.N12481

namespace BstLean.Part269.N12482
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12482 : scalarRow12482.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12482, BstLean.Part268.grid12482, BstLean.Part263.worldGrid]

theorem supplies12482 (j : Fin 43) : Supply 12482 (parameters j)
    (cellLower scalarRow12482.grid (sourceIndex j))
    (cellUpper scalarRow12482.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12482.grid grid_top_bounds12482 j

theorem radii12482 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12482.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12482 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12482 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12482.grid grid_top_bounds12482 j hθ

noncomputable def covarianceInputs12482 :
    BstLean.Part263.CovarianceInputs 12482 scalarRow12482.grid parameters (caps repair12482) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12482 grid_top_bounds12482 repair12482

noncomputable def covarianceEvent12482 : Set (AgFam 12482) :=
  BstLean.Part263.covarianceEvent 12482 scalarRow12482.grid parameters

theorem covarianceEvent12482_measurable : MeasurableSet covarianceEvent12482 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12482_payment :
    (retDist (paperDesignP 12482).toCentres).real
      (agentEv (paperDesignP 12482) covarianceEvent12482)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12482

theorem localCov12482 : BstLean.Part259.LocalCovarianceOn covarianceEvent12482
    (BstLean.Part263.cell scalarRow12482.grid) (caps repair12482) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12482

theorem covarianceGood12482_payment :
    (retDist (paperDesignP 12482).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12482)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12482_payment



end BstLean.Part269.N12482

namespace BstLean.Part269.N12482
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12482}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12482.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12482) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12482).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12482 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12482) (by norm_num) BstLean.Part268.WorldRow12482.worldPackage rfl
    BstLean.Part268.WorldRow12482.product_lower (BstLean.Part268.WorldRow12482.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12482} (hw : c ∈ Hof BstLean.Part268.WorldRow12482.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12482) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12482) (by norm_num) BstLean.Part268.WorldRow12482.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12482} (hw : c ∈ Hof BstLean.Part268.WorldRow12482.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12482) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12482).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12482) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12482_eq : scalarRow12482.targetFrame = BstLean.Part268.agent12482.frame := by
  norm_num [scalarRow12482,BstLean.Part268.agent12482]

noncomputable def frameData12482 : BstLean.Part264b.FrameData 12482 :=
  BstLean.Part269.frameData_from_numerics (n := 12482) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12482.worldPackage rfl BstLean.Part268.WorldRow12482.product_lower (BstLean.Part268.WorldRow12482.producthi.2.trans (by norm_num))
    scalarRow12482 repair12482 covarianceInputs12482 (fun i hi => sourceNumerics12482 hi)
    BstLean.Part268.agent12482.frame targetFrame12482_eq


end BstLean.Part269.N12482

namespace BstLean.Part269.N12483
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12483 : scalarRow12483.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12483, BstLean.Part268.grid12483, BstLean.Part263.worldGrid]

theorem supplies12483 (j : Fin 43) : Supply 12483 (parameters j)
    (cellLower scalarRow12483.grid (sourceIndex j))
    (cellUpper scalarRow12483.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12483.grid grid_top_bounds12483 j

theorem radii12483 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12483.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12483 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12483 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12483.grid grid_top_bounds12483 j hθ

noncomputable def covarianceInputs12483 :
    BstLean.Part263.CovarianceInputs 12483 scalarRow12483.grid parameters (caps repair12483) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12483 grid_top_bounds12483 repair12483

noncomputable def covarianceEvent12483 : Set (AgFam 12483) :=
  BstLean.Part263.covarianceEvent 12483 scalarRow12483.grid parameters

theorem covarianceEvent12483_measurable : MeasurableSet covarianceEvent12483 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12483_payment :
    (retDist (paperDesignP 12483).toCentres).real
      (agentEv (paperDesignP 12483) covarianceEvent12483)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12483

theorem localCov12483 : BstLean.Part259.LocalCovarianceOn covarianceEvent12483
    (BstLean.Part263.cell scalarRow12483.grid) (caps repair12483) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12483

theorem covarianceGood12483_payment :
    (retDist (paperDesignP 12483).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12483)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12483_payment



end BstLean.Part269.N12483

namespace BstLean.Part269.N12483
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12483}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12483.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12483) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12483).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12483 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12483) (by norm_num) BstLean.Part268.WorldRow12483.worldPackage rfl
    BstLean.Part268.WorldRow12483.product_lower (BstLean.Part268.WorldRow12483.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12483} (hw : c ∈ Hof BstLean.Part268.WorldRow12483.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12483) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12483) (by norm_num) BstLean.Part268.WorldRow12483.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12483} (hw : c ∈ Hof BstLean.Part268.WorldRow12483.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12483) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12483).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12483) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12483_eq : scalarRow12483.targetFrame = BstLean.Part268.agent12483.frame := by
  norm_num [scalarRow12483,BstLean.Part268.agent12483]

noncomputable def frameData12483 : BstLean.Part264b.FrameData 12483 :=
  BstLean.Part269.frameData_from_numerics (n := 12483) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12483.worldPackage rfl BstLean.Part268.WorldRow12483.product_lower (BstLean.Part268.WorldRow12483.producthi.2.trans (by norm_num))
    scalarRow12483 repair12483 covarianceInputs12483 (fun i hi => sourceNumerics12483 hi)
    BstLean.Part268.agent12483.frame targetFrame12483_eq


end BstLean.Part269.N12483

namespace BstLean.Part269.N12484
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12484 : scalarRow12484.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12484, BstLean.Part268.grid12484, BstLean.Part263.worldGrid]

theorem supplies12484 (j : Fin 43) : Supply 12484 (parameters j)
    (cellLower scalarRow12484.grid (sourceIndex j))
    (cellUpper scalarRow12484.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12484.grid grid_top_bounds12484 j

theorem radii12484 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12484.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12484 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12484 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12484.grid grid_top_bounds12484 j hθ

noncomputable def covarianceInputs12484 :
    BstLean.Part263.CovarianceInputs 12484 scalarRow12484.grid parameters (caps repair12484) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12484 grid_top_bounds12484 repair12484

noncomputable def covarianceEvent12484 : Set (AgFam 12484) :=
  BstLean.Part263.covarianceEvent 12484 scalarRow12484.grid parameters

theorem covarianceEvent12484_measurable : MeasurableSet covarianceEvent12484 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12484_payment :
    (retDist (paperDesignP 12484).toCentres).real
      (agentEv (paperDesignP 12484) covarianceEvent12484)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12484

theorem localCov12484 : BstLean.Part259.LocalCovarianceOn covarianceEvent12484
    (BstLean.Part263.cell scalarRow12484.grid) (caps repair12484) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12484

theorem covarianceGood12484_payment :
    (retDist (paperDesignP 12484).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12484)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12484_payment



end BstLean.Part269.N12484

namespace BstLean.Part269.N12484
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12484}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12484.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12484) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12484).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12484 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12484) (by norm_num) BstLean.Part268.WorldRow12484.worldPackage rfl
    BstLean.Part268.WorldRow12484.product_lower (BstLean.Part268.WorldRow12484.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12484} (hw : c ∈ Hof BstLean.Part268.WorldRow12484.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12484) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12484) (by norm_num) BstLean.Part268.WorldRow12484.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12484} (hw : c ∈ Hof BstLean.Part268.WorldRow12484.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12484) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12484).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12484) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12484_eq : scalarRow12484.targetFrame = BstLean.Part268.agent12484.frame := by
  norm_num [scalarRow12484,BstLean.Part268.agent12484]

noncomputable def frameData12484 : BstLean.Part264b.FrameData 12484 :=
  BstLean.Part269.frameData_from_numerics (n := 12484) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12484.worldPackage rfl BstLean.Part268.WorldRow12484.product_lower (BstLean.Part268.WorldRow12484.producthi.2.trans (by norm_num))
    scalarRow12484 repair12484 covarianceInputs12484 (fun i hi => sourceNumerics12484 hi)
    BstLean.Part268.agent12484.frame targetFrame12484_eq


end BstLean.Part269.N12484
