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

namespace BstLean.Part269.N12490
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12490 : scalarRow12490.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12490, BstLean.Part268.grid12490, BstLean.Part263.worldGrid]

theorem supplies12490 (j : Fin 43) : Supply 12490 (parameters j)
    (cellLower scalarRow12490.grid (sourceIndex j))
    (cellUpper scalarRow12490.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12490.grid grid_top_bounds12490 j

theorem radii12490 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12490.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12490 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12490 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12490.grid grid_top_bounds12490 j hθ

noncomputable def covarianceInputs12490 :
    BstLean.Part263.CovarianceInputs 12490 scalarRow12490.grid parameters (caps repair12490) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12490 grid_top_bounds12490 repair12490

noncomputable def covarianceEvent12490 : Set (AgFam 12490) :=
  BstLean.Part263.covarianceEvent 12490 scalarRow12490.grid parameters

theorem covarianceEvent12490_measurable : MeasurableSet covarianceEvent12490 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12490_payment :
    (retDist (paperDesignP 12490).toCentres).real
      (agentEv (paperDesignP 12490) covarianceEvent12490)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12490

theorem localCov12490 : BstLean.Part259.LocalCovarianceOn covarianceEvent12490
    (BstLean.Part263.cell scalarRow12490.grid) (caps repair12490) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12490

theorem covarianceGood12490_payment :
    (retDist (paperDesignP 12490).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12490)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12490_payment



end BstLean.Part269.N12490

namespace BstLean.Part269.N12490
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12490}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12490.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12490) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12490).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12490 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12490) (by norm_num) BstLean.Part268.WorldRow12490.worldPackage rfl
    BstLean.Part268.WorldRow12490.product_lower (BstLean.Part268.WorldRow12490.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12490} (hw : c ∈ Hof BstLean.Part268.WorldRow12490.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12490) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12490) (by norm_num) BstLean.Part268.WorldRow12490.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12490} (hw : c ∈ Hof BstLean.Part268.WorldRow12490.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12490) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12490).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12490) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12490_eq : scalarRow12490.targetFrame = BstLean.Part268.agent12490.frame := by
  norm_num [scalarRow12490,BstLean.Part268.agent12490]

noncomputable def frameData12490 : BstLean.Part264b.FrameData 12490 :=
  BstLean.Part269.frameData_from_numerics (n := 12490) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12490.worldPackage rfl BstLean.Part268.WorldRow12490.product_lower (BstLean.Part268.WorldRow12490.producthi.2.trans (by norm_num))
    scalarRow12490 repair12490 covarianceInputs12490 (fun i hi => sourceNumerics12490 hi)
    BstLean.Part268.agent12490.frame targetFrame12490_eq


end BstLean.Part269.N12490

namespace BstLean.Part269.N12491
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12491 : scalarRow12491.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12491, BstLean.Part268.grid12491, BstLean.Part263.worldGrid]

theorem supplies12491 (j : Fin 43) : Supply 12491 (parameters j)
    (cellLower scalarRow12491.grid (sourceIndex j))
    (cellUpper scalarRow12491.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12491.grid grid_top_bounds12491 j

theorem radii12491 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12491.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12491 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12491 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12491.grid grid_top_bounds12491 j hθ

noncomputable def covarianceInputs12491 :
    BstLean.Part263.CovarianceInputs 12491 scalarRow12491.grid parameters (caps repair12491) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12491 grid_top_bounds12491 repair12491

noncomputable def covarianceEvent12491 : Set (AgFam 12491) :=
  BstLean.Part263.covarianceEvent 12491 scalarRow12491.grid parameters

theorem covarianceEvent12491_measurable : MeasurableSet covarianceEvent12491 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12491_payment :
    (retDist (paperDesignP 12491).toCentres).real
      (agentEv (paperDesignP 12491) covarianceEvent12491)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12491

theorem localCov12491 : BstLean.Part259.LocalCovarianceOn covarianceEvent12491
    (BstLean.Part263.cell scalarRow12491.grid) (caps repair12491) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12491

theorem covarianceGood12491_payment :
    (retDist (paperDesignP 12491).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12491)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12491_payment



end BstLean.Part269.N12491

namespace BstLean.Part269.N12491
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12491}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12491.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12491) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12491).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12491 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12491) (by norm_num) BstLean.Part268.WorldRow12491.worldPackage rfl
    BstLean.Part268.WorldRow12491.product_lower (BstLean.Part268.WorldRow12491.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12491} (hw : c ∈ Hof BstLean.Part268.WorldRow12491.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12491) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12491) (by norm_num) BstLean.Part268.WorldRow12491.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12491} (hw : c ∈ Hof BstLean.Part268.WorldRow12491.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12491) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12491).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12491) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12491_eq : scalarRow12491.targetFrame = BstLean.Part268.agent12491.frame := by
  norm_num [scalarRow12491,BstLean.Part268.agent12491]

noncomputable def frameData12491 : BstLean.Part264b.FrameData 12491 :=
  BstLean.Part269.frameData_from_numerics (n := 12491) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12491.worldPackage rfl BstLean.Part268.WorldRow12491.product_lower (BstLean.Part268.WorldRow12491.producthi.2.trans (by norm_num))
    scalarRow12491 repair12491 covarianceInputs12491 (fun i hi => sourceNumerics12491 hi)
    BstLean.Part268.agent12491.frame targetFrame12491_eq


end BstLean.Part269.N12491

namespace BstLean.Part269.N12492
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12492 : scalarRow12492.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12492, BstLean.Part268.grid12492, BstLean.Part263.worldGrid]

theorem supplies12492 (j : Fin 43) : Supply 12492 (parameters j)
    (cellLower scalarRow12492.grid (sourceIndex j))
    (cellUpper scalarRow12492.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12492.grid grid_top_bounds12492 j

theorem radii12492 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12492.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12492 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12492 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12492.grid grid_top_bounds12492 j hθ

noncomputable def covarianceInputs12492 :
    BstLean.Part263.CovarianceInputs 12492 scalarRow12492.grid parameters (caps repair12492) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12492 grid_top_bounds12492 repair12492

noncomputable def covarianceEvent12492 : Set (AgFam 12492) :=
  BstLean.Part263.covarianceEvent 12492 scalarRow12492.grid parameters

theorem covarianceEvent12492_measurable : MeasurableSet covarianceEvent12492 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12492_payment :
    (retDist (paperDesignP 12492).toCentres).real
      (agentEv (paperDesignP 12492) covarianceEvent12492)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12492

theorem localCov12492 : BstLean.Part259.LocalCovarianceOn covarianceEvent12492
    (BstLean.Part263.cell scalarRow12492.grid) (caps repair12492) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12492

theorem covarianceGood12492_payment :
    (retDist (paperDesignP 12492).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12492)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12492_payment



end BstLean.Part269.N12492

namespace BstLean.Part269.N12492
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12492}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12492.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12492) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12492).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12492 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12492) (by norm_num) BstLean.Part268.WorldRow12492.worldPackage rfl
    BstLean.Part268.WorldRow12492.product_lower (BstLean.Part268.WorldRow12492.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12492} (hw : c ∈ Hof BstLean.Part268.WorldRow12492.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12492) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12492) (by norm_num) BstLean.Part268.WorldRow12492.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12492} (hw : c ∈ Hof BstLean.Part268.WorldRow12492.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12492) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12492).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12492) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12492_eq : scalarRow12492.targetFrame = BstLean.Part268.agent12492.frame := by
  norm_num [scalarRow12492,BstLean.Part268.agent12492]

noncomputable def frameData12492 : BstLean.Part264b.FrameData 12492 :=
  BstLean.Part269.frameData_from_numerics (n := 12492) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12492.worldPackage rfl BstLean.Part268.WorldRow12492.product_lower (BstLean.Part268.WorldRow12492.producthi.2.trans (by norm_num))
    scalarRow12492 repair12492 covarianceInputs12492 (fun i hi => sourceNumerics12492 hi)
    BstLean.Part268.agent12492.frame targetFrame12492_eq


end BstLean.Part269.N12492

namespace BstLean.Part269.N12493
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12493 : scalarRow12493.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12493, BstLean.Part268.grid12493, BstLean.Part263.worldGrid]

theorem supplies12493 (j : Fin 43) : Supply 12493 (parameters j)
    (cellLower scalarRow12493.grid (sourceIndex j))
    (cellUpper scalarRow12493.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12493.grid grid_top_bounds12493 j

theorem radii12493 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12493.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12493 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12493 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12493.grid grid_top_bounds12493 j hθ

noncomputable def covarianceInputs12493 :
    BstLean.Part263.CovarianceInputs 12493 scalarRow12493.grid parameters (caps repair12493) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12493 grid_top_bounds12493 repair12493

noncomputable def covarianceEvent12493 : Set (AgFam 12493) :=
  BstLean.Part263.covarianceEvent 12493 scalarRow12493.grid parameters

theorem covarianceEvent12493_measurable : MeasurableSet covarianceEvent12493 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12493_payment :
    (retDist (paperDesignP 12493).toCentres).real
      (agentEv (paperDesignP 12493) covarianceEvent12493)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12493

theorem localCov12493 : BstLean.Part259.LocalCovarianceOn covarianceEvent12493
    (BstLean.Part263.cell scalarRow12493.grid) (caps repair12493) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12493

theorem covarianceGood12493_payment :
    (retDist (paperDesignP 12493).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12493)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12493_payment



end BstLean.Part269.N12493

namespace BstLean.Part269.N12493
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12493}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12493.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12493) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12493).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12493 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12493) (by norm_num) BstLean.Part268.WorldRow12493.worldPackage rfl
    BstLean.Part268.WorldRow12493.product_lower (BstLean.Part268.WorldRow12493.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12493} (hw : c ∈ Hof BstLean.Part268.WorldRow12493.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12493) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12493) (by norm_num) BstLean.Part268.WorldRow12493.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12493} (hw : c ∈ Hof BstLean.Part268.WorldRow12493.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12493) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12493).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12493) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12493_eq : scalarRow12493.targetFrame = BstLean.Part268.agent12493.frame := by
  norm_num [scalarRow12493,BstLean.Part268.agent12493]

noncomputable def frameData12493 : BstLean.Part264b.FrameData 12493 :=
  BstLean.Part269.frameData_from_numerics (n := 12493) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12493.worldPackage rfl BstLean.Part268.WorldRow12493.product_lower (BstLean.Part268.WorldRow12493.producthi.2.trans (by norm_num))
    scalarRow12493 repair12493 covarianceInputs12493 (fun i hi => sourceNumerics12493 hi)
    BstLean.Part268.agent12493.frame targetFrame12493_eq


end BstLean.Part269.N12493

namespace BstLean.Part269.N12494
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12494 : scalarRow12494.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12494, BstLean.Part268.grid12494, BstLean.Part263.worldGrid]

theorem supplies12494 (j : Fin 43) : Supply 12494 (parameters j)
    (cellLower scalarRow12494.grid (sourceIndex j))
    (cellUpper scalarRow12494.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12494.grid grid_top_bounds12494 j

theorem radii12494 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12494.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12494 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12494 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12494.grid grid_top_bounds12494 j hθ

noncomputable def covarianceInputs12494 :
    BstLean.Part263.CovarianceInputs 12494 scalarRow12494.grid parameters (caps repair12494) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12494 grid_top_bounds12494 repair12494

noncomputable def covarianceEvent12494 : Set (AgFam 12494) :=
  BstLean.Part263.covarianceEvent 12494 scalarRow12494.grid parameters

theorem covarianceEvent12494_measurable : MeasurableSet covarianceEvent12494 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12494_payment :
    (retDist (paperDesignP 12494).toCentres).real
      (agentEv (paperDesignP 12494) covarianceEvent12494)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12494

theorem localCov12494 : BstLean.Part259.LocalCovarianceOn covarianceEvent12494
    (BstLean.Part263.cell scalarRow12494.grid) (caps repair12494) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12494

theorem covarianceGood12494_payment :
    (retDist (paperDesignP 12494).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12494)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12494_payment



end BstLean.Part269.N12494

namespace BstLean.Part269.N12494
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12494}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12494.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12494) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12494).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12494 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12494) (by norm_num) BstLean.Part268.WorldRow12494.worldPackage rfl
    BstLean.Part268.WorldRow12494.product_lower (BstLean.Part268.WorldRow12494.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12494} (hw : c ∈ Hof BstLean.Part268.WorldRow12494.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12494) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12494) (by norm_num) BstLean.Part268.WorldRow12494.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12494} (hw : c ∈ Hof BstLean.Part268.WorldRow12494.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12494) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12494).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12494) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12494_eq : scalarRow12494.targetFrame = BstLean.Part268.agent12494.frame := by
  norm_num [scalarRow12494,BstLean.Part268.agent12494]

noncomputable def frameData12494 : BstLean.Part264b.FrameData 12494 :=
  BstLean.Part269.frameData_from_numerics (n := 12494) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12494.worldPackage rfl BstLean.Part268.WorldRow12494.product_lower (BstLean.Part268.WorldRow12494.producthi.2.trans (by norm_num))
    scalarRow12494 repair12494 covarianceInputs12494 (fun i hi => sourceNumerics12494 hi)
    BstLean.Part268.agent12494.frame targetFrame12494_eq


end BstLean.Part269.N12494
