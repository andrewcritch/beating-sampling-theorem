import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World6Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs6
import BstLean.Part269Rows6
import BstLean.Part269Sources6
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12500
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12500 : scalarRow12500.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12500, BstLean.Part268.grid12500, BstLean.Part263.worldGrid]

theorem supplies12500 (j : Fin 43) : Supply 12500 (parameters j)
    (cellLower scalarRow12500.grid (sourceIndex j))
    (cellUpper scalarRow12500.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12500.grid grid_top_bounds12500 j

theorem radii12500 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12500.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12500 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12500 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12500.grid grid_top_bounds12500 j hθ

noncomputable def covarianceInputs12500 :
    BstLean.Part263.CovarianceInputs 12500 scalarRow12500.grid parameters (caps repair12500) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12500 grid_top_bounds12500 repair12500

noncomputable def covarianceEvent12500 : Set (AgFam 12500) :=
  BstLean.Part263.covarianceEvent 12500 scalarRow12500.grid parameters

theorem covarianceEvent12500_measurable : MeasurableSet covarianceEvent12500 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12500_payment :
    (retDist (paperDesignP 12500).toCentres).real
      (agentEv (paperDesignP 12500) covarianceEvent12500)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12500

theorem localCov12500 : BstLean.Part259.LocalCovarianceOn covarianceEvent12500
    (BstLean.Part263.cell scalarRow12500.grid) (caps repair12500) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12500

theorem covarianceGood12500_payment :
    (retDist (paperDesignP 12500).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12500)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12500_payment



end BstLean.Part269.N12500

namespace BstLean.Part269.N12500
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12500}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12500.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12500) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12500).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12500 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12500) (by norm_num) BstLean.Part268.WorldRow12500.worldPackage rfl
    BstLean.Part268.WorldRow12500.product_lower (BstLean.Part268.WorldRow12500.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12500} (hw : c ∈ Hof BstLean.Part268.WorldRow12500.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12500) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12500) (by norm_num) BstLean.Part268.WorldRow12500.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12500} (hw : c ∈ Hof BstLean.Part268.WorldRow12500.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12500) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12500).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12500) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12500_eq : scalarRow12500.targetFrame = BstLean.Part268.agent12500.frame := by
  norm_num [scalarRow12500,BstLean.Part268.agent12500]

noncomputable def frameData12500 : BstLean.Part264b.FrameData 12500 :=
  BstLean.Part269.frameData_from_numerics (n := 12500) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12500.worldPackage rfl BstLean.Part268.WorldRow12500.product_lower (BstLean.Part268.WorldRow12500.producthi.2.trans (by norm_num))
    scalarRow12500 repair12500 covarianceInputs12500 (fun i hi => sourceNumerics12500 hi)
    BstLean.Part268.agent12500.frame targetFrame12500_eq


end BstLean.Part269.N12500

namespace BstLean.Part269.N12501
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12501 : scalarRow12501.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12501, BstLean.Part268.grid12501, BstLean.Part263.worldGrid]

theorem supplies12501 (j : Fin 43) : Supply 12501 (parameters j)
    (cellLower scalarRow12501.grid (sourceIndex j))
    (cellUpper scalarRow12501.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12501.grid grid_top_bounds12501 j

theorem radii12501 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12501.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12501 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12501 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12501.grid grid_top_bounds12501 j hθ

noncomputable def covarianceInputs12501 :
    BstLean.Part263.CovarianceInputs 12501 scalarRow12501.grid parameters (caps repair12501) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12501 grid_top_bounds12501 repair12501

noncomputable def covarianceEvent12501 : Set (AgFam 12501) :=
  BstLean.Part263.covarianceEvent 12501 scalarRow12501.grid parameters

theorem covarianceEvent12501_measurable : MeasurableSet covarianceEvent12501 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12501_payment :
    (retDist (paperDesignP 12501).toCentres).real
      (agentEv (paperDesignP 12501) covarianceEvent12501)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12501

theorem localCov12501 : BstLean.Part259.LocalCovarianceOn covarianceEvent12501
    (BstLean.Part263.cell scalarRow12501.grid) (caps repair12501) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12501

theorem covarianceGood12501_payment :
    (retDist (paperDesignP 12501).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12501)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12501_payment



end BstLean.Part269.N12501

namespace BstLean.Part269.N12501
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12501}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12501.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12501) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12501).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12501 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12501) (by norm_num) BstLean.Part268.WorldRow12501.worldPackage rfl
    BstLean.Part268.WorldRow12501.product_lower (BstLean.Part268.WorldRow12501.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12501} (hw : c ∈ Hof BstLean.Part268.WorldRow12501.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12501) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12501) (by norm_num) BstLean.Part268.WorldRow12501.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12501} (hw : c ∈ Hof BstLean.Part268.WorldRow12501.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12501) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12501).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12501) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12501_eq : scalarRow12501.targetFrame = BstLean.Part268.agent12501.frame := by
  norm_num [scalarRow12501,BstLean.Part268.agent12501]

noncomputable def frameData12501 : BstLean.Part264b.FrameData 12501 :=
  BstLean.Part269.frameData_from_numerics (n := 12501) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12501.worldPackage rfl BstLean.Part268.WorldRow12501.product_lower (BstLean.Part268.WorldRow12501.producthi.2.trans (by norm_num))
    scalarRow12501 repair12501 covarianceInputs12501 (fun i hi => sourceNumerics12501 hi)
    BstLean.Part268.agent12501.frame targetFrame12501_eq


end BstLean.Part269.N12501

namespace BstLean.Part269.N12502
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12502 : scalarRow12502.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12502, BstLean.Part268.grid12502, BstLean.Part263.worldGrid]

theorem supplies12502 (j : Fin 43) : Supply 12502 (parameters j)
    (cellLower scalarRow12502.grid (sourceIndex j))
    (cellUpper scalarRow12502.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12502.grid grid_top_bounds12502 j

theorem radii12502 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12502.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12502 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12502 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12502.grid grid_top_bounds12502 j hθ

noncomputable def covarianceInputs12502 :
    BstLean.Part263.CovarianceInputs 12502 scalarRow12502.grid parameters (caps repair12502) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12502 grid_top_bounds12502 repair12502

noncomputable def covarianceEvent12502 : Set (AgFam 12502) :=
  BstLean.Part263.covarianceEvent 12502 scalarRow12502.grid parameters

theorem covarianceEvent12502_measurable : MeasurableSet covarianceEvent12502 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12502_payment :
    (retDist (paperDesignP 12502).toCentres).real
      (agentEv (paperDesignP 12502) covarianceEvent12502)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12502

theorem localCov12502 : BstLean.Part259.LocalCovarianceOn covarianceEvent12502
    (BstLean.Part263.cell scalarRow12502.grid) (caps repair12502) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12502

theorem covarianceGood12502_payment :
    (retDist (paperDesignP 12502).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12502)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12502_payment



end BstLean.Part269.N12502

namespace BstLean.Part269.N12502
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12502}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12502.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12502) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12502).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12502 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12502) (by norm_num) BstLean.Part268.WorldRow12502.worldPackage rfl
    BstLean.Part268.WorldRow12502.product_lower (BstLean.Part268.WorldRow12502.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12502} (hw : c ∈ Hof BstLean.Part268.WorldRow12502.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12502) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12502) (by norm_num) BstLean.Part268.WorldRow12502.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12502} (hw : c ∈ Hof BstLean.Part268.WorldRow12502.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12502) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12502).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12502) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12502_eq : scalarRow12502.targetFrame = BstLean.Part268.agent12502.frame := by
  norm_num [scalarRow12502,BstLean.Part268.agent12502]

noncomputable def frameData12502 : BstLean.Part264b.FrameData 12502 :=
  BstLean.Part269.frameData_from_numerics (n := 12502) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12502.worldPackage rfl BstLean.Part268.WorldRow12502.product_lower (BstLean.Part268.WorldRow12502.producthi.2.trans (by norm_num))
    scalarRow12502 repair12502 covarianceInputs12502 (fun i hi => sourceNumerics12502 hi)
    BstLean.Part268.agent12502.frame targetFrame12502_eq


end BstLean.Part269.N12502

namespace BstLean.Part269.N12503
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12503 : scalarRow12503.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12503, BstLean.Part268.grid12503, BstLean.Part263.worldGrid]

theorem supplies12503 (j : Fin 43) : Supply 12503 (parameters j)
    (cellLower scalarRow12503.grid (sourceIndex j))
    (cellUpper scalarRow12503.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12503.grid grid_top_bounds12503 j

theorem radii12503 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12503.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12503 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12503 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12503.grid grid_top_bounds12503 j hθ

noncomputable def covarianceInputs12503 :
    BstLean.Part263.CovarianceInputs 12503 scalarRow12503.grid parameters (caps repair12503) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12503 grid_top_bounds12503 repair12503

noncomputable def covarianceEvent12503 : Set (AgFam 12503) :=
  BstLean.Part263.covarianceEvent 12503 scalarRow12503.grid parameters

theorem covarianceEvent12503_measurable : MeasurableSet covarianceEvent12503 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12503_payment :
    (retDist (paperDesignP 12503).toCentres).real
      (agentEv (paperDesignP 12503) covarianceEvent12503)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12503

theorem localCov12503 : BstLean.Part259.LocalCovarianceOn covarianceEvent12503
    (BstLean.Part263.cell scalarRow12503.grid) (caps repair12503) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12503

theorem covarianceGood12503_payment :
    (retDist (paperDesignP 12503).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12503)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12503_payment



end BstLean.Part269.N12503

namespace BstLean.Part269.N12503
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12503}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12503.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12503) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12503).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12503 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12503) (by norm_num) BstLean.Part268.WorldRow12503.worldPackage rfl
    BstLean.Part268.WorldRow12503.product_lower (BstLean.Part268.WorldRow12503.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12503} (hw : c ∈ Hof BstLean.Part268.WorldRow12503.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12503) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12503) (by norm_num) BstLean.Part268.WorldRow12503.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12503} (hw : c ∈ Hof BstLean.Part268.WorldRow12503.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12503) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12503).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12503) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12503_eq : scalarRow12503.targetFrame = BstLean.Part268.agent12503.frame := by
  norm_num [scalarRow12503,BstLean.Part268.agent12503]

noncomputable def frameData12503 : BstLean.Part264b.FrameData 12503 :=
  BstLean.Part269.frameData_from_numerics (n := 12503) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12503.worldPackage rfl BstLean.Part268.WorldRow12503.product_lower (BstLean.Part268.WorldRow12503.producthi.2.trans (by norm_num))
    scalarRow12503 repair12503 covarianceInputs12503 (fun i hi => sourceNumerics12503 hi)
    BstLean.Part268.agent12503.frame targetFrame12503_eq


end BstLean.Part269.N12503

namespace BstLean.Part269.N12504
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12504 : scalarRow12504.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12504, BstLean.Part268.grid12504, BstLean.Part263.worldGrid]

theorem supplies12504 (j : Fin 43) : Supply 12504 (parameters j)
    (cellLower scalarRow12504.grid (sourceIndex j))
    (cellUpper scalarRow12504.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12504.grid grid_top_bounds12504 j

theorem radii12504 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12504.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12504 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12504 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12504.grid grid_top_bounds12504 j hθ

noncomputable def covarianceInputs12504 :
    BstLean.Part263.CovarianceInputs 12504 scalarRow12504.grid parameters (caps repair12504) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12504 grid_top_bounds12504 repair12504

noncomputable def covarianceEvent12504 : Set (AgFam 12504) :=
  BstLean.Part263.covarianceEvent 12504 scalarRow12504.grid parameters

theorem covarianceEvent12504_measurable : MeasurableSet covarianceEvent12504 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12504_payment :
    (retDist (paperDesignP 12504).toCentres).real
      (agentEv (paperDesignP 12504) covarianceEvent12504)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12504

theorem localCov12504 : BstLean.Part259.LocalCovarianceOn covarianceEvent12504
    (BstLean.Part263.cell scalarRow12504.grid) (caps repair12504) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12504

theorem covarianceGood12504_payment :
    (retDist (paperDesignP 12504).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12504)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12504_payment



end BstLean.Part269.N12504

namespace BstLean.Part269.N12504
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12504}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12504.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12504) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12504).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12504 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12504) (by norm_num) BstLean.Part268.WorldRow12504.worldPackage rfl
    BstLean.Part268.WorldRow12504.product_lower (BstLean.Part268.WorldRow12504.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12504} (hw : c ∈ Hof BstLean.Part268.WorldRow12504.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12504) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12504) (by norm_num) BstLean.Part268.WorldRow12504.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12504} (hw : c ∈ Hof BstLean.Part268.WorldRow12504.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12504) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12504).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12504) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12504_eq : scalarRow12504.targetFrame = BstLean.Part268.agent12504.frame := by
  norm_num [scalarRow12504,BstLean.Part268.agent12504]

noncomputable def frameData12504 : BstLean.Part264b.FrameData 12504 :=
  BstLean.Part269.frameData_from_numerics (n := 12504) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12504.worldPackage rfl BstLean.Part268.WorldRow12504.product_lower (BstLean.Part268.WorldRow12504.producthi.2.trans (by norm_num))
    scalarRow12504 repair12504 covarianceInputs12504 (fun i hi => sourceNumerics12504 hi)
    BstLean.Part268.agent12504.frame targetFrame12504_eq


end BstLean.Part269.N12504
