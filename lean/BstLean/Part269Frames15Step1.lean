import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World15Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs15
import BstLean.Part269Rows15
import BstLean.Part269Sources15
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12730
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12730 : scalarRow12730.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12730, BstLean.Part268.grid12730, BstLean.Part263.worldGrid]

theorem supplies12730 (j : Fin 43) : Supply 12730 (parameters j)
    (cellLower scalarRow12730.grid (sourceIndex j))
    (cellUpper scalarRow12730.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12730.grid grid_top_bounds12730 j

theorem radii12730 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12730.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12730 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12730 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12730.grid grid_top_bounds12730 j hθ

noncomputable def covarianceInputs12730 :
    BstLean.Part263.CovarianceInputs 12730 scalarRow12730.grid parameters (caps repair12730) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12730 grid_top_bounds12730 repair12730

noncomputable def covarianceEvent12730 : Set (AgFam 12730) :=
  BstLean.Part263.covarianceEvent 12730 scalarRow12730.grid parameters

theorem covarianceEvent12730_measurable : MeasurableSet covarianceEvent12730 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12730_payment :
    (retDist (paperDesignP 12730).toCentres).real
      (agentEv (paperDesignP 12730) covarianceEvent12730)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12730

theorem localCov12730 : BstLean.Part259.LocalCovarianceOn covarianceEvent12730
    (BstLean.Part263.cell scalarRow12730.grid) (caps repair12730) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12730

theorem covarianceGood12730_payment :
    (retDist (paperDesignP 12730).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12730)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12730_payment



end BstLean.Part269.N12730

namespace BstLean.Part269.N12730
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12730}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12730.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12730) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12730).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12730 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12730) (by norm_num) BstLean.Part268.WorldRow12730.worldPackage rfl
    BstLean.Part268.WorldRow12730.product_lower (BstLean.Part268.WorldRow12730.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12730} (hw : c ∈ Hof BstLean.Part268.WorldRow12730.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12730) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12730) (by norm_num) BstLean.Part268.WorldRow12730.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12730} (hw : c ∈ Hof BstLean.Part268.WorldRow12730.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12730) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12730).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12730) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12730_eq : scalarRow12730.targetFrame = BstLean.Part268.agent12730.frame := by
  norm_num [scalarRow12730,BstLean.Part268.agent12730]

noncomputable def frameData12730 : BstLean.Part264b.FrameData 12730 :=
  BstLean.Part269.frameData_from_numerics (n := 12730) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12730.worldPackage rfl BstLean.Part268.WorldRow12730.product_lower (BstLean.Part268.WorldRow12730.producthi.2.trans (by norm_num))
    scalarRow12730 repair12730 covarianceInputs12730 (fun i hi => sourceNumerics12730 hi)
    BstLean.Part268.agent12730.frame targetFrame12730_eq


end BstLean.Part269.N12730

namespace BstLean.Part269.N12731
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12731 : scalarRow12731.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12731, BstLean.Part268.grid12731, BstLean.Part263.worldGrid]

theorem supplies12731 (j : Fin 43) : Supply 12731 (parameters j)
    (cellLower scalarRow12731.grid (sourceIndex j))
    (cellUpper scalarRow12731.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12731.grid grid_top_bounds12731 j

theorem radii12731 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12731.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12731 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12731 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12731.grid grid_top_bounds12731 j hθ

noncomputable def covarianceInputs12731 :
    BstLean.Part263.CovarianceInputs 12731 scalarRow12731.grid parameters (caps repair12731) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12731 grid_top_bounds12731 repair12731

noncomputable def covarianceEvent12731 : Set (AgFam 12731) :=
  BstLean.Part263.covarianceEvent 12731 scalarRow12731.grid parameters

theorem covarianceEvent12731_measurable : MeasurableSet covarianceEvent12731 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12731_payment :
    (retDist (paperDesignP 12731).toCentres).real
      (agentEv (paperDesignP 12731) covarianceEvent12731)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12731

theorem localCov12731 : BstLean.Part259.LocalCovarianceOn covarianceEvent12731
    (BstLean.Part263.cell scalarRow12731.grid) (caps repair12731) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12731

theorem covarianceGood12731_payment :
    (retDist (paperDesignP 12731).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12731)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12731_payment



end BstLean.Part269.N12731

namespace BstLean.Part269.N12731
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12731}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12731.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12731) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12731).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12731 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12731) (by norm_num) BstLean.Part268.WorldRow12731.worldPackage rfl
    BstLean.Part268.WorldRow12731.product_lower (BstLean.Part268.WorldRow12731.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12731} (hw : c ∈ Hof BstLean.Part268.WorldRow12731.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12731) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12731) (by norm_num) BstLean.Part268.WorldRow12731.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12731} (hw : c ∈ Hof BstLean.Part268.WorldRow12731.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12731) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12731).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12731) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12731_eq : scalarRow12731.targetFrame = BstLean.Part268.agent12731.frame := by
  norm_num [scalarRow12731,BstLean.Part268.agent12731]

noncomputable def frameData12731 : BstLean.Part264b.FrameData 12731 :=
  BstLean.Part269.frameData_from_numerics (n := 12731) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12731.worldPackage rfl BstLean.Part268.WorldRow12731.product_lower (BstLean.Part268.WorldRow12731.producthi.2.trans (by norm_num))
    scalarRow12731 repair12731 covarianceInputs12731 (fun i hi => sourceNumerics12731 hi)
    BstLean.Part268.agent12731.frame targetFrame12731_eq


end BstLean.Part269.N12731

namespace BstLean.Part269.N12732
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12732 : scalarRow12732.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12732, BstLean.Part268.grid12732, BstLean.Part263.worldGrid]

theorem supplies12732 (j : Fin 43) : Supply 12732 (parameters j)
    (cellLower scalarRow12732.grid (sourceIndex j))
    (cellUpper scalarRow12732.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12732.grid grid_top_bounds12732 j

theorem radii12732 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12732.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12732 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12732 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12732.grid grid_top_bounds12732 j hθ

noncomputable def covarianceInputs12732 :
    BstLean.Part263.CovarianceInputs 12732 scalarRow12732.grid parameters (caps repair12732) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12732 grid_top_bounds12732 repair12732

noncomputable def covarianceEvent12732 : Set (AgFam 12732) :=
  BstLean.Part263.covarianceEvent 12732 scalarRow12732.grid parameters

theorem covarianceEvent12732_measurable : MeasurableSet covarianceEvent12732 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12732_payment :
    (retDist (paperDesignP 12732).toCentres).real
      (agentEv (paperDesignP 12732) covarianceEvent12732)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12732

theorem localCov12732 : BstLean.Part259.LocalCovarianceOn covarianceEvent12732
    (BstLean.Part263.cell scalarRow12732.grid) (caps repair12732) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12732

theorem covarianceGood12732_payment :
    (retDist (paperDesignP 12732).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12732)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12732_payment



end BstLean.Part269.N12732

namespace BstLean.Part269.N12732
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12732}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12732.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12732) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12732).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12732 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12732) (by norm_num) BstLean.Part268.WorldRow12732.worldPackage rfl
    BstLean.Part268.WorldRow12732.product_lower (BstLean.Part268.WorldRow12732.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12732} (hw : c ∈ Hof BstLean.Part268.WorldRow12732.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12732) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12732) (by norm_num) BstLean.Part268.WorldRow12732.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12732} (hw : c ∈ Hof BstLean.Part268.WorldRow12732.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12732) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12732).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12732) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12732_eq : scalarRow12732.targetFrame = BstLean.Part268.agent12732.frame := by
  norm_num [scalarRow12732,BstLean.Part268.agent12732]

noncomputable def frameData12732 : BstLean.Part264b.FrameData 12732 :=
  BstLean.Part269.frameData_from_numerics (n := 12732) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12732.worldPackage rfl BstLean.Part268.WorldRow12732.product_lower (BstLean.Part268.WorldRow12732.producthi.2.trans (by norm_num))
    scalarRow12732 repair12732 covarianceInputs12732 (fun i hi => sourceNumerics12732 hi)
    BstLean.Part268.agent12732.frame targetFrame12732_eq


end BstLean.Part269.N12732

namespace BstLean.Part269.N12733
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12733 : scalarRow12733.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12733, BstLean.Part268.grid12733, BstLean.Part263.worldGrid]

theorem supplies12733 (j : Fin 43) : Supply 12733 (parameters j)
    (cellLower scalarRow12733.grid (sourceIndex j))
    (cellUpper scalarRow12733.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12733.grid grid_top_bounds12733 j

theorem radii12733 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12733.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12733 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12733 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12733.grid grid_top_bounds12733 j hθ

noncomputable def covarianceInputs12733 :
    BstLean.Part263.CovarianceInputs 12733 scalarRow12733.grid parameters (caps repair12733) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12733 grid_top_bounds12733 repair12733

noncomputable def covarianceEvent12733 : Set (AgFam 12733) :=
  BstLean.Part263.covarianceEvent 12733 scalarRow12733.grid parameters

theorem covarianceEvent12733_measurable : MeasurableSet covarianceEvent12733 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12733_payment :
    (retDist (paperDesignP 12733).toCentres).real
      (agentEv (paperDesignP 12733) covarianceEvent12733)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12733

theorem localCov12733 : BstLean.Part259.LocalCovarianceOn covarianceEvent12733
    (BstLean.Part263.cell scalarRow12733.grid) (caps repair12733) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12733

theorem covarianceGood12733_payment :
    (retDist (paperDesignP 12733).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12733)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12733_payment



end BstLean.Part269.N12733

namespace BstLean.Part269.N12733
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12733}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12733.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12733) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12733).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12733 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12733) (by norm_num) BstLean.Part268.WorldRow12733.worldPackage rfl
    BstLean.Part268.WorldRow12733.product_lower (BstLean.Part268.WorldRow12733.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12733} (hw : c ∈ Hof BstLean.Part268.WorldRow12733.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12733) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12733) (by norm_num) BstLean.Part268.WorldRow12733.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12733} (hw : c ∈ Hof BstLean.Part268.WorldRow12733.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12733) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12733).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12733) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12733_eq : scalarRow12733.targetFrame = BstLean.Part268.agent12733.frame := by
  norm_num [scalarRow12733,BstLean.Part268.agent12733]

noncomputable def frameData12733 : BstLean.Part264b.FrameData 12733 :=
  BstLean.Part269.frameData_from_numerics (n := 12733) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12733.worldPackage rfl BstLean.Part268.WorldRow12733.product_lower (BstLean.Part268.WorldRow12733.producthi.2.trans (by norm_num))
    scalarRow12733 repair12733 covarianceInputs12733 (fun i hi => sourceNumerics12733 hi)
    BstLean.Part268.agent12733.frame targetFrame12733_eq


end BstLean.Part269.N12733

namespace BstLean.Part269.N12734
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12734 : scalarRow12734.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12734, BstLean.Part268.grid12734, BstLean.Part263.worldGrid]

theorem supplies12734 (j : Fin 43) : Supply 12734 (parameters j)
    (cellLower scalarRow12734.grid (sourceIndex j))
    (cellUpper scalarRow12734.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12734.grid grid_top_bounds12734 j

theorem radii12734 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12734.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12734 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12734 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12734.grid grid_top_bounds12734 j hθ

noncomputable def covarianceInputs12734 :
    BstLean.Part263.CovarianceInputs 12734 scalarRow12734.grid parameters (caps repair12734) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12734 grid_top_bounds12734 repair12734

noncomputable def covarianceEvent12734 : Set (AgFam 12734) :=
  BstLean.Part263.covarianceEvent 12734 scalarRow12734.grid parameters

theorem covarianceEvent12734_measurable : MeasurableSet covarianceEvent12734 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12734_payment :
    (retDist (paperDesignP 12734).toCentres).real
      (agentEv (paperDesignP 12734) covarianceEvent12734)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12734

theorem localCov12734 : BstLean.Part259.LocalCovarianceOn covarianceEvent12734
    (BstLean.Part263.cell scalarRow12734.grid) (caps repair12734) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12734

theorem covarianceGood12734_payment :
    (retDist (paperDesignP 12734).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12734)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12734_payment



end BstLean.Part269.N12734

namespace BstLean.Part269.N12734
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12734}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12734.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12734) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12734).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12734 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12734) (by norm_num) BstLean.Part268.WorldRow12734.worldPackage rfl
    BstLean.Part268.WorldRow12734.product_lower (BstLean.Part268.WorldRow12734.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12734} (hw : c ∈ Hof BstLean.Part268.WorldRow12734.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12734) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12734) (by norm_num) BstLean.Part268.WorldRow12734.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12734} (hw : c ∈ Hof BstLean.Part268.WorldRow12734.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12734) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12734).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12734) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12734_eq : scalarRow12734.targetFrame = BstLean.Part268.agent12734.frame := by
  norm_num [scalarRow12734,BstLean.Part268.agent12734]

noncomputable def frameData12734 : BstLean.Part264b.FrameData 12734 :=
  BstLean.Part269.frameData_from_numerics (n := 12734) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12734.worldPackage rfl BstLean.Part268.WorldRow12734.product_lower (BstLean.Part268.WorldRow12734.producthi.2.trans (by norm_num))
    scalarRow12734 repair12734 covarianceInputs12734 (fun i hi => sourceNumerics12734 hi)
    BstLean.Part268.agent12734.frame targetFrame12734_eq


end BstLean.Part269.N12734
