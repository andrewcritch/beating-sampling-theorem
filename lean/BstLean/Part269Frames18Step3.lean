import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World18Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs18
import BstLean.Part269Rows18
import BstLean.Part269Sources18
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12815
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12815 : scalarRow12815.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12815, BstLean.Part268.grid12815, BstLean.Part263.worldGrid]

theorem supplies12815 (j : Fin 43) : Supply 12815 (parameters j)
    (cellLower scalarRow12815.grid (sourceIndex j))
    (cellUpper scalarRow12815.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12815.grid grid_top_bounds12815 j

theorem radii12815 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12815.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12815 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12815 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12815.grid grid_top_bounds12815 j hθ

noncomputable def covarianceInputs12815 :
    BstLean.Part263.CovarianceInputs 12815 scalarRow12815.grid parameters (caps repair12815) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12815 grid_top_bounds12815 repair12815

noncomputable def covarianceEvent12815 : Set (AgFam 12815) :=
  BstLean.Part263.covarianceEvent 12815 scalarRow12815.grid parameters

theorem covarianceEvent12815_measurable : MeasurableSet covarianceEvent12815 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12815_payment :
    (retDist (paperDesignP 12815).toCentres).real
      (agentEv (paperDesignP 12815) covarianceEvent12815)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12815

theorem localCov12815 : BstLean.Part259.LocalCovarianceOn covarianceEvent12815
    (BstLean.Part263.cell scalarRow12815.grid) (caps repair12815) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12815

theorem covarianceGood12815_payment :
    (retDist (paperDesignP 12815).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12815)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12815_payment



end BstLean.Part269.N12815

namespace BstLean.Part269.N12815
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12815}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12815.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12815) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12815).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12815 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12815) (by norm_num) BstLean.Part268.WorldRow12815.worldPackage rfl
    BstLean.Part268.WorldRow12815.product_lower (BstLean.Part268.WorldRow12815.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12815} (hw : c ∈ Hof BstLean.Part268.WorldRow12815.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12815) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12815) (by norm_num) BstLean.Part268.WorldRow12815.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12815} (hw : c ∈ Hof BstLean.Part268.WorldRow12815.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12815) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12815).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12815) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12815_eq : scalarRow12815.targetFrame = BstLean.Part268.agent12815.frame := by
  norm_num [scalarRow12815,BstLean.Part268.agent12815]

noncomputable def frameData12815 : BstLean.Part264b.FrameData 12815 :=
  BstLean.Part269.frameData_from_numerics (n := 12815) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12815.worldPackage rfl BstLean.Part268.WorldRow12815.product_lower (BstLean.Part268.WorldRow12815.producthi.2.trans (by norm_num))
    scalarRow12815 repair12815 covarianceInputs12815 (fun i hi => sourceNumerics12815 hi)
    BstLean.Part268.agent12815.frame targetFrame12815_eq


end BstLean.Part269.N12815

namespace BstLean.Part269.N12816
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12816 : scalarRow12816.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12816, BstLean.Part268.grid12816, BstLean.Part263.worldGrid]

theorem supplies12816 (j : Fin 43) : Supply 12816 (parameters j)
    (cellLower scalarRow12816.grid (sourceIndex j))
    (cellUpper scalarRow12816.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12816.grid grid_top_bounds12816 j

theorem radii12816 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12816.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12816 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12816 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12816.grid grid_top_bounds12816 j hθ

noncomputable def covarianceInputs12816 :
    BstLean.Part263.CovarianceInputs 12816 scalarRow12816.grid parameters (caps repair12816) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12816 grid_top_bounds12816 repair12816

noncomputable def covarianceEvent12816 : Set (AgFam 12816) :=
  BstLean.Part263.covarianceEvent 12816 scalarRow12816.grid parameters

theorem covarianceEvent12816_measurable : MeasurableSet covarianceEvent12816 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12816_payment :
    (retDist (paperDesignP 12816).toCentres).real
      (agentEv (paperDesignP 12816) covarianceEvent12816)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12816

theorem localCov12816 : BstLean.Part259.LocalCovarianceOn covarianceEvent12816
    (BstLean.Part263.cell scalarRow12816.grid) (caps repair12816) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12816

theorem covarianceGood12816_payment :
    (retDist (paperDesignP 12816).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12816)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12816_payment



end BstLean.Part269.N12816

namespace BstLean.Part269.N12816
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12816}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12816.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12816) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12816).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12816 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12816) (by norm_num) BstLean.Part268.WorldRow12816.worldPackage rfl
    BstLean.Part268.WorldRow12816.product_lower (BstLean.Part268.WorldRow12816.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12816} (hw : c ∈ Hof BstLean.Part268.WorldRow12816.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12816) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12816) (by norm_num) BstLean.Part268.WorldRow12816.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12816} (hw : c ∈ Hof BstLean.Part268.WorldRow12816.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12816) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12816).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12816) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12816_eq : scalarRow12816.targetFrame = BstLean.Part268.agent12816.frame := by
  norm_num [scalarRow12816,BstLean.Part268.agent12816]

noncomputable def frameData12816 : BstLean.Part264b.FrameData 12816 :=
  BstLean.Part269.frameData_from_numerics (n := 12816) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12816.worldPackage rfl BstLean.Part268.WorldRow12816.product_lower (BstLean.Part268.WorldRow12816.producthi.2.trans (by norm_num))
    scalarRow12816 repair12816 covarianceInputs12816 (fun i hi => sourceNumerics12816 hi)
    BstLean.Part268.agent12816.frame targetFrame12816_eq


end BstLean.Part269.N12816

namespace BstLean.Part269.N12817
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12817 : scalarRow12817.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12817, BstLean.Part268.grid12817, BstLean.Part263.worldGrid]

theorem supplies12817 (j : Fin 43) : Supply 12817 (parameters j)
    (cellLower scalarRow12817.grid (sourceIndex j))
    (cellUpper scalarRow12817.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12817.grid grid_top_bounds12817 j

theorem radii12817 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12817.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12817 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12817 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12817.grid grid_top_bounds12817 j hθ

noncomputable def covarianceInputs12817 :
    BstLean.Part263.CovarianceInputs 12817 scalarRow12817.grid parameters (caps repair12817) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12817 grid_top_bounds12817 repair12817

noncomputable def covarianceEvent12817 : Set (AgFam 12817) :=
  BstLean.Part263.covarianceEvent 12817 scalarRow12817.grid parameters

theorem covarianceEvent12817_measurable : MeasurableSet covarianceEvent12817 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12817_payment :
    (retDist (paperDesignP 12817).toCentres).real
      (agentEv (paperDesignP 12817) covarianceEvent12817)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12817

theorem localCov12817 : BstLean.Part259.LocalCovarianceOn covarianceEvent12817
    (BstLean.Part263.cell scalarRow12817.grid) (caps repair12817) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12817

theorem covarianceGood12817_payment :
    (retDist (paperDesignP 12817).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12817)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12817_payment



end BstLean.Part269.N12817

namespace BstLean.Part269.N12817
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12817}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12817.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12817) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12817).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12817 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12817) (by norm_num) BstLean.Part268.WorldRow12817.worldPackage rfl
    BstLean.Part268.WorldRow12817.product_lower (BstLean.Part268.WorldRow12817.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12817} (hw : c ∈ Hof BstLean.Part268.WorldRow12817.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12817) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12817) (by norm_num) BstLean.Part268.WorldRow12817.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12817} (hw : c ∈ Hof BstLean.Part268.WorldRow12817.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12817) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12817).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12817) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12817_eq : scalarRow12817.targetFrame = BstLean.Part268.agent12817.frame := by
  norm_num [scalarRow12817,BstLean.Part268.agent12817]

noncomputable def frameData12817 : BstLean.Part264b.FrameData 12817 :=
  BstLean.Part269.frameData_from_numerics (n := 12817) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12817.worldPackage rfl BstLean.Part268.WorldRow12817.product_lower (BstLean.Part268.WorldRow12817.producthi.2.trans (by norm_num))
    scalarRow12817 repair12817 covarianceInputs12817 (fun i hi => sourceNumerics12817 hi)
    BstLean.Part268.agent12817.frame targetFrame12817_eq


end BstLean.Part269.N12817

namespace BstLean.Part269.N12818
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12818 : scalarRow12818.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12818, BstLean.Part268.grid12818, BstLean.Part263.worldGrid]

theorem supplies12818 (j : Fin 43) : Supply 12818 (parameters j)
    (cellLower scalarRow12818.grid (sourceIndex j))
    (cellUpper scalarRow12818.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12818.grid grid_top_bounds12818 j

theorem radii12818 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12818.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12818 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12818 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12818.grid grid_top_bounds12818 j hθ

noncomputable def covarianceInputs12818 :
    BstLean.Part263.CovarianceInputs 12818 scalarRow12818.grid parameters (caps repair12818) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12818 grid_top_bounds12818 repair12818

noncomputable def covarianceEvent12818 : Set (AgFam 12818) :=
  BstLean.Part263.covarianceEvent 12818 scalarRow12818.grid parameters

theorem covarianceEvent12818_measurable : MeasurableSet covarianceEvent12818 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12818_payment :
    (retDist (paperDesignP 12818).toCentres).real
      (agentEv (paperDesignP 12818) covarianceEvent12818)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12818

theorem localCov12818 : BstLean.Part259.LocalCovarianceOn covarianceEvent12818
    (BstLean.Part263.cell scalarRow12818.grid) (caps repair12818) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12818

theorem covarianceGood12818_payment :
    (retDist (paperDesignP 12818).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12818)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12818_payment



end BstLean.Part269.N12818

namespace BstLean.Part269.N12818
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12818}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12818.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12818) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12818).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12818 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12818) (by norm_num) BstLean.Part268.WorldRow12818.worldPackage rfl
    BstLean.Part268.WorldRow12818.product_lower (BstLean.Part268.WorldRow12818.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12818} (hw : c ∈ Hof BstLean.Part268.WorldRow12818.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12818) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12818) (by norm_num) BstLean.Part268.WorldRow12818.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12818} (hw : c ∈ Hof BstLean.Part268.WorldRow12818.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12818) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12818).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12818) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12818_eq : scalarRow12818.targetFrame = BstLean.Part268.agent12818.frame := by
  norm_num [scalarRow12818,BstLean.Part268.agent12818]

noncomputable def frameData12818 : BstLean.Part264b.FrameData 12818 :=
  BstLean.Part269.frameData_from_numerics (n := 12818) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12818.worldPackage rfl BstLean.Part268.WorldRow12818.product_lower (BstLean.Part268.WorldRow12818.producthi.2.trans (by norm_num))
    scalarRow12818 repair12818 covarianceInputs12818 (fun i hi => sourceNumerics12818 hi)
    BstLean.Part268.agent12818.frame targetFrame12818_eq


end BstLean.Part269.N12818

namespace BstLean.Part269.N12819
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12819 : scalarRow12819.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12819, BstLean.Part268.grid12819, BstLean.Part263.worldGrid]

theorem supplies12819 (j : Fin 43) : Supply 12819 (parameters j)
    (cellLower scalarRow12819.grid (sourceIndex j))
    (cellUpper scalarRow12819.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12819.grid grid_top_bounds12819 j

theorem radii12819 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12819.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12819 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12819 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12819.grid grid_top_bounds12819 j hθ

noncomputable def covarianceInputs12819 :
    BstLean.Part263.CovarianceInputs 12819 scalarRow12819.grid parameters (caps repair12819) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12819 grid_top_bounds12819 repair12819

noncomputable def covarianceEvent12819 : Set (AgFam 12819) :=
  BstLean.Part263.covarianceEvent 12819 scalarRow12819.grid parameters

theorem covarianceEvent12819_measurable : MeasurableSet covarianceEvent12819 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12819_payment :
    (retDist (paperDesignP 12819).toCentres).real
      (agentEv (paperDesignP 12819) covarianceEvent12819)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12819

theorem localCov12819 : BstLean.Part259.LocalCovarianceOn covarianceEvent12819
    (BstLean.Part263.cell scalarRow12819.grid) (caps repair12819) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12819

theorem covarianceGood12819_payment :
    (retDist (paperDesignP 12819).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12819)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12819_payment



end BstLean.Part269.N12819

namespace BstLean.Part269.N12819
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12819}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12819.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12819) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12819).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12819 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12819) (by norm_num) BstLean.Part268.WorldRow12819.worldPackage rfl
    BstLean.Part268.WorldRow12819.product_lower (BstLean.Part268.WorldRow12819.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12819} (hw : c ∈ Hof BstLean.Part268.WorldRow12819.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12819) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12819) (by norm_num) BstLean.Part268.WorldRow12819.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12819} (hw : c ∈ Hof BstLean.Part268.WorldRow12819.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12819) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12819).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12819) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12819_eq : scalarRow12819.targetFrame = BstLean.Part268.agent12819.frame := by
  norm_num [scalarRow12819,BstLean.Part268.agent12819]

noncomputable def frameData12819 : BstLean.Part264b.FrameData 12819 :=
  BstLean.Part269.frameData_from_numerics (n := 12819) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12819.worldPackage rfl BstLean.Part268.WorldRow12819.product_lower (BstLean.Part268.WorldRow12819.producthi.2.trans (by norm_num))
    scalarRow12819 repair12819 covarianceInputs12819 (fun i hi => sourceNumerics12819 hi)
    BstLean.Part268.agent12819.frame targetFrame12819_eq


end BstLean.Part269.N12819
