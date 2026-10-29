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

namespace BstLean.Part269.N12805
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12805 : scalarRow12805.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12805, BstLean.Part268.grid12805, BstLean.Part263.worldGrid]

theorem supplies12805 (j : Fin 43) : Supply 12805 (parameters j)
    (cellLower scalarRow12805.grid (sourceIndex j))
    (cellUpper scalarRow12805.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12805.grid grid_top_bounds12805 j

theorem radii12805 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12805.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12805 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12805 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12805.grid grid_top_bounds12805 j hθ

noncomputable def covarianceInputs12805 :
    BstLean.Part263.CovarianceInputs 12805 scalarRow12805.grid parameters (caps repair12805) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12805 grid_top_bounds12805 repair12805

noncomputable def covarianceEvent12805 : Set (AgFam 12805) :=
  BstLean.Part263.covarianceEvent 12805 scalarRow12805.grid parameters

theorem covarianceEvent12805_measurable : MeasurableSet covarianceEvent12805 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12805_payment :
    (retDist (paperDesignP 12805).toCentres).real
      (agentEv (paperDesignP 12805) covarianceEvent12805)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12805

theorem localCov12805 : BstLean.Part259.LocalCovarianceOn covarianceEvent12805
    (BstLean.Part263.cell scalarRow12805.grid) (caps repair12805) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12805

theorem covarianceGood12805_payment :
    (retDist (paperDesignP 12805).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12805)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12805_payment



end BstLean.Part269.N12805

namespace BstLean.Part269.N12805
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12805}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12805.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12805) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12805).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12805 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12805) (by norm_num) BstLean.Part268.WorldRow12805.worldPackage rfl
    BstLean.Part268.WorldRow12805.product_lower (BstLean.Part268.WorldRow12805.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12805} (hw : c ∈ Hof BstLean.Part268.WorldRow12805.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12805) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12805) (by norm_num) BstLean.Part268.WorldRow12805.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12805} (hw : c ∈ Hof BstLean.Part268.WorldRow12805.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12805) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12805).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12805) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12805_eq : scalarRow12805.targetFrame = BstLean.Part268.agent12805.frame := by
  norm_num [scalarRow12805,BstLean.Part268.agent12805]

noncomputable def frameData12805 : BstLean.Part264b.FrameData 12805 :=
  BstLean.Part269.frameData_from_numerics (n := 12805) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12805.worldPackage rfl BstLean.Part268.WorldRow12805.product_lower (BstLean.Part268.WorldRow12805.producthi.2.trans (by norm_num))
    scalarRow12805 repair12805 covarianceInputs12805 (fun i hi => sourceNumerics12805 hi)
    BstLean.Part268.agent12805.frame targetFrame12805_eq


end BstLean.Part269.N12805

namespace BstLean.Part269.N12806
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12806 : scalarRow12806.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12806, BstLean.Part268.grid12806, BstLean.Part263.worldGrid]

theorem supplies12806 (j : Fin 43) : Supply 12806 (parameters j)
    (cellLower scalarRow12806.grid (sourceIndex j))
    (cellUpper scalarRow12806.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12806.grid grid_top_bounds12806 j

theorem radii12806 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12806.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12806 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12806 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12806.grid grid_top_bounds12806 j hθ

noncomputable def covarianceInputs12806 :
    BstLean.Part263.CovarianceInputs 12806 scalarRow12806.grid parameters (caps repair12806) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12806 grid_top_bounds12806 repair12806

noncomputable def covarianceEvent12806 : Set (AgFam 12806) :=
  BstLean.Part263.covarianceEvent 12806 scalarRow12806.grid parameters

theorem covarianceEvent12806_measurable : MeasurableSet covarianceEvent12806 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12806_payment :
    (retDist (paperDesignP 12806).toCentres).real
      (agentEv (paperDesignP 12806) covarianceEvent12806)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12806

theorem localCov12806 : BstLean.Part259.LocalCovarianceOn covarianceEvent12806
    (BstLean.Part263.cell scalarRow12806.grid) (caps repair12806) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12806

theorem covarianceGood12806_payment :
    (retDist (paperDesignP 12806).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12806)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12806_payment



end BstLean.Part269.N12806

namespace BstLean.Part269.N12806
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12806}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12806.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12806) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12806).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12806 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12806) (by norm_num) BstLean.Part268.WorldRow12806.worldPackage rfl
    BstLean.Part268.WorldRow12806.product_lower (BstLean.Part268.WorldRow12806.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12806} (hw : c ∈ Hof BstLean.Part268.WorldRow12806.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12806) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12806) (by norm_num) BstLean.Part268.WorldRow12806.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12806} (hw : c ∈ Hof BstLean.Part268.WorldRow12806.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12806) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12806).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12806) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12806_eq : scalarRow12806.targetFrame = BstLean.Part268.agent12806.frame := by
  norm_num [scalarRow12806,BstLean.Part268.agent12806]

noncomputable def frameData12806 : BstLean.Part264b.FrameData 12806 :=
  BstLean.Part269.frameData_from_numerics (n := 12806) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12806.worldPackage rfl BstLean.Part268.WorldRow12806.product_lower (BstLean.Part268.WorldRow12806.producthi.2.trans (by norm_num))
    scalarRow12806 repair12806 covarianceInputs12806 (fun i hi => sourceNumerics12806 hi)
    BstLean.Part268.agent12806.frame targetFrame12806_eq


end BstLean.Part269.N12806

namespace BstLean.Part269.N12807
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12807 : scalarRow12807.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12807, BstLean.Part268.grid12807, BstLean.Part263.worldGrid]

theorem supplies12807 (j : Fin 43) : Supply 12807 (parameters j)
    (cellLower scalarRow12807.grid (sourceIndex j))
    (cellUpper scalarRow12807.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12807.grid grid_top_bounds12807 j

theorem radii12807 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12807.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12807 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12807 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12807.grid grid_top_bounds12807 j hθ

noncomputable def covarianceInputs12807 :
    BstLean.Part263.CovarianceInputs 12807 scalarRow12807.grid parameters (caps repair12807) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12807 grid_top_bounds12807 repair12807

noncomputable def covarianceEvent12807 : Set (AgFam 12807) :=
  BstLean.Part263.covarianceEvent 12807 scalarRow12807.grid parameters

theorem covarianceEvent12807_measurable : MeasurableSet covarianceEvent12807 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12807_payment :
    (retDist (paperDesignP 12807).toCentres).real
      (agentEv (paperDesignP 12807) covarianceEvent12807)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12807

theorem localCov12807 : BstLean.Part259.LocalCovarianceOn covarianceEvent12807
    (BstLean.Part263.cell scalarRow12807.grid) (caps repair12807) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12807

theorem covarianceGood12807_payment :
    (retDist (paperDesignP 12807).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12807)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12807_payment



end BstLean.Part269.N12807

namespace BstLean.Part269.N12807
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12807}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12807.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12807) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12807).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12807 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12807) (by norm_num) BstLean.Part268.WorldRow12807.worldPackage rfl
    BstLean.Part268.WorldRow12807.product_lower (BstLean.Part268.WorldRow12807.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12807} (hw : c ∈ Hof BstLean.Part268.WorldRow12807.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12807) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12807) (by norm_num) BstLean.Part268.WorldRow12807.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12807} (hw : c ∈ Hof BstLean.Part268.WorldRow12807.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12807) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12807).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12807) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12807_eq : scalarRow12807.targetFrame = BstLean.Part268.agent12807.frame := by
  norm_num [scalarRow12807,BstLean.Part268.agent12807]

noncomputable def frameData12807 : BstLean.Part264b.FrameData 12807 :=
  BstLean.Part269.frameData_from_numerics (n := 12807) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12807.worldPackage rfl BstLean.Part268.WorldRow12807.product_lower (BstLean.Part268.WorldRow12807.producthi.2.trans (by norm_num))
    scalarRow12807 repair12807 covarianceInputs12807 (fun i hi => sourceNumerics12807 hi)
    BstLean.Part268.agent12807.frame targetFrame12807_eq


end BstLean.Part269.N12807

namespace BstLean.Part269.N12808
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12808 : scalarRow12808.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12808, BstLean.Part268.grid12808, BstLean.Part263.worldGrid]

theorem supplies12808 (j : Fin 43) : Supply 12808 (parameters j)
    (cellLower scalarRow12808.grid (sourceIndex j))
    (cellUpper scalarRow12808.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12808.grid grid_top_bounds12808 j

theorem radii12808 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12808.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12808 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12808 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12808.grid grid_top_bounds12808 j hθ

noncomputable def covarianceInputs12808 :
    BstLean.Part263.CovarianceInputs 12808 scalarRow12808.grid parameters (caps repair12808) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12808 grid_top_bounds12808 repair12808

noncomputable def covarianceEvent12808 : Set (AgFam 12808) :=
  BstLean.Part263.covarianceEvent 12808 scalarRow12808.grid parameters

theorem covarianceEvent12808_measurable : MeasurableSet covarianceEvent12808 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12808_payment :
    (retDist (paperDesignP 12808).toCentres).real
      (agentEv (paperDesignP 12808) covarianceEvent12808)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12808

theorem localCov12808 : BstLean.Part259.LocalCovarianceOn covarianceEvent12808
    (BstLean.Part263.cell scalarRow12808.grid) (caps repair12808) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12808

theorem covarianceGood12808_payment :
    (retDist (paperDesignP 12808).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12808)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12808_payment



end BstLean.Part269.N12808

namespace BstLean.Part269.N12808
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12808}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12808.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12808) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12808).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12808 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12808) (by norm_num) BstLean.Part268.WorldRow12808.worldPackage rfl
    BstLean.Part268.WorldRow12808.product_lower (BstLean.Part268.WorldRow12808.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12808} (hw : c ∈ Hof BstLean.Part268.WorldRow12808.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12808) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12808) (by norm_num) BstLean.Part268.WorldRow12808.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12808} (hw : c ∈ Hof BstLean.Part268.WorldRow12808.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12808) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12808).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12808) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12808_eq : scalarRow12808.targetFrame = BstLean.Part268.agent12808.frame := by
  norm_num [scalarRow12808,BstLean.Part268.agent12808]

noncomputable def frameData12808 : BstLean.Part264b.FrameData 12808 :=
  BstLean.Part269.frameData_from_numerics (n := 12808) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12808.worldPackage rfl BstLean.Part268.WorldRow12808.product_lower (BstLean.Part268.WorldRow12808.producthi.2.trans (by norm_num))
    scalarRow12808 repair12808 covarianceInputs12808 (fun i hi => sourceNumerics12808 hi)
    BstLean.Part268.agent12808.frame targetFrame12808_eq


end BstLean.Part269.N12808

namespace BstLean.Part269.N12809
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12809 : scalarRow12809.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12809, BstLean.Part268.grid12809, BstLean.Part263.worldGrid]

theorem supplies12809 (j : Fin 43) : Supply 12809 (parameters j)
    (cellLower scalarRow12809.grid (sourceIndex j))
    (cellUpper scalarRow12809.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12809.grid grid_top_bounds12809 j

theorem radii12809 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12809.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12809 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12809 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12809.grid grid_top_bounds12809 j hθ

noncomputable def covarianceInputs12809 :
    BstLean.Part263.CovarianceInputs 12809 scalarRow12809.grid parameters (caps repair12809) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12809 grid_top_bounds12809 repair12809

noncomputable def covarianceEvent12809 : Set (AgFam 12809) :=
  BstLean.Part263.covarianceEvent 12809 scalarRow12809.grid parameters

theorem covarianceEvent12809_measurable : MeasurableSet covarianceEvent12809 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12809_payment :
    (retDist (paperDesignP 12809).toCentres).real
      (agentEv (paperDesignP 12809) covarianceEvent12809)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12809

theorem localCov12809 : BstLean.Part259.LocalCovarianceOn covarianceEvent12809
    (BstLean.Part263.cell scalarRow12809.grid) (caps repair12809) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12809

theorem covarianceGood12809_payment :
    (retDist (paperDesignP 12809).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12809)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12809_payment



end BstLean.Part269.N12809

namespace BstLean.Part269.N12809
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12809}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12809.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12809) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12809).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12809 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12809) (by norm_num) BstLean.Part268.WorldRow12809.worldPackage rfl
    BstLean.Part268.WorldRow12809.product_lower (BstLean.Part268.WorldRow12809.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12809} (hw : c ∈ Hof BstLean.Part268.WorldRow12809.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12809) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12809) (by norm_num) BstLean.Part268.WorldRow12809.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12809} (hw : c ∈ Hof BstLean.Part268.WorldRow12809.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12809) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12809).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12809) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12809_eq : scalarRow12809.targetFrame = BstLean.Part268.agent12809.frame := by
  norm_num [scalarRow12809,BstLean.Part268.agent12809]

noncomputable def frameData12809 : BstLean.Part264b.FrameData 12809 :=
  BstLean.Part269.frameData_from_numerics (n := 12809) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12809.worldPackage rfl BstLean.Part268.WorldRow12809.product_lower (BstLean.Part268.WorldRow12809.producthi.2.trans (by norm_num))
    scalarRow12809 repair12809 covarianceInputs12809 (fun i hi => sourceNumerics12809 hi)
    BstLean.Part268.agent12809.frame targetFrame12809_eq


end BstLean.Part269.N12809
