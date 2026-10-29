import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World19Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs19
import BstLean.Part269Rows19
import BstLean.Part269Sources19
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12825
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12825 : scalarRow12825.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12825, BstLean.Part268.grid12825, BstLean.Part263.worldGrid]

theorem supplies12825 (j : Fin 43) : Supply 12825 (parameters j)
    (cellLower scalarRow12825.grid (sourceIndex j))
    (cellUpper scalarRow12825.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12825.grid grid_top_bounds12825 j

theorem radii12825 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12825.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12825 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12825 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12825.grid grid_top_bounds12825 j hθ

noncomputable def covarianceInputs12825 :
    BstLean.Part263.CovarianceInputs 12825 scalarRow12825.grid parameters (caps repair12825) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12825 grid_top_bounds12825 repair12825

noncomputable def covarianceEvent12825 : Set (AgFam 12825) :=
  BstLean.Part263.covarianceEvent 12825 scalarRow12825.grid parameters

theorem covarianceEvent12825_measurable : MeasurableSet covarianceEvent12825 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12825_payment :
    (retDist (paperDesignP 12825).toCentres).real
      (agentEv (paperDesignP 12825) covarianceEvent12825)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12825

theorem localCov12825 : BstLean.Part259.LocalCovarianceOn covarianceEvent12825
    (BstLean.Part263.cell scalarRow12825.grid) (caps repair12825) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12825

theorem covarianceGood12825_payment :
    (retDist (paperDesignP 12825).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12825)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12825_payment



end BstLean.Part269.N12825

namespace BstLean.Part269.N12825
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12825}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12825.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12825) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12825).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12825 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12825) (by norm_num) BstLean.Part268.WorldRow12825.worldPackage rfl
    BstLean.Part268.WorldRow12825.product_lower (BstLean.Part268.WorldRow12825.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12825} (hw : c ∈ Hof BstLean.Part268.WorldRow12825.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12825) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12825) (by norm_num) BstLean.Part268.WorldRow12825.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12825} (hw : c ∈ Hof BstLean.Part268.WorldRow12825.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12825) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12825).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12825) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12825_eq : scalarRow12825.targetFrame = BstLean.Part268.agent12825.frame := by
  norm_num [scalarRow12825,BstLean.Part268.agent12825]

noncomputable def frameData12825 : BstLean.Part264b.FrameData 12825 :=
  BstLean.Part269.frameData_from_numerics (n := 12825) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12825.worldPackage rfl BstLean.Part268.WorldRow12825.product_lower (BstLean.Part268.WorldRow12825.producthi.2.trans (by norm_num))
    scalarRow12825 repair12825 covarianceInputs12825 (fun i hi => sourceNumerics12825 hi)
    BstLean.Part268.agent12825.frame targetFrame12825_eq


end BstLean.Part269.N12825

namespace BstLean.Part269.N12826
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12826 : scalarRow12826.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12826, BstLean.Part268.grid12826, BstLean.Part263.worldGrid]

theorem supplies12826 (j : Fin 43) : Supply 12826 (parameters j)
    (cellLower scalarRow12826.grid (sourceIndex j))
    (cellUpper scalarRow12826.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12826.grid grid_top_bounds12826 j

theorem radii12826 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12826.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12826 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12826 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12826.grid grid_top_bounds12826 j hθ

noncomputable def covarianceInputs12826 :
    BstLean.Part263.CovarianceInputs 12826 scalarRow12826.grid parameters (caps repair12826) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12826 grid_top_bounds12826 repair12826

noncomputable def covarianceEvent12826 : Set (AgFam 12826) :=
  BstLean.Part263.covarianceEvent 12826 scalarRow12826.grid parameters

theorem covarianceEvent12826_measurable : MeasurableSet covarianceEvent12826 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12826_payment :
    (retDist (paperDesignP 12826).toCentres).real
      (agentEv (paperDesignP 12826) covarianceEvent12826)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12826

theorem localCov12826 : BstLean.Part259.LocalCovarianceOn covarianceEvent12826
    (BstLean.Part263.cell scalarRow12826.grid) (caps repair12826) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12826

theorem covarianceGood12826_payment :
    (retDist (paperDesignP 12826).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12826)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12826_payment



end BstLean.Part269.N12826

namespace BstLean.Part269.N12826
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12826}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12826.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12826) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12826).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12826 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12826) (by norm_num) BstLean.Part268.WorldRow12826.worldPackage rfl
    BstLean.Part268.WorldRow12826.product_lower (BstLean.Part268.WorldRow12826.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12826} (hw : c ∈ Hof BstLean.Part268.WorldRow12826.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12826) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12826) (by norm_num) BstLean.Part268.WorldRow12826.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12826} (hw : c ∈ Hof BstLean.Part268.WorldRow12826.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12826) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12826).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12826) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12826_eq : scalarRow12826.targetFrame = BstLean.Part268.agent12826.frame := by
  norm_num [scalarRow12826,BstLean.Part268.agent12826]

noncomputable def frameData12826 : BstLean.Part264b.FrameData 12826 :=
  BstLean.Part269.frameData_from_numerics (n := 12826) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12826.worldPackage rfl BstLean.Part268.WorldRow12826.product_lower (BstLean.Part268.WorldRow12826.producthi.2.trans (by norm_num))
    scalarRow12826 repair12826 covarianceInputs12826 (fun i hi => sourceNumerics12826 hi)
    BstLean.Part268.agent12826.frame targetFrame12826_eq


end BstLean.Part269.N12826

namespace BstLean.Part269.N12827
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12827 : scalarRow12827.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12827, BstLean.Part268.grid12827, BstLean.Part263.worldGrid]

theorem supplies12827 (j : Fin 43) : Supply 12827 (parameters j)
    (cellLower scalarRow12827.grid (sourceIndex j))
    (cellUpper scalarRow12827.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12827.grid grid_top_bounds12827 j

theorem radii12827 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12827.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12827 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12827 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12827.grid grid_top_bounds12827 j hθ

noncomputable def covarianceInputs12827 :
    BstLean.Part263.CovarianceInputs 12827 scalarRow12827.grid parameters (caps repair12827) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12827 grid_top_bounds12827 repair12827

noncomputable def covarianceEvent12827 : Set (AgFam 12827) :=
  BstLean.Part263.covarianceEvent 12827 scalarRow12827.grid parameters

theorem covarianceEvent12827_measurable : MeasurableSet covarianceEvent12827 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12827_payment :
    (retDist (paperDesignP 12827).toCentres).real
      (agentEv (paperDesignP 12827) covarianceEvent12827)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12827

theorem localCov12827 : BstLean.Part259.LocalCovarianceOn covarianceEvent12827
    (BstLean.Part263.cell scalarRow12827.grid) (caps repair12827) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12827

theorem covarianceGood12827_payment :
    (retDist (paperDesignP 12827).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12827)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12827_payment



end BstLean.Part269.N12827

namespace BstLean.Part269.N12827
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12827}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12827.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12827) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12827).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12827 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12827) (by norm_num) BstLean.Part268.WorldRow12827.worldPackage rfl
    BstLean.Part268.WorldRow12827.product_lower (BstLean.Part268.WorldRow12827.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12827} (hw : c ∈ Hof BstLean.Part268.WorldRow12827.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12827) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12827) (by norm_num) BstLean.Part268.WorldRow12827.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12827} (hw : c ∈ Hof BstLean.Part268.WorldRow12827.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12827) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12827).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12827) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12827_eq : scalarRow12827.targetFrame = BstLean.Part268.agent12827.frame := by
  norm_num [scalarRow12827,BstLean.Part268.agent12827]

noncomputable def frameData12827 : BstLean.Part264b.FrameData 12827 :=
  BstLean.Part269.frameData_from_numerics (n := 12827) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12827.worldPackage rfl BstLean.Part268.WorldRow12827.product_lower (BstLean.Part268.WorldRow12827.producthi.2.trans (by norm_num))
    scalarRow12827 repair12827 covarianceInputs12827 (fun i hi => sourceNumerics12827 hi)
    BstLean.Part268.agent12827.frame targetFrame12827_eq


end BstLean.Part269.N12827

namespace BstLean.Part269.N12828
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12828 : scalarRow12828.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12828, BstLean.Part268.grid12828, BstLean.Part263.worldGrid]

theorem supplies12828 (j : Fin 43) : Supply 12828 (parameters j)
    (cellLower scalarRow12828.grid (sourceIndex j))
    (cellUpper scalarRow12828.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12828.grid grid_top_bounds12828 j

theorem radii12828 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12828.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12828 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12828 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12828.grid grid_top_bounds12828 j hθ

noncomputable def covarianceInputs12828 :
    BstLean.Part263.CovarianceInputs 12828 scalarRow12828.grid parameters (caps repair12828) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12828 grid_top_bounds12828 repair12828

noncomputable def covarianceEvent12828 : Set (AgFam 12828) :=
  BstLean.Part263.covarianceEvent 12828 scalarRow12828.grid parameters

theorem covarianceEvent12828_measurable : MeasurableSet covarianceEvent12828 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12828_payment :
    (retDist (paperDesignP 12828).toCentres).real
      (agentEv (paperDesignP 12828) covarianceEvent12828)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12828

theorem localCov12828 : BstLean.Part259.LocalCovarianceOn covarianceEvent12828
    (BstLean.Part263.cell scalarRow12828.grid) (caps repair12828) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12828

theorem covarianceGood12828_payment :
    (retDist (paperDesignP 12828).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12828)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12828_payment



end BstLean.Part269.N12828

namespace BstLean.Part269.N12828
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12828}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12828.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12828) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12828).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12828 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12828) (by norm_num) BstLean.Part268.WorldRow12828.worldPackage rfl
    BstLean.Part268.WorldRow12828.product_lower (BstLean.Part268.WorldRow12828.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12828} (hw : c ∈ Hof BstLean.Part268.WorldRow12828.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12828) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12828) (by norm_num) BstLean.Part268.WorldRow12828.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12828} (hw : c ∈ Hof BstLean.Part268.WorldRow12828.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12828) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12828).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12828) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12828_eq : scalarRow12828.targetFrame = BstLean.Part268.agent12828.frame := by
  norm_num [scalarRow12828,BstLean.Part268.agent12828]

noncomputable def frameData12828 : BstLean.Part264b.FrameData 12828 :=
  BstLean.Part269.frameData_from_numerics (n := 12828) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12828.worldPackage rfl BstLean.Part268.WorldRow12828.product_lower (BstLean.Part268.WorldRow12828.producthi.2.trans (by norm_num))
    scalarRow12828 repair12828 covarianceInputs12828 (fun i hi => sourceNumerics12828 hi)
    BstLean.Part268.agent12828.frame targetFrame12828_eq


end BstLean.Part269.N12828

namespace BstLean.Part269.N12829
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12829 : scalarRow12829.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12829, BstLean.Part268.grid12829, BstLean.Part263.worldGrid]

theorem supplies12829 (j : Fin 43) : Supply 12829 (parameters j)
    (cellLower scalarRow12829.grid (sourceIndex j))
    (cellUpper scalarRow12829.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12829.grid grid_top_bounds12829 j

theorem radii12829 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12829.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12829 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12829 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12829.grid grid_top_bounds12829 j hθ

noncomputable def covarianceInputs12829 :
    BstLean.Part263.CovarianceInputs 12829 scalarRow12829.grid parameters (caps repair12829) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12829 grid_top_bounds12829 repair12829

noncomputable def covarianceEvent12829 : Set (AgFam 12829) :=
  BstLean.Part263.covarianceEvent 12829 scalarRow12829.grid parameters

theorem covarianceEvent12829_measurable : MeasurableSet covarianceEvent12829 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12829_payment :
    (retDist (paperDesignP 12829).toCentres).real
      (agentEv (paperDesignP 12829) covarianceEvent12829)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12829

theorem localCov12829 : BstLean.Part259.LocalCovarianceOn covarianceEvent12829
    (BstLean.Part263.cell scalarRow12829.grid) (caps repair12829) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12829

theorem covarianceGood12829_payment :
    (retDist (paperDesignP 12829).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12829)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12829_payment



end BstLean.Part269.N12829

namespace BstLean.Part269.N12829
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12829}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12829.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12829) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12829).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12829 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12829) (by norm_num) BstLean.Part268.WorldRow12829.worldPackage rfl
    BstLean.Part268.WorldRow12829.product_lower (BstLean.Part268.WorldRow12829.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12829} (hw : c ∈ Hof BstLean.Part268.WorldRow12829.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12829) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12829) (by norm_num) BstLean.Part268.WorldRow12829.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12829} (hw : c ∈ Hof BstLean.Part268.WorldRow12829.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12829) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12829).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12829) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12829_eq : scalarRow12829.targetFrame = BstLean.Part268.agent12829.frame := by
  norm_num [scalarRow12829,BstLean.Part268.agent12829]

noncomputable def frameData12829 : BstLean.Part264b.FrameData 12829 :=
  BstLean.Part269.frameData_from_numerics (n := 12829) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12829.worldPackage rfl BstLean.Part268.WorldRow12829.product_lower (BstLean.Part268.WorldRow12829.producthi.2.trans (by norm_num))
    scalarRow12829 repair12829 covarianceInputs12829 (fun i hi => sourceNumerics12829 hi)
    BstLean.Part268.agent12829.frame targetFrame12829_eq


end BstLean.Part269.N12829
