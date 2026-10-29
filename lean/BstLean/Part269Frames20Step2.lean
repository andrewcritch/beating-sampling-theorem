import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World20Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs20
import BstLean.Part269Rows20
import BstLean.Part269Sources20
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12860
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12860 : scalarRow12860.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12860, BstLean.Part268.grid12860, BstLean.Part263.worldGrid]

theorem supplies12860 (j : Fin 43) : Supply 12860 (parameters j)
    (cellLower scalarRow12860.grid (sourceIndex j))
    (cellUpper scalarRow12860.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12860.grid grid_top_bounds12860 j

theorem radii12860 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12860.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12860 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12860 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12860.grid grid_top_bounds12860 j hθ

noncomputable def covarianceInputs12860 :
    BstLean.Part263.CovarianceInputs 12860 scalarRow12860.grid parameters (caps repair12860) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12860 grid_top_bounds12860 repair12860

noncomputable def covarianceEvent12860 : Set (AgFam 12860) :=
  BstLean.Part263.covarianceEvent 12860 scalarRow12860.grid parameters

theorem covarianceEvent12860_measurable : MeasurableSet covarianceEvent12860 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12860_payment :
    (retDist (paperDesignP 12860).toCentres).real
      (agentEv (paperDesignP 12860) covarianceEvent12860)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12860

theorem localCov12860 : BstLean.Part259.LocalCovarianceOn covarianceEvent12860
    (BstLean.Part263.cell scalarRow12860.grid) (caps repair12860) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12860

theorem covarianceGood12860_payment :
    (retDist (paperDesignP 12860).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12860)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12860_payment



end BstLean.Part269.N12860

namespace BstLean.Part269.N12860
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12860}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12860.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12860) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12860).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12860 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12860) (by norm_num) BstLean.Part268.WorldRow12860.worldPackage rfl
    BstLean.Part268.WorldRow12860.product_lower (BstLean.Part268.WorldRow12860.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12860} (hw : c ∈ Hof BstLean.Part268.WorldRow12860.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12860) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12860) (by norm_num) BstLean.Part268.WorldRow12860.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12860} (hw : c ∈ Hof BstLean.Part268.WorldRow12860.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12860) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12860).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12860) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12860_eq : scalarRow12860.targetFrame = BstLean.Part268.agent12860.frame := by
  norm_num [scalarRow12860,BstLean.Part268.agent12860]

noncomputable def frameData12860 : BstLean.Part264b.FrameData 12860 :=
  BstLean.Part269.frameData_from_numerics (n := 12860) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12860.worldPackage rfl BstLean.Part268.WorldRow12860.product_lower (BstLean.Part268.WorldRow12860.producthi.2.trans (by norm_num))
    scalarRow12860 repair12860 covarianceInputs12860 (fun i hi => sourceNumerics12860 hi)
    BstLean.Part268.agent12860.frame targetFrame12860_eq


end BstLean.Part269.N12860

namespace BstLean.Part269.N12861
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12861 : scalarRow12861.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12861, BstLean.Part268.grid12861, BstLean.Part263.worldGrid]

theorem supplies12861 (j : Fin 43) : Supply 12861 (parameters j)
    (cellLower scalarRow12861.grid (sourceIndex j))
    (cellUpper scalarRow12861.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12861.grid grid_top_bounds12861 j

theorem radii12861 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12861.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12861 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12861 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12861.grid grid_top_bounds12861 j hθ

noncomputable def covarianceInputs12861 :
    BstLean.Part263.CovarianceInputs 12861 scalarRow12861.grid parameters (caps repair12861) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12861 grid_top_bounds12861 repair12861

noncomputable def covarianceEvent12861 : Set (AgFam 12861) :=
  BstLean.Part263.covarianceEvent 12861 scalarRow12861.grid parameters

theorem covarianceEvent12861_measurable : MeasurableSet covarianceEvent12861 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12861_payment :
    (retDist (paperDesignP 12861).toCentres).real
      (agentEv (paperDesignP 12861) covarianceEvent12861)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12861

theorem localCov12861 : BstLean.Part259.LocalCovarianceOn covarianceEvent12861
    (BstLean.Part263.cell scalarRow12861.grid) (caps repair12861) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12861

theorem covarianceGood12861_payment :
    (retDist (paperDesignP 12861).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12861)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12861_payment



end BstLean.Part269.N12861

namespace BstLean.Part269.N12861
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12861}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12861.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12861) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12861).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12861 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12861) (by norm_num) BstLean.Part268.WorldRow12861.worldPackage rfl
    BstLean.Part268.WorldRow12861.product_lower (BstLean.Part268.WorldRow12861.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12861} (hw : c ∈ Hof BstLean.Part268.WorldRow12861.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12861) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12861) (by norm_num) BstLean.Part268.WorldRow12861.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12861} (hw : c ∈ Hof BstLean.Part268.WorldRow12861.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12861) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12861).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12861) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12861_eq : scalarRow12861.targetFrame = BstLean.Part268.agent12861.frame := by
  norm_num [scalarRow12861,BstLean.Part268.agent12861]

noncomputable def frameData12861 : BstLean.Part264b.FrameData 12861 :=
  BstLean.Part269.frameData_from_numerics (n := 12861) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12861.worldPackage rfl BstLean.Part268.WorldRow12861.product_lower (BstLean.Part268.WorldRow12861.producthi.2.trans (by norm_num))
    scalarRow12861 repair12861 covarianceInputs12861 (fun i hi => sourceNumerics12861 hi)
    BstLean.Part268.agent12861.frame targetFrame12861_eq


end BstLean.Part269.N12861

namespace BstLean.Part269.N12862
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12862 : scalarRow12862.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12862, BstLean.Part268.grid12862, BstLean.Part263.worldGrid]

theorem supplies12862 (j : Fin 43) : Supply 12862 (parameters j)
    (cellLower scalarRow12862.grid (sourceIndex j))
    (cellUpper scalarRow12862.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12862.grid grid_top_bounds12862 j

theorem radii12862 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12862.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12862 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12862 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12862.grid grid_top_bounds12862 j hθ

noncomputable def covarianceInputs12862 :
    BstLean.Part263.CovarianceInputs 12862 scalarRow12862.grid parameters (caps repair12862) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12862 grid_top_bounds12862 repair12862

noncomputable def covarianceEvent12862 : Set (AgFam 12862) :=
  BstLean.Part263.covarianceEvent 12862 scalarRow12862.grid parameters

theorem covarianceEvent12862_measurable : MeasurableSet covarianceEvent12862 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12862_payment :
    (retDist (paperDesignP 12862).toCentres).real
      (agentEv (paperDesignP 12862) covarianceEvent12862)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12862

theorem localCov12862 : BstLean.Part259.LocalCovarianceOn covarianceEvent12862
    (BstLean.Part263.cell scalarRow12862.grid) (caps repair12862) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12862

theorem covarianceGood12862_payment :
    (retDist (paperDesignP 12862).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12862)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12862_payment



end BstLean.Part269.N12862

namespace BstLean.Part269.N12862
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12862}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12862.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12862) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12862).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12862 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12862) (by norm_num) BstLean.Part268.WorldRow12862.worldPackage rfl
    BstLean.Part268.WorldRow12862.product_lower (BstLean.Part268.WorldRow12862.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12862} (hw : c ∈ Hof BstLean.Part268.WorldRow12862.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12862) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12862) (by norm_num) BstLean.Part268.WorldRow12862.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12862} (hw : c ∈ Hof BstLean.Part268.WorldRow12862.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12862) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12862).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12862) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12862_eq : scalarRow12862.targetFrame = BstLean.Part268.agent12862.frame := by
  norm_num [scalarRow12862,BstLean.Part268.agent12862]

noncomputable def frameData12862 : BstLean.Part264b.FrameData 12862 :=
  BstLean.Part269.frameData_from_numerics (n := 12862) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12862.worldPackage rfl BstLean.Part268.WorldRow12862.product_lower (BstLean.Part268.WorldRow12862.producthi.2.trans (by norm_num))
    scalarRow12862 repair12862 covarianceInputs12862 (fun i hi => sourceNumerics12862 hi)
    BstLean.Part268.agent12862.frame targetFrame12862_eq


end BstLean.Part269.N12862

namespace BstLean.Part269.N12863
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12863 : scalarRow12863.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12863, BstLean.Part268.grid12863, BstLean.Part263.worldGrid]

theorem supplies12863 (j : Fin 43) : Supply 12863 (parameters j)
    (cellLower scalarRow12863.grid (sourceIndex j))
    (cellUpper scalarRow12863.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12863.grid grid_top_bounds12863 j

theorem radii12863 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12863.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12863 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12863 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12863.grid grid_top_bounds12863 j hθ

noncomputable def covarianceInputs12863 :
    BstLean.Part263.CovarianceInputs 12863 scalarRow12863.grid parameters (caps repair12863) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12863 grid_top_bounds12863 repair12863

noncomputable def covarianceEvent12863 : Set (AgFam 12863) :=
  BstLean.Part263.covarianceEvent 12863 scalarRow12863.grid parameters

theorem covarianceEvent12863_measurable : MeasurableSet covarianceEvent12863 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12863_payment :
    (retDist (paperDesignP 12863).toCentres).real
      (agentEv (paperDesignP 12863) covarianceEvent12863)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12863

theorem localCov12863 : BstLean.Part259.LocalCovarianceOn covarianceEvent12863
    (BstLean.Part263.cell scalarRow12863.grid) (caps repair12863) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12863

theorem covarianceGood12863_payment :
    (retDist (paperDesignP 12863).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12863)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12863_payment



end BstLean.Part269.N12863

namespace BstLean.Part269.N12863
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12863}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12863.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12863) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12863).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12863 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12863) (by norm_num) BstLean.Part268.WorldRow12863.worldPackage rfl
    BstLean.Part268.WorldRow12863.product_lower (BstLean.Part268.WorldRow12863.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12863} (hw : c ∈ Hof BstLean.Part268.WorldRow12863.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12863) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12863) (by norm_num) BstLean.Part268.WorldRow12863.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12863} (hw : c ∈ Hof BstLean.Part268.WorldRow12863.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12863) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12863).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12863) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12863_eq : scalarRow12863.targetFrame = BstLean.Part268.agent12863.frame := by
  norm_num [scalarRow12863,BstLean.Part268.agent12863]

noncomputable def frameData12863 : BstLean.Part264b.FrameData 12863 :=
  BstLean.Part269.frameData_from_numerics (n := 12863) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12863.worldPackage rfl BstLean.Part268.WorldRow12863.product_lower (BstLean.Part268.WorldRow12863.producthi.2.trans (by norm_num))
    scalarRow12863 repair12863 covarianceInputs12863 (fun i hi => sourceNumerics12863 hi)
    BstLean.Part268.agent12863.frame targetFrame12863_eq


end BstLean.Part269.N12863

namespace BstLean.Part269.N12864
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12864 : scalarRow12864.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12864, BstLean.Part268.grid12864, BstLean.Part263.worldGrid]

theorem supplies12864 (j : Fin 43) : Supply 12864 (parameters j)
    (cellLower scalarRow12864.grid (sourceIndex j))
    (cellUpper scalarRow12864.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12864.grid grid_top_bounds12864 j

theorem radii12864 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12864.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12864 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12864 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12864.grid grid_top_bounds12864 j hθ

noncomputable def covarianceInputs12864 :
    BstLean.Part263.CovarianceInputs 12864 scalarRow12864.grid parameters (caps repair12864) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12864 grid_top_bounds12864 repair12864

noncomputable def covarianceEvent12864 : Set (AgFam 12864) :=
  BstLean.Part263.covarianceEvent 12864 scalarRow12864.grid parameters

theorem covarianceEvent12864_measurable : MeasurableSet covarianceEvent12864 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12864_payment :
    (retDist (paperDesignP 12864).toCentres).real
      (agentEv (paperDesignP 12864) covarianceEvent12864)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12864

theorem localCov12864 : BstLean.Part259.LocalCovarianceOn covarianceEvent12864
    (BstLean.Part263.cell scalarRow12864.grid) (caps repair12864) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12864

theorem covarianceGood12864_payment :
    (retDist (paperDesignP 12864).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12864)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12864_payment



end BstLean.Part269.N12864

namespace BstLean.Part269.N12864
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12864}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12864.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12864) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12864).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12864 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12864) (by norm_num) BstLean.Part268.WorldRow12864.worldPackage rfl
    BstLean.Part268.WorldRow12864.product_lower (BstLean.Part268.WorldRow12864.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12864} (hw : c ∈ Hof BstLean.Part268.WorldRow12864.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12864) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12864) (by norm_num) BstLean.Part268.WorldRow12864.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12864} (hw : c ∈ Hof BstLean.Part268.WorldRow12864.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12864) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12864).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12864) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12864_eq : scalarRow12864.targetFrame = BstLean.Part268.agent12864.frame := by
  norm_num [scalarRow12864,BstLean.Part268.agent12864]

noncomputable def frameData12864 : BstLean.Part264b.FrameData 12864 :=
  BstLean.Part269.frameData_from_numerics (n := 12864) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12864.worldPackage rfl BstLean.Part268.WorldRow12864.product_lower (BstLean.Part268.WorldRow12864.producthi.2.trans (by norm_num))
    scalarRow12864 repair12864 covarianceInputs12864 (fun i hi => sourceNumerics12864 hi)
    BstLean.Part268.agent12864.frame targetFrame12864_eq


end BstLean.Part269.N12864
