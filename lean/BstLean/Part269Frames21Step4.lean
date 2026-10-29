import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World21Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs21
import BstLean.Part269Rows21
import BstLean.Part269Sources21
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12895
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12895 : scalarRow12895.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12895, BstLean.Part268.grid12895, BstLean.Part263.worldGrid]

theorem supplies12895 (j : Fin 43) : Supply 12895 (parameters j)
    (cellLower scalarRow12895.grid (sourceIndex j))
    (cellUpper scalarRow12895.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12895.grid grid_top_bounds12895 j

theorem radii12895 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12895.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12895 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12895 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12895.grid grid_top_bounds12895 j hθ

noncomputable def covarianceInputs12895 :
    BstLean.Part263.CovarianceInputs 12895 scalarRow12895.grid parameters (caps repair12895) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12895 grid_top_bounds12895 repair12895

noncomputable def covarianceEvent12895 : Set (AgFam 12895) :=
  BstLean.Part263.covarianceEvent 12895 scalarRow12895.grid parameters

theorem covarianceEvent12895_measurable : MeasurableSet covarianceEvent12895 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12895_payment :
    (retDist (paperDesignP 12895).toCentres).real
      (agentEv (paperDesignP 12895) covarianceEvent12895)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12895

theorem localCov12895 : BstLean.Part259.LocalCovarianceOn covarianceEvent12895
    (BstLean.Part263.cell scalarRow12895.grid) (caps repair12895) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12895

theorem covarianceGood12895_payment :
    (retDist (paperDesignP 12895).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12895)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12895_payment



end BstLean.Part269.N12895

namespace BstLean.Part269.N12895
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12895}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12895.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12895) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12895).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12895 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12895) (by norm_num) BstLean.Part268.WorldRow12895.worldPackage rfl
    BstLean.Part268.WorldRow12895.product_lower (BstLean.Part268.WorldRow12895.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12895} (hw : c ∈ Hof BstLean.Part268.WorldRow12895.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12895) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12895) (by norm_num) BstLean.Part268.WorldRow12895.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12895} (hw : c ∈ Hof BstLean.Part268.WorldRow12895.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12895) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12895).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12895) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12895_eq : scalarRow12895.targetFrame = BstLean.Part268.agent12895.frame := by
  norm_num [scalarRow12895,BstLean.Part268.agent12895]

noncomputable def frameData12895 : BstLean.Part264b.FrameData 12895 :=
  BstLean.Part269.frameData_from_numerics (n := 12895) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12895.worldPackage rfl BstLean.Part268.WorldRow12895.product_lower (BstLean.Part268.WorldRow12895.producthi.2.trans (by norm_num))
    scalarRow12895 repair12895 covarianceInputs12895 (fun i hi => sourceNumerics12895 hi)
    BstLean.Part268.agent12895.frame targetFrame12895_eq


end BstLean.Part269.N12895

namespace BstLean.Part269.N12896
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12896 : scalarRow12896.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12896, BstLean.Part268.grid12896, BstLean.Part263.worldGrid]

theorem supplies12896 (j : Fin 43) : Supply 12896 (parameters j)
    (cellLower scalarRow12896.grid (sourceIndex j))
    (cellUpper scalarRow12896.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12896.grid grid_top_bounds12896 j

theorem radii12896 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12896.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12896 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12896 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12896.grid grid_top_bounds12896 j hθ

noncomputable def covarianceInputs12896 :
    BstLean.Part263.CovarianceInputs 12896 scalarRow12896.grid parameters (caps repair12896) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12896 grid_top_bounds12896 repair12896

noncomputable def covarianceEvent12896 : Set (AgFam 12896) :=
  BstLean.Part263.covarianceEvent 12896 scalarRow12896.grid parameters

theorem covarianceEvent12896_measurable : MeasurableSet covarianceEvent12896 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12896_payment :
    (retDist (paperDesignP 12896).toCentres).real
      (agentEv (paperDesignP 12896) covarianceEvent12896)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12896

theorem localCov12896 : BstLean.Part259.LocalCovarianceOn covarianceEvent12896
    (BstLean.Part263.cell scalarRow12896.grid) (caps repair12896) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12896

theorem covarianceGood12896_payment :
    (retDist (paperDesignP 12896).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12896)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12896_payment



end BstLean.Part269.N12896

namespace BstLean.Part269.N12896
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12896}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12896.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12896) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12896).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12896 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12896) (by norm_num) BstLean.Part268.WorldRow12896.worldPackage rfl
    BstLean.Part268.WorldRow12896.product_lower (BstLean.Part268.WorldRow12896.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12896} (hw : c ∈ Hof BstLean.Part268.WorldRow12896.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12896) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12896) (by norm_num) BstLean.Part268.WorldRow12896.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12896} (hw : c ∈ Hof BstLean.Part268.WorldRow12896.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12896) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12896).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12896) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12896_eq : scalarRow12896.targetFrame = BstLean.Part268.agent12896.frame := by
  norm_num [scalarRow12896,BstLean.Part268.agent12896]

noncomputable def frameData12896 : BstLean.Part264b.FrameData 12896 :=
  BstLean.Part269.frameData_from_numerics (n := 12896) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12896.worldPackage rfl BstLean.Part268.WorldRow12896.product_lower (BstLean.Part268.WorldRow12896.producthi.2.trans (by norm_num))
    scalarRow12896 repair12896 covarianceInputs12896 (fun i hi => sourceNumerics12896 hi)
    BstLean.Part268.agent12896.frame targetFrame12896_eq


end BstLean.Part269.N12896

namespace BstLean.Part269.N12897
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12897 : scalarRow12897.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12897, BstLean.Part268.grid12897, BstLean.Part263.worldGrid]

theorem supplies12897 (j : Fin 43) : Supply 12897 (parameters j)
    (cellLower scalarRow12897.grid (sourceIndex j))
    (cellUpper scalarRow12897.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12897.grid grid_top_bounds12897 j

theorem radii12897 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12897.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12897 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12897 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12897.grid grid_top_bounds12897 j hθ

noncomputable def covarianceInputs12897 :
    BstLean.Part263.CovarianceInputs 12897 scalarRow12897.grid parameters (caps repair12897) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12897 grid_top_bounds12897 repair12897

noncomputable def covarianceEvent12897 : Set (AgFam 12897) :=
  BstLean.Part263.covarianceEvent 12897 scalarRow12897.grid parameters

theorem covarianceEvent12897_measurable : MeasurableSet covarianceEvent12897 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12897_payment :
    (retDist (paperDesignP 12897).toCentres).real
      (agentEv (paperDesignP 12897) covarianceEvent12897)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12897

theorem localCov12897 : BstLean.Part259.LocalCovarianceOn covarianceEvent12897
    (BstLean.Part263.cell scalarRow12897.grid) (caps repair12897) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12897

theorem covarianceGood12897_payment :
    (retDist (paperDesignP 12897).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12897)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12897_payment



end BstLean.Part269.N12897

namespace BstLean.Part269.N12897
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12897}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12897.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12897) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12897).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12897 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12897) (by norm_num) BstLean.Part268.WorldRow12897.worldPackage rfl
    BstLean.Part268.WorldRow12897.product_lower (BstLean.Part268.WorldRow12897.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12897} (hw : c ∈ Hof BstLean.Part268.WorldRow12897.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12897) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12897) (by norm_num) BstLean.Part268.WorldRow12897.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12897} (hw : c ∈ Hof BstLean.Part268.WorldRow12897.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12897) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12897).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12897) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12897_eq : scalarRow12897.targetFrame = BstLean.Part268.agent12897.frame := by
  norm_num [scalarRow12897,BstLean.Part268.agent12897]

noncomputable def frameData12897 : BstLean.Part264b.FrameData 12897 :=
  BstLean.Part269.frameData_from_numerics (n := 12897) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12897.worldPackage rfl BstLean.Part268.WorldRow12897.product_lower (BstLean.Part268.WorldRow12897.producthi.2.trans (by norm_num))
    scalarRow12897 repair12897 covarianceInputs12897 (fun i hi => sourceNumerics12897 hi)
    BstLean.Part268.agent12897.frame targetFrame12897_eq


end BstLean.Part269.N12897

namespace BstLean.Part269.N12898
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12898 : scalarRow12898.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12898, BstLean.Part268.grid12898, BstLean.Part263.worldGrid]

theorem supplies12898 (j : Fin 43) : Supply 12898 (parameters j)
    (cellLower scalarRow12898.grid (sourceIndex j))
    (cellUpper scalarRow12898.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12898.grid grid_top_bounds12898 j

theorem radii12898 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12898.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12898 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12898 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12898.grid grid_top_bounds12898 j hθ

noncomputable def covarianceInputs12898 :
    BstLean.Part263.CovarianceInputs 12898 scalarRow12898.grid parameters (caps repair12898) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12898 grid_top_bounds12898 repair12898

noncomputable def covarianceEvent12898 : Set (AgFam 12898) :=
  BstLean.Part263.covarianceEvent 12898 scalarRow12898.grid parameters

theorem covarianceEvent12898_measurable : MeasurableSet covarianceEvent12898 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12898_payment :
    (retDist (paperDesignP 12898).toCentres).real
      (agentEv (paperDesignP 12898) covarianceEvent12898)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12898

theorem localCov12898 : BstLean.Part259.LocalCovarianceOn covarianceEvent12898
    (BstLean.Part263.cell scalarRow12898.grid) (caps repair12898) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12898

theorem covarianceGood12898_payment :
    (retDist (paperDesignP 12898).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12898)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12898_payment



end BstLean.Part269.N12898

namespace BstLean.Part269.N12898
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12898}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12898.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12898) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12898).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12898 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12898) (by norm_num) BstLean.Part268.WorldRow12898.worldPackage rfl
    BstLean.Part268.WorldRow12898.product_lower (BstLean.Part268.WorldRow12898.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12898} (hw : c ∈ Hof BstLean.Part268.WorldRow12898.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12898) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12898) (by norm_num) BstLean.Part268.WorldRow12898.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12898} (hw : c ∈ Hof BstLean.Part268.WorldRow12898.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12898) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12898).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12898) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12898_eq : scalarRow12898.targetFrame = BstLean.Part268.agent12898.frame := by
  norm_num [scalarRow12898,BstLean.Part268.agent12898]

noncomputable def frameData12898 : BstLean.Part264b.FrameData 12898 :=
  BstLean.Part269.frameData_from_numerics (n := 12898) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12898.worldPackage rfl BstLean.Part268.WorldRow12898.product_lower (BstLean.Part268.WorldRow12898.producthi.2.trans (by norm_num))
    scalarRow12898 repair12898 covarianceInputs12898 (fun i hi => sourceNumerics12898 hi)
    BstLean.Part268.agent12898.frame targetFrame12898_eq


end BstLean.Part269.N12898

namespace BstLean.Part269.N12899
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12899 : scalarRow12899.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12899, BstLean.Part268.grid12899, BstLean.Part263.worldGrid]

theorem supplies12899 (j : Fin 43) : Supply 12899 (parameters j)
    (cellLower scalarRow12899.grid (sourceIndex j))
    (cellUpper scalarRow12899.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12899.grid grid_top_bounds12899 j

theorem radii12899 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12899.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12899 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12899 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12899.grid grid_top_bounds12899 j hθ

noncomputable def covarianceInputs12899 :
    BstLean.Part263.CovarianceInputs 12899 scalarRow12899.grid parameters (caps repair12899) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12899 grid_top_bounds12899 repair12899

noncomputable def covarianceEvent12899 : Set (AgFam 12899) :=
  BstLean.Part263.covarianceEvent 12899 scalarRow12899.grid parameters

theorem covarianceEvent12899_measurable : MeasurableSet covarianceEvent12899 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12899_payment :
    (retDist (paperDesignP 12899).toCentres).real
      (agentEv (paperDesignP 12899) covarianceEvent12899)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12899

theorem localCov12899 : BstLean.Part259.LocalCovarianceOn covarianceEvent12899
    (BstLean.Part263.cell scalarRow12899.grid) (caps repair12899) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12899

theorem covarianceGood12899_payment :
    (retDist (paperDesignP 12899).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12899)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12899_payment



end BstLean.Part269.N12899

namespace BstLean.Part269.N12899
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12899}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12899.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12899) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12899).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12899 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12899) (by norm_num) BstLean.Part268.WorldRow12899.worldPackage rfl
    BstLean.Part268.WorldRow12899.product_lower (BstLean.Part268.WorldRow12899.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12899} (hw : c ∈ Hof BstLean.Part268.WorldRow12899.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12899) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12899) (by norm_num) BstLean.Part268.WorldRow12899.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12899} (hw : c ∈ Hof BstLean.Part268.WorldRow12899.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12899) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12899).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12899) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12899_eq : scalarRow12899.targetFrame = BstLean.Part268.agent12899.frame := by
  norm_num [scalarRow12899,BstLean.Part268.agent12899]

noncomputable def frameData12899 : BstLean.Part264b.FrameData 12899 :=
  BstLean.Part269.frameData_from_numerics (n := 12899) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12899.worldPackage rfl BstLean.Part268.WorldRow12899.product_lower (BstLean.Part268.WorldRow12899.producthi.2.trans (by norm_num))
    scalarRow12899 repair12899 covarianceInputs12899 (fun i hi => sourceNumerics12899 hi)
    BstLean.Part268.agent12899.frame targetFrame12899_eq


end BstLean.Part269.N12899
