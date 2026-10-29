import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World22Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs22
import BstLean.Part269Rows22
import BstLean.Part269Sources22
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12915
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12915 : scalarRow12915.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12915, BstLean.Part268.grid12915, BstLean.Part263.worldGrid]

theorem supplies12915 (j : Fin 43) : Supply 12915 (parameters j)
    (cellLower scalarRow12915.grid (sourceIndex j))
    (cellUpper scalarRow12915.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12915.grid grid_top_bounds12915 j

theorem radii12915 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12915.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12915 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12915 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12915.grid grid_top_bounds12915 j hθ

noncomputable def covarianceInputs12915 :
    BstLean.Part263.CovarianceInputs 12915 scalarRow12915.grid parameters (caps repair12915) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12915 grid_top_bounds12915 repair12915

noncomputable def covarianceEvent12915 : Set (AgFam 12915) :=
  BstLean.Part263.covarianceEvent 12915 scalarRow12915.grid parameters

theorem covarianceEvent12915_measurable : MeasurableSet covarianceEvent12915 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12915_payment :
    (retDist (paperDesignP 12915).toCentres).real
      (agentEv (paperDesignP 12915) covarianceEvent12915)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12915

theorem localCov12915 : BstLean.Part259.LocalCovarianceOn covarianceEvent12915
    (BstLean.Part263.cell scalarRow12915.grid) (caps repair12915) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12915

theorem covarianceGood12915_payment :
    (retDist (paperDesignP 12915).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12915)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12915_payment



end BstLean.Part269.N12915

namespace BstLean.Part269.N12915
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12915}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12915.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12915) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12915).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12915 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12915) (by norm_num) BstLean.Part268.WorldRow12915.worldPackage rfl
    BstLean.Part268.WorldRow12915.product_lower (BstLean.Part268.WorldRow12915.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12915} (hw : c ∈ Hof BstLean.Part268.WorldRow12915.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12915) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12915) (by norm_num) BstLean.Part268.WorldRow12915.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12915} (hw : c ∈ Hof BstLean.Part268.WorldRow12915.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12915) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12915).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12915) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12915_eq : scalarRow12915.targetFrame = BstLean.Part268.agent12915.frame := by
  norm_num [scalarRow12915,BstLean.Part268.agent12915]

noncomputable def frameData12915 : BstLean.Part264b.FrameData 12915 :=
  BstLean.Part269.frameData_from_numerics (n := 12915) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12915.worldPackage rfl BstLean.Part268.WorldRow12915.product_lower (BstLean.Part268.WorldRow12915.producthi.2.trans (by norm_num))
    scalarRow12915 repair12915 covarianceInputs12915 (fun i hi => sourceNumerics12915 hi)
    BstLean.Part268.agent12915.frame targetFrame12915_eq


end BstLean.Part269.N12915

namespace BstLean.Part269.N12916
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12916 : scalarRow12916.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12916, BstLean.Part268.grid12916, BstLean.Part263.worldGrid]

theorem supplies12916 (j : Fin 43) : Supply 12916 (parameters j)
    (cellLower scalarRow12916.grid (sourceIndex j))
    (cellUpper scalarRow12916.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12916.grid grid_top_bounds12916 j

theorem radii12916 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12916.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12916 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12916 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12916.grid grid_top_bounds12916 j hθ

noncomputable def covarianceInputs12916 :
    BstLean.Part263.CovarianceInputs 12916 scalarRow12916.grid parameters (caps repair12916) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12916 grid_top_bounds12916 repair12916

noncomputable def covarianceEvent12916 : Set (AgFam 12916) :=
  BstLean.Part263.covarianceEvent 12916 scalarRow12916.grid parameters

theorem covarianceEvent12916_measurable : MeasurableSet covarianceEvent12916 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12916_payment :
    (retDist (paperDesignP 12916).toCentres).real
      (agentEv (paperDesignP 12916) covarianceEvent12916)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12916

theorem localCov12916 : BstLean.Part259.LocalCovarianceOn covarianceEvent12916
    (BstLean.Part263.cell scalarRow12916.grid) (caps repair12916) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12916

theorem covarianceGood12916_payment :
    (retDist (paperDesignP 12916).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12916)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12916_payment



end BstLean.Part269.N12916

namespace BstLean.Part269.N12916
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12916}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12916.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12916) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12916).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12916 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12916) (by norm_num) BstLean.Part268.WorldRow12916.worldPackage rfl
    BstLean.Part268.WorldRow12916.product_lower (BstLean.Part268.WorldRow12916.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12916} (hw : c ∈ Hof BstLean.Part268.WorldRow12916.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12916) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12916) (by norm_num) BstLean.Part268.WorldRow12916.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12916} (hw : c ∈ Hof BstLean.Part268.WorldRow12916.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12916) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12916).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12916) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12916_eq : scalarRow12916.targetFrame = BstLean.Part268.agent12916.frame := by
  norm_num [scalarRow12916,BstLean.Part268.agent12916]

noncomputable def frameData12916 : BstLean.Part264b.FrameData 12916 :=
  BstLean.Part269.frameData_from_numerics (n := 12916) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12916.worldPackage rfl BstLean.Part268.WorldRow12916.product_lower (BstLean.Part268.WorldRow12916.producthi.2.trans (by norm_num))
    scalarRow12916 repair12916 covarianceInputs12916 (fun i hi => sourceNumerics12916 hi)
    BstLean.Part268.agent12916.frame targetFrame12916_eq


end BstLean.Part269.N12916

namespace BstLean.Part269.N12917
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12917 : scalarRow12917.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12917, BstLean.Part268.grid12917, BstLean.Part263.worldGrid]

theorem supplies12917 (j : Fin 43) : Supply 12917 (parameters j)
    (cellLower scalarRow12917.grid (sourceIndex j))
    (cellUpper scalarRow12917.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12917.grid grid_top_bounds12917 j

theorem radii12917 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12917.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12917 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12917 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12917.grid grid_top_bounds12917 j hθ

noncomputable def covarianceInputs12917 :
    BstLean.Part263.CovarianceInputs 12917 scalarRow12917.grid parameters (caps repair12917) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12917 grid_top_bounds12917 repair12917

noncomputable def covarianceEvent12917 : Set (AgFam 12917) :=
  BstLean.Part263.covarianceEvent 12917 scalarRow12917.grid parameters

theorem covarianceEvent12917_measurable : MeasurableSet covarianceEvent12917 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12917_payment :
    (retDist (paperDesignP 12917).toCentres).real
      (agentEv (paperDesignP 12917) covarianceEvent12917)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12917

theorem localCov12917 : BstLean.Part259.LocalCovarianceOn covarianceEvent12917
    (BstLean.Part263.cell scalarRow12917.grid) (caps repair12917) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12917

theorem covarianceGood12917_payment :
    (retDist (paperDesignP 12917).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12917)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12917_payment



end BstLean.Part269.N12917

namespace BstLean.Part269.N12917
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12917}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12917.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12917) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12917).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12917 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12917) (by norm_num) BstLean.Part268.WorldRow12917.worldPackage rfl
    BstLean.Part268.WorldRow12917.product_lower (BstLean.Part268.WorldRow12917.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12917} (hw : c ∈ Hof BstLean.Part268.WorldRow12917.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12917) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12917) (by norm_num) BstLean.Part268.WorldRow12917.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12917} (hw : c ∈ Hof BstLean.Part268.WorldRow12917.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12917) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12917).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12917) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12917_eq : scalarRow12917.targetFrame = BstLean.Part268.agent12917.frame := by
  norm_num [scalarRow12917,BstLean.Part268.agent12917]

noncomputable def frameData12917 : BstLean.Part264b.FrameData 12917 :=
  BstLean.Part269.frameData_from_numerics (n := 12917) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12917.worldPackage rfl BstLean.Part268.WorldRow12917.product_lower (BstLean.Part268.WorldRow12917.producthi.2.trans (by norm_num))
    scalarRow12917 repair12917 covarianceInputs12917 (fun i hi => sourceNumerics12917 hi)
    BstLean.Part268.agent12917.frame targetFrame12917_eq


end BstLean.Part269.N12917

namespace BstLean.Part269.N12918
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12918 : scalarRow12918.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12918, BstLean.Part268.grid12918, BstLean.Part263.worldGrid]

theorem supplies12918 (j : Fin 43) : Supply 12918 (parameters j)
    (cellLower scalarRow12918.grid (sourceIndex j))
    (cellUpper scalarRow12918.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12918.grid grid_top_bounds12918 j

theorem radii12918 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12918.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12918 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12918 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12918.grid grid_top_bounds12918 j hθ

noncomputable def covarianceInputs12918 :
    BstLean.Part263.CovarianceInputs 12918 scalarRow12918.grid parameters (caps repair12918) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12918 grid_top_bounds12918 repair12918

noncomputable def covarianceEvent12918 : Set (AgFam 12918) :=
  BstLean.Part263.covarianceEvent 12918 scalarRow12918.grid parameters

theorem covarianceEvent12918_measurable : MeasurableSet covarianceEvent12918 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12918_payment :
    (retDist (paperDesignP 12918).toCentres).real
      (agentEv (paperDesignP 12918) covarianceEvent12918)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12918

theorem localCov12918 : BstLean.Part259.LocalCovarianceOn covarianceEvent12918
    (BstLean.Part263.cell scalarRow12918.grid) (caps repair12918) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12918

theorem covarianceGood12918_payment :
    (retDist (paperDesignP 12918).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12918)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12918_payment



end BstLean.Part269.N12918

namespace BstLean.Part269.N12918
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12918}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12918.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12918) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12918).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12918 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12918) (by norm_num) BstLean.Part268.WorldRow12918.worldPackage rfl
    BstLean.Part268.WorldRow12918.product_lower (BstLean.Part268.WorldRow12918.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12918} (hw : c ∈ Hof BstLean.Part268.WorldRow12918.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12918) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12918) (by norm_num) BstLean.Part268.WorldRow12918.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12918} (hw : c ∈ Hof BstLean.Part268.WorldRow12918.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12918) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12918).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12918) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12918_eq : scalarRow12918.targetFrame = BstLean.Part268.agent12918.frame := by
  norm_num [scalarRow12918,BstLean.Part268.agent12918]

noncomputable def frameData12918 : BstLean.Part264b.FrameData 12918 :=
  BstLean.Part269.frameData_from_numerics (n := 12918) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12918.worldPackage rfl BstLean.Part268.WorldRow12918.product_lower (BstLean.Part268.WorldRow12918.producthi.2.trans (by norm_num))
    scalarRow12918 repair12918 covarianceInputs12918 (fun i hi => sourceNumerics12918 hi)
    BstLean.Part268.agent12918.frame targetFrame12918_eq


end BstLean.Part269.N12918

namespace BstLean.Part269.N12919
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12919 : scalarRow12919.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12919, BstLean.Part268.grid12919, BstLean.Part263.worldGrid]

theorem supplies12919 (j : Fin 43) : Supply 12919 (parameters j)
    (cellLower scalarRow12919.grid (sourceIndex j))
    (cellUpper scalarRow12919.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12919.grid grid_top_bounds12919 j

theorem radii12919 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12919.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12919 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12919 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12919.grid grid_top_bounds12919 j hθ

noncomputable def covarianceInputs12919 :
    BstLean.Part263.CovarianceInputs 12919 scalarRow12919.grid parameters (caps repair12919) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12919 grid_top_bounds12919 repair12919

noncomputable def covarianceEvent12919 : Set (AgFam 12919) :=
  BstLean.Part263.covarianceEvent 12919 scalarRow12919.grid parameters

theorem covarianceEvent12919_measurable : MeasurableSet covarianceEvent12919 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12919_payment :
    (retDist (paperDesignP 12919).toCentres).real
      (agentEv (paperDesignP 12919) covarianceEvent12919)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12919

theorem localCov12919 : BstLean.Part259.LocalCovarianceOn covarianceEvent12919
    (BstLean.Part263.cell scalarRow12919.grid) (caps repair12919) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12919

theorem covarianceGood12919_payment :
    (retDist (paperDesignP 12919).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12919)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12919_payment



end BstLean.Part269.N12919

namespace BstLean.Part269.N12919
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12919}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12919.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12919) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12919).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12919 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12919) (by norm_num) BstLean.Part268.WorldRow12919.worldPackage rfl
    BstLean.Part268.WorldRow12919.product_lower (BstLean.Part268.WorldRow12919.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12919} (hw : c ∈ Hof BstLean.Part268.WorldRow12919.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12919) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12919) (by norm_num) BstLean.Part268.WorldRow12919.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12919} (hw : c ∈ Hof BstLean.Part268.WorldRow12919.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12919) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12919).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12919) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12919_eq : scalarRow12919.targetFrame = BstLean.Part268.agent12919.frame := by
  norm_num [scalarRow12919,BstLean.Part268.agent12919]

noncomputable def frameData12919 : BstLean.Part264b.FrameData 12919 :=
  BstLean.Part269.frameData_from_numerics (n := 12919) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12919.worldPackage rfl BstLean.Part268.WorldRow12919.product_lower (BstLean.Part268.WorldRow12919.producthi.2.trans (by norm_num))
    scalarRow12919 repair12919 covarianceInputs12919 (fun i hi => sourceNumerics12919 hi)
    BstLean.Part268.agent12919.frame targetFrame12919_eq


end BstLean.Part269.N12919
