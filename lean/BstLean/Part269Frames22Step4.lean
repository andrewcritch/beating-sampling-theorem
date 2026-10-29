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

namespace BstLean.Part269.N12920
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12920 : scalarRow12920.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12920, BstLean.Part268.grid12920, BstLean.Part263.worldGrid]

theorem supplies12920 (j : Fin 43) : Supply 12920 (parameters j)
    (cellLower scalarRow12920.grid (sourceIndex j))
    (cellUpper scalarRow12920.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12920.grid grid_top_bounds12920 j

theorem radii12920 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12920.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12920 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12920 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12920.grid grid_top_bounds12920 j hθ

noncomputable def covarianceInputs12920 :
    BstLean.Part263.CovarianceInputs 12920 scalarRow12920.grid parameters (caps repair12920) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12920 grid_top_bounds12920 repair12920

noncomputable def covarianceEvent12920 : Set (AgFam 12920) :=
  BstLean.Part263.covarianceEvent 12920 scalarRow12920.grid parameters

theorem covarianceEvent12920_measurable : MeasurableSet covarianceEvent12920 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12920_payment :
    (retDist (paperDesignP 12920).toCentres).real
      (agentEv (paperDesignP 12920) covarianceEvent12920)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12920

theorem localCov12920 : BstLean.Part259.LocalCovarianceOn covarianceEvent12920
    (BstLean.Part263.cell scalarRow12920.grid) (caps repair12920) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12920

theorem covarianceGood12920_payment :
    (retDist (paperDesignP 12920).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12920)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12920_payment



end BstLean.Part269.N12920

namespace BstLean.Part269.N12920
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12920}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12920.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12920) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12920).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12920 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12920) (by norm_num) BstLean.Part268.WorldRow12920.worldPackage rfl
    BstLean.Part268.WorldRow12920.product_lower (BstLean.Part268.WorldRow12920.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12920} (hw : c ∈ Hof BstLean.Part268.WorldRow12920.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12920) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12920) (by norm_num) BstLean.Part268.WorldRow12920.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12920} (hw : c ∈ Hof BstLean.Part268.WorldRow12920.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12920) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12920).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12920) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12920_eq : scalarRow12920.targetFrame = BstLean.Part268.agent12920.frame := by
  norm_num [scalarRow12920,BstLean.Part268.agent12920]

noncomputable def frameData12920 : BstLean.Part264b.FrameData 12920 :=
  BstLean.Part269.frameData_from_numerics (n := 12920) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12920.worldPackage rfl BstLean.Part268.WorldRow12920.product_lower (BstLean.Part268.WorldRow12920.producthi.2.trans (by norm_num))
    scalarRow12920 repair12920 covarianceInputs12920 (fun i hi => sourceNumerics12920 hi)
    BstLean.Part268.agent12920.frame targetFrame12920_eq


end BstLean.Part269.N12920

namespace BstLean.Part269.N12921
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12921 : scalarRow12921.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12921, BstLean.Part268.grid12921, BstLean.Part263.worldGrid]

theorem supplies12921 (j : Fin 43) : Supply 12921 (parameters j)
    (cellLower scalarRow12921.grid (sourceIndex j))
    (cellUpper scalarRow12921.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12921.grid grid_top_bounds12921 j

theorem radii12921 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12921.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12921 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12921 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12921.grid grid_top_bounds12921 j hθ

noncomputable def covarianceInputs12921 :
    BstLean.Part263.CovarianceInputs 12921 scalarRow12921.grid parameters (caps repair12921) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12921 grid_top_bounds12921 repair12921

noncomputable def covarianceEvent12921 : Set (AgFam 12921) :=
  BstLean.Part263.covarianceEvent 12921 scalarRow12921.grid parameters

theorem covarianceEvent12921_measurable : MeasurableSet covarianceEvent12921 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12921_payment :
    (retDist (paperDesignP 12921).toCentres).real
      (agentEv (paperDesignP 12921) covarianceEvent12921)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12921

theorem localCov12921 : BstLean.Part259.LocalCovarianceOn covarianceEvent12921
    (BstLean.Part263.cell scalarRow12921.grid) (caps repair12921) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12921

theorem covarianceGood12921_payment :
    (retDist (paperDesignP 12921).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12921)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12921_payment



end BstLean.Part269.N12921

namespace BstLean.Part269.N12921
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12921}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12921.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12921) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12921).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12921 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12921) (by norm_num) BstLean.Part268.WorldRow12921.worldPackage rfl
    BstLean.Part268.WorldRow12921.product_lower (BstLean.Part268.WorldRow12921.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12921} (hw : c ∈ Hof BstLean.Part268.WorldRow12921.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12921) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12921) (by norm_num) BstLean.Part268.WorldRow12921.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12921} (hw : c ∈ Hof BstLean.Part268.WorldRow12921.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12921) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12921).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12921) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12921_eq : scalarRow12921.targetFrame = BstLean.Part268.agent12921.frame := by
  norm_num [scalarRow12921,BstLean.Part268.agent12921]

noncomputable def frameData12921 : BstLean.Part264b.FrameData 12921 :=
  BstLean.Part269.frameData_from_numerics (n := 12921) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12921.worldPackage rfl BstLean.Part268.WorldRow12921.product_lower (BstLean.Part268.WorldRow12921.producthi.2.trans (by norm_num))
    scalarRow12921 repair12921 covarianceInputs12921 (fun i hi => sourceNumerics12921 hi)
    BstLean.Part268.agent12921.frame targetFrame12921_eq


end BstLean.Part269.N12921

namespace BstLean.Part269.N12922
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12922 : scalarRow12922.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12922, BstLean.Part268.grid12922, BstLean.Part263.worldGrid]

theorem supplies12922 (j : Fin 43) : Supply 12922 (parameters j)
    (cellLower scalarRow12922.grid (sourceIndex j))
    (cellUpper scalarRow12922.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12922.grid grid_top_bounds12922 j

theorem radii12922 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12922.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12922 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12922 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12922.grid grid_top_bounds12922 j hθ

noncomputable def covarianceInputs12922 :
    BstLean.Part263.CovarianceInputs 12922 scalarRow12922.grid parameters (caps repair12922) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12922 grid_top_bounds12922 repair12922

noncomputable def covarianceEvent12922 : Set (AgFam 12922) :=
  BstLean.Part263.covarianceEvent 12922 scalarRow12922.grid parameters

theorem covarianceEvent12922_measurable : MeasurableSet covarianceEvent12922 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12922_payment :
    (retDist (paperDesignP 12922).toCentres).real
      (agentEv (paperDesignP 12922) covarianceEvent12922)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12922

theorem localCov12922 : BstLean.Part259.LocalCovarianceOn covarianceEvent12922
    (BstLean.Part263.cell scalarRow12922.grid) (caps repair12922) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12922

theorem covarianceGood12922_payment :
    (retDist (paperDesignP 12922).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12922)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12922_payment



end BstLean.Part269.N12922

namespace BstLean.Part269.N12922
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12922}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12922.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12922) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12922).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12922 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12922) (by norm_num) BstLean.Part268.WorldRow12922.worldPackage rfl
    BstLean.Part268.WorldRow12922.product_lower (BstLean.Part268.WorldRow12922.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12922} (hw : c ∈ Hof BstLean.Part268.WorldRow12922.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12922) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12922) (by norm_num) BstLean.Part268.WorldRow12922.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12922} (hw : c ∈ Hof BstLean.Part268.WorldRow12922.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12922) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12922).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12922) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12922_eq : scalarRow12922.targetFrame = BstLean.Part268.agent12922.frame := by
  norm_num [scalarRow12922,BstLean.Part268.agent12922]

noncomputable def frameData12922 : BstLean.Part264b.FrameData 12922 :=
  BstLean.Part269.frameData_from_numerics (n := 12922) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12922.worldPackage rfl BstLean.Part268.WorldRow12922.product_lower (BstLean.Part268.WorldRow12922.producthi.2.trans (by norm_num))
    scalarRow12922 repair12922 covarianceInputs12922 (fun i hi => sourceNumerics12922 hi)
    BstLean.Part268.agent12922.frame targetFrame12922_eq


end BstLean.Part269.N12922

namespace BstLean.Part269.N12923
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12923 : scalarRow12923.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12923, BstLean.Part268.grid12923, BstLean.Part263.worldGrid]

theorem supplies12923 (j : Fin 43) : Supply 12923 (parameters j)
    (cellLower scalarRow12923.grid (sourceIndex j))
    (cellUpper scalarRow12923.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12923.grid grid_top_bounds12923 j

theorem radii12923 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12923.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12923 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12923 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12923.grid grid_top_bounds12923 j hθ

noncomputable def covarianceInputs12923 :
    BstLean.Part263.CovarianceInputs 12923 scalarRow12923.grid parameters (caps repair12923) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12923 grid_top_bounds12923 repair12923

noncomputable def covarianceEvent12923 : Set (AgFam 12923) :=
  BstLean.Part263.covarianceEvent 12923 scalarRow12923.grid parameters

theorem covarianceEvent12923_measurable : MeasurableSet covarianceEvent12923 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12923_payment :
    (retDist (paperDesignP 12923).toCentres).real
      (agentEv (paperDesignP 12923) covarianceEvent12923)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12923

theorem localCov12923 : BstLean.Part259.LocalCovarianceOn covarianceEvent12923
    (BstLean.Part263.cell scalarRow12923.grid) (caps repair12923) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12923

theorem covarianceGood12923_payment :
    (retDist (paperDesignP 12923).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12923)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12923_payment



end BstLean.Part269.N12923

namespace BstLean.Part269.N12923
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12923}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12923.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12923) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12923).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12923 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12923) (by norm_num) BstLean.Part268.WorldRow12923.worldPackage rfl
    BstLean.Part268.WorldRow12923.product_lower (BstLean.Part268.WorldRow12923.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12923} (hw : c ∈ Hof BstLean.Part268.WorldRow12923.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12923) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12923) (by norm_num) BstLean.Part268.WorldRow12923.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12923} (hw : c ∈ Hof BstLean.Part268.WorldRow12923.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12923) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12923).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12923) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12923_eq : scalarRow12923.targetFrame = BstLean.Part268.agent12923.frame := by
  norm_num [scalarRow12923,BstLean.Part268.agent12923]

noncomputable def frameData12923 : BstLean.Part264b.FrameData 12923 :=
  BstLean.Part269.frameData_from_numerics (n := 12923) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12923.worldPackage rfl BstLean.Part268.WorldRow12923.product_lower (BstLean.Part268.WorldRow12923.producthi.2.trans (by norm_num))
    scalarRow12923 repair12923 covarianceInputs12923 (fun i hi => sourceNumerics12923 hi)
    BstLean.Part268.agent12923.frame targetFrame12923_eq


end BstLean.Part269.N12923

namespace BstLean.Part269.N12924
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12924 : scalarRow12924.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12924, BstLean.Part268.grid12924, BstLean.Part263.worldGrid]

theorem supplies12924 (j : Fin 43) : Supply 12924 (parameters j)
    (cellLower scalarRow12924.grid (sourceIndex j))
    (cellUpper scalarRow12924.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12924.grid grid_top_bounds12924 j

theorem radii12924 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12924.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12924 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12924 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12924.grid grid_top_bounds12924 j hθ

noncomputable def covarianceInputs12924 :
    BstLean.Part263.CovarianceInputs 12924 scalarRow12924.grid parameters (caps repair12924) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12924 grid_top_bounds12924 repair12924

noncomputable def covarianceEvent12924 : Set (AgFam 12924) :=
  BstLean.Part263.covarianceEvent 12924 scalarRow12924.grid parameters

theorem covarianceEvent12924_measurable : MeasurableSet covarianceEvent12924 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12924_payment :
    (retDist (paperDesignP 12924).toCentres).real
      (agentEv (paperDesignP 12924) covarianceEvent12924)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12924

theorem localCov12924 : BstLean.Part259.LocalCovarianceOn covarianceEvent12924
    (BstLean.Part263.cell scalarRow12924.grid) (caps repair12924) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12924

theorem covarianceGood12924_payment :
    (retDist (paperDesignP 12924).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12924)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12924_payment



end BstLean.Part269.N12924

namespace BstLean.Part269.N12924
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12924}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12924.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12924) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12924).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12924 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12924) (by norm_num) BstLean.Part268.WorldRow12924.worldPackage rfl
    BstLean.Part268.WorldRow12924.product_lower (BstLean.Part268.WorldRow12924.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12924} (hw : c ∈ Hof BstLean.Part268.WorldRow12924.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12924) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12924) (by norm_num) BstLean.Part268.WorldRow12924.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12924} (hw : c ∈ Hof BstLean.Part268.WorldRow12924.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12924) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12924).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12924) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12924_eq : scalarRow12924.targetFrame = BstLean.Part268.agent12924.frame := by
  norm_num [scalarRow12924,BstLean.Part268.agent12924]

noncomputable def frameData12924 : BstLean.Part264b.FrameData 12924 :=
  BstLean.Part269.frameData_from_numerics (n := 12924) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12924.worldPackage rfl BstLean.Part268.WorldRow12924.product_lower (BstLean.Part268.WorldRow12924.producthi.2.trans (by norm_num))
    scalarRow12924 repair12924 covarianceInputs12924 (fun i hi => sourceNumerics12924 hi)
    BstLean.Part268.agent12924.frame targetFrame12924_eq


end BstLean.Part269.N12924
