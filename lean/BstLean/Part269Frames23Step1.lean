import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World23Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs23
import BstLean.Part269Rows23
import BstLean.Part269Sources23
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12930
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12930 : scalarRow12930.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12930, BstLean.Part268.grid12930, BstLean.Part263.worldGrid]

theorem supplies12930 (j : Fin 43) : Supply 12930 (parameters j)
    (cellLower scalarRow12930.grid (sourceIndex j))
    (cellUpper scalarRow12930.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12930.grid grid_top_bounds12930 j

theorem radii12930 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12930.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12930 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12930 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12930.grid grid_top_bounds12930 j hθ

noncomputable def covarianceInputs12930 :
    BstLean.Part263.CovarianceInputs 12930 scalarRow12930.grid parameters (caps repair12930) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12930 grid_top_bounds12930 repair12930

noncomputable def covarianceEvent12930 : Set (AgFam 12930) :=
  BstLean.Part263.covarianceEvent 12930 scalarRow12930.grid parameters

theorem covarianceEvent12930_measurable : MeasurableSet covarianceEvent12930 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12930_payment :
    (retDist (paperDesignP 12930).toCentres).real
      (agentEv (paperDesignP 12930) covarianceEvent12930)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12930

theorem localCov12930 : BstLean.Part259.LocalCovarianceOn covarianceEvent12930
    (BstLean.Part263.cell scalarRow12930.grid) (caps repair12930) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12930

theorem covarianceGood12930_payment :
    (retDist (paperDesignP 12930).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12930)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12930_payment



end BstLean.Part269.N12930

namespace BstLean.Part269.N12930
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12930}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12930.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12930) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12930).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12930 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12930) (by norm_num) BstLean.Part268.WorldRow12930.worldPackage rfl
    BstLean.Part268.WorldRow12930.product_lower (BstLean.Part268.WorldRow12930.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12930} (hw : c ∈ Hof BstLean.Part268.WorldRow12930.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12930) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12930) (by norm_num) BstLean.Part268.WorldRow12930.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12930} (hw : c ∈ Hof BstLean.Part268.WorldRow12930.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12930) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12930).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12930) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12930_eq : scalarRow12930.targetFrame = BstLean.Part268.agent12930.frame := by
  norm_num [scalarRow12930,BstLean.Part268.agent12930]

noncomputable def frameData12930 : BstLean.Part264b.FrameData 12930 :=
  BstLean.Part269.frameData_from_numerics (n := 12930) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12930.worldPackage rfl BstLean.Part268.WorldRow12930.product_lower (BstLean.Part268.WorldRow12930.producthi.2.trans (by norm_num))
    scalarRow12930 repair12930 covarianceInputs12930 (fun i hi => sourceNumerics12930 hi)
    BstLean.Part268.agent12930.frame targetFrame12930_eq


end BstLean.Part269.N12930

namespace BstLean.Part269.N12931
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12931 : scalarRow12931.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12931, BstLean.Part268.grid12931, BstLean.Part263.worldGrid]

theorem supplies12931 (j : Fin 43) : Supply 12931 (parameters j)
    (cellLower scalarRow12931.grid (sourceIndex j))
    (cellUpper scalarRow12931.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12931.grid grid_top_bounds12931 j

theorem radii12931 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12931.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12931 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12931 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12931.grid grid_top_bounds12931 j hθ

noncomputable def covarianceInputs12931 :
    BstLean.Part263.CovarianceInputs 12931 scalarRow12931.grid parameters (caps repair12931) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12931 grid_top_bounds12931 repair12931

noncomputable def covarianceEvent12931 : Set (AgFam 12931) :=
  BstLean.Part263.covarianceEvent 12931 scalarRow12931.grid parameters

theorem covarianceEvent12931_measurable : MeasurableSet covarianceEvent12931 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12931_payment :
    (retDist (paperDesignP 12931).toCentres).real
      (agentEv (paperDesignP 12931) covarianceEvent12931)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12931

theorem localCov12931 : BstLean.Part259.LocalCovarianceOn covarianceEvent12931
    (BstLean.Part263.cell scalarRow12931.grid) (caps repair12931) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12931

theorem covarianceGood12931_payment :
    (retDist (paperDesignP 12931).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12931)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12931_payment



end BstLean.Part269.N12931

namespace BstLean.Part269.N12931
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12931}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12931.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12931) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12931).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12931 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12931) (by norm_num) BstLean.Part268.WorldRow12931.worldPackage rfl
    BstLean.Part268.WorldRow12931.product_lower (BstLean.Part268.WorldRow12931.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12931} (hw : c ∈ Hof BstLean.Part268.WorldRow12931.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12931) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12931) (by norm_num) BstLean.Part268.WorldRow12931.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12931} (hw : c ∈ Hof BstLean.Part268.WorldRow12931.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12931) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12931).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12931) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12931_eq : scalarRow12931.targetFrame = BstLean.Part268.agent12931.frame := by
  norm_num [scalarRow12931,BstLean.Part268.agent12931]

noncomputable def frameData12931 : BstLean.Part264b.FrameData 12931 :=
  BstLean.Part269.frameData_from_numerics (n := 12931) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12931.worldPackage rfl BstLean.Part268.WorldRow12931.product_lower (BstLean.Part268.WorldRow12931.producthi.2.trans (by norm_num))
    scalarRow12931 repair12931 covarianceInputs12931 (fun i hi => sourceNumerics12931 hi)
    BstLean.Part268.agent12931.frame targetFrame12931_eq


end BstLean.Part269.N12931

namespace BstLean.Part269.N12932
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12932 : scalarRow12932.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12932, BstLean.Part268.grid12932, BstLean.Part263.worldGrid]

theorem supplies12932 (j : Fin 43) : Supply 12932 (parameters j)
    (cellLower scalarRow12932.grid (sourceIndex j))
    (cellUpper scalarRow12932.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12932.grid grid_top_bounds12932 j

theorem radii12932 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12932.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12932 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12932 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12932.grid grid_top_bounds12932 j hθ

noncomputable def covarianceInputs12932 :
    BstLean.Part263.CovarianceInputs 12932 scalarRow12932.grid parameters (caps repair12932) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12932 grid_top_bounds12932 repair12932

noncomputable def covarianceEvent12932 : Set (AgFam 12932) :=
  BstLean.Part263.covarianceEvent 12932 scalarRow12932.grid parameters

theorem covarianceEvent12932_measurable : MeasurableSet covarianceEvent12932 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12932_payment :
    (retDist (paperDesignP 12932).toCentres).real
      (agentEv (paperDesignP 12932) covarianceEvent12932)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12932

theorem localCov12932 : BstLean.Part259.LocalCovarianceOn covarianceEvent12932
    (BstLean.Part263.cell scalarRow12932.grid) (caps repair12932) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12932

theorem covarianceGood12932_payment :
    (retDist (paperDesignP 12932).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12932)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12932_payment



end BstLean.Part269.N12932

namespace BstLean.Part269.N12932
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12932}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12932.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12932) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12932).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12932 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12932) (by norm_num) BstLean.Part268.WorldRow12932.worldPackage rfl
    BstLean.Part268.WorldRow12932.product_lower (BstLean.Part268.WorldRow12932.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12932} (hw : c ∈ Hof BstLean.Part268.WorldRow12932.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12932) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12932) (by norm_num) BstLean.Part268.WorldRow12932.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12932} (hw : c ∈ Hof BstLean.Part268.WorldRow12932.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12932) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12932).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12932) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12932_eq : scalarRow12932.targetFrame = BstLean.Part268.agent12932.frame := by
  norm_num [scalarRow12932,BstLean.Part268.agent12932]

noncomputable def frameData12932 : BstLean.Part264b.FrameData 12932 :=
  BstLean.Part269.frameData_from_numerics (n := 12932) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12932.worldPackage rfl BstLean.Part268.WorldRow12932.product_lower (BstLean.Part268.WorldRow12932.producthi.2.trans (by norm_num))
    scalarRow12932 repair12932 covarianceInputs12932 (fun i hi => sourceNumerics12932 hi)
    BstLean.Part268.agent12932.frame targetFrame12932_eq


end BstLean.Part269.N12932

namespace BstLean.Part269.N12933
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12933 : scalarRow12933.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12933, BstLean.Part268.grid12933, BstLean.Part263.worldGrid]

theorem supplies12933 (j : Fin 43) : Supply 12933 (parameters j)
    (cellLower scalarRow12933.grid (sourceIndex j))
    (cellUpper scalarRow12933.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12933.grid grid_top_bounds12933 j

theorem radii12933 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12933.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12933 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12933 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12933.grid grid_top_bounds12933 j hθ

noncomputable def covarianceInputs12933 :
    BstLean.Part263.CovarianceInputs 12933 scalarRow12933.grid parameters (caps repair12933) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12933 grid_top_bounds12933 repair12933

noncomputable def covarianceEvent12933 : Set (AgFam 12933) :=
  BstLean.Part263.covarianceEvent 12933 scalarRow12933.grid parameters

theorem covarianceEvent12933_measurable : MeasurableSet covarianceEvent12933 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12933_payment :
    (retDist (paperDesignP 12933).toCentres).real
      (agentEv (paperDesignP 12933) covarianceEvent12933)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12933

theorem localCov12933 : BstLean.Part259.LocalCovarianceOn covarianceEvent12933
    (BstLean.Part263.cell scalarRow12933.grid) (caps repair12933) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12933

theorem covarianceGood12933_payment :
    (retDist (paperDesignP 12933).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12933)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12933_payment



end BstLean.Part269.N12933

namespace BstLean.Part269.N12933
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12933}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12933.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12933) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12933).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12933 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12933) (by norm_num) BstLean.Part268.WorldRow12933.worldPackage rfl
    BstLean.Part268.WorldRow12933.product_lower (BstLean.Part268.WorldRow12933.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12933} (hw : c ∈ Hof BstLean.Part268.WorldRow12933.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12933) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12933) (by norm_num) BstLean.Part268.WorldRow12933.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12933} (hw : c ∈ Hof BstLean.Part268.WorldRow12933.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12933) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12933).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12933) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12933_eq : scalarRow12933.targetFrame = BstLean.Part268.agent12933.frame := by
  norm_num [scalarRow12933,BstLean.Part268.agent12933]

noncomputable def frameData12933 : BstLean.Part264b.FrameData 12933 :=
  BstLean.Part269.frameData_from_numerics (n := 12933) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12933.worldPackage rfl BstLean.Part268.WorldRow12933.product_lower (BstLean.Part268.WorldRow12933.producthi.2.trans (by norm_num))
    scalarRow12933 repair12933 covarianceInputs12933 (fun i hi => sourceNumerics12933 hi)
    BstLean.Part268.agent12933.frame targetFrame12933_eq


end BstLean.Part269.N12933

namespace BstLean.Part269.N12934
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12934 : scalarRow12934.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12934, BstLean.Part268.grid12934, BstLean.Part263.worldGrid]

theorem supplies12934 (j : Fin 43) : Supply 12934 (parameters j)
    (cellLower scalarRow12934.grid (sourceIndex j))
    (cellUpper scalarRow12934.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12934.grid grid_top_bounds12934 j

theorem radii12934 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12934.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12934 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12934 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12934.grid grid_top_bounds12934 j hθ

noncomputable def covarianceInputs12934 :
    BstLean.Part263.CovarianceInputs 12934 scalarRow12934.grid parameters (caps repair12934) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12934 grid_top_bounds12934 repair12934

noncomputable def covarianceEvent12934 : Set (AgFam 12934) :=
  BstLean.Part263.covarianceEvent 12934 scalarRow12934.grid parameters

theorem covarianceEvent12934_measurable : MeasurableSet covarianceEvent12934 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12934_payment :
    (retDist (paperDesignP 12934).toCentres).real
      (agentEv (paperDesignP 12934) covarianceEvent12934)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12934

theorem localCov12934 : BstLean.Part259.LocalCovarianceOn covarianceEvent12934
    (BstLean.Part263.cell scalarRow12934.grid) (caps repair12934) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12934

theorem covarianceGood12934_payment :
    (retDist (paperDesignP 12934).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12934)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12934_payment



end BstLean.Part269.N12934

namespace BstLean.Part269.N12934
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12934}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12934.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12934) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12934).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12934 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12934) (by norm_num) BstLean.Part268.WorldRow12934.worldPackage rfl
    BstLean.Part268.WorldRow12934.product_lower (BstLean.Part268.WorldRow12934.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12934} (hw : c ∈ Hof BstLean.Part268.WorldRow12934.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12934) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12934) (by norm_num) BstLean.Part268.WorldRow12934.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12934} (hw : c ∈ Hof BstLean.Part268.WorldRow12934.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12934) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12934).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12934) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12934_eq : scalarRow12934.targetFrame = BstLean.Part268.agent12934.frame := by
  norm_num [scalarRow12934,BstLean.Part268.agent12934]

noncomputable def frameData12934 : BstLean.Part264b.FrameData 12934 :=
  BstLean.Part269.frameData_from_numerics (n := 12934) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12934.worldPackage rfl BstLean.Part268.WorldRow12934.product_lower (BstLean.Part268.WorldRow12934.producthi.2.trans (by norm_num))
    scalarRow12934 repair12934 covarianceInputs12934 (fun i hi => sourceNumerics12934 hi)
    BstLean.Part268.agent12934.frame targetFrame12934_eq


end BstLean.Part269.N12934
