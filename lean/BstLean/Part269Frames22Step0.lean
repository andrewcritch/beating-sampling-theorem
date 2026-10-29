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

namespace BstLean.Part269.N12900
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12900 : scalarRow12900.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12900, BstLean.Part268.grid12900, BstLean.Part263.worldGrid]

theorem supplies12900 (j : Fin 43) : Supply 12900 (parameters j)
    (cellLower scalarRow12900.grid (sourceIndex j))
    (cellUpper scalarRow12900.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12900.grid grid_top_bounds12900 j

theorem radii12900 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12900.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12900 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12900 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12900.grid grid_top_bounds12900 j hθ

noncomputable def covarianceInputs12900 :
    BstLean.Part263.CovarianceInputs 12900 scalarRow12900.grid parameters (caps repair12900) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12900 grid_top_bounds12900 repair12900

noncomputable def covarianceEvent12900 : Set (AgFam 12900) :=
  BstLean.Part263.covarianceEvent 12900 scalarRow12900.grid parameters

theorem covarianceEvent12900_measurable : MeasurableSet covarianceEvent12900 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12900_payment :
    (retDist (paperDesignP 12900).toCentres).real
      (agentEv (paperDesignP 12900) covarianceEvent12900)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12900

theorem localCov12900 : BstLean.Part259.LocalCovarianceOn covarianceEvent12900
    (BstLean.Part263.cell scalarRow12900.grid) (caps repair12900) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12900

theorem covarianceGood12900_payment :
    (retDist (paperDesignP 12900).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12900)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12900_payment



end BstLean.Part269.N12900

namespace BstLean.Part269.N12900
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12900}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12900.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12900) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12900).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12900 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12900) (by norm_num) BstLean.Part268.WorldRow12900.worldPackage rfl
    BstLean.Part268.WorldRow12900.product_lower (BstLean.Part268.WorldRow12900.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12900} (hw : c ∈ Hof BstLean.Part268.WorldRow12900.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12900) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12900) (by norm_num) BstLean.Part268.WorldRow12900.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12900} (hw : c ∈ Hof BstLean.Part268.WorldRow12900.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12900) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12900).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12900) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12900_eq : scalarRow12900.targetFrame = BstLean.Part268.agent12900.frame := by
  norm_num [scalarRow12900,BstLean.Part268.agent12900]

noncomputable def frameData12900 : BstLean.Part264b.FrameData 12900 :=
  BstLean.Part269.frameData_from_numerics (n := 12900) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12900.worldPackage rfl BstLean.Part268.WorldRow12900.product_lower (BstLean.Part268.WorldRow12900.producthi.2.trans (by norm_num))
    scalarRow12900 repair12900 covarianceInputs12900 (fun i hi => sourceNumerics12900 hi)
    BstLean.Part268.agent12900.frame targetFrame12900_eq


end BstLean.Part269.N12900

namespace BstLean.Part269.N12901
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12901 : scalarRow12901.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12901, BstLean.Part268.grid12901, BstLean.Part263.worldGrid]

theorem supplies12901 (j : Fin 43) : Supply 12901 (parameters j)
    (cellLower scalarRow12901.grid (sourceIndex j))
    (cellUpper scalarRow12901.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12901.grid grid_top_bounds12901 j

theorem radii12901 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12901.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12901 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12901 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12901.grid grid_top_bounds12901 j hθ

noncomputable def covarianceInputs12901 :
    BstLean.Part263.CovarianceInputs 12901 scalarRow12901.grid parameters (caps repair12901) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12901 grid_top_bounds12901 repair12901

noncomputable def covarianceEvent12901 : Set (AgFam 12901) :=
  BstLean.Part263.covarianceEvent 12901 scalarRow12901.grid parameters

theorem covarianceEvent12901_measurable : MeasurableSet covarianceEvent12901 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12901_payment :
    (retDist (paperDesignP 12901).toCentres).real
      (agentEv (paperDesignP 12901) covarianceEvent12901)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12901

theorem localCov12901 : BstLean.Part259.LocalCovarianceOn covarianceEvent12901
    (BstLean.Part263.cell scalarRow12901.grid) (caps repair12901) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12901

theorem covarianceGood12901_payment :
    (retDist (paperDesignP 12901).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12901)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12901_payment



end BstLean.Part269.N12901

namespace BstLean.Part269.N12901
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12901}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12901.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12901) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12901).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12901 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12901) (by norm_num) BstLean.Part268.WorldRow12901.worldPackage rfl
    BstLean.Part268.WorldRow12901.product_lower (BstLean.Part268.WorldRow12901.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12901} (hw : c ∈ Hof BstLean.Part268.WorldRow12901.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12901) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12901) (by norm_num) BstLean.Part268.WorldRow12901.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12901} (hw : c ∈ Hof BstLean.Part268.WorldRow12901.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12901) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12901).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12901) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12901_eq : scalarRow12901.targetFrame = BstLean.Part268.agent12901.frame := by
  norm_num [scalarRow12901,BstLean.Part268.agent12901]

noncomputable def frameData12901 : BstLean.Part264b.FrameData 12901 :=
  BstLean.Part269.frameData_from_numerics (n := 12901) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12901.worldPackage rfl BstLean.Part268.WorldRow12901.product_lower (BstLean.Part268.WorldRow12901.producthi.2.trans (by norm_num))
    scalarRow12901 repair12901 covarianceInputs12901 (fun i hi => sourceNumerics12901 hi)
    BstLean.Part268.agent12901.frame targetFrame12901_eq


end BstLean.Part269.N12901

namespace BstLean.Part269.N12902
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12902 : scalarRow12902.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12902, BstLean.Part268.grid12902, BstLean.Part263.worldGrid]

theorem supplies12902 (j : Fin 43) : Supply 12902 (parameters j)
    (cellLower scalarRow12902.grid (sourceIndex j))
    (cellUpper scalarRow12902.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12902.grid grid_top_bounds12902 j

theorem radii12902 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12902.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12902 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12902 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12902.grid grid_top_bounds12902 j hθ

noncomputable def covarianceInputs12902 :
    BstLean.Part263.CovarianceInputs 12902 scalarRow12902.grid parameters (caps repair12902) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12902 grid_top_bounds12902 repair12902

noncomputable def covarianceEvent12902 : Set (AgFam 12902) :=
  BstLean.Part263.covarianceEvent 12902 scalarRow12902.grid parameters

theorem covarianceEvent12902_measurable : MeasurableSet covarianceEvent12902 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12902_payment :
    (retDist (paperDesignP 12902).toCentres).real
      (agentEv (paperDesignP 12902) covarianceEvent12902)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12902

theorem localCov12902 : BstLean.Part259.LocalCovarianceOn covarianceEvent12902
    (BstLean.Part263.cell scalarRow12902.grid) (caps repair12902) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12902

theorem covarianceGood12902_payment :
    (retDist (paperDesignP 12902).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12902)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12902_payment



end BstLean.Part269.N12902

namespace BstLean.Part269.N12902
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12902}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12902.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12902) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12902).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12902 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12902) (by norm_num) BstLean.Part268.WorldRow12902.worldPackage rfl
    BstLean.Part268.WorldRow12902.product_lower (BstLean.Part268.WorldRow12902.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12902} (hw : c ∈ Hof BstLean.Part268.WorldRow12902.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12902) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12902) (by norm_num) BstLean.Part268.WorldRow12902.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12902} (hw : c ∈ Hof BstLean.Part268.WorldRow12902.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12902) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12902).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12902) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12902_eq : scalarRow12902.targetFrame = BstLean.Part268.agent12902.frame := by
  norm_num [scalarRow12902,BstLean.Part268.agent12902]

noncomputable def frameData12902 : BstLean.Part264b.FrameData 12902 :=
  BstLean.Part269.frameData_from_numerics (n := 12902) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12902.worldPackage rfl BstLean.Part268.WorldRow12902.product_lower (BstLean.Part268.WorldRow12902.producthi.2.trans (by norm_num))
    scalarRow12902 repair12902 covarianceInputs12902 (fun i hi => sourceNumerics12902 hi)
    BstLean.Part268.agent12902.frame targetFrame12902_eq


end BstLean.Part269.N12902

namespace BstLean.Part269.N12903
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12903 : scalarRow12903.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12903, BstLean.Part268.grid12903, BstLean.Part263.worldGrid]

theorem supplies12903 (j : Fin 43) : Supply 12903 (parameters j)
    (cellLower scalarRow12903.grid (sourceIndex j))
    (cellUpper scalarRow12903.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12903.grid grid_top_bounds12903 j

theorem radii12903 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12903.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12903 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12903 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12903.grid grid_top_bounds12903 j hθ

noncomputable def covarianceInputs12903 :
    BstLean.Part263.CovarianceInputs 12903 scalarRow12903.grid parameters (caps repair12903) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12903 grid_top_bounds12903 repair12903

noncomputable def covarianceEvent12903 : Set (AgFam 12903) :=
  BstLean.Part263.covarianceEvent 12903 scalarRow12903.grid parameters

theorem covarianceEvent12903_measurable : MeasurableSet covarianceEvent12903 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12903_payment :
    (retDist (paperDesignP 12903).toCentres).real
      (agentEv (paperDesignP 12903) covarianceEvent12903)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12903

theorem localCov12903 : BstLean.Part259.LocalCovarianceOn covarianceEvent12903
    (BstLean.Part263.cell scalarRow12903.grid) (caps repair12903) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12903

theorem covarianceGood12903_payment :
    (retDist (paperDesignP 12903).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12903)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12903_payment



end BstLean.Part269.N12903

namespace BstLean.Part269.N12903
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12903}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12903.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12903) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12903).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12903 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12903) (by norm_num) BstLean.Part268.WorldRow12903.worldPackage rfl
    BstLean.Part268.WorldRow12903.product_lower (BstLean.Part268.WorldRow12903.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12903} (hw : c ∈ Hof BstLean.Part268.WorldRow12903.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12903) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12903) (by norm_num) BstLean.Part268.WorldRow12903.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12903} (hw : c ∈ Hof BstLean.Part268.WorldRow12903.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12903) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12903).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12903) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12903_eq : scalarRow12903.targetFrame = BstLean.Part268.agent12903.frame := by
  norm_num [scalarRow12903,BstLean.Part268.agent12903]

noncomputable def frameData12903 : BstLean.Part264b.FrameData 12903 :=
  BstLean.Part269.frameData_from_numerics (n := 12903) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12903.worldPackage rfl BstLean.Part268.WorldRow12903.product_lower (BstLean.Part268.WorldRow12903.producthi.2.trans (by norm_num))
    scalarRow12903 repair12903 covarianceInputs12903 (fun i hi => sourceNumerics12903 hi)
    BstLean.Part268.agent12903.frame targetFrame12903_eq


end BstLean.Part269.N12903

namespace BstLean.Part269.N12904
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12904 : scalarRow12904.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12904, BstLean.Part268.grid12904, BstLean.Part263.worldGrid]

theorem supplies12904 (j : Fin 43) : Supply 12904 (parameters j)
    (cellLower scalarRow12904.grid (sourceIndex j))
    (cellUpper scalarRow12904.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12904.grid grid_top_bounds12904 j

theorem radii12904 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12904.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12904 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12904 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12904.grid grid_top_bounds12904 j hθ

noncomputable def covarianceInputs12904 :
    BstLean.Part263.CovarianceInputs 12904 scalarRow12904.grid parameters (caps repair12904) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12904 grid_top_bounds12904 repair12904

noncomputable def covarianceEvent12904 : Set (AgFam 12904) :=
  BstLean.Part263.covarianceEvent 12904 scalarRow12904.grid parameters

theorem covarianceEvent12904_measurable : MeasurableSet covarianceEvent12904 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12904_payment :
    (retDist (paperDesignP 12904).toCentres).real
      (agentEv (paperDesignP 12904) covarianceEvent12904)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12904

theorem localCov12904 : BstLean.Part259.LocalCovarianceOn covarianceEvent12904
    (BstLean.Part263.cell scalarRow12904.grid) (caps repair12904) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12904

theorem covarianceGood12904_payment :
    (retDist (paperDesignP 12904).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12904)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12904_payment



end BstLean.Part269.N12904

namespace BstLean.Part269.N12904
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12904}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12904.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12904) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12904).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12904 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12904) (by norm_num) BstLean.Part268.WorldRow12904.worldPackage rfl
    BstLean.Part268.WorldRow12904.product_lower (BstLean.Part268.WorldRow12904.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12904} (hw : c ∈ Hof BstLean.Part268.WorldRow12904.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12904) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12904) (by norm_num) BstLean.Part268.WorldRow12904.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12904} (hw : c ∈ Hof BstLean.Part268.WorldRow12904.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12904) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12904).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12904) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12904_eq : scalarRow12904.targetFrame = BstLean.Part268.agent12904.frame := by
  norm_num [scalarRow12904,BstLean.Part268.agent12904]

noncomputable def frameData12904 : BstLean.Part264b.FrameData 12904 :=
  BstLean.Part269.frameData_from_numerics (n := 12904) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12904.worldPackage rfl BstLean.Part268.WorldRow12904.product_lower (BstLean.Part268.WorldRow12904.producthi.2.trans (by norm_num))
    scalarRow12904 repair12904 covarianceInputs12904 (fun i hi => sourceNumerics12904 hi)
    BstLean.Part268.agent12904.frame targetFrame12904_eq


end BstLean.Part269.N12904
