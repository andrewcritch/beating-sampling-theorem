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

namespace BstLean.Part269.N12925
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12925 : scalarRow12925.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12925, BstLean.Part268.grid12925, BstLean.Part263.worldGrid]

theorem supplies12925 (j : Fin 43) : Supply 12925 (parameters j)
    (cellLower scalarRow12925.grid (sourceIndex j))
    (cellUpper scalarRow12925.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12925.grid grid_top_bounds12925 j

theorem radii12925 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12925.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12925 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12925 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12925.grid grid_top_bounds12925 j hθ

noncomputable def covarianceInputs12925 :
    BstLean.Part263.CovarianceInputs 12925 scalarRow12925.grid parameters (caps repair12925) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12925 grid_top_bounds12925 repair12925

noncomputable def covarianceEvent12925 : Set (AgFam 12925) :=
  BstLean.Part263.covarianceEvent 12925 scalarRow12925.grid parameters

theorem covarianceEvent12925_measurable : MeasurableSet covarianceEvent12925 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12925_payment :
    (retDist (paperDesignP 12925).toCentres).real
      (agentEv (paperDesignP 12925) covarianceEvent12925)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12925

theorem localCov12925 : BstLean.Part259.LocalCovarianceOn covarianceEvent12925
    (BstLean.Part263.cell scalarRow12925.grid) (caps repair12925) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12925

theorem covarianceGood12925_payment :
    (retDist (paperDesignP 12925).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12925)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12925_payment



end BstLean.Part269.N12925

namespace BstLean.Part269.N12925
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12925}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12925.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12925) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12925).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12925 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12925) (by norm_num) BstLean.Part268.WorldRow12925.worldPackage rfl
    BstLean.Part268.WorldRow12925.product_lower (BstLean.Part268.WorldRow12925.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12925} (hw : c ∈ Hof BstLean.Part268.WorldRow12925.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12925) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12925) (by norm_num) BstLean.Part268.WorldRow12925.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12925} (hw : c ∈ Hof BstLean.Part268.WorldRow12925.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12925) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12925).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12925) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12925_eq : scalarRow12925.targetFrame = BstLean.Part268.agent12925.frame := by
  norm_num [scalarRow12925,BstLean.Part268.agent12925]

noncomputable def frameData12925 : BstLean.Part264b.FrameData 12925 :=
  BstLean.Part269.frameData_from_numerics (n := 12925) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12925.worldPackage rfl BstLean.Part268.WorldRow12925.product_lower (BstLean.Part268.WorldRow12925.producthi.2.trans (by norm_num))
    scalarRow12925 repair12925 covarianceInputs12925 (fun i hi => sourceNumerics12925 hi)
    BstLean.Part268.agent12925.frame targetFrame12925_eq


end BstLean.Part269.N12925

namespace BstLean.Part269.N12926
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12926 : scalarRow12926.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12926, BstLean.Part268.grid12926, BstLean.Part263.worldGrid]

theorem supplies12926 (j : Fin 43) : Supply 12926 (parameters j)
    (cellLower scalarRow12926.grid (sourceIndex j))
    (cellUpper scalarRow12926.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12926.grid grid_top_bounds12926 j

theorem radii12926 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12926.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12926 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12926 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12926.grid grid_top_bounds12926 j hθ

noncomputable def covarianceInputs12926 :
    BstLean.Part263.CovarianceInputs 12926 scalarRow12926.grid parameters (caps repair12926) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12926 grid_top_bounds12926 repair12926

noncomputable def covarianceEvent12926 : Set (AgFam 12926) :=
  BstLean.Part263.covarianceEvent 12926 scalarRow12926.grid parameters

theorem covarianceEvent12926_measurable : MeasurableSet covarianceEvent12926 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12926_payment :
    (retDist (paperDesignP 12926).toCentres).real
      (agentEv (paperDesignP 12926) covarianceEvent12926)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12926

theorem localCov12926 : BstLean.Part259.LocalCovarianceOn covarianceEvent12926
    (BstLean.Part263.cell scalarRow12926.grid) (caps repair12926) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12926

theorem covarianceGood12926_payment :
    (retDist (paperDesignP 12926).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12926)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12926_payment



end BstLean.Part269.N12926

namespace BstLean.Part269.N12926
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12926}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12926.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12926) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12926).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12926 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12926) (by norm_num) BstLean.Part268.WorldRow12926.worldPackage rfl
    BstLean.Part268.WorldRow12926.product_lower (BstLean.Part268.WorldRow12926.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12926} (hw : c ∈ Hof BstLean.Part268.WorldRow12926.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12926) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12926) (by norm_num) BstLean.Part268.WorldRow12926.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12926} (hw : c ∈ Hof BstLean.Part268.WorldRow12926.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12926) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12926).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12926) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12926_eq : scalarRow12926.targetFrame = BstLean.Part268.agent12926.frame := by
  norm_num [scalarRow12926,BstLean.Part268.agent12926]

noncomputable def frameData12926 : BstLean.Part264b.FrameData 12926 :=
  BstLean.Part269.frameData_from_numerics (n := 12926) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12926.worldPackage rfl BstLean.Part268.WorldRow12926.product_lower (BstLean.Part268.WorldRow12926.producthi.2.trans (by norm_num))
    scalarRow12926 repair12926 covarianceInputs12926 (fun i hi => sourceNumerics12926 hi)
    BstLean.Part268.agent12926.frame targetFrame12926_eq


end BstLean.Part269.N12926

namespace BstLean.Part269.N12927
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12927 : scalarRow12927.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12927, BstLean.Part268.grid12927, BstLean.Part263.worldGrid]

theorem supplies12927 (j : Fin 43) : Supply 12927 (parameters j)
    (cellLower scalarRow12927.grid (sourceIndex j))
    (cellUpper scalarRow12927.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12927.grid grid_top_bounds12927 j

theorem radii12927 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12927.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12927 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12927 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12927.grid grid_top_bounds12927 j hθ

noncomputable def covarianceInputs12927 :
    BstLean.Part263.CovarianceInputs 12927 scalarRow12927.grid parameters (caps repair12927) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12927 grid_top_bounds12927 repair12927

noncomputable def covarianceEvent12927 : Set (AgFam 12927) :=
  BstLean.Part263.covarianceEvent 12927 scalarRow12927.grid parameters

theorem covarianceEvent12927_measurable : MeasurableSet covarianceEvent12927 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12927_payment :
    (retDist (paperDesignP 12927).toCentres).real
      (agentEv (paperDesignP 12927) covarianceEvent12927)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12927

theorem localCov12927 : BstLean.Part259.LocalCovarianceOn covarianceEvent12927
    (BstLean.Part263.cell scalarRow12927.grid) (caps repair12927) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12927

theorem covarianceGood12927_payment :
    (retDist (paperDesignP 12927).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12927)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12927_payment



end BstLean.Part269.N12927

namespace BstLean.Part269.N12927
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12927}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12927.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12927) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12927).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12927 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12927) (by norm_num) BstLean.Part268.WorldRow12927.worldPackage rfl
    BstLean.Part268.WorldRow12927.product_lower (BstLean.Part268.WorldRow12927.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12927} (hw : c ∈ Hof BstLean.Part268.WorldRow12927.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12927) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12927) (by norm_num) BstLean.Part268.WorldRow12927.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12927} (hw : c ∈ Hof BstLean.Part268.WorldRow12927.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12927) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12927).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12927) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12927_eq : scalarRow12927.targetFrame = BstLean.Part268.agent12927.frame := by
  norm_num [scalarRow12927,BstLean.Part268.agent12927]

noncomputable def frameData12927 : BstLean.Part264b.FrameData 12927 :=
  BstLean.Part269.frameData_from_numerics (n := 12927) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12927.worldPackage rfl BstLean.Part268.WorldRow12927.product_lower (BstLean.Part268.WorldRow12927.producthi.2.trans (by norm_num))
    scalarRow12927 repair12927 covarianceInputs12927 (fun i hi => sourceNumerics12927 hi)
    BstLean.Part268.agent12927.frame targetFrame12927_eq


end BstLean.Part269.N12927

namespace BstLean.Part269.N12928
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12928 : scalarRow12928.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12928, BstLean.Part268.grid12928, BstLean.Part263.worldGrid]

theorem supplies12928 (j : Fin 43) : Supply 12928 (parameters j)
    (cellLower scalarRow12928.grid (sourceIndex j))
    (cellUpper scalarRow12928.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12928.grid grid_top_bounds12928 j

theorem radii12928 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12928.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12928 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12928 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12928.grid grid_top_bounds12928 j hθ

noncomputable def covarianceInputs12928 :
    BstLean.Part263.CovarianceInputs 12928 scalarRow12928.grid parameters (caps repair12928) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12928 grid_top_bounds12928 repair12928

noncomputable def covarianceEvent12928 : Set (AgFam 12928) :=
  BstLean.Part263.covarianceEvent 12928 scalarRow12928.grid parameters

theorem covarianceEvent12928_measurable : MeasurableSet covarianceEvent12928 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12928_payment :
    (retDist (paperDesignP 12928).toCentres).real
      (agentEv (paperDesignP 12928) covarianceEvent12928)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12928

theorem localCov12928 : BstLean.Part259.LocalCovarianceOn covarianceEvent12928
    (BstLean.Part263.cell scalarRow12928.grid) (caps repair12928) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12928

theorem covarianceGood12928_payment :
    (retDist (paperDesignP 12928).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12928)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12928_payment



end BstLean.Part269.N12928

namespace BstLean.Part269.N12928
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12928}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12928.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12928) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12928).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12928 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12928) (by norm_num) BstLean.Part268.WorldRow12928.worldPackage rfl
    BstLean.Part268.WorldRow12928.product_lower (BstLean.Part268.WorldRow12928.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12928} (hw : c ∈ Hof BstLean.Part268.WorldRow12928.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12928) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12928) (by norm_num) BstLean.Part268.WorldRow12928.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12928} (hw : c ∈ Hof BstLean.Part268.WorldRow12928.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12928) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12928).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12928) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12928_eq : scalarRow12928.targetFrame = BstLean.Part268.agent12928.frame := by
  norm_num [scalarRow12928,BstLean.Part268.agent12928]

noncomputable def frameData12928 : BstLean.Part264b.FrameData 12928 :=
  BstLean.Part269.frameData_from_numerics (n := 12928) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12928.worldPackage rfl BstLean.Part268.WorldRow12928.product_lower (BstLean.Part268.WorldRow12928.producthi.2.trans (by norm_num))
    scalarRow12928 repair12928 covarianceInputs12928 (fun i hi => sourceNumerics12928 hi)
    BstLean.Part268.agent12928.frame targetFrame12928_eq


end BstLean.Part269.N12928

namespace BstLean.Part269.N12929
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12929 : scalarRow12929.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12929, BstLean.Part268.grid12929, BstLean.Part263.worldGrid]

theorem supplies12929 (j : Fin 43) : Supply 12929 (parameters j)
    (cellLower scalarRow12929.grid (sourceIndex j))
    (cellUpper scalarRow12929.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12929.grid grid_top_bounds12929 j

theorem radii12929 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12929.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12929 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12929 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12929.grid grid_top_bounds12929 j hθ

noncomputable def covarianceInputs12929 :
    BstLean.Part263.CovarianceInputs 12929 scalarRow12929.grid parameters (caps repair12929) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12929 grid_top_bounds12929 repair12929

noncomputable def covarianceEvent12929 : Set (AgFam 12929) :=
  BstLean.Part263.covarianceEvent 12929 scalarRow12929.grid parameters

theorem covarianceEvent12929_measurable : MeasurableSet covarianceEvent12929 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12929_payment :
    (retDist (paperDesignP 12929).toCentres).real
      (agentEv (paperDesignP 12929) covarianceEvent12929)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12929

theorem localCov12929 : BstLean.Part259.LocalCovarianceOn covarianceEvent12929
    (BstLean.Part263.cell scalarRow12929.grid) (caps repair12929) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12929

theorem covarianceGood12929_payment :
    (retDist (paperDesignP 12929).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12929)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12929_payment



end BstLean.Part269.N12929

namespace BstLean.Part269.N12929
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12929}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12929.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12929) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12929).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12929 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12929) (by norm_num) BstLean.Part268.WorldRow12929.worldPackage rfl
    BstLean.Part268.WorldRow12929.product_lower (BstLean.Part268.WorldRow12929.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12929} (hw : c ∈ Hof BstLean.Part268.WorldRow12929.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12929) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12929) (by norm_num) BstLean.Part268.WorldRow12929.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12929} (hw : c ∈ Hof BstLean.Part268.WorldRow12929.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12929) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12929).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12929) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12929_eq : scalarRow12929.targetFrame = BstLean.Part268.agent12929.frame := by
  norm_num [scalarRow12929,BstLean.Part268.agent12929]

noncomputable def frameData12929 : BstLean.Part264b.FrameData 12929 :=
  BstLean.Part269.frameData_from_numerics (n := 12929) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12929.worldPackage rfl BstLean.Part268.WorldRow12929.product_lower (BstLean.Part268.WorldRow12929.producthi.2.trans (by norm_num))
    scalarRow12929 repair12929 covarianceInputs12929 (fun i hi => sourceNumerics12929 hi)
    BstLean.Part268.agent12929.frame targetFrame12929_eq


end BstLean.Part269.N12929
