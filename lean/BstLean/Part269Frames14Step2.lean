import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World14Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs14
import BstLean.Part269Rows14
import BstLean.Part269Sources14
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12710
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12710 : scalarRow12710.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12710, BstLean.Part268.grid12710, BstLean.Part263.worldGrid]

theorem supplies12710 (j : Fin 43) : Supply 12710 (parameters j)
    (cellLower scalarRow12710.grid (sourceIndex j))
    (cellUpper scalarRow12710.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12710.grid grid_top_bounds12710 j

theorem radii12710 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12710.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12710 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12710 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12710.grid grid_top_bounds12710 j hθ

noncomputable def covarianceInputs12710 :
    BstLean.Part263.CovarianceInputs 12710 scalarRow12710.grid parameters (caps repair12710) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12710 grid_top_bounds12710 repair12710

noncomputable def covarianceEvent12710 : Set (AgFam 12710) :=
  BstLean.Part263.covarianceEvent 12710 scalarRow12710.grid parameters

theorem covarianceEvent12710_measurable : MeasurableSet covarianceEvent12710 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12710_payment :
    (retDist (paperDesignP 12710).toCentres).real
      (agentEv (paperDesignP 12710) covarianceEvent12710)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12710

theorem localCov12710 : BstLean.Part259.LocalCovarianceOn covarianceEvent12710
    (BstLean.Part263.cell scalarRow12710.grid) (caps repair12710) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12710

theorem covarianceGood12710_payment :
    (retDist (paperDesignP 12710).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12710)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12710_payment



end BstLean.Part269.N12710

namespace BstLean.Part269.N12710
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12710}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12710.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12710) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12710).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12710 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12710) (by norm_num) BstLean.Part268.WorldRow12710.worldPackage rfl
    BstLean.Part268.WorldRow12710.product_lower (BstLean.Part268.WorldRow12710.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12710} (hw : c ∈ Hof BstLean.Part268.WorldRow12710.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12710) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12710) (by norm_num) BstLean.Part268.WorldRow12710.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12710} (hw : c ∈ Hof BstLean.Part268.WorldRow12710.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12710) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12710).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12710) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12710_eq : scalarRow12710.targetFrame = BstLean.Part268.agent12710.frame := by
  norm_num [scalarRow12710,BstLean.Part268.agent12710]

noncomputable def frameData12710 : BstLean.Part264b.FrameData 12710 :=
  BstLean.Part269.frameData_from_numerics (n := 12710) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12710.worldPackage rfl BstLean.Part268.WorldRow12710.product_lower (BstLean.Part268.WorldRow12710.producthi.2.trans (by norm_num))
    scalarRow12710 repair12710 covarianceInputs12710 (fun i hi => sourceNumerics12710 hi)
    BstLean.Part268.agent12710.frame targetFrame12710_eq


end BstLean.Part269.N12710

namespace BstLean.Part269.N12711
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12711 : scalarRow12711.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12711, BstLean.Part268.grid12711, BstLean.Part263.worldGrid]

theorem supplies12711 (j : Fin 43) : Supply 12711 (parameters j)
    (cellLower scalarRow12711.grid (sourceIndex j))
    (cellUpper scalarRow12711.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12711.grid grid_top_bounds12711 j

theorem radii12711 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12711.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12711 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12711 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12711.grid grid_top_bounds12711 j hθ

noncomputable def covarianceInputs12711 :
    BstLean.Part263.CovarianceInputs 12711 scalarRow12711.grid parameters (caps repair12711) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12711 grid_top_bounds12711 repair12711

noncomputable def covarianceEvent12711 : Set (AgFam 12711) :=
  BstLean.Part263.covarianceEvent 12711 scalarRow12711.grid parameters

theorem covarianceEvent12711_measurable : MeasurableSet covarianceEvent12711 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12711_payment :
    (retDist (paperDesignP 12711).toCentres).real
      (agentEv (paperDesignP 12711) covarianceEvent12711)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12711

theorem localCov12711 : BstLean.Part259.LocalCovarianceOn covarianceEvent12711
    (BstLean.Part263.cell scalarRow12711.grid) (caps repair12711) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12711

theorem covarianceGood12711_payment :
    (retDist (paperDesignP 12711).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12711)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12711_payment



end BstLean.Part269.N12711

namespace BstLean.Part269.N12711
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12711}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12711.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12711) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12711).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12711 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12711) (by norm_num) BstLean.Part268.WorldRow12711.worldPackage rfl
    BstLean.Part268.WorldRow12711.product_lower (BstLean.Part268.WorldRow12711.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12711} (hw : c ∈ Hof BstLean.Part268.WorldRow12711.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12711) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12711) (by norm_num) BstLean.Part268.WorldRow12711.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12711} (hw : c ∈ Hof BstLean.Part268.WorldRow12711.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12711) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12711).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12711) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12711_eq : scalarRow12711.targetFrame = BstLean.Part268.agent12711.frame := by
  norm_num [scalarRow12711,BstLean.Part268.agent12711]

noncomputable def frameData12711 : BstLean.Part264b.FrameData 12711 :=
  BstLean.Part269.frameData_from_numerics (n := 12711) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12711.worldPackage rfl BstLean.Part268.WorldRow12711.product_lower (BstLean.Part268.WorldRow12711.producthi.2.trans (by norm_num))
    scalarRow12711 repair12711 covarianceInputs12711 (fun i hi => sourceNumerics12711 hi)
    BstLean.Part268.agent12711.frame targetFrame12711_eq


end BstLean.Part269.N12711

namespace BstLean.Part269.N12712
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12712 : scalarRow12712.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12712, BstLean.Part268.grid12712, BstLean.Part263.worldGrid]

theorem supplies12712 (j : Fin 43) : Supply 12712 (parameters j)
    (cellLower scalarRow12712.grid (sourceIndex j))
    (cellUpper scalarRow12712.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12712.grid grid_top_bounds12712 j

theorem radii12712 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12712.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12712 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12712 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12712.grid grid_top_bounds12712 j hθ

noncomputable def covarianceInputs12712 :
    BstLean.Part263.CovarianceInputs 12712 scalarRow12712.grid parameters (caps repair12712) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12712 grid_top_bounds12712 repair12712

noncomputable def covarianceEvent12712 : Set (AgFam 12712) :=
  BstLean.Part263.covarianceEvent 12712 scalarRow12712.grid parameters

theorem covarianceEvent12712_measurable : MeasurableSet covarianceEvent12712 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12712_payment :
    (retDist (paperDesignP 12712).toCentres).real
      (agentEv (paperDesignP 12712) covarianceEvent12712)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12712

theorem localCov12712 : BstLean.Part259.LocalCovarianceOn covarianceEvent12712
    (BstLean.Part263.cell scalarRow12712.grid) (caps repair12712) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12712

theorem covarianceGood12712_payment :
    (retDist (paperDesignP 12712).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12712)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12712_payment



end BstLean.Part269.N12712

namespace BstLean.Part269.N12712
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12712}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12712.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12712) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12712).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12712 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12712) (by norm_num) BstLean.Part268.WorldRow12712.worldPackage rfl
    BstLean.Part268.WorldRow12712.product_lower (BstLean.Part268.WorldRow12712.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12712} (hw : c ∈ Hof BstLean.Part268.WorldRow12712.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12712) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12712) (by norm_num) BstLean.Part268.WorldRow12712.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12712} (hw : c ∈ Hof BstLean.Part268.WorldRow12712.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12712) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12712).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12712) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12712_eq : scalarRow12712.targetFrame = BstLean.Part268.agent12712.frame := by
  norm_num [scalarRow12712,BstLean.Part268.agent12712]

noncomputable def frameData12712 : BstLean.Part264b.FrameData 12712 :=
  BstLean.Part269.frameData_from_numerics (n := 12712) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12712.worldPackage rfl BstLean.Part268.WorldRow12712.product_lower (BstLean.Part268.WorldRow12712.producthi.2.trans (by norm_num))
    scalarRow12712 repair12712 covarianceInputs12712 (fun i hi => sourceNumerics12712 hi)
    BstLean.Part268.agent12712.frame targetFrame12712_eq


end BstLean.Part269.N12712

namespace BstLean.Part269.N12713
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12713 : scalarRow12713.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12713, BstLean.Part268.grid12713, BstLean.Part263.worldGrid]

theorem supplies12713 (j : Fin 43) : Supply 12713 (parameters j)
    (cellLower scalarRow12713.grid (sourceIndex j))
    (cellUpper scalarRow12713.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12713.grid grid_top_bounds12713 j

theorem radii12713 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12713.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12713 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12713 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12713.grid grid_top_bounds12713 j hθ

noncomputable def covarianceInputs12713 :
    BstLean.Part263.CovarianceInputs 12713 scalarRow12713.grid parameters (caps repair12713) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12713 grid_top_bounds12713 repair12713

noncomputable def covarianceEvent12713 : Set (AgFam 12713) :=
  BstLean.Part263.covarianceEvent 12713 scalarRow12713.grid parameters

theorem covarianceEvent12713_measurable : MeasurableSet covarianceEvent12713 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12713_payment :
    (retDist (paperDesignP 12713).toCentres).real
      (agentEv (paperDesignP 12713) covarianceEvent12713)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12713

theorem localCov12713 : BstLean.Part259.LocalCovarianceOn covarianceEvent12713
    (BstLean.Part263.cell scalarRow12713.grid) (caps repair12713) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12713

theorem covarianceGood12713_payment :
    (retDist (paperDesignP 12713).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12713)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12713_payment



end BstLean.Part269.N12713

namespace BstLean.Part269.N12713
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12713}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12713.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12713) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12713).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12713 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12713) (by norm_num) BstLean.Part268.WorldRow12713.worldPackage rfl
    BstLean.Part268.WorldRow12713.product_lower (BstLean.Part268.WorldRow12713.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12713} (hw : c ∈ Hof BstLean.Part268.WorldRow12713.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12713) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12713) (by norm_num) BstLean.Part268.WorldRow12713.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12713} (hw : c ∈ Hof BstLean.Part268.WorldRow12713.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12713) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12713).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12713) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12713_eq : scalarRow12713.targetFrame = BstLean.Part268.agent12713.frame := by
  norm_num [scalarRow12713,BstLean.Part268.agent12713]

noncomputable def frameData12713 : BstLean.Part264b.FrameData 12713 :=
  BstLean.Part269.frameData_from_numerics (n := 12713) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12713.worldPackage rfl BstLean.Part268.WorldRow12713.product_lower (BstLean.Part268.WorldRow12713.producthi.2.trans (by norm_num))
    scalarRow12713 repair12713 covarianceInputs12713 (fun i hi => sourceNumerics12713 hi)
    BstLean.Part268.agent12713.frame targetFrame12713_eq


end BstLean.Part269.N12713

namespace BstLean.Part269.N12714
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12714 : scalarRow12714.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12714, BstLean.Part268.grid12714, BstLean.Part263.worldGrid]

theorem supplies12714 (j : Fin 43) : Supply 12714 (parameters j)
    (cellLower scalarRow12714.grid (sourceIndex j))
    (cellUpper scalarRow12714.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12714.grid grid_top_bounds12714 j

theorem radii12714 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12714.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12714 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12714 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12714.grid grid_top_bounds12714 j hθ

noncomputable def covarianceInputs12714 :
    BstLean.Part263.CovarianceInputs 12714 scalarRow12714.grid parameters (caps repair12714) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12714 grid_top_bounds12714 repair12714

noncomputable def covarianceEvent12714 : Set (AgFam 12714) :=
  BstLean.Part263.covarianceEvent 12714 scalarRow12714.grid parameters

theorem covarianceEvent12714_measurable : MeasurableSet covarianceEvent12714 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12714_payment :
    (retDist (paperDesignP 12714).toCentres).real
      (agentEv (paperDesignP 12714) covarianceEvent12714)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12714

theorem localCov12714 : BstLean.Part259.LocalCovarianceOn covarianceEvent12714
    (BstLean.Part263.cell scalarRow12714.grid) (caps repair12714) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12714

theorem covarianceGood12714_payment :
    (retDist (paperDesignP 12714).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12714)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12714_payment



end BstLean.Part269.N12714

namespace BstLean.Part269.N12714
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12714}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12714.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12714) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12714).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12714 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12714) (by norm_num) BstLean.Part268.WorldRow12714.worldPackage rfl
    BstLean.Part268.WorldRow12714.product_lower (BstLean.Part268.WorldRow12714.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12714} (hw : c ∈ Hof BstLean.Part268.WorldRow12714.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12714) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12714) (by norm_num) BstLean.Part268.WorldRow12714.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12714} (hw : c ∈ Hof BstLean.Part268.WorldRow12714.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12714) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12714).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12714) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12714_eq : scalarRow12714.targetFrame = BstLean.Part268.agent12714.frame := by
  norm_num [scalarRow12714,BstLean.Part268.agent12714]

noncomputable def frameData12714 : BstLean.Part264b.FrameData 12714 :=
  BstLean.Part269.frameData_from_numerics (n := 12714) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12714.worldPackage rfl BstLean.Part268.WorldRow12714.product_lower (BstLean.Part268.WorldRow12714.producthi.2.trans (by norm_num))
    scalarRow12714 repair12714 covarianceInputs12714 (fun i hi => sourceNumerics12714 hi)
    BstLean.Part268.agent12714.frame targetFrame12714_eq


end BstLean.Part269.N12714
