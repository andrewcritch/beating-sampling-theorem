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

namespace BstLean.Part269.N12835
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12835 : scalarRow12835.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12835, BstLean.Part268.grid12835, BstLean.Part263.worldGrid]

theorem supplies12835 (j : Fin 43) : Supply 12835 (parameters j)
    (cellLower scalarRow12835.grid (sourceIndex j))
    (cellUpper scalarRow12835.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12835.grid grid_top_bounds12835 j

theorem radii12835 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12835.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12835 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12835 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12835.grid grid_top_bounds12835 j hθ

noncomputable def covarianceInputs12835 :
    BstLean.Part263.CovarianceInputs 12835 scalarRow12835.grid parameters (caps repair12835) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12835 grid_top_bounds12835 repair12835

noncomputable def covarianceEvent12835 : Set (AgFam 12835) :=
  BstLean.Part263.covarianceEvent 12835 scalarRow12835.grid parameters

theorem covarianceEvent12835_measurable : MeasurableSet covarianceEvent12835 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12835_payment :
    (retDist (paperDesignP 12835).toCentres).real
      (agentEv (paperDesignP 12835) covarianceEvent12835)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12835

theorem localCov12835 : BstLean.Part259.LocalCovarianceOn covarianceEvent12835
    (BstLean.Part263.cell scalarRow12835.grid) (caps repair12835) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12835

theorem covarianceGood12835_payment :
    (retDist (paperDesignP 12835).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12835)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12835_payment



end BstLean.Part269.N12835

namespace BstLean.Part269.N12835
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12835}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12835.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12835) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12835).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12835 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12835) (by norm_num) BstLean.Part268.WorldRow12835.worldPackage rfl
    BstLean.Part268.WorldRow12835.product_lower (BstLean.Part268.WorldRow12835.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12835} (hw : c ∈ Hof BstLean.Part268.WorldRow12835.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12835) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12835) (by norm_num) BstLean.Part268.WorldRow12835.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12835} (hw : c ∈ Hof BstLean.Part268.WorldRow12835.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12835) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12835).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12835) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12835_eq : scalarRow12835.targetFrame = BstLean.Part268.agent12835.frame := by
  norm_num [scalarRow12835,BstLean.Part268.agent12835]

noncomputable def frameData12835 : BstLean.Part264b.FrameData 12835 :=
  BstLean.Part269.frameData_from_numerics (n := 12835) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12835.worldPackage rfl BstLean.Part268.WorldRow12835.product_lower (BstLean.Part268.WorldRow12835.producthi.2.trans (by norm_num))
    scalarRow12835 repair12835 covarianceInputs12835 (fun i hi => sourceNumerics12835 hi)
    BstLean.Part268.agent12835.frame targetFrame12835_eq


end BstLean.Part269.N12835

namespace BstLean.Part269.N12836
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12836 : scalarRow12836.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12836, BstLean.Part268.grid12836, BstLean.Part263.worldGrid]

theorem supplies12836 (j : Fin 43) : Supply 12836 (parameters j)
    (cellLower scalarRow12836.grid (sourceIndex j))
    (cellUpper scalarRow12836.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12836.grid grid_top_bounds12836 j

theorem radii12836 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12836.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12836 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12836 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12836.grid grid_top_bounds12836 j hθ

noncomputable def covarianceInputs12836 :
    BstLean.Part263.CovarianceInputs 12836 scalarRow12836.grid parameters (caps repair12836) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12836 grid_top_bounds12836 repair12836

noncomputable def covarianceEvent12836 : Set (AgFam 12836) :=
  BstLean.Part263.covarianceEvent 12836 scalarRow12836.grid parameters

theorem covarianceEvent12836_measurable : MeasurableSet covarianceEvent12836 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12836_payment :
    (retDist (paperDesignP 12836).toCentres).real
      (agentEv (paperDesignP 12836) covarianceEvent12836)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12836

theorem localCov12836 : BstLean.Part259.LocalCovarianceOn covarianceEvent12836
    (BstLean.Part263.cell scalarRow12836.grid) (caps repair12836) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12836

theorem covarianceGood12836_payment :
    (retDist (paperDesignP 12836).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12836)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12836_payment



end BstLean.Part269.N12836

namespace BstLean.Part269.N12836
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12836}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12836.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12836) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12836).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12836 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12836) (by norm_num) BstLean.Part268.WorldRow12836.worldPackage rfl
    BstLean.Part268.WorldRow12836.product_lower (BstLean.Part268.WorldRow12836.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12836} (hw : c ∈ Hof BstLean.Part268.WorldRow12836.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12836) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12836) (by norm_num) BstLean.Part268.WorldRow12836.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12836} (hw : c ∈ Hof BstLean.Part268.WorldRow12836.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12836) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12836).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12836) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12836_eq : scalarRow12836.targetFrame = BstLean.Part268.agent12836.frame := by
  norm_num [scalarRow12836,BstLean.Part268.agent12836]

noncomputable def frameData12836 : BstLean.Part264b.FrameData 12836 :=
  BstLean.Part269.frameData_from_numerics (n := 12836) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12836.worldPackage rfl BstLean.Part268.WorldRow12836.product_lower (BstLean.Part268.WorldRow12836.producthi.2.trans (by norm_num))
    scalarRow12836 repair12836 covarianceInputs12836 (fun i hi => sourceNumerics12836 hi)
    BstLean.Part268.agent12836.frame targetFrame12836_eq


end BstLean.Part269.N12836

namespace BstLean.Part269.N12837
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12837 : scalarRow12837.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12837, BstLean.Part268.grid12837, BstLean.Part263.worldGrid]

theorem supplies12837 (j : Fin 43) : Supply 12837 (parameters j)
    (cellLower scalarRow12837.grid (sourceIndex j))
    (cellUpper scalarRow12837.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12837.grid grid_top_bounds12837 j

theorem radii12837 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12837.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12837 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12837 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12837.grid grid_top_bounds12837 j hθ

noncomputable def covarianceInputs12837 :
    BstLean.Part263.CovarianceInputs 12837 scalarRow12837.grid parameters (caps repair12837) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12837 grid_top_bounds12837 repair12837

noncomputable def covarianceEvent12837 : Set (AgFam 12837) :=
  BstLean.Part263.covarianceEvent 12837 scalarRow12837.grid parameters

theorem covarianceEvent12837_measurable : MeasurableSet covarianceEvent12837 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12837_payment :
    (retDist (paperDesignP 12837).toCentres).real
      (agentEv (paperDesignP 12837) covarianceEvent12837)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12837

theorem localCov12837 : BstLean.Part259.LocalCovarianceOn covarianceEvent12837
    (BstLean.Part263.cell scalarRow12837.grid) (caps repair12837) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12837

theorem covarianceGood12837_payment :
    (retDist (paperDesignP 12837).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12837)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12837_payment



end BstLean.Part269.N12837

namespace BstLean.Part269.N12837
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12837}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12837.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12837) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12837).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12837 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12837) (by norm_num) BstLean.Part268.WorldRow12837.worldPackage rfl
    BstLean.Part268.WorldRow12837.product_lower (BstLean.Part268.WorldRow12837.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12837} (hw : c ∈ Hof BstLean.Part268.WorldRow12837.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12837) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12837) (by norm_num) BstLean.Part268.WorldRow12837.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12837} (hw : c ∈ Hof BstLean.Part268.WorldRow12837.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12837) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12837).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12837) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12837_eq : scalarRow12837.targetFrame = BstLean.Part268.agent12837.frame := by
  norm_num [scalarRow12837,BstLean.Part268.agent12837]

noncomputable def frameData12837 : BstLean.Part264b.FrameData 12837 :=
  BstLean.Part269.frameData_from_numerics (n := 12837) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12837.worldPackage rfl BstLean.Part268.WorldRow12837.product_lower (BstLean.Part268.WorldRow12837.producthi.2.trans (by norm_num))
    scalarRow12837 repair12837 covarianceInputs12837 (fun i hi => sourceNumerics12837 hi)
    BstLean.Part268.agent12837.frame targetFrame12837_eq


end BstLean.Part269.N12837

namespace BstLean.Part269.N12838
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12838 : scalarRow12838.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12838, BstLean.Part268.grid12838, BstLean.Part263.worldGrid]

theorem supplies12838 (j : Fin 43) : Supply 12838 (parameters j)
    (cellLower scalarRow12838.grid (sourceIndex j))
    (cellUpper scalarRow12838.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12838.grid grid_top_bounds12838 j

theorem radii12838 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12838.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12838 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12838 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12838.grid grid_top_bounds12838 j hθ

noncomputable def covarianceInputs12838 :
    BstLean.Part263.CovarianceInputs 12838 scalarRow12838.grid parameters (caps repair12838) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12838 grid_top_bounds12838 repair12838

noncomputable def covarianceEvent12838 : Set (AgFam 12838) :=
  BstLean.Part263.covarianceEvent 12838 scalarRow12838.grid parameters

theorem covarianceEvent12838_measurable : MeasurableSet covarianceEvent12838 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12838_payment :
    (retDist (paperDesignP 12838).toCentres).real
      (agentEv (paperDesignP 12838) covarianceEvent12838)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12838

theorem localCov12838 : BstLean.Part259.LocalCovarianceOn covarianceEvent12838
    (BstLean.Part263.cell scalarRow12838.grid) (caps repair12838) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12838

theorem covarianceGood12838_payment :
    (retDist (paperDesignP 12838).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12838)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12838_payment



end BstLean.Part269.N12838

namespace BstLean.Part269.N12838
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12838}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12838.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12838) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12838).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12838 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12838) (by norm_num) BstLean.Part268.WorldRow12838.worldPackage rfl
    BstLean.Part268.WorldRow12838.product_lower (BstLean.Part268.WorldRow12838.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12838} (hw : c ∈ Hof BstLean.Part268.WorldRow12838.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12838) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12838) (by norm_num) BstLean.Part268.WorldRow12838.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12838} (hw : c ∈ Hof BstLean.Part268.WorldRow12838.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12838) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12838).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12838) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12838_eq : scalarRow12838.targetFrame = BstLean.Part268.agent12838.frame := by
  norm_num [scalarRow12838,BstLean.Part268.agent12838]

noncomputable def frameData12838 : BstLean.Part264b.FrameData 12838 :=
  BstLean.Part269.frameData_from_numerics (n := 12838) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12838.worldPackage rfl BstLean.Part268.WorldRow12838.product_lower (BstLean.Part268.WorldRow12838.producthi.2.trans (by norm_num))
    scalarRow12838 repair12838 covarianceInputs12838 (fun i hi => sourceNumerics12838 hi)
    BstLean.Part268.agent12838.frame targetFrame12838_eq


end BstLean.Part269.N12838

namespace BstLean.Part269.N12839
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12839 : scalarRow12839.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12839, BstLean.Part268.grid12839, BstLean.Part263.worldGrid]

theorem supplies12839 (j : Fin 43) : Supply 12839 (parameters j)
    (cellLower scalarRow12839.grid (sourceIndex j))
    (cellUpper scalarRow12839.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12839.grid grid_top_bounds12839 j

theorem radii12839 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12839.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12839 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12839 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12839.grid grid_top_bounds12839 j hθ

noncomputable def covarianceInputs12839 :
    BstLean.Part263.CovarianceInputs 12839 scalarRow12839.grid parameters (caps repair12839) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12839 grid_top_bounds12839 repair12839

noncomputable def covarianceEvent12839 : Set (AgFam 12839) :=
  BstLean.Part263.covarianceEvent 12839 scalarRow12839.grid parameters

theorem covarianceEvent12839_measurable : MeasurableSet covarianceEvent12839 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12839_payment :
    (retDist (paperDesignP 12839).toCentres).real
      (agentEv (paperDesignP 12839) covarianceEvent12839)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12839

theorem localCov12839 : BstLean.Part259.LocalCovarianceOn covarianceEvent12839
    (BstLean.Part263.cell scalarRow12839.grid) (caps repair12839) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12839

theorem covarianceGood12839_payment :
    (retDist (paperDesignP 12839).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12839)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12839_payment



end BstLean.Part269.N12839

namespace BstLean.Part269.N12839
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12839}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12839.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12839) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12839).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12839 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12839) (by norm_num) BstLean.Part268.WorldRow12839.worldPackage rfl
    BstLean.Part268.WorldRow12839.product_lower (BstLean.Part268.WorldRow12839.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12839} (hw : c ∈ Hof BstLean.Part268.WorldRow12839.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12839) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12839) (by norm_num) BstLean.Part268.WorldRow12839.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12839} (hw : c ∈ Hof BstLean.Part268.WorldRow12839.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12839) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12839).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12839) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12839_eq : scalarRow12839.targetFrame = BstLean.Part268.agent12839.frame := by
  norm_num [scalarRow12839,BstLean.Part268.agent12839]

noncomputable def frameData12839 : BstLean.Part264b.FrameData 12839 :=
  BstLean.Part269.frameData_from_numerics (n := 12839) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12839.worldPackage rfl BstLean.Part268.WorldRow12839.product_lower (BstLean.Part268.WorldRow12839.producthi.2.trans (by norm_num))
    scalarRow12839 repair12839 covarianceInputs12839 (fun i hi => sourceNumerics12839 hi)
    BstLean.Part268.agent12839.frame targetFrame12839_eq


end BstLean.Part269.N12839
