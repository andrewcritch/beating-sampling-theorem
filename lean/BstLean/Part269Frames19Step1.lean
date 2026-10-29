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

namespace BstLean.Part269.N12830
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12830 : scalarRow12830.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12830, BstLean.Part268.grid12830, BstLean.Part263.worldGrid]

theorem supplies12830 (j : Fin 43) : Supply 12830 (parameters j)
    (cellLower scalarRow12830.grid (sourceIndex j))
    (cellUpper scalarRow12830.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12830.grid grid_top_bounds12830 j

theorem radii12830 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12830.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12830 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12830 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12830.grid grid_top_bounds12830 j hθ

noncomputable def covarianceInputs12830 :
    BstLean.Part263.CovarianceInputs 12830 scalarRow12830.grid parameters (caps repair12830) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12830 grid_top_bounds12830 repair12830

noncomputable def covarianceEvent12830 : Set (AgFam 12830) :=
  BstLean.Part263.covarianceEvent 12830 scalarRow12830.grid parameters

theorem covarianceEvent12830_measurable : MeasurableSet covarianceEvent12830 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12830_payment :
    (retDist (paperDesignP 12830).toCentres).real
      (agentEv (paperDesignP 12830) covarianceEvent12830)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12830

theorem localCov12830 : BstLean.Part259.LocalCovarianceOn covarianceEvent12830
    (BstLean.Part263.cell scalarRow12830.grid) (caps repair12830) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12830

theorem covarianceGood12830_payment :
    (retDist (paperDesignP 12830).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12830)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12830_payment



end BstLean.Part269.N12830

namespace BstLean.Part269.N12830
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12830}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12830.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12830) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12830).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12830 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12830) (by norm_num) BstLean.Part268.WorldRow12830.worldPackage rfl
    BstLean.Part268.WorldRow12830.product_lower (BstLean.Part268.WorldRow12830.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12830} (hw : c ∈ Hof BstLean.Part268.WorldRow12830.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12830) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12830) (by norm_num) BstLean.Part268.WorldRow12830.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12830} (hw : c ∈ Hof BstLean.Part268.WorldRow12830.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12830) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12830).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12830) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12830_eq : scalarRow12830.targetFrame = BstLean.Part268.agent12830.frame := by
  norm_num [scalarRow12830,BstLean.Part268.agent12830]

noncomputable def frameData12830 : BstLean.Part264b.FrameData 12830 :=
  BstLean.Part269.frameData_from_numerics (n := 12830) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12830.worldPackage rfl BstLean.Part268.WorldRow12830.product_lower (BstLean.Part268.WorldRow12830.producthi.2.trans (by norm_num))
    scalarRow12830 repair12830 covarianceInputs12830 (fun i hi => sourceNumerics12830 hi)
    BstLean.Part268.agent12830.frame targetFrame12830_eq


end BstLean.Part269.N12830

namespace BstLean.Part269.N12831
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12831 : scalarRow12831.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12831, BstLean.Part268.grid12831, BstLean.Part263.worldGrid]

theorem supplies12831 (j : Fin 43) : Supply 12831 (parameters j)
    (cellLower scalarRow12831.grid (sourceIndex j))
    (cellUpper scalarRow12831.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12831.grid grid_top_bounds12831 j

theorem radii12831 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12831.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12831 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12831 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12831.grid grid_top_bounds12831 j hθ

noncomputable def covarianceInputs12831 :
    BstLean.Part263.CovarianceInputs 12831 scalarRow12831.grid parameters (caps repair12831) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12831 grid_top_bounds12831 repair12831

noncomputable def covarianceEvent12831 : Set (AgFam 12831) :=
  BstLean.Part263.covarianceEvent 12831 scalarRow12831.grid parameters

theorem covarianceEvent12831_measurable : MeasurableSet covarianceEvent12831 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12831_payment :
    (retDist (paperDesignP 12831).toCentres).real
      (agentEv (paperDesignP 12831) covarianceEvent12831)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12831

theorem localCov12831 : BstLean.Part259.LocalCovarianceOn covarianceEvent12831
    (BstLean.Part263.cell scalarRow12831.grid) (caps repair12831) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12831

theorem covarianceGood12831_payment :
    (retDist (paperDesignP 12831).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12831)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12831_payment



end BstLean.Part269.N12831

namespace BstLean.Part269.N12831
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12831}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12831.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12831) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12831).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12831 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12831) (by norm_num) BstLean.Part268.WorldRow12831.worldPackage rfl
    BstLean.Part268.WorldRow12831.product_lower (BstLean.Part268.WorldRow12831.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12831} (hw : c ∈ Hof BstLean.Part268.WorldRow12831.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12831) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12831) (by norm_num) BstLean.Part268.WorldRow12831.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12831} (hw : c ∈ Hof BstLean.Part268.WorldRow12831.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12831) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12831).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12831) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12831_eq : scalarRow12831.targetFrame = BstLean.Part268.agent12831.frame := by
  norm_num [scalarRow12831,BstLean.Part268.agent12831]

noncomputable def frameData12831 : BstLean.Part264b.FrameData 12831 :=
  BstLean.Part269.frameData_from_numerics (n := 12831) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12831.worldPackage rfl BstLean.Part268.WorldRow12831.product_lower (BstLean.Part268.WorldRow12831.producthi.2.trans (by norm_num))
    scalarRow12831 repair12831 covarianceInputs12831 (fun i hi => sourceNumerics12831 hi)
    BstLean.Part268.agent12831.frame targetFrame12831_eq


end BstLean.Part269.N12831

namespace BstLean.Part269.N12832
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12832 : scalarRow12832.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12832, BstLean.Part268.grid12832, BstLean.Part263.worldGrid]

theorem supplies12832 (j : Fin 43) : Supply 12832 (parameters j)
    (cellLower scalarRow12832.grid (sourceIndex j))
    (cellUpper scalarRow12832.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12832.grid grid_top_bounds12832 j

theorem radii12832 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12832.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12832 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12832 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12832.grid grid_top_bounds12832 j hθ

noncomputable def covarianceInputs12832 :
    BstLean.Part263.CovarianceInputs 12832 scalarRow12832.grid parameters (caps repair12832) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12832 grid_top_bounds12832 repair12832

noncomputable def covarianceEvent12832 : Set (AgFam 12832) :=
  BstLean.Part263.covarianceEvent 12832 scalarRow12832.grid parameters

theorem covarianceEvent12832_measurable : MeasurableSet covarianceEvent12832 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12832_payment :
    (retDist (paperDesignP 12832).toCentres).real
      (agentEv (paperDesignP 12832) covarianceEvent12832)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12832

theorem localCov12832 : BstLean.Part259.LocalCovarianceOn covarianceEvent12832
    (BstLean.Part263.cell scalarRow12832.grid) (caps repair12832) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12832

theorem covarianceGood12832_payment :
    (retDist (paperDesignP 12832).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12832)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12832_payment



end BstLean.Part269.N12832

namespace BstLean.Part269.N12832
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12832}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12832.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12832) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12832).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12832 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12832) (by norm_num) BstLean.Part268.WorldRow12832.worldPackage rfl
    BstLean.Part268.WorldRow12832.product_lower (BstLean.Part268.WorldRow12832.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12832} (hw : c ∈ Hof BstLean.Part268.WorldRow12832.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12832) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12832) (by norm_num) BstLean.Part268.WorldRow12832.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12832} (hw : c ∈ Hof BstLean.Part268.WorldRow12832.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12832) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12832).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12832) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12832_eq : scalarRow12832.targetFrame = BstLean.Part268.agent12832.frame := by
  norm_num [scalarRow12832,BstLean.Part268.agent12832]

noncomputable def frameData12832 : BstLean.Part264b.FrameData 12832 :=
  BstLean.Part269.frameData_from_numerics (n := 12832) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12832.worldPackage rfl BstLean.Part268.WorldRow12832.product_lower (BstLean.Part268.WorldRow12832.producthi.2.trans (by norm_num))
    scalarRow12832 repair12832 covarianceInputs12832 (fun i hi => sourceNumerics12832 hi)
    BstLean.Part268.agent12832.frame targetFrame12832_eq


end BstLean.Part269.N12832

namespace BstLean.Part269.N12833
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12833 : scalarRow12833.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12833, BstLean.Part268.grid12833, BstLean.Part263.worldGrid]

theorem supplies12833 (j : Fin 43) : Supply 12833 (parameters j)
    (cellLower scalarRow12833.grid (sourceIndex j))
    (cellUpper scalarRow12833.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12833.grid grid_top_bounds12833 j

theorem radii12833 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12833.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12833 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12833 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12833.grid grid_top_bounds12833 j hθ

noncomputable def covarianceInputs12833 :
    BstLean.Part263.CovarianceInputs 12833 scalarRow12833.grid parameters (caps repair12833) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12833 grid_top_bounds12833 repair12833

noncomputable def covarianceEvent12833 : Set (AgFam 12833) :=
  BstLean.Part263.covarianceEvent 12833 scalarRow12833.grid parameters

theorem covarianceEvent12833_measurable : MeasurableSet covarianceEvent12833 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12833_payment :
    (retDist (paperDesignP 12833).toCentres).real
      (agentEv (paperDesignP 12833) covarianceEvent12833)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12833

theorem localCov12833 : BstLean.Part259.LocalCovarianceOn covarianceEvent12833
    (BstLean.Part263.cell scalarRow12833.grid) (caps repair12833) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12833

theorem covarianceGood12833_payment :
    (retDist (paperDesignP 12833).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12833)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12833_payment



end BstLean.Part269.N12833

namespace BstLean.Part269.N12833
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12833}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12833.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12833) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12833).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12833 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12833) (by norm_num) BstLean.Part268.WorldRow12833.worldPackage rfl
    BstLean.Part268.WorldRow12833.product_lower (BstLean.Part268.WorldRow12833.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12833} (hw : c ∈ Hof BstLean.Part268.WorldRow12833.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12833) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12833) (by norm_num) BstLean.Part268.WorldRow12833.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12833} (hw : c ∈ Hof BstLean.Part268.WorldRow12833.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12833) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12833).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12833) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12833_eq : scalarRow12833.targetFrame = BstLean.Part268.agent12833.frame := by
  norm_num [scalarRow12833,BstLean.Part268.agent12833]

noncomputable def frameData12833 : BstLean.Part264b.FrameData 12833 :=
  BstLean.Part269.frameData_from_numerics (n := 12833) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12833.worldPackage rfl BstLean.Part268.WorldRow12833.product_lower (BstLean.Part268.WorldRow12833.producthi.2.trans (by norm_num))
    scalarRow12833 repair12833 covarianceInputs12833 (fun i hi => sourceNumerics12833 hi)
    BstLean.Part268.agent12833.frame targetFrame12833_eq


end BstLean.Part269.N12833

namespace BstLean.Part269.N12834
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12834 : scalarRow12834.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12834, BstLean.Part268.grid12834, BstLean.Part263.worldGrid]

theorem supplies12834 (j : Fin 43) : Supply 12834 (parameters j)
    (cellLower scalarRow12834.grid (sourceIndex j))
    (cellUpper scalarRow12834.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12834.grid grid_top_bounds12834 j

theorem radii12834 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12834.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12834 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12834 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12834.grid grid_top_bounds12834 j hθ

noncomputable def covarianceInputs12834 :
    BstLean.Part263.CovarianceInputs 12834 scalarRow12834.grid parameters (caps repair12834) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12834 grid_top_bounds12834 repair12834

noncomputable def covarianceEvent12834 : Set (AgFam 12834) :=
  BstLean.Part263.covarianceEvent 12834 scalarRow12834.grid parameters

theorem covarianceEvent12834_measurable : MeasurableSet covarianceEvent12834 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12834_payment :
    (retDist (paperDesignP 12834).toCentres).real
      (agentEv (paperDesignP 12834) covarianceEvent12834)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12834

theorem localCov12834 : BstLean.Part259.LocalCovarianceOn covarianceEvent12834
    (BstLean.Part263.cell scalarRow12834.grid) (caps repair12834) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12834

theorem covarianceGood12834_payment :
    (retDist (paperDesignP 12834).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12834)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12834_payment



end BstLean.Part269.N12834

namespace BstLean.Part269.N12834
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12834}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12834.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12834) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12834).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12834 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12834) (by norm_num) BstLean.Part268.WorldRow12834.worldPackage rfl
    BstLean.Part268.WorldRow12834.product_lower (BstLean.Part268.WorldRow12834.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12834} (hw : c ∈ Hof BstLean.Part268.WorldRow12834.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12834) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12834) (by norm_num) BstLean.Part268.WorldRow12834.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12834} (hw : c ∈ Hof BstLean.Part268.WorldRow12834.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12834) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12834).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12834) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12834_eq : scalarRow12834.targetFrame = BstLean.Part268.agent12834.frame := by
  norm_num [scalarRow12834,BstLean.Part268.agent12834]

noncomputable def frameData12834 : BstLean.Part264b.FrameData 12834 :=
  BstLean.Part269.frameData_from_numerics (n := 12834) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12834.worldPackage rfl BstLean.Part268.WorldRow12834.product_lower (BstLean.Part268.WorldRow12834.producthi.2.trans (by norm_num))
    scalarRow12834 repair12834 covarianceInputs12834 (fun i hi => sourceNumerics12834 hi)
    BstLean.Part268.agent12834.frame targetFrame12834_eq


end BstLean.Part269.N12834
