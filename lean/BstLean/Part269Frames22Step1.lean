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

namespace BstLean.Part269.N12905
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12905 : scalarRow12905.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12905, BstLean.Part268.grid12905, BstLean.Part263.worldGrid]

theorem supplies12905 (j : Fin 43) : Supply 12905 (parameters j)
    (cellLower scalarRow12905.grid (sourceIndex j))
    (cellUpper scalarRow12905.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12905.grid grid_top_bounds12905 j

theorem radii12905 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12905.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12905 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12905 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12905.grid grid_top_bounds12905 j hθ

noncomputable def covarianceInputs12905 :
    BstLean.Part263.CovarianceInputs 12905 scalarRow12905.grid parameters (caps repair12905) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12905 grid_top_bounds12905 repair12905

noncomputable def covarianceEvent12905 : Set (AgFam 12905) :=
  BstLean.Part263.covarianceEvent 12905 scalarRow12905.grid parameters

theorem covarianceEvent12905_measurable : MeasurableSet covarianceEvent12905 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12905_payment :
    (retDist (paperDesignP 12905).toCentres).real
      (agentEv (paperDesignP 12905) covarianceEvent12905)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12905

theorem localCov12905 : BstLean.Part259.LocalCovarianceOn covarianceEvent12905
    (BstLean.Part263.cell scalarRow12905.grid) (caps repair12905) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12905

theorem covarianceGood12905_payment :
    (retDist (paperDesignP 12905).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12905)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12905_payment



end BstLean.Part269.N12905

namespace BstLean.Part269.N12905
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12905}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12905.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12905) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12905).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12905 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12905) (by norm_num) BstLean.Part268.WorldRow12905.worldPackage rfl
    BstLean.Part268.WorldRow12905.product_lower (BstLean.Part268.WorldRow12905.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12905} (hw : c ∈ Hof BstLean.Part268.WorldRow12905.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12905) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12905) (by norm_num) BstLean.Part268.WorldRow12905.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12905} (hw : c ∈ Hof BstLean.Part268.WorldRow12905.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12905) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12905).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12905) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12905_eq : scalarRow12905.targetFrame = BstLean.Part268.agent12905.frame := by
  norm_num [scalarRow12905,BstLean.Part268.agent12905]

noncomputable def frameData12905 : BstLean.Part264b.FrameData 12905 :=
  BstLean.Part269.frameData_from_numerics (n := 12905) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12905.worldPackage rfl BstLean.Part268.WorldRow12905.product_lower (BstLean.Part268.WorldRow12905.producthi.2.trans (by norm_num))
    scalarRow12905 repair12905 covarianceInputs12905 (fun i hi => sourceNumerics12905 hi)
    BstLean.Part268.agent12905.frame targetFrame12905_eq


end BstLean.Part269.N12905

namespace BstLean.Part269.N12906
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12906 : scalarRow12906.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12906, BstLean.Part268.grid12906, BstLean.Part263.worldGrid]

theorem supplies12906 (j : Fin 43) : Supply 12906 (parameters j)
    (cellLower scalarRow12906.grid (sourceIndex j))
    (cellUpper scalarRow12906.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12906.grid grid_top_bounds12906 j

theorem radii12906 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12906.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12906 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12906 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12906.grid grid_top_bounds12906 j hθ

noncomputable def covarianceInputs12906 :
    BstLean.Part263.CovarianceInputs 12906 scalarRow12906.grid parameters (caps repair12906) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12906 grid_top_bounds12906 repair12906

noncomputable def covarianceEvent12906 : Set (AgFam 12906) :=
  BstLean.Part263.covarianceEvent 12906 scalarRow12906.grid parameters

theorem covarianceEvent12906_measurable : MeasurableSet covarianceEvent12906 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12906_payment :
    (retDist (paperDesignP 12906).toCentres).real
      (agentEv (paperDesignP 12906) covarianceEvent12906)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12906

theorem localCov12906 : BstLean.Part259.LocalCovarianceOn covarianceEvent12906
    (BstLean.Part263.cell scalarRow12906.grid) (caps repair12906) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12906

theorem covarianceGood12906_payment :
    (retDist (paperDesignP 12906).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12906)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12906_payment



end BstLean.Part269.N12906

namespace BstLean.Part269.N12906
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12906}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12906.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12906) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12906).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12906 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12906) (by norm_num) BstLean.Part268.WorldRow12906.worldPackage rfl
    BstLean.Part268.WorldRow12906.product_lower (BstLean.Part268.WorldRow12906.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12906} (hw : c ∈ Hof BstLean.Part268.WorldRow12906.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12906) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12906) (by norm_num) BstLean.Part268.WorldRow12906.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12906} (hw : c ∈ Hof BstLean.Part268.WorldRow12906.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12906) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12906).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12906) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12906_eq : scalarRow12906.targetFrame = BstLean.Part268.agent12906.frame := by
  norm_num [scalarRow12906,BstLean.Part268.agent12906]

noncomputable def frameData12906 : BstLean.Part264b.FrameData 12906 :=
  BstLean.Part269.frameData_from_numerics (n := 12906) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12906.worldPackage rfl BstLean.Part268.WorldRow12906.product_lower (BstLean.Part268.WorldRow12906.producthi.2.trans (by norm_num))
    scalarRow12906 repair12906 covarianceInputs12906 (fun i hi => sourceNumerics12906 hi)
    BstLean.Part268.agent12906.frame targetFrame12906_eq


end BstLean.Part269.N12906

namespace BstLean.Part269.N12907
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12907 : scalarRow12907.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12907, BstLean.Part268.grid12907, BstLean.Part263.worldGrid]

theorem supplies12907 (j : Fin 43) : Supply 12907 (parameters j)
    (cellLower scalarRow12907.grid (sourceIndex j))
    (cellUpper scalarRow12907.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12907.grid grid_top_bounds12907 j

theorem radii12907 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12907.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12907 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12907 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12907.grid grid_top_bounds12907 j hθ

noncomputable def covarianceInputs12907 :
    BstLean.Part263.CovarianceInputs 12907 scalarRow12907.grid parameters (caps repair12907) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12907 grid_top_bounds12907 repair12907

noncomputable def covarianceEvent12907 : Set (AgFam 12907) :=
  BstLean.Part263.covarianceEvent 12907 scalarRow12907.grid parameters

theorem covarianceEvent12907_measurable : MeasurableSet covarianceEvent12907 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12907_payment :
    (retDist (paperDesignP 12907).toCentres).real
      (agentEv (paperDesignP 12907) covarianceEvent12907)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12907

theorem localCov12907 : BstLean.Part259.LocalCovarianceOn covarianceEvent12907
    (BstLean.Part263.cell scalarRow12907.grid) (caps repair12907) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12907

theorem covarianceGood12907_payment :
    (retDist (paperDesignP 12907).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12907)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12907_payment



end BstLean.Part269.N12907

namespace BstLean.Part269.N12907
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12907}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12907.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12907) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12907).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12907 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12907) (by norm_num) BstLean.Part268.WorldRow12907.worldPackage rfl
    BstLean.Part268.WorldRow12907.product_lower (BstLean.Part268.WorldRow12907.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12907} (hw : c ∈ Hof BstLean.Part268.WorldRow12907.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12907) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12907) (by norm_num) BstLean.Part268.WorldRow12907.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12907} (hw : c ∈ Hof BstLean.Part268.WorldRow12907.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12907) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12907).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12907) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12907_eq : scalarRow12907.targetFrame = BstLean.Part268.agent12907.frame := by
  norm_num [scalarRow12907,BstLean.Part268.agent12907]

noncomputable def frameData12907 : BstLean.Part264b.FrameData 12907 :=
  BstLean.Part269.frameData_from_numerics (n := 12907) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12907.worldPackage rfl BstLean.Part268.WorldRow12907.product_lower (BstLean.Part268.WorldRow12907.producthi.2.trans (by norm_num))
    scalarRow12907 repair12907 covarianceInputs12907 (fun i hi => sourceNumerics12907 hi)
    BstLean.Part268.agent12907.frame targetFrame12907_eq


end BstLean.Part269.N12907

namespace BstLean.Part269.N12908
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12908 : scalarRow12908.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12908, BstLean.Part268.grid12908, BstLean.Part263.worldGrid]

theorem supplies12908 (j : Fin 43) : Supply 12908 (parameters j)
    (cellLower scalarRow12908.grid (sourceIndex j))
    (cellUpper scalarRow12908.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12908.grid grid_top_bounds12908 j

theorem radii12908 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12908.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12908 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12908 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12908.grid grid_top_bounds12908 j hθ

noncomputable def covarianceInputs12908 :
    BstLean.Part263.CovarianceInputs 12908 scalarRow12908.grid parameters (caps repair12908) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12908 grid_top_bounds12908 repair12908

noncomputable def covarianceEvent12908 : Set (AgFam 12908) :=
  BstLean.Part263.covarianceEvent 12908 scalarRow12908.grid parameters

theorem covarianceEvent12908_measurable : MeasurableSet covarianceEvent12908 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12908_payment :
    (retDist (paperDesignP 12908).toCentres).real
      (agentEv (paperDesignP 12908) covarianceEvent12908)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12908

theorem localCov12908 : BstLean.Part259.LocalCovarianceOn covarianceEvent12908
    (BstLean.Part263.cell scalarRow12908.grid) (caps repair12908) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12908

theorem covarianceGood12908_payment :
    (retDist (paperDesignP 12908).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12908)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12908_payment



end BstLean.Part269.N12908

namespace BstLean.Part269.N12908
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12908}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12908.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12908) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12908).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12908 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12908) (by norm_num) BstLean.Part268.WorldRow12908.worldPackage rfl
    BstLean.Part268.WorldRow12908.product_lower (BstLean.Part268.WorldRow12908.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12908} (hw : c ∈ Hof BstLean.Part268.WorldRow12908.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12908) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12908) (by norm_num) BstLean.Part268.WorldRow12908.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12908} (hw : c ∈ Hof BstLean.Part268.WorldRow12908.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12908) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12908).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12908) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12908_eq : scalarRow12908.targetFrame = BstLean.Part268.agent12908.frame := by
  norm_num [scalarRow12908,BstLean.Part268.agent12908]

noncomputable def frameData12908 : BstLean.Part264b.FrameData 12908 :=
  BstLean.Part269.frameData_from_numerics (n := 12908) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12908.worldPackage rfl BstLean.Part268.WorldRow12908.product_lower (BstLean.Part268.WorldRow12908.producthi.2.trans (by norm_num))
    scalarRow12908 repair12908 covarianceInputs12908 (fun i hi => sourceNumerics12908 hi)
    BstLean.Part268.agent12908.frame targetFrame12908_eq


end BstLean.Part269.N12908

namespace BstLean.Part269.N12909
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12909 : scalarRow12909.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12909, BstLean.Part268.grid12909, BstLean.Part263.worldGrid]

theorem supplies12909 (j : Fin 43) : Supply 12909 (parameters j)
    (cellLower scalarRow12909.grid (sourceIndex j))
    (cellUpper scalarRow12909.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12909.grid grid_top_bounds12909 j

theorem radii12909 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12909.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12909 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12909 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12909.grid grid_top_bounds12909 j hθ

noncomputable def covarianceInputs12909 :
    BstLean.Part263.CovarianceInputs 12909 scalarRow12909.grid parameters (caps repair12909) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12909 grid_top_bounds12909 repair12909

noncomputable def covarianceEvent12909 : Set (AgFam 12909) :=
  BstLean.Part263.covarianceEvent 12909 scalarRow12909.grid parameters

theorem covarianceEvent12909_measurable : MeasurableSet covarianceEvent12909 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12909_payment :
    (retDist (paperDesignP 12909).toCentres).real
      (agentEv (paperDesignP 12909) covarianceEvent12909)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12909

theorem localCov12909 : BstLean.Part259.LocalCovarianceOn covarianceEvent12909
    (BstLean.Part263.cell scalarRow12909.grid) (caps repair12909) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12909

theorem covarianceGood12909_payment :
    (retDist (paperDesignP 12909).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12909)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12909_payment



end BstLean.Part269.N12909

namespace BstLean.Part269.N12909
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12909}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12909.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12909) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12909).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12909 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12909) (by norm_num) BstLean.Part268.WorldRow12909.worldPackage rfl
    BstLean.Part268.WorldRow12909.product_lower (BstLean.Part268.WorldRow12909.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12909} (hw : c ∈ Hof BstLean.Part268.WorldRow12909.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12909) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12909) (by norm_num) BstLean.Part268.WorldRow12909.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12909} (hw : c ∈ Hof BstLean.Part268.WorldRow12909.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12909) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12909).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12909) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12909_eq : scalarRow12909.targetFrame = BstLean.Part268.agent12909.frame := by
  norm_num [scalarRow12909,BstLean.Part268.agent12909]

noncomputable def frameData12909 : BstLean.Part264b.FrameData 12909 :=
  BstLean.Part269.frameData_from_numerics (n := 12909) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12909.worldPackage rfl BstLean.Part268.WorldRow12909.product_lower (BstLean.Part268.WorldRow12909.producthi.2.trans (by norm_num))
    scalarRow12909 repair12909 covarianceInputs12909 (fun i hi => sourceNumerics12909 hi)
    BstLean.Part268.agent12909.frame targetFrame12909_eq


end BstLean.Part269.N12909
