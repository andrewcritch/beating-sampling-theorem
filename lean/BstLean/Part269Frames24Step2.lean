import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World24Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs24
import BstLean.Part269Rows24
import BstLean.Part269Sources24
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12960
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12960 : scalarRow12960.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12960, BstLean.Part268.grid12960, BstLean.Part263.worldGrid]

theorem supplies12960 (j : Fin 43) : Supply 12960 (parameters j)
    (cellLower scalarRow12960.grid (sourceIndex j))
    (cellUpper scalarRow12960.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12960.grid grid_top_bounds12960 j

theorem radii12960 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12960.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12960 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12960 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12960.grid grid_top_bounds12960 j hθ

noncomputable def covarianceInputs12960 :
    BstLean.Part263.CovarianceInputs 12960 scalarRow12960.grid parameters (caps repair12960) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12960 grid_top_bounds12960 repair12960

noncomputable def covarianceEvent12960 : Set (AgFam 12960) :=
  BstLean.Part263.covarianceEvent 12960 scalarRow12960.grid parameters

theorem covarianceEvent12960_measurable : MeasurableSet covarianceEvent12960 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12960_payment :
    (retDist (paperDesignP 12960).toCentres).real
      (agentEv (paperDesignP 12960) covarianceEvent12960)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12960

theorem localCov12960 : BstLean.Part259.LocalCovarianceOn covarianceEvent12960
    (BstLean.Part263.cell scalarRow12960.grid) (caps repair12960) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12960

theorem covarianceGood12960_payment :
    (retDist (paperDesignP 12960).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12960)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12960_payment



end BstLean.Part269.N12960

namespace BstLean.Part269.N12960
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12960}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12960.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12960) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12960).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12960 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12960) (by norm_num) BstLean.Part268.WorldRow12960.worldPackage rfl
    BstLean.Part268.WorldRow12960.product_lower (BstLean.Part268.WorldRow12960.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12960} (hw : c ∈ Hof BstLean.Part268.WorldRow12960.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12960) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12960) (by norm_num) BstLean.Part268.WorldRow12960.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12960} (hw : c ∈ Hof BstLean.Part268.WorldRow12960.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12960) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12960).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12960) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12960_eq : scalarRow12960.targetFrame = BstLean.Part268.agent12960.frame := by
  norm_num [scalarRow12960,BstLean.Part268.agent12960]

noncomputable def frameData12960 : BstLean.Part264b.FrameData 12960 :=
  BstLean.Part269.frameData_from_numerics (n := 12960) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12960.worldPackage rfl BstLean.Part268.WorldRow12960.product_lower (BstLean.Part268.WorldRow12960.producthi.2.trans (by norm_num))
    scalarRow12960 repair12960 covarianceInputs12960 (fun i hi => sourceNumerics12960 hi)
    BstLean.Part268.agent12960.frame targetFrame12960_eq


end BstLean.Part269.N12960

namespace BstLean.Part269.N12961
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12961 : scalarRow12961.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12961, BstLean.Part268.grid12961, BstLean.Part263.worldGrid]

theorem supplies12961 (j : Fin 43) : Supply 12961 (parameters j)
    (cellLower scalarRow12961.grid (sourceIndex j))
    (cellUpper scalarRow12961.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12961.grid grid_top_bounds12961 j

theorem radii12961 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12961.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12961 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12961 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12961.grid grid_top_bounds12961 j hθ

noncomputable def covarianceInputs12961 :
    BstLean.Part263.CovarianceInputs 12961 scalarRow12961.grid parameters (caps repair12961) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12961 grid_top_bounds12961 repair12961

noncomputable def covarianceEvent12961 : Set (AgFam 12961) :=
  BstLean.Part263.covarianceEvent 12961 scalarRow12961.grid parameters

theorem covarianceEvent12961_measurable : MeasurableSet covarianceEvent12961 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12961_payment :
    (retDist (paperDesignP 12961).toCentres).real
      (agentEv (paperDesignP 12961) covarianceEvent12961)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12961

theorem localCov12961 : BstLean.Part259.LocalCovarianceOn covarianceEvent12961
    (BstLean.Part263.cell scalarRow12961.grid) (caps repair12961) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12961

theorem covarianceGood12961_payment :
    (retDist (paperDesignP 12961).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12961)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12961_payment



end BstLean.Part269.N12961

namespace BstLean.Part269.N12961
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12961}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12961.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12961) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12961).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12961 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12961) (by norm_num) BstLean.Part268.WorldRow12961.worldPackage rfl
    BstLean.Part268.WorldRow12961.product_lower (BstLean.Part268.WorldRow12961.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12961} (hw : c ∈ Hof BstLean.Part268.WorldRow12961.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12961) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12961) (by norm_num) BstLean.Part268.WorldRow12961.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12961} (hw : c ∈ Hof BstLean.Part268.WorldRow12961.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12961) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12961).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12961) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12961_eq : scalarRow12961.targetFrame = BstLean.Part268.agent12961.frame := by
  norm_num [scalarRow12961,BstLean.Part268.agent12961]

noncomputable def frameData12961 : BstLean.Part264b.FrameData 12961 :=
  BstLean.Part269.frameData_from_numerics (n := 12961) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12961.worldPackage rfl BstLean.Part268.WorldRow12961.product_lower (BstLean.Part268.WorldRow12961.producthi.2.trans (by norm_num))
    scalarRow12961 repair12961 covarianceInputs12961 (fun i hi => sourceNumerics12961 hi)
    BstLean.Part268.agent12961.frame targetFrame12961_eq


end BstLean.Part269.N12961

namespace BstLean.Part269.N12962
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12962 : scalarRow12962.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12962, BstLean.Part268.grid12962, BstLean.Part263.worldGrid]

theorem supplies12962 (j : Fin 43) : Supply 12962 (parameters j)
    (cellLower scalarRow12962.grid (sourceIndex j))
    (cellUpper scalarRow12962.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12962.grid grid_top_bounds12962 j

theorem radii12962 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12962.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12962 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12962 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12962.grid grid_top_bounds12962 j hθ

noncomputable def covarianceInputs12962 :
    BstLean.Part263.CovarianceInputs 12962 scalarRow12962.grid parameters (caps repair12962) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12962 grid_top_bounds12962 repair12962

noncomputable def covarianceEvent12962 : Set (AgFam 12962) :=
  BstLean.Part263.covarianceEvent 12962 scalarRow12962.grid parameters

theorem covarianceEvent12962_measurable : MeasurableSet covarianceEvent12962 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12962_payment :
    (retDist (paperDesignP 12962).toCentres).real
      (agentEv (paperDesignP 12962) covarianceEvent12962)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12962

theorem localCov12962 : BstLean.Part259.LocalCovarianceOn covarianceEvent12962
    (BstLean.Part263.cell scalarRow12962.grid) (caps repair12962) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12962

theorem covarianceGood12962_payment :
    (retDist (paperDesignP 12962).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12962)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12962_payment



end BstLean.Part269.N12962

namespace BstLean.Part269.N12962
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12962}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12962.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12962) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12962).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12962 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12962) (by norm_num) BstLean.Part268.WorldRow12962.worldPackage rfl
    BstLean.Part268.WorldRow12962.product_lower (BstLean.Part268.WorldRow12962.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12962} (hw : c ∈ Hof BstLean.Part268.WorldRow12962.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12962) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12962) (by norm_num) BstLean.Part268.WorldRow12962.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12962} (hw : c ∈ Hof BstLean.Part268.WorldRow12962.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12962) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12962).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12962) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12962_eq : scalarRow12962.targetFrame = BstLean.Part268.agent12962.frame := by
  norm_num [scalarRow12962,BstLean.Part268.agent12962]

noncomputable def frameData12962 : BstLean.Part264b.FrameData 12962 :=
  BstLean.Part269.frameData_from_numerics (n := 12962) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12962.worldPackage rfl BstLean.Part268.WorldRow12962.product_lower (BstLean.Part268.WorldRow12962.producthi.2.trans (by norm_num))
    scalarRow12962 repair12962 covarianceInputs12962 (fun i hi => sourceNumerics12962 hi)
    BstLean.Part268.agent12962.frame targetFrame12962_eq


end BstLean.Part269.N12962

namespace BstLean.Part269.N12963
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12963 : scalarRow12963.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12963, BstLean.Part268.grid12963, BstLean.Part263.worldGrid]

theorem supplies12963 (j : Fin 43) : Supply 12963 (parameters j)
    (cellLower scalarRow12963.grid (sourceIndex j))
    (cellUpper scalarRow12963.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12963.grid grid_top_bounds12963 j

theorem radii12963 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12963.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12963 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12963 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12963.grid grid_top_bounds12963 j hθ

noncomputable def covarianceInputs12963 :
    BstLean.Part263.CovarianceInputs 12963 scalarRow12963.grid parameters (caps repair12963) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12963 grid_top_bounds12963 repair12963

noncomputable def covarianceEvent12963 : Set (AgFam 12963) :=
  BstLean.Part263.covarianceEvent 12963 scalarRow12963.grid parameters

theorem covarianceEvent12963_measurable : MeasurableSet covarianceEvent12963 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12963_payment :
    (retDist (paperDesignP 12963).toCentres).real
      (agentEv (paperDesignP 12963) covarianceEvent12963)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12963

theorem localCov12963 : BstLean.Part259.LocalCovarianceOn covarianceEvent12963
    (BstLean.Part263.cell scalarRow12963.grid) (caps repair12963) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12963

theorem covarianceGood12963_payment :
    (retDist (paperDesignP 12963).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12963)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12963_payment



end BstLean.Part269.N12963

namespace BstLean.Part269.N12963
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12963}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12963.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12963) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12963).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12963 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12963) (by norm_num) BstLean.Part268.WorldRow12963.worldPackage rfl
    BstLean.Part268.WorldRow12963.product_lower (BstLean.Part268.WorldRow12963.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12963} (hw : c ∈ Hof BstLean.Part268.WorldRow12963.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12963) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12963) (by norm_num) BstLean.Part268.WorldRow12963.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12963} (hw : c ∈ Hof BstLean.Part268.WorldRow12963.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12963) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12963).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12963) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12963_eq : scalarRow12963.targetFrame = BstLean.Part268.agent12963.frame := by
  norm_num [scalarRow12963,BstLean.Part268.agent12963]

noncomputable def frameData12963 : BstLean.Part264b.FrameData 12963 :=
  BstLean.Part269.frameData_from_numerics (n := 12963) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12963.worldPackage rfl BstLean.Part268.WorldRow12963.product_lower (BstLean.Part268.WorldRow12963.producthi.2.trans (by norm_num))
    scalarRow12963 repair12963 covarianceInputs12963 (fun i hi => sourceNumerics12963 hi)
    BstLean.Part268.agent12963.frame targetFrame12963_eq


end BstLean.Part269.N12963

namespace BstLean.Part269.N12964
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12964 : scalarRow12964.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12964, BstLean.Part268.grid12964, BstLean.Part263.worldGrid]

theorem supplies12964 (j : Fin 43) : Supply 12964 (parameters j)
    (cellLower scalarRow12964.grid (sourceIndex j))
    (cellUpper scalarRow12964.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12964.grid grid_top_bounds12964 j

theorem radii12964 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12964.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12964 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12964 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12964.grid grid_top_bounds12964 j hθ

noncomputable def covarianceInputs12964 :
    BstLean.Part263.CovarianceInputs 12964 scalarRow12964.grid parameters (caps repair12964) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12964 grid_top_bounds12964 repair12964

noncomputable def covarianceEvent12964 : Set (AgFam 12964) :=
  BstLean.Part263.covarianceEvent 12964 scalarRow12964.grid parameters

theorem covarianceEvent12964_measurable : MeasurableSet covarianceEvent12964 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12964_payment :
    (retDist (paperDesignP 12964).toCentres).real
      (agentEv (paperDesignP 12964) covarianceEvent12964)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12964

theorem localCov12964 : BstLean.Part259.LocalCovarianceOn covarianceEvent12964
    (BstLean.Part263.cell scalarRow12964.grid) (caps repair12964) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12964

theorem covarianceGood12964_payment :
    (retDist (paperDesignP 12964).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12964)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12964_payment



end BstLean.Part269.N12964

namespace BstLean.Part269.N12964
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12964}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12964.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12964) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12964).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12964 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12964) (by norm_num) BstLean.Part268.WorldRow12964.worldPackage rfl
    BstLean.Part268.WorldRow12964.product_lower (BstLean.Part268.WorldRow12964.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12964} (hw : c ∈ Hof BstLean.Part268.WorldRow12964.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12964) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12964) (by norm_num) BstLean.Part268.WorldRow12964.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12964} (hw : c ∈ Hof BstLean.Part268.WorldRow12964.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12964) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12964).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12964) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12964_eq : scalarRow12964.targetFrame = BstLean.Part268.agent12964.frame := by
  norm_num [scalarRow12964,BstLean.Part268.agent12964]

noncomputable def frameData12964 : BstLean.Part264b.FrameData 12964 :=
  BstLean.Part269.frameData_from_numerics (n := 12964) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12964.worldPackage rfl BstLean.Part268.WorldRow12964.product_lower (BstLean.Part268.WorldRow12964.producthi.2.trans (by norm_num))
    scalarRow12964 repair12964 covarianceInputs12964 (fun i hi => sourceNumerics12964 hi)
    BstLean.Part268.agent12964.frame targetFrame12964_eq


end BstLean.Part269.N12964
