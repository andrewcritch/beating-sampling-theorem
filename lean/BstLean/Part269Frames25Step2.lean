import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World25Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs25
import BstLean.Part269Rows25
import BstLean.Part269Sources25
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12985
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12985 : scalarRow12985.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12985, BstLean.Part268.grid12985, BstLean.Part263.worldGrid]

theorem supplies12985 (j : Fin 43) : Supply 12985 (parameters j)
    (cellLower scalarRow12985.grid (sourceIndex j))
    (cellUpper scalarRow12985.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12985.grid grid_top_bounds12985 j

theorem radii12985 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12985.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12985 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12985 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12985.grid grid_top_bounds12985 j hθ

noncomputable def covarianceInputs12985 :
    BstLean.Part263.CovarianceInputs 12985 scalarRow12985.grid parameters (caps repair12985) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12985 grid_top_bounds12985 repair12985

noncomputable def covarianceEvent12985 : Set (AgFam 12985) :=
  BstLean.Part263.covarianceEvent 12985 scalarRow12985.grid parameters

theorem covarianceEvent12985_measurable : MeasurableSet covarianceEvent12985 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12985_payment :
    (retDist (paperDesignP 12985).toCentres).real
      (agentEv (paperDesignP 12985) covarianceEvent12985)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12985

theorem localCov12985 : BstLean.Part259.LocalCovarianceOn covarianceEvent12985
    (BstLean.Part263.cell scalarRow12985.grid) (caps repair12985) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12985

theorem covarianceGood12985_payment :
    (retDist (paperDesignP 12985).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12985)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12985_payment



end BstLean.Part269.N12985

namespace BstLean.Part269.N12985
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12985}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12985.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12985) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12985).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12985 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12985) (by norm_num) BstLean.Part268.WorldRow12985.worldPackage rfl
    BstLean.Part268.WorldRow12985.product_lower (BstLean.Part268.WorldRow12985.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12985} (hw : c ∈ Hof BstLean.Part268.WorldRow12985.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12985) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12985) (by norm_num) BstLean.Part268.WorldRow12985.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12985} (hw : c ∈ Hof BstLean.Part268.WorldRow12985.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12985) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12985).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12985) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12985_eq : scalarRow12985.targetFrame = BstLean.Part268.agent12985.frame := by
  norm_num [scalarRow12985,BstLean.Part268.agent12985]

noncomputable def frameData12985 : BstLean.Part264b.FrameData 12985 :=
  BstLean.Part269.frameData_from_numerics (n := 12985) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12985.worldPackage rfl BstLean.Part268.WorldRow12985.product_lower (BstLean.Part268.WorldRow12985.producthi.2.trans (by norm_num))
    scalarRow12985 repair12985 covarianceInputs12985 (fun i hi => sourceNumerics12985 hi)
    BstLean.Part268.agent12985.frame targetFrame12985_eq


end BstLean.Part269.N12985

namespace BstLean.Part269.N12986
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12986 : scalarRow12986.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12986, BstLean.Part268.grid12986, BstLean.Part263.worldGrid]

theorem supplies12986 (j : Fin 43) : Supply 12986 (parameters j)
    (cellLower scalarRow12986.grid (sourceIndex j))
    (cellUpper scalarRow12986.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12986.grid grid_top_bounds12986 j

theorem radii12986 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12986.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12986 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12986 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12986.grid grid_top_bounds12986 j hθ

noncomputable def covarianceInputs12986 :
    BstLean.Part263.CovarianceInputs 12986 scalarRow12986.grid parameters (caps repair12986) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12986 grid_top_bounds12986 repair12986

noncomputable def covarianceEvent12986 : Set (AgFam 12986) :=
  BstLean.Part263.covarianceEvent 12986 scalarRow12986.grid parameters

theorem covarianceEvent12986_measurable : MeasurableSet covarianceEvent12986 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12986_payment :
    (retDist (paperDesignP 12986).toCentres).real
      (agentEv (paperDesignP 12986) covarianceEvent12986)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12986

theorem localCov12986 : BstLean.Part259.LocalCovarianceOn covarianceEvent12986
    (BstLean.Part263.cell scalarRow12986.grid) (caps repair12986) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12986

theorem covarianceGood12986_payment :
    (retDist (paperDesignP 12986).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12986)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12986_payment



end BstLean.Part269.N12986

namespace BstLean.Part269.N12986
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12986}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12986.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12986) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12986).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12986 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12986) (by norm_num) BstLean.Part268.WorldRow12986.worldPackage rfl
    BstLean.Part268.WorldRow12986.product_lower (BstLean.Part268.WorldRow12986.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12986} (hw : c ∈ Hof BstLean.Part268.WorldRow12986.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12986) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12986) (by norm_num) BstLean.Part268.WorldRow12986.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12986} (hw : c ∈ Hof BstLean.Part268.WorldRow12986.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12986) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12986).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12986) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12986_eq : scalarRow12986.targetFrame = BstLean.Part268.agent12986.frame := by
  norm_num [scalarRow12986,BstLean.Part268.agent12986]

noncomputable def frameData12986 : BstLean.Part264b.FrameData 12986 :=
  BstLean.Part269.frameData_from_numerics (n := 12986) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12986.worldPackage rfl BstLean.Part268.WorldRow12986.product_lower (BstLean.Part268.WorldRow12986.producthi.2.trans (by norm_num))
    scalarRow12986 repair12986 covarianceInputs12986 (fun i hi => sourceNumerics12986 hi)
    BstLean.Part268.agent12986.frame targetFrame12986_eq


end BstLean.Part269.N12986

namespace BstLean.Part269.N12987
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12987 : scalarRow12987.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12987, BstLean.Part268.grid12987, BstLean.Part263.worldGrid]

theorem supplies12987 (j : Fin 43) : Supply 12987 (parameters j)
    (cellLower scalarRow12987.grid (sourceIndex j))
    (cellUpper scalarRow12987.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12987.grid grid_top_bounds12987 j

theorem radii12987 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12987.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12987 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12987 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12987.grid grid_top_bounds12987 j hθ

noncomputable def covarianceInputs12987 :
    BstLean.Part263.CovarianceInputs 12987 scalarRow12987.grid parameters (caps repair12987) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12987 grid_top_bounds12987 repair12987

noncomputable def covarianceEvent12987 : Set (AgFam 12987) :=
  BstLean.Part263.covarianceEvent 12987 scalarRow12987.grid parameters

theorem covarianceEvent12987_measurable : MeasurableSet covarianceEvent12987 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12987_payment :
    (retDist (paperDesignP 12987).toCentres).real
      (agentEv (paperDesignP 12987) covarianceEvent12987)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12987

theorem localCov12987 : BstLean.Part259.LocalCovarianceOn covarianceEvent12987
    (BstLean.Part263.cell scalarRow12987.grid) (caps repair12987) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12987

theorem covarianceGood12987_payment :
    (retDist (paperDesignP 12987).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12987)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12987_payment



end BstLean.Part269.N12987

namespace BstLean.Part269.N12987
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12987}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12987.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12987) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12987).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12987 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12987) (by norm_num) BstLean.Part268.WorldRow12987.worldPackage rfl
    BstLean.Part268.WorldRow12987.product_lower (BstLean.Part268.WorldRow12987.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12987} (hw : c ∈ Hof BstLean.Part268.WorldRow12987.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12987) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12987) (by norm_num) BstLean.Part268.WorldRow12987.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12987} (hw : c ∈ Hof BstLean.Part268.WorldRow12987.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12987) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12987).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12987) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12987_eq : scalarRow12987.targetFrame = BstLean.Part268.agent12987.frame := by
  norm_num [scalarRow12987,BstLean.Part268.agent12987]

noncomputable def frameData12987 : BstLean.Part264b.FrameData 12987 :=
  BstLean.Part269.frameData_from_numerics (n := 12987) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12987.worldPackage rfl BstLean.Part268.WorldRow12987.product_lower (BstLean.Part268.WorldRow12987.producthi.2.trans (by norm_num))
    scalarRow12987 repair12987 covarianceInputs12987 (fun i hi => sourceNumerics12987 hi)
    BstLean.Part268.agent12987.frame targetFrame12987_eq


end BstLean.Part269.N12987

namespace BstLean.Part269.N12988
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12988 : scalarRow12988.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12988, BstLean.Part268.grid12988, BstLean.Part263.worldGrid]

theorem supplies12988 (j : Fin 43) : Supply 12988 (parameters j)
    (cellLower scalarRow12988.grid (sourceIndex j))
    (cellUpper scalarRow12988.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12988.grid grid_top_bounds12988 j

theorem radii12988 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12988.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12988 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12988 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12988.grid grid_top_bounds12988 j hθ

noncomputable def covarianceInputs12988 :
    BstLean.Part263.CovarianceInputs 12988 scalarRow12988.grid parameters (caps repair12988) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12988 grid_top_bounds12988 repair12988

noncomputable def covarianceEvent12988 : Set (AgFam 12988) :=
  BstLean.Part263.covarianceEvent 12988 scalarRow12988.grid parameters

theorem covarianceEvent12988_measurable : MeasurableSet covarianceEvent12988 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12988_payment :
    (retDist (paperDesignP 12988).toCentres).real
      (agentEv (paperDesignP 12988) covarianceEvent12988)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12988

theorem localCov12988 : BstLean.Part259.LocalCovarianceOn covarianceEvent12988
    (BstLean.Part263.cell scalarRow12988.grid) (caps repair12988) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12988

theorem covarianceGood12988_payment :
    (retDist (paperDesignP 12988).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12988)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12988_payment



end BstLean.Part269.N12988

namespace BstLean.Part269.N12988
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12988}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12988.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12988) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12988).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12988 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12988) (by norm_num) BstLean.Part268.WorldRow12988.worldPackage rfl
    BstLean.Part268.WorldRow12988.product_lower (BstLean.Part268.WorldRow12988.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12988} (hw : c ∈ Hof BstLean.Part268.WorldRow12988.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12988) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12988) (by norm_num) BstLean.Part268.WorldRow12988.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12988} (hw : c ∈ Hof BstLean.Part268.WorldRow12988.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12988) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12988).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12988) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12988_eq : scalarRow12988.targetFrame = BstLean.Part268.agent12988.frame := by
  norm_num [scalarRow12988,BstLean.Part268.agent12988]

noncomputable def frameData12988 : BstLean.Part264b.FrameData 12988 :=
  BstLean.Part269.frameData_from_numerics (n := 12988) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12988.worldPackage rfl BstLean.Part268.WorldRow12988.product_lower (BstLean.Part268.WorldRow12988.producthi.2.trans (by norm_num))
    scalarRow12988 repair12988 covarianceInputs12988 (fun i hi => sourceNumerics12988 hi)
    BstLean.Part268.agent12988.frame targetFrame12988_eq


end BstLean.Part269.N12988

namespace BstLean.Part269.N12989
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12989 : scalarRow12989.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12989, BstLean.Part268.grid12989, BstLean.Part263.worldGrid]

theorem supplies12989 (j : Fin 43) : Supply 12989 (parameters j)
    (cellLower scalarRow12989.grid (sourceIndex j))
    (cellUpper scalarRow12989.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12989.grid grid_top_bounds12989 j

theorem radii12989 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12989.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12989 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12989 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12989.grid grid_top_bounds12989 j hθ

noncomputable def covarianceInputs12989 :
    BstLean.Part263.CovarianceInputs 12989 scalarRow12989.grid parameters (caps repair12989) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12989 grid_top_bounds12989 repair12989

noncomputable def covarianceEvent12989 : Set (AgFam 12989) :=
  BstLean.Part263.covarianceEvent 12989 scalarRow12989.grid parameters

theorem covarianceEvent12989_measurable : MeasurableSet covarianceEvent12989 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12989_payment :
    (retDist (paperDesignP 12989).toCentres).real
      (agentEv (paperDesignP 12989) covarianceEvent12989)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12989

theorem localCov12989 : BstLean.Part259.LocalCovarianceOn covarianceEvent12989
    (BstLean.Part263.cell scalarRow12989.grid) (caps repair12989) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12989

theorem covarianceGood12989_payment :
    (retDist (paperDesignP 12989).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12989)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12989_payment



end BstLean.Part269.N12989

namespace BstLean.Part269.N12989
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12989}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12989.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12989) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12989).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12989 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12989) (by norm_num) BstLean.Part268.WorldRow12989.worldPackage rfl
    BstLean.Part268.WorldRow12989.product_lower (BstLean.Part268.WorldRow12989.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12989} (hw : c ∈ Hof BstLean.Part268.WorldRow12989.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12989) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12989) (by norm_num) BstLean.Part268.WorldRow12989.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12989} (hw : c ∈ Hof BstLean.Part268.WorldRow12989.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12989) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12989).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12989) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12989_eq : scalarRow12989.targetFrame = BstLean.Part268.agent12989.frame := by
  norm_num [scalarRow12989,BstLean.Part268.agent12989]

noncomputable def frameData12989 : BstLean.Part264b.FrameData 12989 :=
  BstLean.Part269.frameData_from_numerics (n := 12989) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12989.worldPackage rfl BstLean.Part268.WorldRow12989.product_lower (BstLean.Part268.WorldRow12989.producthi.2.trans (by norm_num))
    scalarRow12989 repair12989 covarianceInputs12989 (fun i hi => sourceNumerics12989 hi)
    BstLean.Part268.agent12989.frame targetFrame12989_eq


end BstLean.Part269.N12989
