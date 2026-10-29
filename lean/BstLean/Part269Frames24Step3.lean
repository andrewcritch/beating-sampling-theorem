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

namespace BstLean.Part269.N12965
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12965 : scalarRow12965.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12965, BstLean.Part268.grid12965, BstLean.Part263.worldGrid]

theorem supplies12965 (j : Fin 43) : Supply 12965 (parameters j)
    (cellLower scalarRow12965.grid (sourceIndex j))
    (cellUpper scalarRow12965.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12965.grid grid_top_bounds12965 j

theorem radii12965 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12965.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12965 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12965 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12965.grid grid_top_bounds12965 j hθ

noncomputable def covarianceInputs12965 :
    BstLean.Part263.CovarianceInputs 12965 scalarRow12965.grid parameters (caps repair12965) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12965 grid_top_bounds12965 repair12965

noncomputable def covarianceEvent12965 : Set (AgFam 12965) :=
  BstLean.Part263.covarianceEvent 12965 scalarRow12965.grid parameters

theorem covarianceEvent12965_measurable : MeasurableSet covarianceEvent12965 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12965_payment :
    (retDist (paperDesignP 12965).toCentres).real
      (agentEv (paperDesignP 12965) covarianceEvent12965)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12965

theorem localCov12965 : BstLean.Part259.LocalCovarianceOn covarianceEvent12965
    (BstLean.Part263.cell scalarRow12965.grid) (caps repair12965) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12965

theorem covarianceGood12965_payment :
    (retDist (paperDesignP 12965).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12965)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12965_payment



end BstLean.Part269.N12965

namespace BstLean.Part269.N12965
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12965}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12965.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12965) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12965).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12965 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12965) (by norm_num) BstLean.Part268.WorldRow12965.worldPackage rfl
    BstLean.Part268.WorldRow12965.product_lower (BstLean.Part268.WorldRow12965.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12965} (hw : c ∈ Hof BstLean.Part268.WorldRow12965.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12965) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12965) (by norm_num) BstLean.Part268.WorldRow12965.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12965} (hw : c ∈ Hof BstLean.Part268.WorldRow12965.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12965) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12965).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12965) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12965_eq : scalarRow12965.targetFrame = BstLean.Part268.agent12965.frame := by
  norm_num [scalarRow12965,BstLean.Part268.agent12965]

noncomputable def frameData12965 : BstLean.Part264b.FrameData 12965 :=
  BstLean.Part269.frameData_from_numerics (n := 12965) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12965.worldPackage rfl BstLean.Part268.WorldRow12965.product_lower (BstLean.Part268.WorldRow12965.producthi.2.trans (by norm_num))
    scalarRow12965 repair12965 covarianceInputs12965 (fun i hi => sourceNumerics12965 hi)
    BstLean.Part268.agent12965.frame targetFrame12965_eq


end BstLean.Part269.N12965

namespace BstLean.Part269.N12966
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12966 : scalarRow12966.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12966, BstLean.Part268.grid12966, BstLean.Part263.worldGrid]

theorem supplies12966 (j : Fin 43) : Supply 12966 (parameters j)
    (cellLower scalarRow12966.grid (sourceIndex j))
    (cellUpper scalarRow12966.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12966.grid grid_top_bounds12966 j

theorem radii12966 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12966.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12966 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12966 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12966.grid grid_top_bounds12966 j hθ

noncomputable def covarianceInputs12966 :
    BstLean.Part263.CovarianceInputs 12966 scalarRow12966.grid parameters (caps repair12966) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12966 grid_top_bounds12966 repair12966

noncomputable def covarianceEvent12966 : Set (AgFam 12966) :=
  BstLean.Part263.covarianceEvent 12966 scalarRow12966.grid parameters

theorem covarianceEvent12966_measurable : MeasurableSet covarianceEvent12966 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12966_payment :
    (retDist (paperDesignP 12966).toCentres).real
      (agentEv (paperDesignP 12966) covarianceEvent12966)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12966

theorem localCov12966 : BstLean.Part259.LocalCovarianceOn covarianceEvent12966
    (BstLean.Part263.cell scalarRow12966.grid) (caps repair12966) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12966

theorem covarianceGood12966_payment :
    (retDist (paperDesignP 12966).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12966)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12966_payment



end BstLean.Part269.N12966

namespace BstLean.Part269.N12966
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12966}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12966.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12966) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12966).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12966 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12966) (by norm_num) BstLean.Part268.WorldRow12966.worldPackage rfl
    BstLean.Part268.WorldRow12966.product_lower (BstLean.Part268.WorldRow12966.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12966} (hw : c ∈ Hof BstLean.Part268.WorldRow12966.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12966) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12966) (by norm_num) BstLean.Part268.WorldRow12966.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12966} (hw : c ∈ Hof BstLean.Part268.WorldRow12966.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12966) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12966).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12966) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12966_eq : scalarRow12966.targetFrame = BstLean.Part268.agent12966.frame := by
  norm_num [scalarRow12966,BstLean.Part268.agent12966]

noncomputable def frameData12966 : BstLean.Part264b.FrameData 12966 :=
  BstLean.Part269.frameData_from_numerics (n := 12966) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12966.worldPackage rfl BstLean.Part268.WorldRow12966.product_lower (BstLean.Part268.WorldRow12966.producthi.2.trans (by norm_num))
    scalarRow12966 repair12966 covarianceInputs12966 (fun i hi => sourceNumerics12966 hi)
    BstLean.Part268.agent12966.frame targetFrame12966_eq


end BstLean.Part269.N12966

namespace BstLean.Part269.N12967
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12967 : scalarRow12967.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12967, BstLean.Part268.grid12967, BstLean.Part263.worldGrid]

theorem supplies12967 (j : Fin 43) : Supply 12967 (parameters j)
    (cellLower scalarRow12967.grid (sourceIndex j))
    (cellUpper scalarRow12967.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12967.grid grid_top_bounds12967 j

theorem radii12967 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12967.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12967 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12967 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12967.grid grid_top_bounds12967 j hθ

noncomputable def covarianceInputs12967 :
    BstLean.Part263.CovarianceInputs 12967 scalarRow12967.grid parameters (caps repair12967) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12967 grid_top_bounds12967 repair12967

noncomputable def covarianceEvent12967 : Set (AgFam 12967) :=
  BstLean.Part263.covarianceEvent 12967 scalarRow12967.grid parameters

theorem covarianceEvent12967_measurable : MeasurableSet covarianceEvent12967 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12967_payment :
    (retDist (paperDesignP 12967).toCentres).real
      (agentEv (paperDesignP 12967) covarianceEvent12967)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12967

theorem localCov12967 : BstLean.Part259.LocalCovarianceOn covarianceEvent12967
    (BstLean.Part263.cell scalarRow12967.grid) (caps repair12967) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12967

theorem covarianceGood12967_payment :
    (retDist (paperDesignP 12967).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12967)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12967_payment



end BstLean.Part269.N12967

namespace BstLean.Part269.N12967
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12967}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12967.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12967) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12967).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12967 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12967) (by norm_num) BstLean.Part268.WorldRow12967.worldPackage rfl
    BstLean.Part268.WorldRow12967.product_lower (BstLean.Part268.WorldRow12967.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12967} (hw : c ∈ Hof BstLean.Part268.WorldRow12967.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12967) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12967) (by norm_num) BstLean.Part268.WorldRow12967.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12967} (hw : c ∈ Hof BstLean.Part268.WorldRow12967.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12967) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12967).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12967) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12967_eq : scalarRow12967.targetFrame = BstLean.Part268.agent12967.frame := by
  norm_num [scalarRow12967,BstLean.Part268.agent12967]

noncomputable def frameData12967 : BstLean.Part264b.FrameData 12967 :=
  BstLean.Part269.frameData_from_numerics (n := 12967) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12967.worldPackage rfl BstLean.Part268.WorldRow12967.product_lower (BstLean.Part268.WorldRow12967.producthi.2.trans (by norm_num))
    scalarRow12967 repair12967 covarianceInputs12967 (fun i hi => sourceNumerics12967 hi)
    BstLean.Part268.agent12967.frame targetFrame12967_eq


end BstLean.Part269.N12967

namespace BstLean.Part269.N12968
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12968 : scalarRow12968.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12968, BstLean.Part268.grid12968, BstLean.Part263.worldGrid]

theorem supplies12968 (j : Fin 43) : Supply 12968 (parameters j)
    (cellLower scalarRow12968.grid (sourceIndex j))
    (cellUpper scalarRow12968.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12968.grid grid_top_bounds12968 j

theorem radii12968 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12968.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12968 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12968 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12968.grid grid_top_bounds12968 j hθ

noncomputable def covarianceInputs12968 :
    BstLean.Part263.CovarianceInputs 12968 scalarRow12968.grid parameters (caps repair12968) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12968 grid_top_bounds12968 repair12968

noncomputable def covarianceEvent12968 : Set (AgFam 12968) :=
  BstLean.Part263.covarianceEvent 12968 scalarRow12968.grid parameters

theorem covarianceEvent12968_measurable : MeasurableSet covarianceEvent12968 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12968_payment :
    (retDist (paperDesignP 12968).toCentres).real
      (agentEv (paperDesignP 12968) covarianceEvent12968)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12968

theorem localCov12968 : BstLean.Part259.LocalCovarianceOn covarianceEvent12968
    (BstLean.Part263.cell scalarRow12968.grid) (caps repair12968) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12968

theorem covarianceGood12968_payment :
    (retDist (paperDesignP 12968).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12968)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12968_payment



end BstLean.Part269.N12968

namespace BstLean.Part269.N12968
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12968}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12968.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12968) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12968).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12968 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12968) (by norm_num) BstLean.Part268.WorldRow12968.worldPackage rfl
    BstLean.Part268.WorldRow12968.product_lower (BstLean.Part268.WorldRow12968.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12968} (hw : c ∈ Hof BstLean.Part268.WorldRow12968.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12968) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12968) (by norm_num) BstLean.Part268.WorldRow12968.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12968} (hw : c ∈ Hof BstLean.Part268.WorldRow12968.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12968) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12968).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12968) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12968_eq : scalarRow12968.targetFrame = BstLean.Part268.agent12968.frame := by
  norm_num [scalarRow12968,BstLean.Part268.agent12968]

noncomputable def frameData12968 : BstLean.Part264b.FrameData 12968 :=
  BstLean.Part269.frameData_from_numerics (n := 12968) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12968.worldPackage rfl BstLean.Part268.WorldRow12968.product_lower (BstLean.Part268.WorldRow12968.producthi.2.trans (by norm_num))
    scalarRow12968 repair12968 covarianceInputs12968 (fun i hi => sourceNumerics12968 hi)
    BstLean.Part268.agent12968.frame targetFrame12968_eq


end BstLean.Part269.N12968

namespace BstLean.Part269.N12969
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12969 : scalarRow12969.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12969, BstLean.Part268.grid12969, BstLean.Part263.worldGrid]

theorem supplies12969 (j : Fin 43) : Supply 12969 (parameters j)
    (cellLower scalarRow12969.grid (sourceIndex j))
    (cellUpper scalarRow12969.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12969.grid grid_top_bounds12969 j

theorem radii12969 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12969.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12969 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12969 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12969.grid grid_top_bounds12969 j hθ

noncomputable def covarianceInputs12969 :
    BstLean.Part263.CovarianceInputs 12969 scalarRow12969.grid parameters (caps repair12969) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12969 grid_top_bounds12969 repair12969

noncomputable def covarianceEvent12969 : Set (AgFam 12969) :=
  BstLean.Part263.covarianceEvent 12969 scalarRow12969.grid parameters

theorem covarianceEvent12969_measurable : MeasurableSet covarianceEvent12969 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12969_payment :
    (retDist (paperDesignP 12969).toCentres).real
      (agentEv (paperDesignP 12969) covarianceEvent12969)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12969

theorem localCov12969 : BstLean.Part259.LocalCovarianceOn covarianceEvent12969
    (BstLean.Part263.cell scalarRow12969.grid) (caps repair12969) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12969

theorem covarianceGood12969_payment :
    (retDist (paperDesignP 12969).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12969)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12969_payment



end BstLean.Part269.N12969

namespace BstLean.Part269.N12969
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12969}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12969.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12969) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12969).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12969 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12969) (by norm_num) BstLean.Part268.WorldRow12969.worldPackage rfl
    BstLean.Part268.WorldRow12969.product_lower (BstLean.Part268.WorldRow12969.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12969} (hw : c ∈ Hof BstLean.Part268.WorldRow12969.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12969) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12969) (by norm_num) BstLean.Part268.WorldRow12969.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12969} (hw : c ∈ Hof BstLean.Part268.WorldRow12969.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12969) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12969).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12969) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12969_eq : scalarRow12969.targetFrame = BstLean.Part268.agent12969.frame := by
  norm_num [scalarRow12969,BstLean.Part268.agent12969]

noncomputable def frameData12969 : BstLean.Part264b.FrameData 12969 :=
  BstLean.Part269.frameData_from_numerics (n := 12969) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12969.worldPackage rfl BstLean.Part268.WorldRow12969.product_lower (BstLean.Part268.WorldRow12969.producthi.2.trans (by norm_num))
    scalarRow12969 repair12969 covarianceInputs12969 (fun i hi => sourceNumerics12969 hi)
    BstLean.Part268.agent12969.frame targetFrame12969_eq


end BstLean.Part269.N12969
