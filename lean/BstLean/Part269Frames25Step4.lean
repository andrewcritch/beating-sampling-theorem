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

namespace BstLean.Part269.N12995
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12995 : scalarRow12995.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12995, BstLean.Part268.grid12995, BstLean.Part263.worldGrid]

theorem supplies12995 (j : Fin 43) : Supply 12995 (parameters j)
    (cellLower scalarRow12995.grid (sourceIndex j))
    (cellUpper scalarRow12995.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12995.grid grid_top_bounds12995 j

theorem radii12995 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12995.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12995 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12995 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12995.grid grid_top_bounds12995 j hθ

noncomputable def covarianceInputs12995 :
    BstLean.Part263.CovarianceInputs 12995 scalarRow12995.grid parameters (caps repair12995) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12995 grid_top_bounds12995 repair12995

noncomputable def covarianceEvent12995 : Set (AgFam 12995) :=
  BstLean.Part263.covarianceEvent 12995 scalarRow12995.grid parameters

theorem covarianceEvent12995_measurable : MeasurableSet covarianceEvent12995 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12995_payment :
    (retDist (paperDesignP 12995).toCentres).real
      (agentEv (paperDesignP 12995) covarianceEvent12995)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12995

theorem localCov12995 : BstLean.Part259.LocalCovarianceOn covarianceEvent12995
    (BstLean.Part263.cell scalarRow12995.grid) (caps repair12995) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12995

theorem covarianceGood12995_payment :
    (retDist (paperDesignP 12995).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12995)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12995_payment



end BstLean.Part269.N12995

namespace BstLean.Part269.N12995
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12995}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12995.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12995) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12995).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12995 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12995) (by norm_num) BstLean.Part268.WorldRow12995.worldPackage rfl
    BstLean.Part268.WorldRow12995.product_lower (BstLean.Part268.WorldRow12995.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12995} (hw : c ∈ Hof BstLean.Part268.WorldRow12995.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12995) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12995) (by norm_num) BstLean.Part268.WorldRow12995.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12995} (hw : c ∈ Hof BstLean.Part268.WorldRow12995.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12995) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12995).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12995) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12995_eq : scalarRow12995.targetFrame = BstLean.Part268.agent12995.frame := by
  norm_num [scalarRow12995,BstLean.Part268.agent12995]

noncomputable def frameData12995 : BstLean.Part264b.FrameData 12995 :=
  BstLean.Part269.frameData_from_numerics (n := 12995) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12995.worldPackage rfl BstLean.Part268.WorldRow12995.product_lower (BstLean.Part268.WorldRow12995.producthi.2.trans (by norm_num))
    scalarRow12995 repair12995 covarianceInputs12995 (fun i hi => sourceNumerics12995 hi)
    BstLean.Part268.agent12995.frame targetFrame12995_eq


end BstLean.Part269.N12995

namespace BstLean.Part269.N12996
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12996 : scalarRow12996.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12996, BstLean.Part268.grid12996, BstLean.Part263.worldGrid]

theorem supplies12996 (j : Fin 43) : Supply 12996 (parameters j)
    (cellLower scalarRow12996.grid (sourceIndex j))
    (cellUpper scalarRow12996.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12996.grid grid_top_bounds12996 j

theorem radii12996 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12996.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12996 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12996 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12996.grid grid_top_bounds12996 j hθ

noncomputable def covarianceInputs12996 :
    BstLean.Part263.CovarianceInputs 12996 scalarRow12996.grid parameters (caps repair12996) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12996 grid_top_bounds12996 repair12996

noncomputable def covarianceEvent12996 : Set (AgFam 12996) :=
  BstLean.Part263.covarianceEvent 12996 scalarRow12996.grid parameters

theorem covarianceEvent12996_measurable : MeasurableSet covarianceEvent12996 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12996_payment :
    (retDist (paperDesignP 12996).toCentres).real
      (agentEv (paperDesignP 12996) covarianceEvent12996)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12996

theorem localCov12996 : BstLean.Part259.LocalCovarianceOn covarianceEvent12996
    (BstLean.Part263.cell scalarRow12996.grid) (caps repair12996) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12996

theorem covarianceGood12996_payment :
    (retDist (paperDesignP 12996).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12996)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12996_payment



end BstLean.Part269.N12996

namespace BstLean.Part269.N12996
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12996}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12996.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12996) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12996).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12996 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12996) (by norm_num) BstLean.Part268.WorldRow12996.worldPackage rfl
    BstLean.Part268.WorldRow12996.product_lower (BstLean.Part268.WorldRow12996.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12996} (hw : c ∈ Hof BstLean.Part268.WorldRow12996.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12996) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12996) (by norm_num) BstLean.Part268.WorldRow12996.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12996} (hw : c ∈ Hof BstLean.Part268.WorldRow12996.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12996) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12996).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12996) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12996_eq : scalarRow12996.targetFrame = BstLean.Part268.agent12996.frame := by
  norm_num [scalarRow12996,BstLean.Part268.agent12996]

noncomputable def frameData12996 : BstLean.Part264b.FrameData 12996 :=
  BstLean.Part269.frameData_from_numerics (n := 12996) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12996.worldPackage rfl BstLean.Part268.WorldRow12996.product_lower (BstLean.Part268.WorldRow12996.producthi.2.trans (by norm_num))
    scalarRow12996 repair12996 covarianceInputs12996 (fun i hi => sourceNumerics12996 hi)
    BstLean.Part268.agent12996.frame targetFrame12996_eq


end BstLean.Part269.N12996

namespace BstLean.Part269.N12997
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12997 : scalarRow12997.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12997, BstLean.Part268.grid12997, BstLean.Part263.worldGrid]

theorem supplies12997 (j : Fin 43) : Supply 12997 (parameters j)
    (cellLower scalarRow12997.grid (sourceIndex j))
    (cellUpper scalarRow12997.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12997.grid grid_top_bounds12997 j

theorem radii12997 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12997.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12997 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12997 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12997.grid grid_top_bounds12997 j hθ

noncomputable def covarianceInputs12997 :
    BstLean.Part263.CovarianceInputs 12997 scalarRow12997.grid parameters (caps repair12997) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12997 grid_top_bounds12997 repair12997

noncomputable def covarianceEvent12997 : Set (AgFam 12997) :=
  BstLean.Part263.covarianceEvent 12997 scalarRow12997.grid parameters

theorem covarianceEvent12997_measurable : MeasurableSet covarianceEvent12997 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12997_payment :
    (retDist (paperDesignP 12997).toCentres).real
      (agentEv (paperDesignP 12997) covarianceEvent12997)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12997

theorem localCov12997 : BstLean.Part259.LocalCovarianceOn covarianceEvent12997
    (BstLean.Part263.cell scalarRow12997.grid) (caps repair12997) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12997

theorem covarianceGood12997_payment :
    (retDist (paperDesignP 12997).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12997)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12997_payment



end BstLean.Part269.N12997

namespace BstLean.Part269.N12997
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12997}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12997.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12997) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12997).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12997 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12997) (by norm_num) BstLean.Part268.WorldRow12997.worldPackage rfl
    BstLean.Part268.WorldRow12997.product_lower (BstLean.Part268.WorldRow12997.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12997} (hw : c ∈ Hof BstLean.Part268.WorldRow12997.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12997) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12997) (by norm_num) BstLean.Part268.WorldRow12997.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12997} (hw : c ∈ Hof BstLean.Part268.WorldRow12997.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12997) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12997).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12997) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12997_eq : scalarRow12997.targetFrame = BstLean.Part268.agent12997.frame := by
  norm_num [scalarRow12997,BstLean.Part268.agent12997]

noncomputable def frameData12997 : BstLean.Part264b.FrameData 12997 :=
  BstLean.Part269.frameData_from_numerics (n := 12997) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12997.worldPackage rfl BstLean.Part268.WorldRow12997.product_lower (BstLean.Part268.WorldRow12997.producthi.2.trans (by norm_num))
    scalarRow12997 repair12997 covarianceInputs12997 (fun i hi => sourceNumerics12997 hi)
    BstLean.Part268.agent12997.frame targetFrame12997_eq


end BstLean.Part269.N12997

namespace BstLean.Part269.N12998
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12998 : scalarRow12998.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12998, BstLean.Part268.grid12998, BstLean.Part263.worldGrid]

theorem supplies12998 (j : Fin 43) : Supply 12998 (parameters j)
    (cellLower scalarRow12998.grid (sourceIndex j))
    (cellUpper scalarRow12998.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12998.grid grid_top_bounds12998 j

theorem radii12998 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12998.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12998 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12998 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12998.grid grid_top_bounds12998 j hθ

noncomputable def covarianceInputs12998 :
    BstLean.Part263.CovarianceInputs 12998 scalarRow12998.grid parameters (caps repair12998) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12998 grid_top_bounds12998 repair12998

noncomputable def covarianceEvent12998 : Set (AgFam 12998) :=
  BstLean.Part263.covarianceEvent 12998 scalarRow12998.grid parameters

theorem covarianceEvent12998_measurable : MeasurableSet covarianceEvent12998 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12998_payment :
    (retDist (paperDesignP 12998).toCentres).real
      (agentEv (paperDesignP 12998) covarianceEvent12998)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12998

theorem localCov12998 : BstLean.Part259.LocalCovarianceOn covarianceEvent12998
    (BstLean.Part263.cell scalarRow12998.grid) (caps repair12998) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12998

theorem covarianceGood12998_payment :
    (retDist (paperDesignP 12998).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12998)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12998_payment



end BstLean.Part269.N12998

namespace BstLean.Part269.N12998
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12998}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12998.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12998) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12998).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12998 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12998) (by norm_num) BstLean.Part268.WorldRow12998.worldPackage rfl
    BstLean.Part268.WorldRow12998.product_lower (BstLean.Part268.WorldRow12998.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12998} (hw : c ∈ Hof BstLean.Part268.WorldRow12998.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12998) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12998) (by norm_num) BstLean.Part268.WorldRow12998.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12998} (hw : c ∈ Hof BstLean.Part268.WorldRow12998.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12998) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12998).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12998) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12998_eq : scalarRow12998.targetFrame = BstLean.Part268.agent12998.frame := by
  norm_num [scalarRow12998,BstLean.Part268.agent12998]

noncomputable def frameData12998 : BstLean.Part264b.FrameData 12998 :=
  BstLean.Part269.frameData_from_numerics (n := 12998) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12998.worldPackage rfl BstLean.Part268.WorldRow12998.product_lower (BstLean.Part268.WorldRow12998.producthi.2.trans (by norm_num))
    scalarRow12998 repair12998 covarianceInputs12998 (fun i hi => sourceNumerics12998 hi)
    BstLean.Part268.agent12998.frame targetFrame12998_eq


end BstLean.Part269.N12998

namespace BstLean.Part269.N12999
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12999 : scalarRow12999.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12999, BstLean.Part268.grid12999, BstLean.Part263.worldGrid]

theorem supplies12999 (j : Fin 43) : Supply 12999 (parameters j)
    (cellLower scalarRow12999.grid (sourceIndex j))
    (cellUpper scalarRow12999.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12999.grid grid_top_bounds12999 j

theorem radii12999 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12999.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12999 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12999 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12999.grid grid_top_bounds12999 j hθ

noncomputable def covarianceInputs12999 :
    BstLean.Part263.CovarianceInputs 12999 scalarRow12999.grid parameters (caps repair12999) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12999 grid_top_bounds12999 repair12999

noncomputable def covarianceEvent12999 : Set (AgFam 12999) :=
  BstLean.Part263.covarianceEvent 12999 scalarRow12999.grid parameters

theorem covarianceEvent12999_measurable : MeasurableSet covarianceEvent12999 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12999_payment :
    (retDist (paperDesignP 12999).toCentres).real
      (agentEv (paperDesignP 12999) covarianceEvent12999)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12999

theorem localCov12999 : BstLean.Part259.LocalCovarianceOn covarianceEvent12999
    (BstLean.Part263.cell scalarRow12999.grid) (caps repair12999) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12999

theorem covarianceGood12999_payment :
    (retDist (paperDesignP 12999).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12999)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12999_payment



end BstLean.Part269.N12999

namespace BstLean.Part269.N12999
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12999}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12999.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12999) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12999).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12999 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12999) (by norm_num) BstLean.Part268.WorldRow12999.worldPackage rfl
    BstLean.Part268.WorldRow12999.product_lower (BstLean.Part268.WorldRow12999.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12999} (hw : c ∈ Hof BstLean.Part268.WorldRow12999.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12999) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12999) (by norm_num) BstLean.Part268.WorldRow12999.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12999} (hw : c ∈ Hof BstLean.Part268.WorldRow12999.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12999) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12999).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12999) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12999_eq : scalarRow12999.targetFrame = BstLean.Part268.agent12999.frame := by
  norm_num [scalarRow12999,BstLean.Part268.agent12999]

noncomputable def frameData12999 : BstLean.Part264b.FrameData 12999 :=
  BstLean.Part269.frameData_from_numerics (n := 12999) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12999.worldPackage rfl BstLean.Part268.WorldRow12999.product_lower (BstLean.Part268.WorldRow12999.producthi.2.trans (by norm_num))
    scalarRow12999 repair12999 covarianceInputs12999 (fun i hi => sourceNumerics12999 hi)
    BstLean.Part268.agent12999.frame targetFrame12999_eq


end BstLean.Part269.N12999
