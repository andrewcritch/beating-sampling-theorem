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

namespace BstLean.Part269.N12990
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12990 : scalarRow12990.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12990, BstLean.Part268.grid12990, BstLean.Part263.worldGrid]

theorem supplies12990 (j : Fin 43) : Supply 12990 (parameters j)
    (cellLower scalarRow12990.grid (sourceIndex j))
    (cellUpper scalarRow12990.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12990.grid grid_top_bounds12990 j

theorem radii12990 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12990.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12990 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12990 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12990.grid grid_top_bounds12990 j hθ

noncomputable def covarianceInputs12990 :
    BstLean.Part263.CovarianceInputs 12990 scalarRow12990.grid parameters (caps repair12990) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12990 grid_top_bounds12990 repair12990

noncomputable def covarianceEvent12990 : Set (AgFam 12990) :=
  BstLean.Part263.covarianceEvent 12990 scalarRow12990.grid parameters

theorem covarianceEvent12990_measurable : MeasurableSet covarianceEvent12990 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12990_payment :
    (retDist (paperDesignP 12990).toCentres).real
      (agentEv (paperDesignP 12990) covarianceEvent12990)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12990

theorem localCov12990 : BstLean.Part259.LocalCovarianceOn covarianceEvent12990
    (BstLean.Part263.cell scalarRow12990.grid) (caps repair12990) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12990

theorem covarianceGood12990_payment :
    (retDist (paperDesignP 12990).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12990)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12990_payment



end BstLean.Part269.N12990

namespace BstLean.Part269.N12990
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12990}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12990.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12990) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12990).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12990 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12990) (by norm_num) BstLean.Part268.WorldRow12990.worldPackage rfl
    BstLean.Part268.WorldRow12990.product_lower (BstLean.Part268.WorldRow12990.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12990} (hw : c ∈ Hof BstLean.Part268.WorldRow12990.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12990) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12990) (by norm_num) BstLean.Part268.WorldRow12990.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12990} (hw : c ∈ Hof BstLean.Part268.WorldRow12990.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12990) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12990).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12990) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12990_eq : scalarRow12990.targetFrame = BstLean.Part268.agent12990.frame := by
  norm_num [scalarRow12990,BstLean.Part268.agent12990]

noncomputable def frameData12990 : BstLean.Part264b.FrameData 12990 :=
  BstLean.Part269.frameData_from_numerics (n := 12990) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12990.worldPackage rfl BstLean.Part268.WorldRow12990.product_lower (BstLean.Part268.WorldRow12990.producthi.2.trans (by norm_num))
    scalarRow12990 repair12990 covarianceInputs12990 (fun i hi => sourceNumerics12990 hi)
    BstLean.Part268.agent12990.frame targetFrame12990_eq


end BstLean.Part269.N12990

namespace BstLean.Part269.N12991
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12991 : scalarRow12991.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12991, BstLean.Part268.grid12991, BstLean.Part263.worldGrid]

theorem supplies12991 (j : Fin 43) : Supply 12991 (parameters j)
    (cellLower scalarRow12991.grid (sourceIndex j))
    (cellUpper scalarRow12991.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12991.grid grid_top_bounds12991 j

theorem radii12991 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12991.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12991 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12991 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12991.grid grid_top_bounds12991 j hθ

noncomputable def covarianceInputs12991 :
    BstLean.Part263.CovarianceInputs 12991 scalarRow12991.grid parameters (caps repair12991) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12991 grid_top_bounds12991 repair12991

noncomputable def covarianceEvent12991 : Set (AgFam 12991) :=
  BstLean.Part263.covarianceEvent 12991 scalarRow12991.grid parameters

theorem covarianceEvent12991_measurable : MeasurableSet covarianceEvent12991 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12991_payment :
    (retDist (paperDesignP 12991).toCentres).real
      (agentEv (paperDesignP 12991) covarianceEvent12991)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12991

theorem localCov12991 : BstLean.Part259.LocalCovarianceOn covarianceEvent12991
    (BstLean.Part263.cell scalarRow12991.grid) (caps repair12991) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12991

theorem covarianceGood12991_payment :
    (retDist (paperDesignP 12991).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12991)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12991_payment



end BstLean.Part269.N12991

namespace BstLean.Part269.N12991
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12991}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12991.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12991) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12991).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12991 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12991) (by norm_num) BstLean.Part268.WorldRow12991.worldPackage rfl
    BstLean.Part268.WorldRow12991.product_lower (BstLean.Part268.WorldRow12991.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12991} (hw : c ∈ Hof BstLean.Part268.WorldRow12991.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12991) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12991) (by norm_num) BstLean.Part268.WorldRow12991.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12991} (hw : c ∈ Hof BstLean.Part268.WorldRow12991.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12991) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12991).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12991) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12991_eq : scalarRow12991.targetFrame = BstLean.Part268.agent12991.frame := by
  norm_num [scalarRow12991,BstLean.Part268.agent12991]

noncomputable def frameData12991 : BstLean.Part264b.FrameData 12991 :=
  BstLean.Part269.frameData_from_numerics (n := 12991) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12991.worldPackage rfl BstLean.Part268.WorldRow12991.product_lower (BstLean.Part268.WorldRow12991.producthi.2.trans (by norm_num))
    scalarRow12991 repair12991 covarianceInputs12991 (fun i hi => sourceNumerics12991 hi)
    BstLean.Part268.agent12991.frame targetFrame12991_eq


end BstLean.Part269.N12991

namespace BstLean.Part269.N12992
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12992 : scalarRow12992.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12992, BstLean.Part268.grid12992, BstLean.Part263.worldGrid]

theorem supplies12992 (j : Fin 43) : Supply 12992 (parameters j)
    (cellLower scalarRow12992.grid (sourceIndex j))
    (cellUpper scalarRow12992.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12992.grid grid_top_bounds12992 j

theorem radii12992 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12992.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12992 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12992 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12992.grid grid_top_bounds12992 j hθ

noncomputable def covarianceInputs12992 :
    BstLean.Part263.CovarianceInputs 12992 scalarRow12992.grid parameters (caps repair12992) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12992 grid_top_bounds12992 repair12992

noncomputable def covarianceEvent12992 : Set (AgFam 12992) :=
  BstLean.Part263.covarianceEvent 12992 scalarRow12992.grid parameters

theorem covarianceEvent12992_measurable : MeasurableSet covarianceEvent12992 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12992_payment :
    (retDist (paperDesignP 12992).toCentres).real
      (agentEv (paperDesignP 12992) covarianceEvent12992)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12992

theorem localCov12992 : BstLean.Part259.LocalCovarianceOn covarianceEvent12992
    (BstLean.Part263.cell scalarRow12992.grid) (caps repair12992) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12992

theorem covarianceGood12992_payment :
    (retDist (paperDesignP 12992).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12992)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12992_payment



end BstLean.Part269.N12992

namespace BstLean.Part269.N12992
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12992}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12992.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12992) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12992).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12992 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12992) (by norm_num) BstLean.Part268.WorldRow12992.worldPackage rfl
    BstLean.Part268.WorldRow12992.product_lower (BstLean.Part268.WorldRow12992.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12992} (hw : c ∈ Hof BstLean.Part268.WorldRow12992.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12992) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12992) (by norm_num) BstLean.Part268.WorldRow12992.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12992} (hw : c ∈ Hof BstLean.Part268.WorldRow12992.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12992) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12992).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12992) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12992_eq : scalarRow12992.targetFrame = BstLean.Part268.agent12992.frame := by
  norm_num [scalarRow12992,BstLean.Part268.agent12992]

noncomputable def frameData12992 : BstLean.Part264b.FrameData 12992 :=
  BstLean.Part269.frameData_from_numerics (n := 12992) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12992.worldPackage rfl BstLean.Part268.WorldRow12992.product_lower (BstLean.Part268.WorldRow12992.producthi.2.trans (by norm_num))
    scalarRow12992 repair12992 covarianceInputs12992 (fun i hi => sourceNumerics12992 hi)
    BstLean.Part268.agent12992.frame targetFrame12992_eq


end BstLean.Part269.N12992

namespace BstLean.Part269.N12993
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12993 : scalarRow12993.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12993, BstLean.Part268.grid12993, BstLean.Part263.worldGrid]

theorem supplies12993 (j : Fin 43) : Supply 12993 (parameters j)
    (cellLower scalarRow12993.grid (sourceIndex j))
    (cellUpper scalarRow12993.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12993.grid grid_top_bounds12993 j

theorem radii12993 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12993.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12993 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12993 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12993.grid grid_top_bounds12993 j hθ

noncomputable def covarianceInputs12993 :
    BstLean.Part263.CovarianceInputs 12993 scalarRow12993.grid parameters (caps repair12993) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12993 grid_top_bounds12993 repair12993

noncomputable def covarianceEvent12993 : Set (AgFam 12993) :=
  BstLean.Part263.covarianceEvent 12993 scalarRow12993.grid parameters

theorem covarianceEvent12993_measurable : MeasurableSet covarianceEvent12993 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12993_payment :
    (retDist (paperDesignP 12993).toCentres).real
      (agentEv (paperDesignP 12993) covarianceEvent12993)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12993

theorem localCov12993 : BstLean.Part259.LocalCovarianceOn covarianceEvent12993
    (BstLean.Part263.cell scalarRow12993.grid) (caps repair12993) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12993

theorem covarianceGood12993_payment :
    (retDist (paperDesignP 12993).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12993)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12993_payment



end BstLean.Part269.N12993

namespace BstLean.Part269.N12993
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12993}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12993.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12993) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12993).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12993 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12993) (by norm_num) BstLean.Part268.WorldRow12993.worldPackage rfl
    BstLean.Part268.WorldRow12993.product_lower (BstLean.Part268.WorldRow12993.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12993} (hw : c ∈ Hof BstLean.Part268.WorldRow12993.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12993) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12993) (by norm_num) BstLean.Part268.WorldRow12993.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12993} (hw : c ∈ Hof BstLean.Part268.WorldRow12993.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12993) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12993).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12993) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12993_eq : scalarRow12993.targetFrame = BstLean.Part268.agent12993.frame := by
  norm_num [scalarRow12993,BstLean.Part268.agent12993]

noncomputable def frameData12993 : BstLean.Part264b.FrameData 12993 :=
  BstLean.Part269.frameData_from_numerics (n := 12993) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12993.worldPackage rfl BstLean.Part268.WorldRow12993.product_lower (BstLean.Part268.WorldRow12993.producthi.2.trans (by norm_num))
    scalarRow12993 repair12993 covarianceInputs12993 (fun i hi => sourceNumerics12993 hi)
    BstLean.Part268.agent12993.frame targetFrame12993_eq


end BstLean.Part269.N12993

namespace BstLean.Part269.N12994
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12994 : scalarRow12994.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12994, BstLean.Part268.grid12994, BstLean.Part263.worldGrid]

theorem supplies12994 (j : Fin 43) : Supply 12994 (parameters j)
    (cellLower scalarRow12994.grid (sourceIndex j))
    (cellUpper scalarRow12994.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12994.grid grid_top_bounds12994 j

theorem radii12994 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12994.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12994 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12994 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12994.grid grid_top_bounds12994 j hθ

noncomputable def covarianceInputs12994 :
    BstLean.Part263.CovarianceInputs 12994 scalarRow12994.grid parameters (caps repair12994) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12994 grid_top_bounds12994 repair12994

noncomputable def covarianceEvent12994 : Set (AgFam 12994) :=
  BstLean.Part263.covarianceEvent 12994 scalarRow12994.grid parameters

theorem covarianceEvent12994_measurable : MeasurableSet covarianceEvent12994 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12994_payment :
    (retDist (paperDesignP 12994).toCentres).real
      (agentEv (paperDesignP 12994) covarianceEvent12994)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12994

theorem localCov12994 : BstLean.Part259.LocalCovarianceOn covarianceEvent12994
    (BstLean.Part263.cell scalarRow12994.grid) (caps repair12994) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12994

theorem covarianceGood12994_payment :
    (retDist (paperDesignP 12994).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12994)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12994_payment



end BstLean.Part269.N12994

namespace BstLean.Part269.N12994
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12994}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12994.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12994) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12994).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12994 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12994) (by norm_num) BstLean.Part268.WorldRow12994.worldPackage rfl
    BstLean.Part268.WorldRow12994.product_lower (BstLean.Part268.WorldRow12994.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12994} (hw : c ∈ Hof BstLean.Part268.WorldRow12994.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12994) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12994) (by norm_num) BstLean.Part268.WorldRow12994.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12994} (hw : c ∈ Hof BstLean.Part268.WorldRow12994.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12994) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12994).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12994) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12994_eq : scalarRow12994.targetFrame = BstLean.Part268.agent12994.frame := by
  norm_num [scalarRow12994,BstLean.Part268.agent12994]

noncomputable def frameData12994 : BstLean.Part264b.FrameData 12994 :=
  BstLean.Part269.frameData_from_numerics (n := 12994) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12994.worldPackage rfl BstLean.Part268.WorldRow12994.product_lower (BstLean.Part268.WorldRow12994.producthi.2.trans (by norm_num))
    scalarRow12994 repair12994 covarianceInputs12994 (fun i hi => sourceNumerics12994 hi)
    BstLean.Part268.agent12994.frame targetFrame12994_eq


end BstLean.Part269.N12994
