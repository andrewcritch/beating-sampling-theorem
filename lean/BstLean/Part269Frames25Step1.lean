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

namespace BstLean.Part269.N12980
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12980 : scalarRow12980.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12980, BstLean.Part268.grid12980, BstLean.Part263.worldGrid]

theorem supplies12980 (j : Fin 43) : Supply 12980 (parameters j)
    (cellLower scalarRow12980.grid (sourceIndex j))
    (cellUpper scalarRow12980.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12980.grid grid_top_bounds12980 j

theorem radii12980 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12980.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12980 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12980 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12980.grid grid_top_bounds12980 j hθ

noncomputable def covarianceInputs12980 :
    BstLean.Part263.CovarianceInputs 12980 scalarRow12980.grid parameters (caps repair12980) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12980 grid_top_bounds12980 repair12980

noncomputable def covarianceEvent12980 : Set (AgFam 12980) :=
  BstLean.Part263.covarianceEvent 12980 scalarRow12980.grid parameters

theorem covarianceEvent12980_measurable : MeasurableSet covarianceEvent12980 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12980_payment :
    (retDist (paperDesignP 12980).toCentres).real
      (agentEv (paperDesignP 12980) covarianceEvent12980)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12980

theorem localCov12980 : BstLean.Part259.LocalCovarianceOn covarianceEvent12980
    (BstLean.Part263.cell scalarRow12980.grid) (caps repair12980) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12980

theorem covarianceGood12980_payment :
    (retDist (paperDesignP 12980).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12980)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12980_payment



end BstLean.Part269.N12980

namespace BstLean.Part269.N12980
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12980}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12980.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12980) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12980).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12980 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12980) (by norm_num) BstLean.Part268.WorldRow12980.worldPackage rfl
    BstLean.Part268.WorldRow12980.product_lower (BstLean.Part268.WorldRow12980.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12980} (hw : c ∈ Hof BstLean.Part268.WorldRow12980.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12980) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12980) (by norm_num) BstLean.Part268.WorldRow12980.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12980} (hw : c ∈ Hof BstLean.Part268.WorldRow12980.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12980) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12980).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12980) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12980_eq : scalarRow12980.targetFrame = BstLean.Part268.agent12980.frame := by
  norm_num [scalarRow12980,BstLean.Part268.agent12980]

noncomputable def frameData12980 : BstLean.Part264b.FrameData 12980 :=
  BstLean.Part269.frameData_from_numerics (n := 12980) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12980.worldPackage rfl BstLean.Part268.WorldRow12980.product_lower (BstLean.Part268.WorldRow12980.producthi.2.trans (by norm_num))
    scalarRow12980 repair12980 covarianceInputs12980 (fun i hi => sourceNumerics12980 hi)
    BstLean.Part268.agent12980.frame targetFrame12980_eq


end BstLean.Part269.N12980

namespace BstLean.Part269.N12981
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12981 : scalarRow12981.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12981, BstLean.Part268.grid12981, BstLean.Part263.worldGrid]

theorem supplies12981 (j : Fin 43) : Supply 12981 (parameters j)
    (cellLower scalarRow12981.grid (sourceIndex j))
    (cellUpper scalarRow12981.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12981.grid grid_top_bounds12981 j

theorem radii12981 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12981.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12981 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12981 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12981.grid grid_top_bounds12981 j hθ

noncomputable def covarianceInputs12981 :
    BstLean.Part263.CovarianceInputs 12981 scalarRow12981.grid parameters (caps repair12981) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12981 grid_top_bounds12981 repair12981

noncomputable def covarianceEvent12981 : Set (AgFam 12981) :=
  BstLean.Part263.covarianceEvent 12981 scalarRow12981.grid parameters

theorem covarianceEvent12981_measurable : MeasurableSet covarianceEvent12981 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12981_payment :
    (retDist (paperDesignP 12981).toCentres).real
      (agentEv (paperDesignP 12981) covarianceEvent12981)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12981

theorem localCov12981 : BstLean.Part259.LocalCovarianceOn covarianceEvent12981
    (BstLean.Part263.cell scalarRow12981.grid) (caps repair12981) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12981

theorem covarianceGood12981_payment :
    (retDist (paperDesignP 12981).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12981)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12981_payment



end BstLean.Part269.N12981

namespace BstLean.Part269.N12981
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12981}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12981.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12981) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12981).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12981 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12981) (by norm_num) BstLean.Part268.WorldRow12981.worldPackage rfl
    BstLean.Part268.WorldRow12981.product_lower (BstLean.Part268.WorldRow12981.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12981} (hw : c ∈ Hof BstLean.Part268.WorldRow12981.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12981) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12981) (by norm_num) BstLean.Part268.WorldRow12981.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12981} (hw : c ∈ Hof BstLean.Part268.WorldRow12981.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12981) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12981).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12981) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12981_eq : scalarRow12981.targetFrame = BstLean.Part268.agent12981.frame := by
  norm_num [scalarRow12981,BstLean.Part268.agent12981]

noncomputable def frameData12981 : BstLean.Part264b.FrameData 12981 :=
  BstLean.Part269.frameData_from_numerics (n := 12981) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12981.worldPackage rfl BstLean.Part268.WorldRow12981.product_lower (BstLean.Part268.WorldRow12981.producthi.2.trans (by norm_num))
    scalarRow12981 repair12981 covarianceInputs12981 (fun i hi => sourceNumerics12981 hi)
    BstLean.Part268.agent12981.frame targetFrame12981_eq


end BstLean.Part269.N12981

namespace BstLean.Part269.N12982
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12982 : scalarRow12982.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12982, BstLean.Part268.grid12982, BstLean.Part263.worldGrid]

theorem supplies12982 (j : Fin 43) : Supply 12982 (parameters j)
    (cellLower scalarRow12982.grid (sourceIndex j))
    (cellUpper scalarRow12982.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12982.grid grid_top_bounds12982 j

theorem radii12982 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12982.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12982 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12982 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12982.grid grid_top_bounds12982 j hθ

noncomputable def covarianceInputs12982 :
    BstLean.Part263.CovarianceInputs 12982 scalarRow12982.grid parameters (caps repair12982) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12982 grid_top_bounds12982 repair12982

noncomputable def covarianceEvent12982 : Set (AgFam 12982) :=
  BstLean.Part263.covarianceEvent 12982 scalarRow12982.grid parameters

theorem covarianceEvent12982_measurable : MeasurableSet covarianceEvent12982 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12982_payment :
    (retDist (paperDesignP 12982).toCentres).real
      (agentEv (paperDesignP 12982) covarianceEvent12982)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12982

theorem localCov12982 : BstLean.Part259.LocalCovarianceOn covarianceEvent12982
    (BstLean.Part263.cell scalarRow12982.grid) (caps repair12982) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12982

theorem covarianceGood12982_payment :
    (retDist (paperDesignP 12982).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12982)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12982_payment



end BstLean.Part269.N12982

namespace BstLean.Part269.N12982
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12982}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12982.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12982) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12982).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12982 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12982) (by norm_num) BstLean.Part268.WorldRow12982.worldPackage rfl
    BstLean.Part268.WorldRow12982.product_lower (BstLean.Part268.WorldRow12982.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12982} (hw : c ∈ Hof BstLean.Part268.WorldRow12982.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12982) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12982) (by norm_num) BstLean.Part268.WorldRow12982.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12982} (hw : c ∈ Hof BstLean.Part268.WorldRow12982.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12982) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12982).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12982) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12982_eq : scalarRow12982.targetFrame = BstLean.Part268.agent12982.frame := by
  norm_num [scalarRow12982,BstLean.Part268.agent12982]

noncomputable def frameData12982 : BstLean.Part264b.FrameData 12982 :=
  BstLean.Part269.frameData_from_numerics (n := 12982) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12982.worldPackage rfl BstLean.Part268.WorldRow12982.product_lower (BstLean.Part268.WorldRow12982.producthi.2.trans (by norm_num))
    scalarRow12982 repair12982 covarianceInputs12982 (fun i hi => sourceNumerics12982 hi)
    BstLean.Part268.agent12982.frame targetFrame12982_eq


end BstLean.Part269.N12982

namespace BstLean.Part269.N12983
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12983 : scalarRow12983.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12983, BstLean.Part268.grid12983, BstLean.Part263.worldGrid]

theorem supplies12983 (j : Fin 43) : Supply 12983 (parameters j)
    (cellLower scalarRow12983.grid (sourceIndex j))
    (cellUpper scalarRow12983.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12983.grid grid_top_bounds12983 j

theorem radii12983 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12983.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12983 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12983 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12983.grid grid_top_bounds12983 j hθ

noncomputable def covarianceInputs12983 :
    BstLean.Part263.CovarianceInputs 12983 scalarRow12983.grid parameters (caps repair12983) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12983 grid_top_bounds12983 repair12983

noncomputable def covarianceEvent12983 : Set (AgFam 12983) :=
  BstLean.Part263.covarianceEvent 12983 scalarRow12983.grid parameters

theorem covarianceEvent12983_measurable : MeasurableSet covarianceEvent12983 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12983_payment :
    (retDist (paperDesignP 12983).toCentres).real
      (agentEv (paperDesignP 12983) covarianceEvent12983)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12983

theorem localCov12983 : BstLean.Part259.LocalCovarianceOn covarianceEvent12983
    (BstLean.Part263.cell scalarRow12983.grid) (caps repair12983) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12983

theorem covarianceGood12983_payment :
    (retDist (paperDesignP 12983).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12983)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12983_payment



end BstLean.Part269.N12983

namespace BstLean.Part269.N12983
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12983}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12983.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12983) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12983).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12983 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12983) (by norm_num) BstLean.Part268.WorldRow12983.worldPackage rfl
    BstLean.Part268.WorldRow12983.product_lower (BstLean.Part268.WorldRow12983.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12983} (hw : c ∈ Hof BstLean.Part268.WorldRow12983.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12983) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12983) (by norm_num) BstLean.Part268.WorldRow12983.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12983} (hw : c ∈ Hof BstLean.Part268.WorldRow12983.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12983) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12983).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12983) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12983_eq : scalarRow12983.targetFrame = BstLean.Part268.agent12983.frame := by
  norm_num [scalarRow12983,BstLean.Part268.agent12983]

noncomputable def frameData12983 : BstLean.Part264b.FrameData 12983 :=
  BstLean.Part269.frameData_from_numerics (n := 12983) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12983.worldPackage rfl BstLean.Part268.WorldRow12983.product_lower (BstLean.Part268.WorldRow12983.producthi.2.trans (by norm_num))
    scalarRow12983 repair12983 covarianceInputs12983 (fun i hi => sourceNumerics12983 hi)
    BstLean.Part268.agent12983.frame targetFrame12983_eq


end BstLean.Part269.N12983

namespace BstLean.Part269.N12984
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12984 : scalarRow12984.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12984, BstLean.Part268.grid12984, BstLean.Part263.worldGrid]

theorem supplies12984 (j : Fin 43) : Supply 12984 (parameters j)
    (cellLower scalarRow12984.grid (sourceIndex j))
    (cellUpper scalarRow12984.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12984.grid grid_top_bounds12984 j

theorem radii12984 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12984.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12984 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12984 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12984.grid grid_top_bounds12984 j hθ

noncomputable def covarianceInputs12984 :
    BstLean.Part263.CovarianceInputs 12984 scalarRow12984.grid parameters (caps repair12984) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12984 grid_top_bounds12984 repair12984

noncomputable def covarianceEvent12984 : Set (AgFam 12984) :=
  BstLean.Part263.covarianceEvent 12984 scalarRow12984.grid parameters

theorem covarianceEvent12984_measurable : MeasurableSet covarianceEvent12984 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12984_payment :
    (retDist (paperDesignP 12984).toCentres).real
      (agentEv (paperDesignP 12984) covarianceEvent12984)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12984

theorem localCov12984 : BstLean.Part259.LocalCovarianceOn covarianceEvent12984
    (BstLean.Part263.cell scalarRow12984.grid) (caps repair12984) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12984

theorem covarianceGood12984_payment :
    (retDist (paperDesignP 12984).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12984)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12984_payment



end BstLean.Part269.N12984

namespace BstLean.Part269.N12984
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12984}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12984.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12984) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12984).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12984 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12984) (by norm_num) BstLean.Part268.WorldRow12984.worldPackage rfl
    BstLean.Part268.WorldRow12984.product_lower (BstLean.Part268.WorldRow12984.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12984} (hw : c ∈ Hof BstLean.Part268.WorldRow12984.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12984) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12984) (by norm_num) BstLean.Part268.WorldRow12984.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12984} (hw : c ∈ Hof BstLean.Part268.WorldRow12984.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12984) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12984).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12984) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12984_eq : scalarRow12984.targetFrame = BstLean.Part268.agent12984.frame := by
  norm_num [scalarRow12984,BstLean.Part268.agent12984]

noncomputable def frameData12984 : BstLean.Part264b.FrameData 12984 :=
  BstLean.Part269.frameData_from_numerics (n := 12984) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12984.worldPackage rfl BstLean.Part268.WorldRow12984.product_lower (BstLean.Part268.WorldRow12984.producthi.2.trans (by norm_num))
    scalarRow12984 repair12984 covarianceInputs12984 (fun i hi => sourceNumerics12984 hi)
    BstLean.Part268.agent12984.frame targetFrame12984_eq


end BstLean.Part269.N12984
