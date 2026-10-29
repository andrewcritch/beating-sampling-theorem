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

namespace BstLean.Part269.N12970
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12970 : scalarRow12970.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12970, BstLean.Part268.grid12970, BstLean.Part263.worldGrid]

theorem supplies12970 (j : Fin 43) : Supply 12970 (parameters j)
    (cellLower scalarRow12970.grid (sourceIndex j))
    (cellUpper scalarRow12970.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12970.grid grid_top_bounds12970 j

theorem radii12970 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12970.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12970 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12970 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12970.grid grid_top_bounds12970 j hθ

noncomputable def covarianceInputs12970 :
    BstLean.Part263.CovarianceInputs 12970 scalarRow12970.grid parameters (caps repair12970) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12970 grid_top_bounds12970 repair12970

noncomputable def covarianceEvent12970 : Set (AgFam 12970) :=
  BstLean.Part263.covarianceEvent 12970 scalarRow12970.grid parameters

theorem covarianceEvent12970_measurable : MeasurableSet covarianceEvent12970 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12970_payment :
    (retDist (paperDesignP 12970).toCentres).real
      (agentEv (paperDesignP 12970) covarianceEvent12970)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12970

theorem localCov12970 : BstLean.Part259.LocalCovarianceOn covarianceEvent12970
    (BstLean.Part263.cell scalarRow12970.grid) (caps repair12970) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12970

theorem covarianceGood12970_payment :
    (retDist (paperDesignP 12970).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12970)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12970_payment



end BstLean.Part269.N12970

namespace BstLean.Part269.N12970
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12970}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12970.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12970) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12970).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12970 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12970) (by norm_num) BstLean.Part268.WorldRow12970.worldPackage rfl
    BstLean.Part268.WorldRow12970.product_lower (BstLean.Part268.WorldRow12970.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12970} (hw : c ∈ Hof BstLean.Part268.WorldRow12970.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12970) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12970) (by norm_num) BstLean.Part268.WorldRow12970.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12970} (hw : c ∈ Hof BstLean.Part268.WorldRow12970.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12970) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12970).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12970) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12970_eq : scalarRow12970.targetFrame = BstLean.Part268.agent12970.frame := by
  norm_num [scalarRow12970,BstLean.Part268.agent12970]

noncomputable def frameData12970 : BstLean.Part264b.FrameData 12970 :=
  BstLean.Part269.frameData_from_numerics (n := 12970) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12970.worldPackage rfl BstLean.Part268.WorldRow12970.product_lower (BstLean.Part268.WorldRow12970.producthi.2.trans (by norm_num))
    scalarRow12970 repair12970 covarianceInputs12970 (fun i hi => sourceNumerics12970 hi)
    BstLean.Part268.agent12970.frame targetFrame12970_eq


end BstLean.Part269.N12970

namespace BstLean.Part269.N12971
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12971 : scalarRow12971.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12971, BstLean.Part268.grid12971, BstLean.Part263.worldGrid]

theorem supplies12971 (j : Fin 43) : Supply 12971 (parameters j)
    (cellLower scalarRow12971.grid (sourceIndex j))
    (cellUpper scalarRow12971.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12971.grid grid_top_bounds12971 j

theorem radii12971 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12971.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12971 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12971 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12971.grid grid_top_bounds12971 j hθ

noncomputable def covarianceInputs12971 :
    BstLean.Part263.CovarianceInputs 12971 scalarRow12971.grid parameters (caps repair12971) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12971 grid_top_bounds12971 repair12971

noncomputable def covarianceEvent12971 : Set (AgFam 12971) :=
  BstLean.Part263.covarianceEvent 12971 scalarRow12971.grid parameters

theorem covarianceEvent12971_measurable : MeasurableSet covarianceEvent12971 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12971_payment :
    (retDist (paperDesignP 12971).toCentres).real
      (agentEv (paperDesignP 12971) covarianceEvent12971)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12971

theorem localCov12971 : BstLean.Part259.LocalCovarianceOn covarianceEvent12971
    (BstLean.Part263.cell scalarRow12971.grid) (caps repair12971) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12971

theorem covarianceGood12971_payment :
    (retDist (paperDesignP 12971).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12971)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12971_payment



end BstLean.Part269.N12971

namespace BstLean.Part269.N12971
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12971}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12971.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12971) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12971).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12971 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12971) (by norm_num) BstLean.Part268.WorldRow12971.worldPackage rfl
    BstLean.Part268.WorldRow12971.product_lower (BstLean.Part268.WorldRow12971.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12971} (hw : c ∈ Hof BstLean.Part268.WorldRow12971.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12971) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12971) (by norm_num) BstLean.Part268.WorldRow12971.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12971} (hw : c ∈ Hof BstLean.Part268.WorldRow12971.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12971) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12971).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12971) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12971_eq : scalarRow12971.targetFrame = BstLean.Part268.agent12971.frame := by
  norm_num [scalarRow12971,BstLean.Part268.agent12971]

noncomputable def frameData12971 : BstLean.Part264b.FrameData 12971 :=
  BstLean.Part269.frameData_from_numerics (n := 12971) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12971.worldPackage rfl BstLean.Part268.WorldRow12971.product_lower (BstLean.Part268.WorldRow12971.producthi.2.trans (by norm_num))
    scalarRow12971 repair12971 covarianceInputs12971 (fun i hi => sourceNumerics12971 hi)
    BstLean.Part268.agent12971.frame targetFrame12971_eq


end BstLean.Part269.N12971

namespace BstLean.Part269.N12972
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12972 : scalarRow12972.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12972, BstLean.Part268.grid12972, BstLean.Part263.worldGrid]

theorem supplies12972 (j : Fin 43) : Supply 12972 (parameters j)
    (cellLower scalarRow12972.grid (sourceIndex j))
    (cellUpper scalarRow12972.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12972.grid grid_top_bounds12972 j

theorem radii12972 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12972.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12972 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12972 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12972.grid grid_top_bounds12972 j hθ

noncomputable def covarianceInputs12972 :
    BstLean.Part263.CovarianceInputs 12972 scalarRow12972.grid parameters (caps repair12972) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12972 grid_top_bounds12972 repair12972

noncomputable def covarianceEvent12972 : Set (AgFam 12972) :=
  BstLean.Part263.covarianceEvent 12972 scalarRow12972.grid parameters

theorem covarianceEvent12972_measurable : MeasurableSet covarianceEvent12972 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12972_payment :
    (retDist (paperDesignP 12972).toCentres).real
      (agentEv (paperDesignP 12972) covarianceEvent12972)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12972

theorem localCov12972 : BstLean.Part259.LocalCovarianceOn covarianceEvent12972
    (BstLean.Part263.cell scalarRow12972.grid) (caps repair12972) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12972

theorem covarianceGood12972_payment :
    (retDist (paperDesignP 12972).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12972)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12972_payment



end BstLean.Part269.N12972

namespace BstLean.Part269.N12972
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12972}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12972.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12972) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12972).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12972 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12972) (by norm_num) BstLean.Part268.WorldRow12972.worldPackage rfl
    BstLean.Part268.WorldRow12972.product_lower (BstLean.Part268.WorldRow12972.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12972} (hw : c ∈ Hof BstLean.Part268.WorldRow12972.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12972) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12972) (by norm_num) BstLean.Part268.WorldRow12972.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12972} (hw : c ∈ Hof BstLean.Part268.WorldRow12972.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12972) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12972).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12972) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12972_eq : scalarRow12972.targetFrame = BstLean.Part268.agent12972.frame := by
  norm_num [scalarRow12972,BstLean.Part268.agent12972]

noncomputable def frameData12972 : BstLean.Part264b.FrameData 12972 :=
  BstLean.Part269.frameData_from_numerics (n := 12972) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12972.worldPackage rfl BstLean.Part268.WorldRow12972.product_lower (BstLean.Part268.WorldRow12972.producthi.2.trans (by norm_num))
    scalarRow12972 repair12972 covarianceInputs12972 (fun i hi => sourceNumerics12972 hi)
    BstLean.Part268.agent12972.frame targetFrame12972_eq


end BstLean.Part269.N12972

namespace BstLean.Part269.N12973
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12973 : scalarRow12973.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12973, BstLean.Part268.grid12973, BstLean.Part263.worldGrid]

theorem supplies12973 (j : Fin 43) : Supply 12973 (parameters j)
    (cellLower scalarRow12973.grid (sourceIndex j))
    (cellUpper scalarRow12973.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12973.grid grid_top_bounds12973 j

theorem radii12973 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12973.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12973 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12973 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12973.grid grid_top_bounds12973 j hθ

noncomputable def covarianceInputs12973 :
    BstLean.Part263.CovarianceInputs 12973 scalarRow12973.grid parameters (caps repair12973) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12973 grid_top_bounds12973 repair12973

noncomputable def covarianceEvent12973 : Set (AgFam 12973) :=
  BstLean.Part263.covarianceEvent 12973 scalarRow12973.grid parameters

theorem covarianceEvent12973_measurable : MeasurableSet covarianceEvent12973 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12973_payment :
    (retDist (paperDesignP 12973).toCentres).real
      (agentEv (paperDesignP 12973) covarianceEvent12973)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12973

theorem localCov12973 : BstLean.Part259.LocalCovarianceOn covarianceEvent12973
    (BstLean.Part263.cell scalarRow12973.grid) (caps repair12973) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12973

theorem covarianceGood12973_payment :
    (retDist (paperDesignP 12973).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12973)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12973_payment



end BstLean.Part269.N12973

namespace BstLean.Part269.N12973
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12973}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12973.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12973) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12973).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12973 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12973) (by norm_num) BstLean.Part268.WorldRow12973.worldPackage rfl
    BstLean.Part268.WorldRow12973.product_lower (BstLean.Part268.WorldRow12973.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12973} (hw : c ∈ Hof BstLean.Part268.WorldRow12973.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12973) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12973) (by norm_num) BstLean.Part268.WorldRow12973.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12973} (hw : c ∈ Hof BstLean.Part268.WorldRow12973.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12973) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12973).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12973) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12973_eq : scalarRow12973.targetFrame = BstLean.Part268.agent12973.frame := by
  norm_num [scalarRow12973,BstLean.Part268.agent12973]

noncomputable def frameData12973 : BstLean.Part264b.FrameData 12973 :=
  BstLean.Part269.frameData_from_numerics (n := 12973) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12973.worldPackage rfl BstLean.Part268.WorldRow12973.product_lower (BstLean.Part268.WorldRow12973.producthi.2.trans (by norm_num))
    scalarRow12973 repair12973 covarianceInputs12973 (fun i hi => sourceNumerics12973 hi)
    BstLean.Part268.agent12973.frame targetFrame12973_eq


end BstLean.Part269.N12973

namespace BstLean.Part269.N12974
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12974 : scalarRow12974.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12974, BstLean.Part268.grid12974, BstLean.Part263.worldGrid]

theorem supplies12974 (j : Fin 43) : Supply 12974 (parameters j)
    (cellLower scalarRow12974.grid (sourceIndex j))
    (cellUpper scalarRow12974.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12974.grid grid_top_bounds12974 j

theorem radii12974 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12974.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12974 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12974 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12974.grid grid_top_bounds12974 j hθ

noncomputable def covarianceInputs12974 :
    BstLean.Part263.CovarianceInputs 12974 scalarRow12974.grid parameters (caps repair12974) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12974 grid_top_bounds12974 repair12974

noncomputable def covarianceEvent12974 : Set (AgFam 12974) :=
  BstLean.Part263.covarianceEvent 12974 scalarRow12974.grid parameters

theorem covarianceEvent12974_measurable : MeasurableSet covarianceEvent12974 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12974_payment :
    (retDist (paperDesignP 12974).toCentres).real
      (agentEv (paperDesignP 12974) covarianceEvent12974)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12974

theorem localCov12974 : BstLean.Part259.LocalCovarianceOn covarianceEvent12974
    (BstLean.Part263.cell scalarRow12974.grid) (caps repair12974) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12974

theorem covarianceGood12974_payment :
    (retDist (paperDesignP 12974).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12974)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12974_payment



end BstLean.Part269.N12974

namespace BstLean.Part269.N12974
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12974}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12974.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12974) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12974).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12974 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12974) (by norm_num) BstLean.Part268.WorldRow12974.worldPackage rfl
    BstLean.Part268.WorldRow12974.product_lower (BstLean.Part268.WorldRow12974.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12974} (hw : c ∈ Hof BstLean.Part268.WorldRow12974.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12974) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12974) (by norm_num) BstLean.Part268.WorldRow12974.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12974} (hw : c ∈ Hof BstLean.Part268.WorldRow12974.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12974) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12974).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12974) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12974_eq : scalarRow12974.targetFrame = BstLean.Part268.agent12974.frame := by
  norm_num [scalarRow12974,BstLean.Part268.agent12974]

noncomputable def frameData12974 : BstLean.Part264b.FrameData 12974 :=
  BstLean.Part269.frameData_from_numerics (n := 12974) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12974.worldPackage rfl BstLean.Part268.WorldRow12974.product_lower (BstLean.Part268.WorldRow12974.producthi.2.trans (by norm_num))
    scalarRow12974 repair12974 covarianceInputs12974 (fun i hi => sourceNumerics12974 hi)
    BstLean.Part268.agent12974.frame targetFrame12974_eq


end BstLean.Part269.N12974
