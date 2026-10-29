import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World17Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs17
import BstLean.Part269Rows17
import BstLean.Part269Sources17
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12785
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12785 : scalarRow12785.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12785, BstLean.Part268.grid12785, BstLean.Part263.worldGrid]

theorem supplies12785 (j : Fin 43) : Supply 12785 (parameters j)
    (cellLower scalarRow12785.grid (sourceIndex j))
    (cellUpper scalarRow12785.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12785.grid grid_top_bounds12785 j

theorem radii12785 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12785.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12785 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12785 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12785.grid grid_top_bounds12785 j hθ

noncomputable def covarianceInputs12785 :
    BstLean.Part263.CovarianceInputs 12785 scalarRow12785.grid parameters (caps repair12785) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12785 grid_top_bounds12785 repair12785

noncomputable def covarianceEvent12785 : Set (AgFam 12785) :=
  BstLean.Part263.covarianceEvent 12785 scalarRow12785.grid parameters

theorem covarianceEvent12785_measurable : MeasurableSet covarianceEvent12785 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12785_payment :
    (retDist (paperDesignP 12785).toCentres).real
      (agentEv (paperDesignP 12785) covarianceEvent12785)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12785

theorem localCov12785 : BstLean.Part259.LocalCovarianceOn covarianceEvent12785
    (BstLean.Part263.cell scalarRow12785.grid) (caps repair12785) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12785

theorem covarianceGood12785_payment :
    (retDist (paperDesignP 12785).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12785)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12785_payment



end BstLean.Part269.N12785

namespace BstLean.Part269.N12785
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12785}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12785.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12785) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12785).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12785 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12785) (by norm_num) BstLean.Part268.WorldRow12785.worldPackage rfl
    BstLean.Part268.WorldRow12785.product_lower (BstLean.Part268.WorldRow12785.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12785} (hw : c ∈ Hof BstLean.Part268.WorldRow12785.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12785) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12785) (by norm_num) BstLean.Part268.WorldRow12785.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12785} (hw : c ∈ Hof BstLean.Part268.WorldRow12785.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12785) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12785).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12785) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12785_eq : scalarRow12785.targetFrame = BstLean.Part268.agent12785.frame := by
  norm_num [scalarRow12785,BstLean.Part268.agent12785]

noncomputable def frameData12785 : BstLean.Part264b.FrameData 12785 :=
  BstLean.Part269.frameData_from_numerics (n := 12785) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12785.worldPackage rfl BstLean.Part268.WorldRow12785.product_lower (BstLean.Part268.WorldRow12785.producthi.2.trans (by norm_num))
    scalarRow12785 repair12785 covarianceInputs12785 (fun i hi => sourceNumerics12785 hi)
    BstLean.Part268.agent12785.frame targetFrame12785_eq


end BstLean.Part269.N12785

namespace BstLean.Part269.N12786
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12786 : scalarRow12786.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12786, BstLean.Part268.grid12786, BstLean.Part263.worldGrid]

theorem supplies12786 (j : Fin 43) : Supply 12786 (parameters j)
    (cellLower scalarRow12786.grid (sourceIndex j))
    (cellUpper scalarRow12786.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12786.grid grid_top_bounds12786 j

theorem radii12786 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12786.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12786 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12786 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12786.grid grid_top_bounds12786 j hθ

noncomputable def covarianceInputs12786 :
    BstLean.Part263.CovarianceInputs 12786 scalarRow12786.grid parameters (caps repair12786) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12786 grid_top_bounds12786 repair12786

noncomputable def covarianceEvent12786 : Set (AgFam 12786) :=
  BstLean.Part263.covarianceEvent 12786 scalarRow12786.grid parameters

theorem covarianceEvent12786_measurable : MeasurableSet covarianceEvent12786 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12786_payment :
    (retDist (paperDesignP 12786).toCentres).real
      (agentEv (paperDesignP 12786) covarianceEvent12786)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12786

theorem localCov12786 : BstLean.Part259.LocalCovarianceOn covarianceEvent12786
    (BstLean.Part263.cell scalarRow12786.grid) (caps repair12786) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12786

theorem covarianceGood12786_payment :
    (retDist (paperDesignP 12786).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12786)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12786_payment



end BstLean.Part269.N12786

namespace BstLean.Part269.N12786
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12786}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12786.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12786) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12786).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12786 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12786) (by norm_num) BstLean.Part268.WorldRow12786.worldPackage rfl
    BstLean.Part268.WorldRow12786.product_lower (BstLean.Part268.WorldRow12786.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12786} (hw : c ∈ Hof BstLean.Part268.WorldRow12786.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12786) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12786) (by norm_num) BstLean.Part268.WorldRow12786.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12786} (hw : c ∈ Hof BstLean.Part268.WorldRow12786.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12786) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12786).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12786) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12786_eq : scalarRow12786.targetFrame = BstLean.Part268.agent12786.frame := by
  norm_num [scalarRow12786,BstLean.Part268.agent12786]

noncomputable def frameData12786 : BstLean.Part264b.FrameData 12786 :=
  BstLean.Part269.frameData_from_numerics (n := 12786) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12786.worldPackage rfl BstLean.Part268.WorldRow12786.product_lower (BstLean.Part268.WorldRow12786.producthi.2.trans (by norm_num))
    scalarRow12786 repair12786 covarianceInputs12786 (fun i hi => sourceNumerics12786 hi)
    BstLean.Part268.agent12786.frame targetFrame12786_eq


end BstLean.Part269.N12786

namespace BstLean.Part269.N12787
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12787 : scalarRow12787.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12787, BstLean.Part268.grid12787, BstLean.Part263.worldGrid]

theorem supplies12787 (j : Fin 43) : Supply 12787 (parameters j)
    (cellLower scalarRow12787.grid (sourceIndex j))
    (cellUpper scalarRow12787.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12787.grid grid_top_bounds12787 j

theorem radii12787 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12787.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12787 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12787 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12787.grid grid_top_bounds12787 j hθ

noncomputable def covarianceInputs12787 :
    BstLean.Part263.CovarianceInputs 12787 scalarRow12787.grid parameters (caps repair12787) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12787 grid_top_bounds12787 repair12787

noncomputable def covarianceEvent12787 : Set (AgFam 12787) :=
  BstLean.Part263.covarianceEvent 12787 scalarRow12787.grid parameters

theorem covarianceEvent12787_measurable : MeasurableSet covarianceEvent12787 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12787_payment :
    (retDist (paperDesignP 12787).toCentres).real
      (agentEv (paperDesignP 12787) covarianceEvent12787)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12787

theorem localCov12787 : BstLean.Part259.LocalCovarianceOn covarianceEvent12787
    (BstLean.Part263.cell scalarRow12787.grid) (caps repair12787) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12787

theorem covarianceGood12787_payment :
    (retDist (paperDesignP 12787).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12787)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12787_payment



end BstLean.Part269.N12787

namespace BstLean.Part269.N12787
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12787}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12787.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12787) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12787).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12787 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12787) (by norm_num) BstLean.Part268.WorldRow12787.worldPackage rfl
    BstLean.Part268.WorldRow12787.product_lower (BstLean.Part268.WorldRow12787.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12787} (hw : c ∈ Hof BstLean.Part268.WorldRow12787.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12787) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12787) (by norm_num) BstLean.Part268.WorldRow12787.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12787} (hw : c ∈ Hof BstLean.Part268.WorldRow12787.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12787) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12787).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12787) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12787_eq : scalarRow12787.targetFrame = BstLean.Part268.agent12787.frame := by
  norm_num [scalarRow12787,BstLean.Part268.agent12787]

noncomputable def frameData12787 : BstLean.Part264b.FrameData 12787 :=
  BstLean.Part269.frameData_from_numerics (n := 12787) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12787.worldPackage rfl BstLean.Part268.WorldRow12787.product_lower (BstLean.Part268.WorldRow12787.producthi.2.trans (by norm_num))
    scalarRow12787 repair12787 covarianceInputs12787 (fun i hi => sourceNumerics12787 hi)
    BstLean.Part268.agent12787.frame targetFrame12787_eq


end BstLean.Part269.N12787

namespace BstLean.Part269.N12788
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12788 : scalarRow12788.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12788, BstLean.Part268.grid12788, BstLean.Part263.worldGrid]

theorem supplies12788 (j : Fin 43) : Supply 12788 (parameters j)
    (cellLower scalarRow12788.grid (sourceIndex j))
    (cellUpper scalarRow12788.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12788.grid grid_top_bounds12788 j

theorem radii12788 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12788.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12788 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12788 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12788.grid grid_top_bounds12788 j hθ

noncomputable def covarianceInputs12788 :
    BstLean.Part263.CovarianceInputs 12788 scalarRow12788.grid parameters (caps repair12788) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12788 grid_top_bounds12788 repair12788

noncomputable def covarianceEvent12788 : Set (AgFam 12788) :=
  BstLean.Part263.covarianceEvent 12788 scalarRow12788.grid parameters

theorem covarianceEvent12788_measurable : MeasurableSet covarianceEvent12788 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12788_payment :
    (retDist (paperDesignP 12788).toCentres).real
      (agentEv (paperDesignP 12788) covarianceEvent12788)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12788

theorem localCov12788 : BstLean.Part259.LocalCovarianceOn covarianceEvent12788
    (BstLean.Part263.cell scalarRow12788.grid) (caps repair12788) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12788

theorem covarianceGood12788_payment :
    (retDist (paperDesignP 12788).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12788)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12788_payment



end BstLean.Part269.N12788

namespace BstLean.Part269.N12788
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12788}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12788.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12788) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12788).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12788 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12788) (by norm_num) BstLean.Part268.WorldRow12788.worldPackage rfl
    BstLean.Part268.WorldRow12788.product_lower (BstLean.Part268.WorldRow12788.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12788} (hw : c ∈ Hof BstLean.Part268.WorldRow12788.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12788) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12788) (by norm_num) BstLean.Part268.WorldRow12788.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12788} (hw : c ∈ Hof BstLean.Part268.WorldRow12788.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12788) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12788).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12788) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12788_eq : scalarRow12788.targetFrame = BstLean.Part268.agent12788.frame := by
  norm_num [scalarRow12788,BstLean.Part268.agent12788]

noncomputable def frameData12788 : BstLean.Part264b.FrameData 12788 :=
  BstLean.Part269.frameData_from_numerics (n := 12788) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12788.worldPackage rfl BstLean.Part268.WorldRow12788.product_lower (BstLean.Part268.WorldRow12788.producthi.2.trans (by norm_num))
    scalarRow12788 repair12788 covarianceInputs12788 (fun i hi => sourceNumerics12788 hi)
    BstLean.Part268.agent12788.frame targetFrame12788_eq


end BstLean.Part269.N12788

namespace BstLean.Part269.N12789
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12789 : scalarRow12789.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12789, BstLean.Part268.grid12789, BstLean.Part263.worldGrid]

theorem supplies12789 (j : Fin 43) : Supply 12789 (parameters j)
    (cellLower scalarRow12789.grid (sourceIndex j))
    (cellUpper scalarRow12789.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12789.grid grid_top_bounds12789 j

theorem radii12789 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12789.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12789 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12789 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12789.grid grid_top_bounds12789 j hθ

noncomputable def covarianceInputs12789 :
    BstLean.Part263.CovarianceInputs 12789 scalarRow12789.grid parameters (caps repair12789) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12789 grid_top_bounds12789 repair12789

noncomputable def covarianceEvent12789 : Set (AgFam 12789) :=
  BstLean.Part263.covarianceEvent 12789 scalarRow12789.grid parameters

theorem covarianceEvent12789_measurable : MeasurableSet covarianceEvent12789 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12789_payment :
    (retDist (paperDesignP 12789).toCentres).real
      (agentEv (paperDesignP 12789) covarianceEvent12789)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12789

theorem localCov12789 : BstLean.Part259.LocalCovarianceOn covarianceEvent12789
    (BstLean.Part263.cell scalarRow12789.grid) (caps repair12789) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12789

theorem covarianceGood12789_payment :
    (retDist (paperDesignP 12789).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12789)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12789_payment



end BstLean.Part269.N12789

namespace BstLean.Part269.N12789
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12789}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12789.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12789) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12789).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12789 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12789) (by norm_num) BstLean.Part268.WorldRow12789.worldPackage rfl
    BstLean.Part268.WorldRow12789.product_lower (BstLean.Part268.WorldRow12789.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12789} (hw : c ∈ Hof BstLean.Part268.WorldRow12789.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12789) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12789) (by norm_num) BstLean.Part268.WorldRow12789.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12789} (hw : c ∈ Hof BstLean.Part268.WorldRow12789.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12789) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12789).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12789) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12789_eq : scalarRow12789.targetFrame = BstLean.Part268.agent12789.frame := by
  norm_num [scalarRow12789,BstLean.Part268.agent12789]

noncomputable def frameData12789 : BstLean.Part264b.FrameData 12789 :=
  BstLean.Part269.frameData_from_numerics (n := 12789) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12789.worldPackage rfl BstLean.Part268.WorldRow12789.product_lower (BstLean.Part268.WorldRow12789.producthi.2.trans (by norm_num))
    scalarRow12789 repair12789 covarianceInputs12789 (fun i hi => sourceNumerics12789 hi)
    BstLean.Part268.agent12789.frame targetFrame12789_eq


end BstLean.Part269.N12789
