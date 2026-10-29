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

namespace BstLean.Part269.N12795
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12795 : scalarRow12795.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12795, BstLean.Part268.grid12795, BstLean.Part263.worldGrid]

theorem supplies12795 (j : Fin 43) : Supply 12795 (parameters j)
    (cellLower scalarRow12795.grid (sourceIndex j))
    (cellUpper scalarRow12795.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12795.grid grid_top_bounds12795 j

theorem radii12795 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12795.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12795 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12795 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12795.grid grid_top_bounds12795 j hθ

noncomputable def covarianceInputs12795 :
    BstLean.Part263.CovarianceInputs 12795 scalarRow12795.grid parameters (caps repair12795) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12795 grid_top_bounds12795 repair12795

noncomputable def covarianceEvent12795 : Set (AgFam 12795) :=
  BstLean.Part263.covarianceEvent 12795 scalarRow12795.grid parameters

theorem covarianceEvent12795_measurable : MeasurableSet covarianceEvent12795 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12795_payment :
    (retDist (paperDesignP 12795).toCentres).real
      (agentEv (paperDesignP 12795) covarianceEvent12795)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12795

theorem localCov12795 : BstLean.Part259.LocalCovarianceOn covarianceEvent12795
    (BstLean.Part263.cell scalarRow12795.grid) (caps repair12795) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12795

theorem covarianceGood12795_payment :
    (retDist (paperDesignP 12795).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12795)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12795_payment



end BstLean.Part269.N12795

namespace BstLean.Part269.N12795
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12795}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12795.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12795) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12795).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12795 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12795) (by norm_num) BstLean.Part268.WorldRow12795.worldPackage rfl
    BstLean.Part268.WorldRow12795.product_lower (BstLean.Part268.WorldRow12795.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12795} (hw : c ∈ Hof BstLean.Part268.WorldRow12795.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12795) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12795) (by norm_num) BstLean.Part268.WorldRow12795.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12795} (hw : c ∈ Hof BstLean.Part268.WorldRow12795.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12795) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12795).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12795) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12795_eq : scalarRow12795.targetFrame = BstLean.Part268.agent12795.frame := by
  norm_num [scalarRow12795,BstLean.Part268.agent12795]

noncomputable def frameData12795 : BstLean.Part264b.FrameData 12795 :=
  BstLean.Part269.frameData_from_numerics (n := 12795) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12795.worldPackage rfl BstLean.Part268.WorldRow12795.product_lower (BstLean.Part268.WorldRow12795.producthi.2.trans (by norm_num))
    scalarRow12795 repair12795 covarianceInputs12795 (fun i hi => sourceNumerics12795 hi)
    BstLean.Part268.agent12795.frame targetFrame12795_eq


end BstLean.Part269.N12795

namespace BstLean.Part269.N12796
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12796 : scalarRow12796.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12796, BstLean.Part268.grid12796, BstLean.Part263.worldGrid]

theorem supplies12796 (j : Fin 43) : Supply 12796 (parameters j)
    (cellLower scalarRow12796.grid (sourceIndex j))
    (cellUpper scalarRow12796.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12796.grid grid_top_bounds12796 j

theorem radii12796 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12796.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12796 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12796 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12796.grid grid_top_bounds12796 j hθ

noncomputable def covarianceInputs12796 :
    BstLean.Part263.CovarianceInputs 12796 scalarRow12796.grid parameters (caps repair12796) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12796 grid_top_bounds12796 repair12796

noncomputable def covarianceEvent12796 : Set (AgFam 12796) :=
  BstLean.Part263.covarianceEvent 12796 scalarRow12796.grid parameters

theorem covarianceEvent12796_measurable : MeasurableSet covarianceEvent12796 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12796_payment :
    (retDist (paperDesignP 12796).toCentres).real
      (agentEv (paperDesignP 12796) covarianceEvent12796)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12796

theorem localCov12796 : BstLean.Part259.LocalCovarianceOn covarianceEvent12796
    (BstLean.Part263.cell scalarRow12796.grid) (caps repair12796) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12796

theorem covarianceGood12796_payment :
    (retDist (paperDesignP 12796).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12796)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12796_payment



end BstLean.Part269.N12796

namespace BstLean.Part269.N12796
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12796}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12796.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12796) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12796).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12796 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12796) (by norm_num) BstLean.Part268.WorldRow12796.worldPackage rfl
    BstLean.Part268.WorldRow12796.product_lower (BstLean.Part268.WorldRow12796.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12796} (hw : c ∈ Hof BstLean.Part268.WorldRow12796.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12796) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12796) (by norm_num) BstLean.Part268.WorldRow12796.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12796} (hw : c ∈ Hof BstLean.Part268.WorldRow12796.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12796) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12796).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12796) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12796_eq : scalarRow12796.targetFrame = BstLean.Part268.agent12796.frame := by
  norm_num [scalarRow12796,BstLean.Part268.agent12796]

noncomputable def frameData12796 : BstLean.Part264b.FrameData 12796 :=
  BstLean.Part269.frameData_from_numerics (n := 12796) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12796.worldPackage rfl BstLean.Part268.WorldRow12796.product_lower (BstLean.Part268.WorldRow12796.producthi.2.trans (by norm_num))
    scalarRow12796 repair12796 covarianceInputs12796 (fun i hi => sourceNumerics12796 hi)
    BstLean.Part268.agent12796.frame targetFrame12796_eq


end BstLean.Part269.N12796

namespace BstLean.Part269.N12797
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12797 : scalarRow12797.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12797, BstLean.Part268.grid12797, BstLean.Part263.worldGrid]

theorem supplies12797 (j : Fin 43) : Supply 12797 (parameters j)
    (cellLower scalarRow12797.grid (sourceIndex j))
    (cellUpper scalarRow12797.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12797.grid grid_top_bounds12797 j

theorem radii12797 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12797.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12797 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12797 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12797.grid grid_top_bounds12797 j hθ

noncomputable def covarianceInputs12797 :
    BstLean.Part263.CovarianceInputs 12797 scalarRow12797.grid parameters (caps repair12797) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12797 grid_top_bounds12797 repair12797

noncomputable def covarianceEvent12797 : Set (AgFam 12797) :=
  BstLean.Part263.covarianceEvent 12797 scalarRow12797.grid parameters

theorem covarianceEvent12797_measurable : MeasurableSet covarianceEvent12797 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12797_payment :
    (retDist (paperDesignP 12797).toCentres).real
      (agentEv (paperDesignP 12797) covarianceEvent12797)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12797

theorem localCov12797 : BstLean.Part259.LocalCovarianceOn covarianceEvent12797
    (BstLean.Part263.cell scalarRow12797.grid) (caps repair12797) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12797

theorem covarianceGood12797_payment :
    (retDist (paperDesignP 12797).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12797)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12797_payment



end BstLean.Part269.N12797

namespace BstLean.Part269.N12797
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12797}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12797.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12797) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12797).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12797 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12797) (by norm_num) BstLean.Part268.WorldRow12797.worldPackage rfl
    BstLean.Part268.WorldRow12797.product_lower (BstLean.Part268.WorldRow12797.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12797} (hw : c ∈ Hof BstLean.Part268.WorldRow12797.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12797) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12797) (by norm_num) BstLean.Part268.WorldRow12797.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12797} (hw : c ∈ Hof BstLean.Part268.WorldRow12797.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12797) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12797).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12797) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12797_eq : scalarRow12797.targetFrame = BstLean.Part268.agent12797.frame := by
  norm_num [scalarRow12797,BstLean.Part268.agent12797]

noncomputable def frameData12797 : BstLean.Part264b.FrameData 12797 :=
  BstLean.Part269.frameData_from_numerics (n := 12797) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12797.worldPackage rfl BstLean.Part268.WorldRow12797.product_lower (BstLean.Part268.WorldRow12797.producthi.2.trans (by norm_num))
    scalarRow12797 repair12797 covarianceInputs12797 (fun i hi => sourceNumerics12797 hi)
    BstLean.Part268.agent12797.frame targetFrame12797_eq


end BstLean.Part269.N12797

namespace BstLean.Part269.N12798
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12798 : scalarRow12798.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12798, BstLean.Part268.grid12798, BstLean.Part263.worldGrid]

theorem supplies12798 (j : Fin 43) : Supply 12798 (parameters j)
    (cellLower scalarRow12798.grid (sourceIndex j))
    (cellUpper scalarRow12798.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12798.grid grid_top_bounds12798 j

theorem radii12798 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12798.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12798 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12798 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12798.grid grid_top_bounds12798 j hθ

noncomputable def covarianceInputs12798 :
    BstLean.Part263.CovarianceInputs 12798 scalarRow12798.grid parameters (caps repair12798) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12798 grid_top_bounds12798 repair12798

noncomputable def covarianceEvent12798 : Set (AgFam 12798) :=
  BstLean.Part263.covarianceEvent 12798 scalarRow12798.grid parameters

theorem covarianceEvent12798_measurable : MeasurableSet covarianceEvent12798 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12798_payment :
    (retDist (paperDesignP 12798).toCentres).real
      (agentEv (paperDesignP 12798) covarianceEvent12798)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12798

theorem localCov12798 : BstLean.Part259.LocalCovarianceOn covarianceEvent12798
    (BstLean.Part263.cell scalarRow12798.grid) (caps repair12798) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12798

theorem covarianceGood12798_payment :
    (retDist (paperDesignP 12798).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12798)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12798_payment



end BstLean.Part269.N12798

namespace BstLean.Part269.N12798
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12798}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12798.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12798) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12798).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12798 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12798) (by norm_num) BstLean.Part268.WorldRow12798.worldPackage rfl
    BstLean.Part268.WorldRow12798.product_lower (BstLean.Part268.WorldRow12798.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12798} (hw : c ∈ Hof BstLean.Part268.WorldRow12798.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12798) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12798) (by norm_num) BstLean.Part268.WorldRow12798.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12798} (hw : c ∈ Hof BstLean.Part268.WorldRow12798.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12798) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12798).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12798) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12798_eq : scalarRow12798.targetFrame = BstLean.Part268.agent12798.frame := by
  norm_num [scalarRow12798,BstLean.Part268.agent12798]

noncomputable def frameData12798 : BstLean.Part264b.FrameData 12798 :=
  BstLean.Part269.frameData_from_numerics (n := 12798) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12798.worldPackage rfl BstLean.Part268.WorldRow12798.product_lower (BstLean.Part268.WorldRow12798.producthi.2.trans (by norm_num))
    scalarRow12798 repair12798 covarianceInputs12798 (fun i hi => sourceNumerics12798 hi)
    BstLean.Part268.agent12798.frame targetFrame12798_eq


end BstLean.Part269.N12798

namespace BstLean.Part269.N12799
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12799 : scalarRow12799.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12799, BstLean.Part268.grid12799, BstLean.Part263.worldGrid]

theorem supplies12799 (j : Fin 43) : Supply 12799 (parameters j)
    (cellLower scalarRow12799.grid (sourceIndex j))
    (cellUpper scalarRow12799.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12799.grid grid_top_bounds12799 j

theorem radii12799 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12799.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12799 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12799 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12799.grid grid_top_bounds12799 j hθ

noncomputable def covarianceInputs12799 :
    BstLean.Part263.CovarianceInputs 12799 scalarRow12799.grid parameters (caps repair12799) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12799 grid_top_bounds12799 repair12799

noncomputable def covarianceEvent12799 : Set (AgFam 12799) :=
  BstLean.Part263.covarianceEvent 12799 scalarRow12799.grid parameters

theorem covarianceEvent12799_measurable : MeasurableSet covarianceEvent12799 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12799_payment :
    (retDist (paperDesignP 12799).toCentres).real
      (agentEv (paperDesignP 12799) covarianceEvent12799)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12799

theorem localCov12799 : BstLean.Part259.LocalCovarianceOn covarianceEvent12799
    (BstLean.Part263.cell scalarRow12799.grid) (caps repair12799) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12799

theorem covarianceGood12799_payment :
    (retDist (paperDesignP 12799).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12799)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12799_payment



end BstLean.Part269.N12799

namespace BstLean.Part269.N12799
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12799}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12799.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12799) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12799).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12799 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12799) (by norm_num) BstLean.Part268.WorldRow12799.worldPackage rfl
    BstLean.Part268.WorldRow12799.product_lower (BstLean.Part268.WorldRow12799.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12799} (hw : c ∈ Hof BstLean.Part268.WorldRow12799.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12799) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12799) (by norm_num) BstLean.Part268.WorldRow12799.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12799} (hw : c ∈ Hof BstLean.Part268.WorldRow12799.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12799) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12799).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12799) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12799_eq : scalarRow12799.targetFrame = BstLean.Part268.agent12799.frame := by
  norm_num [scalarRow12799,BstLean.Part268.agent12799]

noncomputable def frameData12799 : BstLean.Part264b.FrameData 12799 :=
  BstLean.Part269.frameData_from_numerics (n := 12799) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12799.worldPackage rfl BstLean.Part268.WorldRow12799.product_lower (BstLean.Part268.WorldRow12799.producthi.2.trans (by norm_num))
    scalarRow12799 repair12799 covarianceInputs12799 (fun i hi => sourceNumerics12799 hi)
    BstLean.Part268.agent12799.frame targetFrame12799_eq


end BstLean.Part269.N12799
