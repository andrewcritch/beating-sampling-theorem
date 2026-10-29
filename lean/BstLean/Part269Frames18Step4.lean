import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World18Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs18
import BstLean.Part269Rows18
import BstLean.Part269Sources18
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12820
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12820 : scalarRow12820.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12820, BstLean.Part268.grid12820, BstLean.Part263.worldGrid]

theorem supplies12820 (j : Fin 43) : Supply 12820 (parameters j)
    (cellLower scalarRow12820.grid (sourceIndex j))
    (cellUpper scalarRow12820.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12820.grid grid_top_bounds12820 j

theorem radii12820 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12820.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12820 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12820 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12820.grid grid_top_bounds12820 j hθ

noncomputable def covarianceInputs12820 :
    BstLean.Part263.CovarianceInputs 12820 scalarRow12820.grid parameters (caps repair12820) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12820 grid_top_bounds12820 repair12820

noncomputable def covarianceEvent12820 : Set (AgFam 12820) :=
  BstLean.Part263.covarianceEvent 12820 scalarRow12820.grid parameters

theorem covarianceEvent12820_measurable : MeasurableSet covarianceEvent12820 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12820_payment :
    (retDist (paperDesignP 12820).toCentres).real
      (agentEv (paperDesignP 12820) covarianceEvent12820)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12820

theorem localCov12820 : BstLean.Part259.LocalCovarianceOn covarianceEvent12820
    (BstLean.Part263.cell scalarRow12820.grid) (caps repair12820) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12820

theorem covarianceGood12820_payment :
    (retDist (paperDesignP 12820).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12820)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12820_payment



end BstLean.Part269.N12820

namespace BstLean.Part269.N12820
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12820}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12820.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12820) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12820).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12820 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12820) (by norm_num) BstLean.Part268.WorldRow12820.worldPackage rfl
    BstLean.Part268.WorldRow12820.product_lower (BstLean.Part268.WorldRow12820.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12820} (hw : c ∈ Hof BstLean.Part268.WorldRow12820.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12820) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12820) (by norm_num) BstLean.Part268.WorldRow12820.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12820} (hw : c ∈ Hof BstLean.Part268.WorldRow12820.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12820) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12820).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12820) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12820_eq : scalarRow12820.targetFrame = BstLean.Part268.agent12820.frame := by
  norm_num [scalarRow12820,BstLean.Part268.agent12820]

noncomputable def frameData12820 : BstLean.Part264b.FrameData 12820 :=
  BstLean.Part269.frameData_from_numerics (n := 12820) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12820.worldPackage rfl BstLean.Part268.WorldRow12820.product_lower (BstLean.Part268.WorldRow12820.producthi.2.trans (by norm_num))
    scalarRow12820 repair12820 covarianceInputs12820 (fun i hi => sourceNumerics12820 hi)
    BstLean.Part268.agent12820.frame targetFrame12820_eq


end BstLean.Part269.N12820

namespace BstLean.Part269.N12821
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12821 : scalarRow12821.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12821, BstLean.Part268.grid12821, BstLean.Part263.worldGrid]

theorem supplies12821 (j : Fin 43) : Supply 12821 (parameters j)
    (cellLower scalarRow12821.grid (sourceIndex j))
    (cellUpper scalarRow12821.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12821.grid grid_top_bounds12821 j

theorem radii12821 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12821.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12821 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12821 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12821.grid grid_top_bounds12821 j hθ

noncomputable def covarianceInputs12821 :
    BstLean.Part263.CovarianceInputs 12821 scalarRow12821.grid parameters (caps repair12821) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12821 grid_top_bounds12821 repair12821

noncomputable def covarianceEvent12821 : Set (AgFam 12821) :=
  BstLean.Part263.covarianceEvent 12821 scalarRow12821.grid parameters

theorem covarianceEvent12821_measurable : MeasurableSet covarianceEvent12821 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12821_payment :
    (retDist (paperDesignP 12821).toCentres).real
      (agentEv (paperDesignP 12821) covarianceEvent12821)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12821

theorem localCov12821 : BstLean.Part259.LocalCovarianceOn covarianceEvent12821
    (BstLean.Part263.cell scalarRow12821.grid) (caps repair12821) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12821

theorem covarianceGood12821_payment :
    (retDist (paperDesignP 12821).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12821)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12821_payment



end BstLean.Part269.N12821

namespace BstLean.Part269.N12821
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12821}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12821.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12821) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12821).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12821 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12821) (by norm_num) BstLean.Part268.WorldRow12821.worldPackage rfl
    BstLean.Part268.WorldRow12821.product_lower (BstLean.Part268.WorldRow12821.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12821} (hw : c ∈ Hof BstLean.Part268.WorldRow12821.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12821) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12821) (by norm_num) BstLean.Part268.WorldRow12821.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12821} (hw : c ∈ Hof BstLean.Part268.WorldRow12821.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12821) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12821).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12821) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12821_eq : scalarRow12821.targetFrame = BstLean.Part268.agent12821.frame := by
  norm_num [scalarRow12821,BstLean.Part268.agent12821]

noncomputable def frameData12821 : BstLean.Part264b.FrameData 12821 :=
  BstLean.Part269.frameData_from_numerics (n := 12821) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12821.worldPackage rfl BstLean.Part268.WorldRow12821.product_lower (BstLean.Part268.WorldRow12821.producthi.2.trans (by norm_num))
    scalarRow12821 repair12821 covarianceInputs12821 (fun i hi => sourceNumerics12821 hi)
    BstLean.Part268.agent12821.frame targetFrame12821_eq


end BstLean.Part269.N12821

namespace BstLean.Part269.N12822
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12822 : scalarRow12822.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12822, BstLean.Part268.grid12822, BstLean.Part263.worldGrid]

theorem supplies12822 (j : Fin 43) : Supply 12822 (parameters j)
    (cellLower scalarRow12822.grid (sourceIndex j))
    (cellUpper scalarRow12822.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12822.grid grid_top_bounds12822 j

theorem radii12822 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12822.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12822 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12822 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12822.grid grid_top_bounds12822 j hθ

noncomputable def covarianceInputs12822 :
    BstLean.Part263.CovarianceInputs 12822 scalarRow12822.grid parameters (caps repair12822) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12822 grid_top_bounds12822 repair12822

noncomputable def covarianceEvent12822 : Set (AgFam 12822) :=
  BstLean.Part263.covarianceEvent 12822 scalarRow12822.grid parameters

theorem covarianceEvent12822_measurable : MeasurableSet covarianceEvent12822 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12822_payment :
    (retDist (paperDesignP 12822).toCentres).real
      (agentEv (paperDesignP 12822) covarianceEvent12822)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12822

theorem localCov12822 : BstLean.Part259.LocalCovarianceOn covarianceEvent12822
    (BstLean.Part263.cell scalarRow12822.grid) (caps repair12822) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12822

theorem covarianceGood12822_payment :
    (retDist (paperDesignP 12822).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12822)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12822_payment



end BstLean.Part269.N12822

namespace BstLean.Part269.N12822
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12822}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12822.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12822) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12822).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12822 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12822) (by norm_num) BstLean.Part268.WorldRow12822.worldPackage rfl
    BstLean.Part268.WorldRow12822.product_lower (BstLean.Part268.WorldRow12822.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12822} (hw : c ∈ Hof BstLean.Part268.WorldRow12822.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12822) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12822) (by norm_num) BstLean.Part268.WorldRow12822.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12822} (hw : c ∈ Hof BstLean.Part268.WorldRow12822.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12822) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12822).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12822) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12822_eq : scalarRow12822.targetFrame = BstLean.Part268.agent12822.frame := by
  norm_num [scalarRow12822,BstLean.Part268.agent12822]

noncomputable def frameData12822 : BstLean.Part264b.FrameData 12822 :=
  BstLean.Part269.frameData_from_numerics (n := 12822) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12822.worldPackage rfl BstLean.Part268.WorldRow12822.product_lower (BstLean.Part268.WorldRow12822.producthi.2.trans (by norm_num))
    scalarRow12822 repair12822 covarianceInputs12822 (fun i hi => sourceNumerics12822 hi)
    BstLean.Part268.agent12822.frame targetFrame12822_eq


end BstLean.Part269.N12822

namespace BstLean.Part269.N12823
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12823 : scalarRow12823.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12823, BstLean.Part268.grid12823, BstLean.Part263.worldGrid]

theorem supplies12823 (j : Fin 43) : Supply 12823 (parameters j)
    (cellLower scalarRow12823.grid (sourceIndex j))
    (cellUpper scalarRow12823.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12823.grid grid_top_bounds12823 j

theorem radii12823 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12823.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12823 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12823 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12823.grid grid_top_bounds12823 j hθ

noncomputable def covarianceInputs12823 :
    BstLean.Part263.CovarianceInputs 12823 scalarRow12823.grid parameters (caps repair12823) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12823 grid_top_bounds12823 repair12823

noncomputable def covarianceEvent12823 : Set (AgFam 12823) :=
  BstLean.Part263.covarianceEvent 12823 scalarRow12823.grid parameters

theorem covarianceEvent12823_measurable : MeasurableSet covarianceEvent12823 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12823_payment :
    (retDist (paperDesignP 12823).toCentres).real
      (agentEv (paperDesignP 12823) covarianceEvent12823)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12823

theorem localCov12823 : BstLean.Part259.LocalCovarianceOn covarianceEvent12823
    (BstLean.Part263.cell scalarRow12823.grid) (caps repair12823) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12823

theorem covarianceGood12823_payment :
    (retDist (paperDesignP 12823).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12823)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12823_payment



end BstLean.Part269.N12823

namespace BstLean.Part269.N12823
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12823}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12823.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12823) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12823).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12823 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12823) (by norm_num) BstLean.Part268.WorldRow12823.worldPackage rfl
    BstLean.Part268.WorldRow12823.product_lower (BstLean.Part268.WorldRow12823.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12823} (hw : c ∈ Hof BstLean.Part268.WorldRow12823.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12823) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12823) (by norm_num) BstLean.Part268.WorldRow12823.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12823} (hw : c ∈ Hof BstLean.Part268.WorldRow12823.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12823) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12823).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12823) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12823_eq : scalarRow12823.targetFrame = BstLean.Part268.agent12823.frame := by
  norm_num [scalarRow12823,BstLean.Part268.agent12823]

noncomputable def frameData12823 : BstLean.Part264b.FrameData 12823 :=
  BstLean.Part269.frameData_from_numerics (n := 12823) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12823.worldPackage rfl BstLean.Part268.WorldRow12823.product_lower (BstLean.Part268.WorldRow12823.producthi.2.trans (by norm_num))
    scalarRow12823 repair12823 covarianceInputs12823 (fun i hi => sourceNumerics12823 hi)
    BstLean.Part268.agent12823.frame targetFrame12823_eq


end BstLean.Part269.N12823

namespace BstLean.Part269.N12824
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12824 : scalarRow12824.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12824, BstLean.Part268.grid12824, BstLean.Part263.worldGrid]

theorem supplies12824 (j : Fin 43) : Supply 12824 (parameters j)
    (cellLower scalarRow12824.grid (sourceIndex j))
    (cellUpper scalarRow12824.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12824.grid grid_top_bounds12824 j

theorem radii12824 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12824.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12824 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12824 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12824.grid grid_top_bounds12824 j hθ

noncomputable def covarianceInputs12824 :
    BstLean.Part263.CovarianceInputs 12824 scalarRow12824.grid parameters (caps repair12824) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12824 grid_top_bounds12824 repair12824

noncomputable def covarianceEvent12824 : Set (AgFam 12824) :=
  BstLean.Part263.covarianceEvent 12824 scalarRow12824.grid parameters

theorem covarianceEvent12824_measurable : MeasurableSet covarianceEvent12824 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12824_payment :
    (retDist (paperDesignP 12824).toCentres).real
      (agentEv (paperDesignP 12824) covarianceEvent12824)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12824

theorem localCov12824 : BstLean.Part259.LocalCovarianceOn covarianceEvent12824
    (BstLean.Part263.cell scalarRow12824.grid) (caps repair12824) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12824

theorem covarianceGood12824_payment :
    (retDist (paperDesignP 12824).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12824)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12824_payment



end BstLean.Part269.N12824

namespace BstLean.Part269.N12824
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12824}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12824.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12824) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12824).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12824 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12824) (by norm_num) BstLean.Part268.WorldRow12824.worldPackage rfl
    BstLean.Part268.WorldRow12824.product_lower (BstLean.Part268.WorldRow12824.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12824} (hw : c ∈ Hof BstLean.Part268.WorldRow12824.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12824) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12824) (by norm_num) BstLean.Part268.WorldRow12824.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12824} (hw : c ∈ Hof BstLean.Part268.WorldRow12824.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12824) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12824).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12824) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12824_eq : scalarRow12824.targetFrame = BstLean.Part268.agent12824.frame := by
  norm_num [scalarRow12824,BstLean.Part268.agent12824]

noncomputable def frameData12824 : BstLean.Part264b.FrameData 12824 :=
  BstLean.Part269.frameData_from_numerics (n := 12824) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12824.worldPackage rfl BstLean.Part268.WorldRow12824.product_lower (BstLean.Part268.WorldRow12824.producthi.2.trans (by norm_num))
    scalarRow12824 repair12824 covarianceInputs12824 (fun i hi => sourceNumerics12824 hi)
    BstLean.Part268.agent12824.frame targetFrame12824_eq


end BstLean.Part269.N12824
