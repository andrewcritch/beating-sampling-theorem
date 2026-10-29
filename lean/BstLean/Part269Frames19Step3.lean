import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World19Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs19
import BstLean.Part269Rows19
import BstLean.Part269Sources19
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12840
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12840 : scalarRow12840.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12840, BstLean.Part268.grid12840, BstLean.Part263.worldGrid]

theorem supplies12840 (j : Fin 43) : Supply 12840 (parameters j)
    (cellLower scalarRow12840.grid (sourceIndex j))
    (cellUpper scalarRow12840.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12840.grid grid_top_bounds12840 j

theorem radii12840 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12840.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12840 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12840 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12840.grid grid_top_bounds12840 j hθ

noncomputable def covarianceInputs12840 :
    BstLean.Part263.CovarianceInputs 12840 scalarRow12840.grid parameters (caps repair12840) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12840 grid_top_bounds12840 repair12840

noncomputable def covarianceEvent12840 : Set (AgFam 12840) :=
  BstLean.Part263.covarianceEvent 12840 scalarRow12840.grid parameters

theorem covarianceEvent12840_measurable : MeasurableSet covarianceEvent12840 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12840_payment :
    (retDist (paperDesignP 12840).toCentres).real
      (agentEv (paperDesignP 12840) covarianceEvent12840)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12840

theorem localCov12840 : BstLean.Part259.LocalCovarianceOn covarianceEvent12840
    (BstLean.Part263.cell scalarRow12840.grid) (caps repair12840) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12840

theorem covarianceGood12840_payment :
    (retDist (paperDesignP 12840).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12840)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12840_payment



end BstLean.Part269.N12840

namespace BstLean.Part269.N12840
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12840}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12840.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12840) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12840).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12840 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12840) (by norm_num) BstLean.Part268.WorldRow12840.worldPackage rfl
    BstLean.Part268.WorldRow12840.product_lower (BstLean.Part268.WorldRow12840.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12840} (hw : c ∈ Hof BstLean.Part268.WorldRow12840.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12840) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12840) (by norm_num) BstLean.Part268.WorldRow12840.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12840} (hw : c ∈ Hof BstLean.Part268.WorldRow12840.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12840) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12840).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12840) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12840_eq : scalarRow12840.targetFrame = BstLean.Part268.agent12840.frame := by
  norm_num [scalarRow12840,BstLean.Part268.agent12840]

noncomputable def frameData12840 : BstLean.Part264b.FrameData 12840 :=
  BstLean.Part269.frameData_from_numerics (n := 12840) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12840.worldPackage rfl BstLean.Part268.WorldRow12840.product_lower (BstLean.Part268.WorldRow12840.producthi.2.trans (by norm_num))
    scalarRow12840 repair12840 covarianceInputs12840 (fun i hi => sourceNumerics12840 hi)
    BstLean.Part268.agent12840.frame targetFrame12840_eq


end BstLean.Part269.N12840

namespace BstLean.Part269.N12841
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12841 : scalarRow12841.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12841, BstLean.Part268.grid12841, BstLean.Part263.worldGrid]

theorem supplies12841 (j : Fin 43) : Supply 12841 (parameters j)
    (cellLower scalarRow12841.grid (sourceIndex j))
    (cellUpper scalarRow12841.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12841.grid grid_top_bounds12841 j

theorem radii12841 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12841.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12841 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12841 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12841.grid grid_top_bounds12841 j hθ

noncomputable def covarianceInputs12841 :
    BstLean.Part263.CovarianceInputs 12841 scalarRow12841.grid parameters (caps repair12841) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12841 grid_top_bounds12841 repair12841

noncomputable def covarianceEvent12841 : Set (AgFam 12841) :=
  BstLean.Part263.covarianceEvent 12841 scalarRow12841.grid parameters

theorem covarianceEvent12841_measurable : MeasurableSet covarianceEvent12841 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12841_payment :
    (retDist (paperDesignP 12841).toCentres).real
      (agentEv (paperDesignP 12841) covarianceEvent12841)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12841

theorem localCov12841 : BstLean.Part259.LocalCovarianceOn covarianceEvent12841
    (BstLean.Part263.cell scalarRow12841.grid) (caps repair12841) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12841

theorem covarianceGood12841_payment :
    (retDist (paperDesignP 12841).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12841)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12841_payment



end BstLean.Part269.N12841

namespace BstLean.Part269.N12841
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12841}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12841.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12841) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12841).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12841 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12841) (by norm_num) BstLean.Part268.WorldRow12841.worldPackage rfl
    BstLean.Part268.WorldRow12841.product_lower (BstLean.Part268.WorldRow12841.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12841} (hw : c ∈ Hof BstLean.Part268.WorldRow12841.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12841) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12841) (by norm_num) BstLean.Part268.WorldRow12841.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12841} (hw : c ∈ Hof BstLean.Part268.WorldRow12841.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12841) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12841).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12841) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12841_eq : scalarRow12841.targetFrame = BstLean.Part268.agent12841.frame := by
  norm_num [scalarRow12841,BstLean.Part268.agent12841]

noncomputable def frameData12841 : BstLean.Part264b.FrameData 12841 :=
  BstLean.Part269.frameData_from_numerics (n := 12841) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12841.worldPackage rfl BstLean.Part268.WorldRow12841.product_lower (BstLean.Part268.WorldRow12841.producthi.2.trans (by norm_num))
    scalarRow12841 repair12841 covarianceInputs12841 (fun i hi => sourceNumerics12841 hi)
    BstLean.Part268.agent12841.frame targetFrame12841_eq


end BstLean.Part269.N12841

namespace BstLean.Part269.N12842
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12842 : scalarRow12842.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12842, BstLean.Part268.grid12842, BstLean.Part263.worldGrid]

theorem supplies12842 (j : Fin 43) : Supply 12842 (parameters j)
    (cellLower scalarRow12842.grid (sourceIndex j))
    (cellUpper scalarRow12842.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12842.grid grid_top_bounds12842 j

theorem radii12842 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12842.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12842 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12842 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12842.grid grid_top_bounds12842 j hθ

noncomputable def covarianceInputs12842 :
    BstLean.Part263.CovarianceInputs 12842 scalarRow12842.grid parameters (caps repair12842) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12842 grid_top_bounds12842 repair12842

noncomputable def covarianceEvent12842 : Set (AgFam 12842) :=
  BstLean.Part263.covarianceEvent 12842 scalarRow12842.grid parameters

theorem covarianceEvent12842_measurable : MeasurableSet covarianceEvent12842 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12842_payment :
    (retDist (paperDesignP 12842).toCentres).real
      (agentEv (paperDesignP 12842) covarianceEvent12842)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12842

theorem localCov12842 : BstLean.Part259.LocalCovarianceOn covarianceEvent12842
    (BstLean.Part263.cell scalarRow12842.grid) (caps repair12842) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12842

theorem covarianceGood12842_payment :
    (retDist (paperDesignP 12842).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12842)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12842_payment



end BstLean.Part269.N12842

namespace BstLean.Part269.N12842
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12842}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12842.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12842) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12842).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12842 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12842) (by norm_num) BstLean.Part268.WorldRow12842.worldPackage rfl
    BstLean.Part268.WorldRow12842.product_lower (BstLean.Part268.WorldRow12842.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12842} (hw : c ∈ Hof BstLean.Part268.WorldRow12842.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12842) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12842) (by norm_num) BstLean.Part268.WorldRow12842.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12842} (hw : c ∈ Hof BstLean.Part268.WorldRow12842.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12842) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12842).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12842) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12842_eq : scalarRow12842.targetFrame = BstLean.Part268.agent12842.frame := by
  norm_num [scalarRow12842,BstLean.Part268.agent12842]

noncomputable def frameData12842 : BstLean.Part264b.FrameData 12842 :=
  BstLean.Part269.frameData_from_numerics (n := 12842) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12842.worldPackage rfl BstLean.Part268.WorldRow12842.product_lower (BstLean.Part268.WorldRow12842.producthi.2.trans (by norm_num))
    scalarRow12842 repair12842 covarianceInputs12842 (fun i hi => sourceNumerics12842 hi)
    BstLean.Part268.agent12842.frame targetFrame12842_eq


end BstLean.Part269.N12842

namespace BstLean.Part269.N12843
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12843 : scalarRow12843.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12843, BstLean.Part268.grid12843, BstLean.Part263.worldGrid]

theorem supplies12843 (j : Fin 43) : Supply 12843 (parameters j)
    (cellLower scalarRow12843.grid (sourceIndex j))
    (cellUpper scalarRow12843.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12843.grid grid_top_bounds12843 j

theorem radii12843 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12843.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12843 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12843 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12843.grid grid_top_bounds12843 j hθ

noncomputable def covarianceInputs12843 :
    BstLean.Part263.CovarianceInputs 12843 scalarRow12843.grid parameters (caps repair12843) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12843 grid_top_bounds12843 repair12843

noncomputable def covarianceEvent12843 : Set (AgFam 12843) :=
  BstLean.Part263.covarianceEvent 12843 scalarRow12843.grid parameters

theorem covarianceEvent12843_measurable : MeasurableSet covarianceEvent12843 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12843_payment :
    (retDist (paperDesignP 12843).toCentres).real
      (agentEv (paperDesignP 12843) covarianceEvent12843)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12843

theorem localCov12843 : BstLean.Part259.LocalCovarianceOn covarianceEvent12843
    (BstLean.Part263.cell scalarRow12843.grid) (caps repair12843) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12843

theorem covarianceGood12843_payment :
    (retDist (paperDesignP 12843).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12843)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12843_payment



end BstLean.Part269.N12843

namespace BstLean.Part269.N12843
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12843}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12843.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12843) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12843).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12843 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12843) (by norm_num) BstLean.Part268.WorldRow12843.worldPackage rfl
    BstLean.Part268.WorldRow12843.product_lower (BstLean.Part268.WorldRow12843.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12843} (hw : c ∈ Hof BstLean.Part268.WorldRow12843.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12843) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12843) (by norm_num) BstLean.Part268.WorldRow12843.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12843} (hw : c ∈ Hof BstLean.Part268.WorldRow12843.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12843) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12843).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12843) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12843_eq : scalarRow12843.targetFrame = BstLean.Part268.agent12843.frame := by
  norm_num [scalarRow12843,BstLean.Part268.agent12843]

noncomputable def frameData12843 : BstLean.Part264b.FrameData 12843 :=
  BstLean.Part269.frameData_from_numerics (n := 12843) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12843.worldPackage rfl BstLean.Part268.WorldRow12843.product_lower (BstLean.Part268.WorldRow12843.producthi.2.trans (by norm_num))
    scalarRow12843 repair12843 covarianceInputs12843 (fun i hi => sourceNumerics12843 hi)
    BstLean.Part268.agent12843.frame targetFrame12843_eq


end BstLean.Part269.N12843

namespace BstLean.Part269.N12844
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12844 : scalarRow12844.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12844, BstLean.Part268.grid12844, BstLean.Part263.worldGrid]

theorem supplies12844 (j : Fin 43) : Supply 12844 (parameters j)
    (cellLower scalarRow12844.grid (sourceIndex j))
    (cellUpper scalarRow12844.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12844.grid grid_top_bounds12844 j

theorem radii12844 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12844.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12844 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12844 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12844.grid grid_top_bounds12844 j hθ

noncomputable def covarianceInputs12844 :
    BstLean.Part263.CovarianceInputs 12844 scalarRow12844.grid parameters (caps repair12844) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12844 grid_top_bounds12844 repair12844

noncomputable def covarianceEvent12844 : Set (AgFam 12844) :=
  BstLean.Part263.covarianceEvent 12844 scalarRow12844.grid parameters

theorem covarianceEvent12844_measurable : MeasurableSet covarianceEvent12844 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12844_payment :
    (retDist (paperDesignP 12844).toCentres).real
      (agentEv (paperDesignP 12844) covarianceEvent12844)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12844

theorem localCov12844 : BstLean.Part259.LocalCovarianceOn covarianceEvent12844
    (BstLean.Part263.cell scalarRow12844.grid) (caps repair12844) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12844

theorem covarianceGood12844_payment :
    (retDist (paperDesignP 12844).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12844)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12844_payment



end BstLean.Part269.N12844

namespace BstLean.Part269.N12844
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12844}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12844.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12844) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12844).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12844 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12844) (by norm_num) BstLean.Part268.WorldRow12844.worldPackage rfl
    BstLean.Part268.WorldRow12844.product_lower (BstLean.Part268.WorldRow12844.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12844} (hw : c ∈ Hof BstLean.Part268.WorldRow12844.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12844) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12844) (by norm_num) BstLean.Part268.WorldRow12844.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12844} (hw : c ∈ Hof BstLean.Part268.WorldRow12844.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12844) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12844).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12844) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12844_eq : scalarRow12844.targetFrame = BstLean.Part268.agent12844.frame := by
  norm_num [scalarRow12844,BstLean.Part268.agent12844]

noncomputable def frameData12844 : BstLean.Part264b.FrameData 12844 :=
  BstLean.Part269.frameData_from_numerics (n := 12844) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12844.worldPackage rfl BstLean.Part268.WorldRow12844.product_lower (BstLean.Part268.WorldRow12844.producthi.2.trans (by norm_num))
    scalarRow12844 repair12844 covarianceInputs12844 (fun i hi => sourceNumerics12844 hi)
    BstLean.Part268.agent12844.frame targetFrame12844_eq


end BstLean.Part269.N12844
