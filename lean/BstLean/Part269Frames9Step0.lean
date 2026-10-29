import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World9Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs9
import BstLean.Part269Rows9
import BstLean.Part269Sources9
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12575
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12575 : scalarRow12575.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12575, BstLean.Part268.grid12575, BstLean.Part263.worldGrid]

theorem supplies12575 (j : Fin 43) : Supply 12575 (parameters j)
    (cellLower scalarRow12575.grid (sourceIndex j))
    (cellUpper scalarRow12575.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12575.grid grid_top_bounds12575 j

theorem radii12575 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12575.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12575 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12575 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12575.grid grid_top_bounds12575 j hθ

noncomputable def covarianceInputs12575 :
    BstLean.Part263.CovarianceInputs 12575 scalarRow12575.grid parameters (caps repair12575) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12575 grid_top_bounds12575 repair12575

noncomputable def covarianceEvent12575 : Set (AgFam 12575) :=
  BstLean.Part263.covarianceEvent 12575 scalarRow12575.grid parameters

theorem covarianceEvent12575_measurable : MeasurableSet covarianceEvent12575 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12575_payment :
    (retDist (paperDesignP 12575).toCentres).real
      (agentEv (paperDesignP 12575) covarianceEvent12575)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12575

theorem localCov12575 : BstLean.Part259.LocalCovarianceOn covarianceEvent12575
    (BstLean.Part263.cell scalarRow12575.grid) (caps repair12575) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12575

theorem covarianceGood12575_payment :
    (retDist (paperDesignP 12575).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12575)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12575_payment



end BstLean.Part269.N12575

namespace BstLean.Part269.N12575
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12575}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12575.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12575) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12575).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12575 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12575) (by norm_num) BstLean.Part268.WorldRow12575.worldPackage rfl
    BstLean.Part268.WorldRow12575.product_lower (BstLean.Part268.WorldRow12575.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12575} (hw : c ∈ Hof BstLean.Part268.WorldRow12575.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12575) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12575) (by norm_num) BstLean.Part268.WorldRow12575.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12575} (hw : c ∈ Hof BstLean.Part268.WorldRow12575.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12575) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12575).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12575) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12575_eq : scalarRow12575.targetFrame = BstLean.Part268.agent12575.frame := by
  norm_num [scalarRow12575,BstLean.Part268.agent12575]

noncomputable def frameData12575 : BstLean.Part264b.FrameData 12575 :=
  BstLean.Part269.frameData_from_numerics (n := 12575) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12575.worldPackage rfl BstLean.Part268.WorldRow12575.product_lower (BstLean.Part268.WorldRow12575.producthi.2.trans (by norm_num))
    scalarRow12575 repair12575 covarianceInputs12575 (fun i hi => sourceNumerics12575 hi)
    BstLean.Part268.agent12575.frame targetFrame12575_eq


end BstLean.Part269.N12575

namespace BstLean.Part269.N12576
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12576 : scalarRow12576.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12576, BstLean.Part268.grid12576, BstLean.Part263.worldGrid]

theorem supplies12576 (j : Fin 43) : Supply 12576 (parameters j)
    (cellLower scalarRow12576.grid (sourceIndex j))
    (cellUpper scalarRow12576.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12576.grid grid_top_bounds12576 j

theorem radii12576 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12576.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12576 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12576 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12576.grid grid_top_bounds12576 j hθ

noncomputable def covarianceInputs12576 :
    BstLean.Part263.CovarianceInputs 12576 scalarRow12576.grid parameters (caps repair12576) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12576 grid_top_bounds12576 repair12576

noncomputable def covarianceEvent12576 : Set (AgFam 12576) :=
  BstLean.Part263.covarianceEvent 12576 scalarRow12576.grid parameters

theorem covarianceEvent12576_measurable : MeasurableSet covarianceEvent12576 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12576_payment :
    (retDist (paperDesignP 12576).toCentres).real
      (agentEv (paperDesignP 12576) covarianceEvent12576)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12576

theorem localCov12576 : BstLean.Part259.LocalCovarianceOn covarianceEvent12576
    (BstLean.Part263.cell scalarRow12576.grid) (caps repair12576) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12576

theorem covarianceGood12576_payment :
    (retDist (paperDesignP 12576).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12576)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12576_payment



end BstLean.Part269.N12576

namespace BstLean.Part269.N12576
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12576}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12576.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12576) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12576).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12576 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12576) (by norm_num) BstLean.Part268.WorldRow12576.worldPackage rfl
    BstLean.Part268.WorldRow12576.product_lower (BstLean.Part268.WorldRow12576.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12576} (hw : c ∈ Hof BstLean.Part268.WorldRow12576.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12576) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12576) (by norm_num) BstLean.Part268.WorldRow12576.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12576} (hw : c ∈ Hof BstLean.Part268.WorldRow12576.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12576) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12576).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12576) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12576_eq : scalarRow12576.targetFrame = BstLean.Part268.agent12576.frame := by
  norm_num [scalarRow12576,BstLean.Part268.agent12576]

noncomputable def frameData12576 : BstLean.Part264b.FrameData 12576 :=
  BstLean.Part269.frameData_from_numerics (n := 12576) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12576.worldPackage rfl BstLean.Part268.WorldRow12576.product_lower (BstLean.Part268.WorldRow12576.producthi.2.trans (by norm_num))
    scalarRow12576 repair12576 covarianceInputs12576 (fun i hi => sourceNumerics12576 hi)
    BstLean.Part268.agent12576.frame targetFrame12576_eq


end BstLean.Part269.N12576

namespace BstLean.Part269.N12577
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12577 : scalarRow12577.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12577, BstLean.Part268.grid12577, BstLean.Part263.worldGrid]

theorem supplies12577 (j : Fin 43) : Supply 12577 (parameters j)
    (cellLower scalarRow12577.grid (sourceIndex j))
    (cellUpper scalarRow12577.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12577.grid grid_top_bounds12577 j

theorem radii12577 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12577.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12577 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12577 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12577.grid grid_top_bounds12577 j hθ

noncomputable def covarianceInputs12577 :
    BstLean.Part263.CovarianceInputs 12577 scalarRow12577.grid parameters (caps repair12577) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12577 grid_top_bounds12577 repair12577

noncomputable def covarianceEvent12577 : Set (AgFam 12577) :=
  BstLean.Part263.covarianceEvent 12577 scalarRow12577.grid parameters

theorem covarianceEvent12577_measurable : MeasurableSet covarianceEvent12577 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12577_payment :
    (retDist (paperDesignP 12577).toCentres).real
      (agentEv (paperDesignP 12577) covarianceEvent12577)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12577

theorem localCov12577 : BstLean.Part259.LocalCovarianceOn covarianceEvent12577
    (BstLean.Part263.cell scalarRow12577.grid) (caps repair12577) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12577

theorem covarianceGood12577_payment :
    (retDist (paperDesignP 12577).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12577)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12577_payment



end BstLean.Part269.N12577

namespace BstLean.Part269.N12577
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12577}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12577.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12577) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12577).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12577 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12577) (by norm_num) BstLean.Part268.WorldRow12577.worldPackage rfl
    BstLean.Part268.WorldRow12577.product_lower (BstLean.Part268.WorldRow12577.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12577} (hw : c ∈ Hof BstLean.Part268.WorldRow12577.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12577) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12577) (by norm_num) BstLean.Part268.WorldRow12577.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12577} (hw : c ∈ Hof BstLean.Part268.WorldRow12577.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12577) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12577).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12577) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12577_eq : scalarRow12577.targetFrame = BstLean.Part268.agent12577.frame := by
  norm_num [scalarRow12577,BstLean.Part268.agent12577]

noncomputable def frameData12577 : BstLean.Part264b.FrameData 12577 :=
  BstLean.Part269.frameData_from_numerics (n := 12577) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12577.worldPackage rfl BstLean.Part268.WorldRow12577.product_lower (BstLean.Part268.WorldRow12577.producthi.2.trans (by norm_num))
    scalarRow12577 repair12577 covarianceInputs12577 (fun i hi => sourceNumerics12577 hi)
    BstLean.Part268.agent12577.frame targetFrame12577_eq


end BstLean.Part269.N12577

namespace BstLean.Part269.N12578
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12578 : scalarRow12578.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12578, BstLean.Part268.grid12578, BstLean.Part263.worldGrid]

theorem supplies12578 (j : Fin 43) : Supply 12578 (parameters j)
    (cellLower scalarRow12578.grid (sourceIndex j))
    (cellUpper scalarRow12578.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12578.grid grid_top_bounds12578 j

theorem radii12578 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12578.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12578 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12578 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12578.grid grid_top_bounds12578 j hθ

noncomputable def covarianceInputs12578 :
    BstLean.Part263.CovarianceInputs 12578 scalarRow12578.grid parameters (caps repair12578) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12578 grid_top_bounds12578 repair12578

noncomputable def covarianceEvent12578 : Set (AgFam 12578) :=
  BstLean.Part263.covarianceEvent 12578 scalarRow12578.grid parameters

theorem covarianceEvent12578_measurable : MeasurableSet covarianceEvent12578 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12578_payment :
    (retDist (paperDesignP 12578).toCentres).real
      (agentEv (paperDesignP 12578) covarianceEvent12578)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12578

theorem localCov12578 : BstLean.Part259.LocalCovarianceOn covarianceEvent12578
    (BstLean.Part263.cell scalarRow12578.grid) (caps repair12578) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12578

theorem covarianceGood12578_payment :
    (retDist (paperDesignP 12578).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12578)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12578_payment



end BstLean.Part269.N12578

namespace BstLean.Part269.N12578
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12578}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12578.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12578) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12578).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12578 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12578) (by norm_num) BstLean.Part268.WorldRow12578.worldPackage rfl
    BstLean.Part268.WorldRow12578.product_lower (BstLean.Part268.WorldRow12578.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12578} (hw : c ∈ Hof BstLean.Part268.WorldRow12578.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12578) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12578) (by norm_num) BstLean.Part268.WorldRow12578.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12578} (hw : c ∈ Hof BstLean.Part268.WorldRow12578.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12578) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12578).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12578) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12578_eq : scalarRow12578.targetFrame = BstLean.Part268.agent12578.frame := by
  norm_num [scalarRow12578,BstLean.Part268.agent12578]

noncomputable def frameData12578 : BstLean.Part264b.FrameData 12578 :=
  BstLean.Part269.frameData_from_numerics (n := 12578) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12578.worldPackage rfl BstLean.Part268.WorldRow12578.product_lower (BstLean.Part268.WorldRow12578.producthi.2.trans (by norm_num))
    scalarRow12578 repair12578 covarianceInputs12578 (fun i hi => sourceNumerics12578 hi)
    BstLean.Part268.agent12578.frame targetFrame12578_eq


end BstLean.Part269.N12578

namespace BstLean.Part269.N12579
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12579 : scalarRow12579.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12579, BstLean.Part268.grid12579, BstLean.Part263.worldGrid]

theorem supplies12579 (j : Fin 43) : Supply 12579 (parameters j)
    (cellLower scalarRow12579.grid (sourceIndex j))
    (cellUpper scalarRow12579.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12579.grid grid_top_bounds12579 j

theorem radii12579 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12579.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12579 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12579 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12579.grid grid_top_bounds12579 j hθ

noncomputable def covarianceInputs12579 :
    BstLean.Part263.CovarianceInputs 12579 scalarRow12579.grid parameters (caps repair12579) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12579 grid_top_bounds12579 repair12579

noncomputable def covarianceEvent12579 : Set (AgFam 12579) :=
  BstLean.Part263.covarianceEvent 12579 scalarRow12579.grid parameters

theorem covarianceEvent12579_measurable : MeasurableSet covarianceEvent12579 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12579_payment :
    (retDist (paperDesignP 12579).toCentres).real
      (agentEv (paperDesignP 12579) covarianceEvent12579)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12579

theorem localCov12579 : BstLean.Part259.LocalCovarianceOn covarianceEvent12579
    (BstLean.Part263.cell scalarRow12579.grid) (caps repair12579) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12579

theorem covarianceGood12579_payment :
    (retDist (paperDesignP 12579).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12579)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12579_payment



end BstLean.Part269.N12579

namespace BstLean.Part269.N12579
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12579}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12579.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12579) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12579).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12579 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12579) (by norm_num) BstLean.Part268.WorldRow12579.worldPackage rfl
    BstLean.Part268.WorldRow12579.product_lower (BstLean.Part268.WorldRow12579.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12579} (hw : c ∈ Hof BstLean.Part268.WorldRow12579.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12579) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12579) (by norm_num) BstLean.Part268.WorldRow12579.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12579} (hw : c ∈ Hof BstLean.Part268.WorldRow12579.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12579) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12579).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12579) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12579_eq : scalarRow12579.targetFrame = BstLean.Part268.agent12579.frame := by
  norm_num [scalarRow12579,BstLean.Part268.agent12579]

noncomputable def frameData12579 : BstLean.Part264b.FrameData 12579 :=
  BstLean.Part269.frameData_from_numerics (n := 12579) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12579.worldPackage rfl BstLean.Part268.WorldRow12579.product_lower (BstLean.Part268.WorldRow12579.producthi.2.trans (by norm_num))
    scalarRow12579 repair12579 covarianceInputs12579 (fun i hi => sourceNumerics12579 hi)
    BstLean.Part268.agent12579.frame targetFrame12579_eq


end BstLean.Part269.N12579
