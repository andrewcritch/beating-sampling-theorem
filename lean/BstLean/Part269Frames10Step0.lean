import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World10Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs10
import BstLean.Part269Rows10
import BstLean.Part269Sources10
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12600
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12600 : scalarRow12600.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12600, BstLean.Part268.grid12600, BstLean.Part263.worldGrid]

theorem supplies12600 (j : Fin 43) : Supply 12600 (parameters j)
    (cellLower scalarRow12600.grid (sourceIndex j))
    (cellUpper scalarRow12600.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12600.grid grid_top_bounds12600 j

theorem radii12600 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12600.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12600 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12600 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12600.grid grid_top_bounds12600 j hθ

noncomputable def covarianceInputs12600 :
    BstLean.Part263.CovarianceInputs 12600 scalarRow12600.grid parameters (caps repair12600) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12600 grid_top_bounds12600 repair12600

noncomputable def covarianceEvent12600 : Set (AgFam 12600) :=
  BstLean.Part263.covarianceEvent 12600 scalarRow12600.grid parameters

theorem covarianceEvent12600_measurable : MeasurableSet covarianceEvent12600 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12600_payment :
    (retDist (paperDesignP 12600).toCentres).real
      (agentEv (paperDesignP 12600) covarianceEvent12600)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12600

theorem localCov12600 : BstLean.Part259.LocalCovarianceOn covarianceEvent12600
    (BstLean.Part263.cell scalarRow12600.grid) (caps repair12600) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12600

theorem covarianceGood12600_payment :
    (retDist (paperDesignP 12600).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12600)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12600_payment



end BstLean.Part269.N12600

namespace BstLean.Part269.N12600
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12600}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12600.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12600) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12600).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12600 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12600) (by norm_num) BstLean.Part268.WorldRow12600.worldPackage rfl
    BstLean.Part268.WorldRow12600.product_lower (BstLean.Part268.WorldRow12600.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12600} (hw : c ∈ Hof BstLean.Part268.WorldRow12600.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12600) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12600) (by norm_num) BstLean.Part268.WorldRow12600.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12600} (hw : c ∈ Hof BstLean.Part268.WorldRow12600.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12600) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12600).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12600) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12600_eq : scalarRow12600.targetFrame = BstLean.Part268.agent12600.frame := by
  norm_num [scalarRow12600,BstLean.Part268.agent12600]

noncomputable def frameData12600 : BstLean.Part264b.FrameData 12600 :=
  BstLean.Part269.frameData_from_numerics (n := 12600) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12600.worldPackage rfl BstLean.Part268.WorldRow12600.product_lower (BstLean.Part268.WorldRow12600.producthi.2.trans (by norm_num))
    scalarRow12600 repair12600 covarianceInputs12600 (fun i hi => sourceNumerics12600 hi)
    BstLean.Part268.agent12600.frame targetFrame12600_eq


end BstLean.Part269.N12600

namespace BstLean.Part269.N12601
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12601 : scalarRow12601.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12601, BstLean.Part268.grid12601, BstLean.Part263.worldGrid]

theorem supplies12601 (j : Fin 43) : Supply 12601 (parameters j)
    (cellLower scalarRow12601.grid (sourceIndex j))
    (cellUpper scalarRow12601.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12601.grid grid_top_bounds12601 j

theorem radii12601 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12601.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12601 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12601 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12601.grid grid_top_bounds12601 j hθ

noncomputable def covarianceInputs12601 :
    BstLean.Part263.CovarianceInputs 12601 scalarRow12601.grid parameters (caps repair12601) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12601 grid_top_bounds12601 repair12601

noncomputable def covarianceEvent12601 : Set (AgFam 12601) :=
  BstLean.Part263.covarianceEvent 12601 scalarRow12601.grid parameters

theorem covarianceEvent12601_measurable : MeasurableSet covarianceEvent12601 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12601_payment :
    (retDist (paperDesignP 12601).toCentres).real
      (agentEv (paperDesignP 12601) covarianceEvent12601)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12601

theorem localCov12601 : BstLean.Part259.LocalCovarianceOn covarianceEvent12601
    (BstLean.Part263.cell scalarRow12601.grid) (caps repair12601) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12601

theorem covarianceGood12601_payment :
    (retDist (paperDesignP 12601).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12601)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12601_payment



end BstLean.Part269.N12601

namespace BstLean.Part269.N12601
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12601}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12601.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12601) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12601).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12601 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12601) (by norm_num) BstLean.Part268.WorldRow12601.worldPackage rfl
    BstLean.Part268.WorldRow12601.product_lower (BstLean.Part268.WorldRow12601.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12601} (hw : c ∈ Hof BstLean.Part268.WorldRow12601.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12601) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12601) (by norm_num) BstLean.Part268.WorldRow12601.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12601} (hw : c ∈ Hof BstLean.Part268.WorldRow12601.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12601) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12601).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12601) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12601_eq : scalarRow12601.targetFrame = BstLean.Part268.agent12601.frame := by
  norm_num [scalarRow12601,BstLean.Part268.agent12601]

noncomputable def frameData12601 : BstLean.Part264b.FrameData 12601 :=
  BstLean.Part269.frameData_from_numerics (n := 12601) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12601.worldPackage rfl BstLean.Part268.WorldRow12601.product_lower (BstLean.Part268.WorldRow12601.producthi.2.trans (by norm_num))
    scalarRow12601 repair12601 covarianceInputs12601 (fun i hi => sourceNumerics12601 hi)
    BstLean.Part268.agent12601.frame targetFrame12601_eq


end BstLean.Part269.N12601

namespace BstLean.Part269.N12602
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12602 : scalarRow12602.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12602, BstLean.Part268.grid12602, BstLean.Part263.worldGrid]

theorem supplies12602 (j : Fin 43) : Supply 12602 (parameters j)
    (cellLower scalarRow12602.grid (sourceIndex j))
    (cellUpper scalarRow12602.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12602.grid grid_top_bounds12602 j

theorem radii12602 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12602.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12602 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12602 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12602.grid grid_top_bounds12602 j hθ

noncomputable def covarianceInputs12602 :
    BstLean.Part263.CovarianceInputs 12602 scalarRow12602.grid parameters (caps repair12602) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12602 grid_top_bounds12602 repair12602

noncomputable def covarianceEvent12602 : Set (AgFam 12602) :=
  BstLean.Part263.covarianceEvent 12602 scalarRow12602.grid parameters

theorem covarianceEvent12602_measurable : MeasurableSet covarianceEvent12602 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12602_payment :
    (retDist (paperDesignP 12602).toCentres).real
      (agentEv (paperDesignP 12602) covarianceEvent12602)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12602

theorem localCov12602 : BstLean.Part259.LocalCovarianceOn covarianceEvent12602
    (BstLean.Part263.cell scalarRow12602.grid) (caps repair12602) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12602

theorem covarianceGood12602_payment :
    (retDist (paperDesignP 12602).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12602)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12602_payment



end BstLean.Part269.N12602

namespace BstLean.Part269.N12602
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12602}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12602.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12602) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12602).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12602 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12602) (by norm_num) BstLean.Part268.WorldRow12602.worldPackage rfl
    BstLean.Part268.WorldRow12602.product_lower (BstLean.Part268.WorldRow12602.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12602} (hw : c ∈ Hof BstLean.Part268.WorldRow12602.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12602) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12602) (by norm_num) BstLean.Part268.WorldRow12602.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12602} (hw : c ∈ Hof BstLean.Part268.WorldRow12602.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12602) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12602).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12602) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12602_eq : scalarRow12602.targetFrame = BstLean.Part268.agent12602.frame := by
  norm_num [scalarRow12602,BstLean.Part268.agent12602]

noncomputable def frameData12602 : BstLean.Part264b.FrameData 12602 :=
  BstLean.Part269.frameData_from_numerics (n := 12602) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12602.worldPackage rfl BstLean.Part268.WorldRow12602.product_lower (BstLean.Part268.WorldRow12602.producthi.2.trans (by norm_num))
    scalarRow12602 repair12602 covarianceInputs12602 (fun i hi => sourceNumerics12602 hi)
    BstLean.Part268.agent12602.frame targetFrame12602_eq


end BstLean.Part269.N12602

namespace BstLean.Part269.N12603
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12603 : scalarRow12603.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12603, BstLean.Part268.grid12603, BstLean.Part263.worldGrid]

theorem supplies12603 (j : Fin 43) : Supply 12603 (parameters j)
    (cellLower scalarRow12603.grid (sourceIndex j))
    (cellUpper scalarRow12603.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12603.grid grid_top_bounds12603 j

theorem radii12603 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12603.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12603 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12603 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12603.grid grid_top_bounds12603 j hθ

noncomputable def covarianceInputs12603 :
    BstLean.Part263.CovarianceInputs 12603 scalarRow12603.grid parameters (caps repair12603) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12603 grid_top_bounds12603 repair12603

noncomputable def covarianceEvent12603 : Set (AgFam 12603) :=
  BstLean.Part263.covarianceEvent 12603 scalarRow12603.grid parameters

theorem covarianceEvent12603_measurable : MeasurableSet covarianceEvent12603 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12603_payment :
    (retDist (paperDesignP 12603).toCentres).real
      (agentEv (paperDesignP 12603) covarianceEvent12603)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12603

theorem localCov12603 : BstLean.Part259.LocalCovarianceOn covarianceEvent12603
    (BstLean.Part263.cell scalarRow12603.grid) (caps repair12603) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12603

theorem covarianceGood12603_payment :
    (retDist (paperDesignP 12603).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12603)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12603_payment



end BstLean.Part269.N12603

namespace BstLean.Part269.N12603
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12603}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12603.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12603) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12603).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12603 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12603) (by norm_num) BstLean.Part268.WorldRow12603.worldPackage rfl
    BstLean.Part268.WorldRow12603.product_lower (BstLean.Part268.WorldRow12603.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12603} (hw : c ∈ Hof BstLean.Part268.WorldRow12603.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12603) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12603) (by norm_num) BstLean.Part268.WorldRow12603.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12603} (hw : c ∈ Hof BstLean.Part268.WorldRow12603.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12603) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12603).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12603) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12603_eq : scalarRow12603.targetFrame = BstLean.Part268.agent12603.frame := by
  norm_num [scalarRow12603,BstLean.Part268.agent12603]

noncomputable def frameData12603 : BstLean.Part264b.FrameData 12603 :=
  BstLean.Part269.frameData_from_numerics (n := 12603) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12603.worldPackage rfl BstLean.Part268.WorldRow12603.product_lower (BstLean.Part268.WorldRow12603.producthi.2.trans (by norm_num))
    scalarRow12603 repair12603 covarianceInputs12603 (fun i hi => sourceNumerics12603 hi)
    BstLean.Part268.agent12603.frame targetFrame12603_eq


end BstLean.Part269.N12603

namespace BstLean.Part269.N12604
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12604 : scalarRow12604.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12604, BstLean.Part268.grid12604, BstLean.Part263.worldGrid]

theorem supplies12604 (j : Fin 43) : Supply 12604 (parameters j)
    (cellLower scalarRow12604.grid (sourceIndex j))
    (cellUpper scalarRow12604.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12604.grid grid_top_bounds12604 j

theorem radii12604 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12604.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12604 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12604 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12604.grid grid_top_bounds12604 j hθ

noncomputable def covarianceInputs12604 :
    BstLean.Part263.CovarianceInputs 12604 scalarRow12604.grid parameters (caps repair12604) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12604 grid_top_bounds12604 repair12604

noncomputable def covarianceEvent12604 : Set (AgFam 12604) :=
  BstLean.Part263.covarianceEvent 12604 scalarRow12604.grid parameters

theorem covarianceEvent12604_measurable : MeasurableSet covarianceEvent12604 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12604_payment :
    (retDist (paperDesignP 12604).toCentres).real
      (agentEv (paperDesignP 12604) covarianceEvent12604)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12604

theorem localCov12604 : BstLean.Part259.LocalCovarianceOn covarianceEvent12604
    (BstLean.Part263.cell scalarRow12604.grid) (caps repair12604) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12604

theorem covarianceGood12604_payment :
    (retDist (paperDesignP 12604).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12604)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12604_payment



end BstLean.Part269.N12604

namespace BstLean.Part269.N12604
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12604}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12604.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12604) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12604).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12604 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12604) (by norm_num) BstLean.Part268.WorldRow12604.worldPackage rfl
    BstLean.Part268.WorldRow12604.product_lower (BstLean.Part268.WorldRow12604.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12604} (hw : c ∈ Hof BstLean.Part268.WorldRow12604.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12604) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12604) (by norm_num) BstLean.Part268.WorldRow12604.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12604} (hw : c ∈ Hof BstLean.Part268.WorldRow12604.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12604) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12604).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12604) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12604_eq : scalarRow12604.targetFrame = BstLean.Part268.agent12604.frame := by
  norm_num [scalarRow12604,BstLean.Part268.agent12604]

noncomputable def frameData12604 : BstLean.Part264b.FrameData 12604 :=
  BstLean.Part269.frameData_from_numerics (n := 12604) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12604.worldPackage rfl BstLean.Part268.WorldRow12604.product_lower (BstLean.Part268.WorldRow12604.producthi.2.trans (by norm_num))
    scalarRow12604 repair12604 covarianceInputs12604 (fun i hi => sourceNumerics12604 hi)
    BstLean.Part268.agent12604.frame targetFrame12604_eq


end BstLean.Part269.N12604
