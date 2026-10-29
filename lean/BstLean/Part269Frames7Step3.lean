import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World7Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs7
import BstLean.Part269Rows7
import BstLean.Part269Sources7
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12540
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12540 : scalarRow12540.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12540, BstLean.Part268.grid12540, BstLean.Part263.worldGrid]

theorem supplies12540 (j : Fin 43) : Supply 12540 (parameters j)
    (cellLower scalarRow12540.grid (sourceIndex j))
    (cellUpper scalarRow12540.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12540.grid grid_top_bounds12540 j

theorem radii12540 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12540.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12540 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12540 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12540.grid grid_top_bounds12540 j hθ

noncomputable def covarianceInputs12540 :
    BstLean.Part263.CovarianceInputs 12540 scalarRow12540.grid parameters (caps repair12540) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12540 grid_top_bounds12540 repair12540

noncomputable def covarianceEvent12540 : Set (AgFam 12540) :=
  BstLean.Part263.covarianceEvent 12540 scalarRow12540.grid parameters

theorem covarianceEvent12540_measurable : MeasurableSet covarianceEvent12540 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12540_payment :
    (retDist (paperDesignP 12540).toCentres).real
      (agentEv (paperDesignP 12540) covarianceEvent12540)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12540

theorem localCov12540 : BstLean.Part259.LocalCovarianceOn covarianceEvent12540
    (BstLean.Part263.cell scalarRow12540.grid) (caps repair12540) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12540

theorem covarianceGood12540_payment :
    (retDist (paperDesignP 12540).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12540)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12540_payment



end BstLean.Part269.N12540

namespace BstLean.Part269.N12540
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12540}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12540.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12540) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12540).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12540 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12540) (by norm_num) BstLean.Part268.WorldRow12540.worldPackage rfl
    BstLean.Part268.WorldRow12540.product_lower (BstLean.Part268.WorldRow12540.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12540} (hw : c ∈ Hof BstLean.Part268.WorldRow12540.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12540) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12540) (by norm_num) BstLean.Part268.WorldRow12540.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12540} (hw : c ∈ Hof BstLean.Part268.WorldRow12540.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12540) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12540).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12540) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12540_eq : scalarRow12540.targetFrame = BstLean.Part268.agent12540.frame := by
  norm_num [scalarRow12540,BstLean.Part268.agent12540]

noncomputable def frameData12540 : BstLean.Part264b.FrameData 12540 :=
  BstLean.Part269.frameData_from_numerics (n := 12540) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12540.worldPackage rfl BstLean.Part268.WorldRow12540.product_lower (BstLean.Part268.WorldRow12540.producthi.2.trans (by norm_num))
    scalarRow12540 repair12540 covarianceInputs12540 (fun i hi => sourceNumerics12540 hi)
    BstLean.Part268.agent12540.frame targetFrame12540_eq


end BstLean.Part269.N12540

namespace BstLean.Part269.N12541
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12541 : scalarRow12541.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12541, BstLean.Part268.grid12541, BstLean.Part263.worldGrid]

theorem supplies12541 (j : Fin 43) : Supply 12541 (parameters j)
    (cellLower scalarRow12541.grid (sourceIndex j))
    (cellUpper scalarRow12541.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12541.grid grid_top_bounds12541 j

theorem radii12541 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12541.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12541 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12541 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12541.grid grid_top_bounds12541 j hθ

noncomputable def covarianceInputs12541 :
    BstLean.Part263.CovarianceInputs 12541 scalarRow12541.grid parameters (caps repair12541) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12541 grid_top_bounds12541 repair12541

noncomputable def covarianceEvent12541 : Set (AgFam 12541) :=
  BstLean.Part263.covarianceEvent 12541 scalarRow12541.grid parameters

theorem covarianceEvent12541_measurable : MeasurableSet covarianceEvent12541 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12541_payment :
    (retDist (paperDesignP 12541).toCentres).real
      (agentEv (paperDesignP 12541) covarianceEvent12541)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12541

theorem localCov12541 : BstLean.Part259.LocalCovarianceOn covarianceEvent12541
    (BstLean.Part263.cell scalarRow12541.grid) (caps repair12541) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12541

theorem covarianceGood12541_payment :
    (retDist (paperDesignP 12541).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12541)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12541_payment



end BstLean.Part269.N12541

namespace BstLean.Part269.N12541
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12541}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12541.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12541) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12541).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12541 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12541) (by norm_num) BstLean.Part268.WorldRow12541.worldPackage rfl
    BstLean.Part268.WorldRow12541.product_lower (BstLean.Part268.WorldRow12541.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12541} (hw : c ∈ Hof BstLean.Part268.WorldRow12541.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12541) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12541) (by norm_num) BstLean.Part268.WorldRow12541.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12541} (hw : c ∈ Hof BstLean.Part268.WorldRow12541.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12541) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12541).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12541) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12541_eq : scalarRow12541.targetFrame = BstLean.Part268.agent12541.frame := by
  norm_num [scalarRow12541,BstLean.Part268.agent12541]

noncomputable def frameData12541 : BstLean.Part264b.FrameData 12541 :=
  BstLean.Part269.frameData_from_numerics (n := 12541) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12541.worldPackage rfl BstLean.Part268.WorldRow12541.product_lower (BstLean.Part268.WorldRow12541.producthi.2.trans (by norm_num))
    scalarRow12541 repair12541 covarianceInputs12541 (fun i hi => sourceNumerics12541 hi)
    BstLean.Part268.agent12541.frame targetFrame12541_eq


end BstLean.Part269.N12541

namespace BstLean.Part269.N12542
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12542 : scalarRow12542.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12542, BstLean.Part268.grid12542, BstLean.Part263.worldGrid]

theorem supplies12542 (j : Fin 43) : Supply 12542 (parameters j)
    (cellLower scalarRow12542.grid (sourceIndex j))
    (cellUpper scalarRow12542.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12542.grid grid_top_bounds12542 j

theorem radii12542 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12542.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12542 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12542 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12542.grid grid_top_bounds12542 j hθ

noncomputable def covarianceInputs12542 :
    BstLean.Part263.CovarianceInputs 12542 scalarRow12542.grid parameters (caps repair12542) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12542 grid_top_bounds12542 repair12542

noncomputable def covarianceEvent12542 : Set (AgFam 12542) :=
  BstLean.Part263.covarianceEvent 12542 scalarRow12542.grid parameters

theorem covarianceEvent12542_measurable : MeasurableSet covarianceEvent12542 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12542_payment :
    (retDist (paperDesignP 12542).toCentres).real
      (agentEv (paperDesignP 12542) covarianceEvent12542)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12542

theorem localCov12542 : BstLean.Part259.LocalCovarianceOn covarianceEvent12542
    (BstLean.Part263.cell scalarRow12542.grid) (caps repair12542) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12542

theorem covarianceGood12542_payment :
    (retDist (paperDesignP 12542).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12542)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12542_payment



end BstLean.Part269.N12542

namespace BstLean.Part269.N12542
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12542}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12542.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12542) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12542).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12542 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12542) (by norm_num) BstLean.Part268.WorldRow12542.worldPackage rfl
    BstLean.Part268.WorldRow12542.product_lower (BstLean.Part268.WorldRow12542.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12542} (hw : c ∈ Hof BstLean.Part268.WorldRow12542.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12542) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12542) (by norm_num) BstLean.Part268.WorldRow12542.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12542} (hw : c ∈ Hof BstLean.Part268.WorldRow12542.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12542) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12542).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12542) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12542_eq : scalarRow12542.targetFrame = BstLean.Part268.agent12542.frame := by
  norm_num [scalarRow12542,BstLean.Part268.agent12542]

noncomputable def frameData12542 : BstLean.Part264b.FrameData 12542 :=
  BstLean.Part269.frameData_from_numerics (n := 12542) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12542.worldPackage rfl BstLean.Part268.WorldRow12542.product_lower (BstLean.Part268.WorldRow12542.producthi.2.trans (by norm_num))
    scalarRow12542 repair12542 covarianceInputs12542 (fun i hi => sourceNumerics12542 hi)
    BstLean.Part268.agent12542.frame targetFrame12542_eq


end BstLean.Part269.N12542

namespace BstLean.Part269.N12543
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12543 : scalarRow12543.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12543, BstLean.Part268.grid12543, BstLean.Part263.worldGrid]

theorem supplies12543 (j : Fin 43) : Supply 12543 (parameters j)
    (cellLower scalarRow12543.grid (sourceIndex j))
    (cellUpper scalarRow12543.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12543.grid grid_top_bounds12543 j

theorem radii12543 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12543.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12543 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12543 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12543.grid grid_top_bounds12543 j hθ

noncomputable def covarianceInputs12543 :
    BstLean.Part263.CovarianceInputs 12543 scalarRow12543.grid parameters (caps repair12543) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12543 grid_top_bounds12543 repair12543

noncomputable def covarianceEvent12543 : Set (AgFam 12543) :=
  BstLean.Part263.covarianceEvent 12543 scalarRow12543.grid parameters

theorem covarianceEvent12543_measurable : MeasurableSet covarianceEvent12543 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12543_payment :
    (retDist (paperDesignP 12543).toCentres).real
      (agentEv (paperDesignP 12543) covarianceEvent12543)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12543

theorem localCov12543 : BstLean.Part259.LocalCovarianceOn covarianceEvent12543
    (BstLean.Part263.cell scalarRow12543.grid) (caps repair12543) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12543

theorem covarianceGood12543_payment :
    (retDist (paperDesignP 12543).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12543)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12543_payment



end BstLean.Part269.N12543

namespace BstLean.Part269.N12543
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12543}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12543.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12543) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12543).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12543 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12543) (by norm_num) BstLean.Part268.WorldRow12543.worldPackage rfl
    BstLean.Part268.WorldRow12543.product_lower (BstLean.Part268.WorldRow12543.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12543} (hw : c ∈ Hof BstLean.Part268.WorldRow12543.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12543) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12543) (by norm_num) BstLean.Part268.WorldRow12543.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12543} (hw : c ∈ Hof BstLean.Part268.WorldRow12543.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12543) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12543).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12543) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12543_eq : scalarRow12543.targetFrame = BstLean.Part268.agent12543.frame := by
  norm_num [scalarRow12543,BstLean.Part268.agent12543]

noncomputable def frameData12543 : BstLean.Part264b.FrameData 12543 :=
  BstLean.Part269.frameData_from_numerics (n := 12543) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12543.worldPackage rfl BstLean.Part268.WorldRow12543.product_lower (BstLean.Part268.WorldRow12543.producthi.2.trans (by norm_num))
    scalarRow12543 repair12543 covarianceInputs12543 (fun i hi => sourceNumerics12543 hi)
    BstLean.Part268.agent12543.frame targetFrame12543_eq


end BstLean.Part269.N12543

namespace BstLean.Part269.N12544
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12544 : scalarRow12544.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12544, BstLean.Part268.grid12544, BstLean.Part263.worldGrid]

theorem supplies12544 (j : Fin 43) : Supply 12544 (parameters j)
    (cellLower scalarRow12544.grid (sourceIndex j))
    (cellUpper scalarRow12544.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12544.grid grid_top_bounds12544 j

theorem radii12544 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12544.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12544 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12544 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12544.grid grid_top_bounds12544 j hθ

noncomputable def covarianceInputs12544 :
    BstLean.Part263.CovarianceInputs 12544 scalarRow12544.grid parameters (caps repair12544) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12544 grid_top_bounds12544 repair12544

noncomputable def covarianceEvent12544 : Set (AgFam 12544) :=
  BstLean.Part263.covarianceEvent 12544 scalarRow12544.grid parameters

theorem covarianceEvent12544_measurable : MeasurableSet covarianceEvent12544 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12544_payment :
    (retDist (paperDesignP 12544).toCentres).real
      (agentEv (paperDesignP 12544) covarianceEvent12544)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12544

theorem localCov12544 : BstLean.Part259.LocalCovarianceOn covarianceEvent12544
    (BstLean.Part263.cell scalarRow12544.grid) (caps repair12544) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12544

theorem covarianceGood12544_payment :
    (retDist (paperDesignP 12544).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12544)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12544_payment



end BstLean.Part269.N12544

namespace BstLean.Part269.N12544
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12544}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12544.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12544) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12544).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12544 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12544) (by norm_num) BstLean.Part268.WorldRow12544.worldPackage rfl
    BstLean.Part268.WorldRow12544.product_lower (BstLean.Part268.WorldRow12544.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12544} (hw : c ∈ Hof BstLean.Part268.WorldRow12544.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12544) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12544) (by norm_num) BstLean.Part268.WorldRow12544.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12544} (hw : c ∈ Hof BstLean.Part268.WorldRow12544.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12544) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12544).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12544) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12544_eq : scalarRow12544.targetFrame = BstLean.Part268.agent12544.frame := by
  norm_num [scalarRow12544,BstLean.Part268.agent12544]

noncomputable def frameData12544 : BstLean.Part264b.FrameData 12544 :=
  BstLean.Part269.frameData_from_numerics (n := 12544) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12544.worldPackage rfl BstLean.Part268.WorldRow12544.product_lower (BstLean.Part268.WorldRow12544.producthi.2.trans (by norm_num))
    scalarRow12544 repair12544 covarianceInputs12544 (fun i hi => sourceNumerics12544 hi)
    BstLean.Part268.agent12544.frame targetFrame12544_eq


end BstLean.Part269.N12544
