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

namespace BstLean.Part269.N12585
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12585 : scalarRow12585.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12585, BstLean.Part268.grid12585, BstLean.Part263.worldGrid]

theorem supplies12585 (j : Fin 43) : Supply 12585 (parameters j)
    (cellLower scalarRow12585.grid (sourceIndex j))
    (cellUpper scalarRow12585.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12585.grid grid_top_bounds12585 j

theorem radii12585 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12585.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12585 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12585 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12585.grid grid_top_bounds12585 j hθ

noncomputable def covarianceInputs12585 :
    BstLean.Part263.CovarianceInputs 12585 scalarRow12585.grid parameters (caps repair12585) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12585 grid_top_bounds12585 repair12585

noncomputable def covarianceEvent12585 : Set (AgFam 12585) :=
  BstLean.Part263.covarianceEvent 12585 scalarRow12585.grid parameters

theorem covarianceEvent12585_measurable : MeasurableSet covarianceEvent12585 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12585_payment :
    (retDist (paperDesignP 12585).toCentres).real
      (agentEv (paperDesignP 12585) covarianceEvent12585)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12585

theorem localCov12585 : BstLean.Part259.LocalCovarianceOn covarianceEvent12585
    (BstLean.Part263.cell scalarRow12585.grid) (caps repair12585) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12585

theorem covarianceGood12585_payment :
    (retDist (paperDesignP 12585).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12585)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12585_payment



end BstLean.Part269.N12585

namespace BstLean.Part269.N12585
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12585}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12585.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12585) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12585).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12585 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12585) (by norm_num) BstLean.Part268.WorldRow12585.worldPackage rfl
    BstLean.Part268.WorldRow12585.product_lower (BstLean.Part268.WorldRow12585.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12585} (hw : c ∈ Hof BstLean.Part268.WorldRow12585.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12585) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12585) (by norm_num) BstLean.Part268.WorldRow12585.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12585} (hw : c ∈ Hof BstLean.Part268.WorldRow12585.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12585) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12585).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12585) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12585_eq : scalarRow12585.targetFrame = BstLean.Part268.agent12585.frame := by
  norm_num [scalarRow12585,BstLean.Part268.agent12585]

noncomputable def frameData12585 : BstLean.Part264b.FrameData 12585 :=
  BstLean.Part269.frameData_from_numerics (n := 12585) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12585.worldPackage rfl BstLean.Part268.WorldRow12585.product_lower (BstLean.Part268.WorldRow12585.producthi.2.trans (by norm_num))
    scalarRow12585 repair12585 covarianceInputs12585 (fun i hi => sourceNumerics12585 hi)
    BstLean.Part268.agent12585.frame targetFrame12585_eq


end BstLean.Part269.N12585

namespace BstLean.Part269.N12586
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12586 : scalarRow12586.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12586, BstLean.Part268.grid12586, BstLean.Part263.worldGrid]

theorem supplies12586 (j : Fin 43) : Supply 12586 (parameters j)
    (cellLower scalarRow12586.grid (sourceIndex j))
    (cellUpper scalarRow12586.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12586.grid grid_top_bounds12586 j

theorem radii12586 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12586.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12586 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12586 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12586.grid grid_top_bounds12586 j hθ

noncomputable def covarianceInputs12586 :
    BstLean.Part263.CovarianceInputs 12586 scalarRow12586.grid parameters (caps repair12586) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12586 grid_top_bounds12586 repair12586

noncomputable def covarianceEvent12586 : Set (AgFam 12586) :=
  BstLean.Part263.covarianceEvent 12586 scalarRow12586.grid parameters

theorem covarianceEvent12586_measurable : MeasurableSet covarianceEvent12586 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12586_payment :
    (retDist (paperDesignP 12586).toCentres).real
      (agentEv (paperDesignP 12586) covarianceEvent12586)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12586

theorem localCov12586 : BstLean.Part259.LocalCovarianceOn covarianceEvent12586
    (BstLean.Part263.cell scalarRow12586.grid) (caps repair12586) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12586

theorem covarianceGood12586_payment :
    (retDist (paperDesignP 12586).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12586)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12586_payment



end BstLean.Part269.N12586

namespace BstLean.Part269.N12586
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12586}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12586.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12586) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12586).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12586 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12586) (by norm_num) BstLean.Part268.WorldRow12586.worldPackage rfl
    BstLean.Part268.WorldRow12586.product_lower (BstLean.Part268.WorldRow12586.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12586} (hw : c ∈ Hof BstLean.Part268.WorldRow12586.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12586) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12586) (by norm_num) BstLean.Part268.WorldRow12586.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12586} (hw : c ∈ Hof BstLean.Part268.WorldRow12586.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12586) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12586).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12586) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12586_eq : scalarRow12586.targetFrame = BstLean.Part268.agent12586.frame := by
  norm_num [scalarRow12586,BstLean.Part268.agent12586]

noncomputable def frameData12586 : BstLean.Part264b.FrameData 12586 :=
  BstLean.Part269.frameData_from_numerics (n := 12586) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12586.worldPackage rfl BstLean.Part268.WorldRow12586.product_lower (BstLean.Part268.WorldRow12586.producthi.2.trans (by norm_num))
    scalarRow12586 repair12586 covarianceInputs12586 (fun i hi => sourceNumerics12586 hi)
    BstLean.Part268.agent12586.frame targetFrame12586_eq


end BstLean.Part269.N12586

namespace BstLean.Part269.N12587
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12587 : scalarRow12587.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12587, BstLean.Part268.grid12587, BstLean.Part263.worldGrid]

theorem supplies12587 (j : Fin 43) : Supply 12587 (parameters j)
    (cellLower scalarRow12587.grid (sourceIndex j))
    (cellUpper scalarRow12587.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12587.grid grid_top_bounds12587 j

theorem radii12587 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12587.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12587 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12587 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12587.grid grid_top_bounds12587 j hθ

noncomputable def covarianceInputs12587 :
    BstLean.Part263.CovarianceInputs 12587 scalarRow12587.grid parameters (caps repair12587) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12587 grid_top_bounds12587 repair12587

noncomputable def covarianceEvent12587 : Set (AgFam 12587) :=
  BstLean.Part263.covarianceEvent 12587 scalarRow12587.grid parameters

theorem covarianceEvent12587_measurable : MeasurableSet covarianceEvent12587 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12587_payment :
    (retDist (paperDesignP 12587).toCentres).real
      (agentEv (paperDesignP 12587) covarianceEvent12587)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12587

theorem localCov12587 : BstLean.Part259.LocalCovarianceOn covarianceEvent12587
    (BstLean.Part263.cell scalarRow12587.grid) (caps repair12587) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12587

theorem covarianceGood12587_payment :
    (retDist (paperDesignP 12587).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12587)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12587_payment



end BstLean.Part269.N12587

namespace BstLean.Part269.N12587
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12587}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12587.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12587) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12587).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12587 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12587) (by norm_num) BstLean.Part268.WorldRow12587.worldPackage rfl
    BstLean.Part268.WorldRow12587.product_lower (BstLean.Part268.WorldRow12587.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12587} (hw : c ∈ Hof BstLean.Part268.WorldRow12587.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12587) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12587) (by norm_num) BstLean.Part268.WorldRow12587.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12587} (hw : c ∈ Hof BstLean.Part268.WorldRow12587.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12587) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12587).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12587) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12587_eq : scalarRow12587.targetFrame = BstLean.Part268.agent12587.frame := by
  norm_num [scalarRow12587,BstLean.Part268.agent12587]

noncomputable def frameData12587 : BstLean.Part264b.FrameData 12587 :=
  BstLean.Part269.frameData_from_numerics (n := 12587) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12587.worldPackage rfl BstLean.Part268.WorldRow12587.product_lower (BstLean.Part268.WorldRow12587.producthi.2.trans (by norm_num))
    scalarRow12587 repair12587 covarianceInputs12587 (fun i hi => sourceNumerics12587 hi)
    BstLean.Part268.agent12587.frame targetFrame12587_eq


end BstLean.Part269.N12587

namespace BstLean.Part269.N12588
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12588 : scalarRow12588.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12588, BstLean.Part268.grid12588, BstLean.Part263.worldGrid]

theorem supplies12588 (j : Fin 43) : Supply 12588 (parameters j)
    (cellLower scalarRow12588.grid (sourceIndex j))
    (cellUpper scalarRow12588.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12588.grid grid_top_bounds12588 j

theorem radii12588 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12588.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12588 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12588 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12588.grid grid_top_bounds12588 j hθ

noncomputable def covarianceInputs12588 :
    BstLean.Part263.CovarianceInputs 12588 scalarRow12588.grid parameters (caps repair12588) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12588 grid_top_bounds12588 repair12588

noncomputable def covarianceEvent12588 : Set (AgFam 12588) :=
  BstLean.Part263.covarianceEvent 12588 scalarRow12588.grid parameters

theorem covarianceEvent12588_measurable : MeasurableSet covarianceEvent12588 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12588_payment :
    (retDist (paperDesignP 12588).toCentres).real
      (agentEv (paperDesignP 12588) covarianceEvent12588)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12588

theorem localCov12588 : BstLean.Part259.LocalCovarianceOn covarianceEvent12588
    (BstLean.Part263.cell scalarRow12588.grid) (caps repair12588) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12588

theorem covarianceGood12588_payment :
    (retDist (paperDesignP 12588).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12588)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12588_payment



end BstLean.Part269.N12588

namespace BstLean.Part269.N12588
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12588}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12588.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12588) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12588).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12588 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12588) (by norm_num) BstLean.Part268.WorldRow12588.worldPackage rfl
    BstLean.Part268.WorldRow12588.product_lower (BstLean.Part268.WorldRow12588.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12588} (hw : c ∈ Hof BstLean.Part268.WorldRow12588.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12588) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12588) (by norm_num) BstLean.Part268.WorldRow12588.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12588} (hw : c ∈ Hof BstLean.Part268.WorldRow12588.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12588) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12588).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12588) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12588_eq : scalarRow12588.targetFrame = BstLean.Part268.agent12588.frame := by
  norm_num [scalarRow12588,BstLean.Part268.agent12588]

noncomputable def frameData12588 : BstLean.Part264b.FrameData 12588 :=
  BstLean.Part269.frameData_from_numerics (n := 12588) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12588.worldPackage rfl BstLean.Part268.WorldRow12588.product_lower (BstLean.Part268.WorldRow12588.producthi.2.trans (by norm_num))
    scalarRow12588 repair12588 covarianceInputs12588 (fun i hi => sourceNumerics12588 hi)
    BstLean.Part268.agent12588.frame targetFrame12588_eq


end BstLean.Part269.N12588

namespace BstLean.Part269.N12589
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12589 : scalarRow12589.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12589, BstLean.Part268.grid12589, BstLean.Part263.worldGrid]

theorem supplies12589 (j : Fin 43) : Supply 12589 (parameters j)
    (cellLower scalarRow12589.grid (sourceIndex j))
    (cellUpper scalarRow12589.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12589.grid grid_top_bounds12589 j

theorem radii12589 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12589.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12589 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12589 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12589.grid grid_top_bounds12589 j hθ

noncomputable def covarianceInputs12589 :
    BstLean.Part263.CovarianceInputs 12589 scalarRow12589.grid parameters (caps repair12589) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12589 grid_top_bounds12589 repair12589

noncomputable def covarianceEvent12589 : Set (AgFam 12589) :=
  BstLean.Part263.covarianceEvent 12589 scalarRow12589.grid parameters

theorem covarianceEvent12589_measurable : MeasurableSet covarianceEvent12589 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12589_payment :
    (retDist (paperDesignP 12589).toCentres).real
      (agentEv (paperDesignP 12589) covarianceEvent12589)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12589

theorem localCov12589 : BstLean.Part259.LocalCovarianceOn covarianceEvent12589
    (BstLean.Part263.cell scalarRow12589.grid) (caps repair12589) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12589

theorem covarianceGood12589_payment :
    (retDist (paperDesignP 12589).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12589)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12589_payment



end BstLean.Part269.N12589

namespace BstLean.Part269.N12589
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12589}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12589.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12589) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12589).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12589 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12589) (by norm_num) BstLean.Part268.WorldRow12589.worldPackage rfl
    BstLean.Part268.WorldRow12589.product_lower (BstLean.Part268.WorldRow12589.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12589} (hw : c ∈ Hof BstLean.Part268.WorldRow12589.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12589) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12589) (by norm_num) BstLean.Part268.WorldRow12589.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12589} (hw : c ∈ Hof BstLean.Part268.WorldRow12589.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12589) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12589).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12589) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12589_eq : scalarRow12589.targetFrame = BstLean.Part268.agent12589.frame := by
  norm_num [scalarRow12589,BstLean.Part268.agent12589]

noncomputable def frameData12589 : BstLean.Part264b.FrameData 12589 :=
  BstLean.Part269.frameData_from_numerics (n := 12589) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12589.worldPackage rfl BstLean.Part268.WorldRow12589.product_lower (BstLean.Part268.WorldRow12589.producthi.2.trans (by norm_num))
    scalarRow12589 repair12589 covarianceInputs12589 (fun i hi => sourceNumerics12589 hi)
    BstLean.Part268.agent12589.frame targetFrame12589_eq


end BstLean.Part269.N12589
