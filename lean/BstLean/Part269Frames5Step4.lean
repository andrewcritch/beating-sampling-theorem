import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World5Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs5
import BstLean.Part269Rows5
import BstLean.Part269Sources5
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12495
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12495 : scalarRow12495.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12495, BstLean.Part268.grid12495, BstLean.Part263.worldGrid]

theorem supplies12495 (j : Fin 43) : Supply 12495 (parameters j)
    (cellLower scalarRow12495.grid (sourceIndex j))
    (cellUpper scalarRow12495.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12495.grid grid_top_bounds12495 j

theorem radii12495 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12495.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12495 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12495 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12495.grid grid_top_bounds12495 j hθ

noncomputable def covarianceInputs12495 :
    BstLean.Part263.CovarianceInputs 12495 scalarRow12495.grid parameters (caps repair12495) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12495 grid_top_bounds12495 repair12495

noncomputable def covarianceEvent12495 : Set (AgFam 12495) :=
  BstLean.Part263.covarianceEvent 12495 scalarRow12495.grid parameters

theorem covarianceEvent12495_measurable : MeasurableSet covarianceEvent12495 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12495_payment :
    (retDist (paperDesignP 12495).toCentres).real
      (agentEv (paperDesignP 12495) covarianceEvent12495)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12495

theorem localCov12495 : BstLean.Part259.LocalCovarianceOn covarianceEvent12495
    (BstLean.Part263.cell scalarRow12495.grid) (caps repair12495) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12495

theorem covarianceGood12495_payment :
    (retDist (paperDesignP 12495).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12495)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12495_payment



end BstLean.Part269.N12495

namespace BstLean.Part269.N12495
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12495}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12495.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12495) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12495).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12495 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12495) (by norm_num) BstLean.Part268.WorldRow12495.worldPackage rfl
    BstLean.Part268.WorldRow12495.product_lower (BstLean.Part268.WorldRow12495.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12495} (hw : c ∈ Hof BstLean.Part268.WorldRow12495.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12495) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12495) (by norm_num) BstLean.Part268.WorldRow12495.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12495} (hw : c ∈ Hof BstLean.Part268.WorldRow12495.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12495) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12495).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12495) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12495_eq : scalarRow12495.targetFrame = BstLean.Part268.agent12495.frame := by
  norm_num [scalarRow12495,BstLean.Part268.agent12495]

noncomputable def frameData12495 : BstLean.Part264b.FrameData 12495 :=
  BstLean.Part269.frameData_from_numerics (n := 12495) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12495.worldPackage rfl BstLean.Part268.WorldRow12495.product_lower (BstLean.Part268.WorldRow12495.producthi.2.trans (by norm_num))
    scalarRow12495 repair12495 covarianceInputs12495 (fun i hi => sourceNumerics12495 hi)
    BstLean.Part268.agent12495.frame targetFrame12495_eq


end BstLean.Part269.N12495

namespace BstLean.Part269.N12496
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12496 : scalarRow12496.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12496, BstLean.Part268.grid12496, BstLean.Part263.worldGrid]

theorem supplies12496 (j : Fin 43) : Supply 12496 (parameters j)
    (cellLower scalarRow12496.grid (sourceIndex j))
    (cellUpper scalarRow12496.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12496.grid grid_top_bounds12496 j

theorem radii12496 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12496.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12496 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12496 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12496.grid grid_top_bounds12496 j hθ

noncomputable def covarianceInputs12496 :
    BstLean.Part263.CovarianceInputs 12496 scalarRow12496.grid parameters (caps repair12496) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12496 grid_top_bounds12496 repair12496

noncomputable def covarianceEvent12496 : Set (AgFam 12496) :=
  BstLean.Part263.covarianceEvent 12496 scalarRow12496.grid parameters

theorem covarianceEvent12496_measurable : MeasurableSet covarianceEvent12496 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12496_payment :
    (retDist (paperDesignP 12496).toCentres).real
      (agentEv (paperDesignP 12496) covarianceEvent12496)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12496

theorem localCov12496 : BstLean.Part259.LocalCovarianceOn covarianceEvent12496
    (BstLean.Part263.cell scalarRow12496.grid) (caps repair12496) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12496

theorem covarianceGood12496_payment :
    (retDist (paperDesignP 12496).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12496)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12496_payment



end BstLean.Part269.N12496

namespace BstLean.Part269.N12496
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12496}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12496.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12496) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12496).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12496 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12496) (by norm_num) BstLean.Part268.WorldRow12496.worldPackage rfl
    BstLean.Part268.WorldRow12496.product_lower (BstLean.Part268.WorldRow12496.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12496} (hw : c ∈ Hof BstLean.Part268.WorldRow12496.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12496) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12496) (by norm_num) BstLean.Part268.WorldRow12496.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12496} (hw : c ∈ Hof BstLean.Part268.WorldRow12496.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12496) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12496).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12496) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12496_eq : scalarRow12496.targetFrame = BstLean.Part268.agent12496.frame := by
  norm_num [scalarRow12496,BstLean.Part268.agent12496]

noncomputable def frameData12496 : BstLean.Part264b.FrameData 12496 :=
  BstLean.Part269.frameData_from_numerics (n := 12496) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12496.worldPackage rfl BstLean.Part268.WorldRow12496.product_lower (BstLean.Part268.WorldRow12496.producthi.2.trans (by norm_num))
    scalarRow12496 repair12496 covarianceInputs12496 (fun i hi => sourceNumerics12496 hi)
    BstLean.Part268.agent12496.frame targetFrame12496_eq


end BstLean.Part269.N12496

namespace BstLean.Part269.N12497
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12497 : scalarRow12497.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12497, BstLean.Part268.grid12497, BstLean.Part263.worldGrid]

theorem supplies12497 (j : Fin 43) : Supply 12497 (parameters j)
    (cellLower scalarRow12497.grid (sourceIndex j))
    (cellUpper scalarRow12497.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12497.grid grid_top_bounds12497 j

theorem radii12497 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12497.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12497 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12497 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12497.grid grid_top_bounds12497 j hθ

noncomputable def covarianceInputs12497 :
    BstLean.Part263.CovarianceInputs 12497 scalarRow12497.grid parameters (caps repair12497) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12497 grid_top_bounds12497 repair12497

noncomputable def covarianceEvent12497 : Set (AgFam 12497) :=
  BstLean.Part263.covarianceEvent 12497 scalarRow12497.grid parameters

theorem covarianceEvent12497_measurable : MeasurableSet covarianceEvent12497 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12497_payment :
    (retDist (paperDesignP 12497).toCentres).real
      (agentEv (paperDesignP 12497) covarianceEvent12497)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12497

theorem localCov12497 : BstLean.Part259.LocalCovarianceOn covarianceEvent12497
    (BstLean.Part263.cell scalarRow12497.grid) (caps repair12497) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12497

theorem covarianceGood12497_payment :
    (retDist (paperDesignP 12497).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12497)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12497_payment



end BstLean.Part269.N12497

namespace BstLean.Part269.N12497
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12497}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12497.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12497) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12497).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12497 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12497) (by norm_num) BstLean.Part268.WorldRow12497.worldPackage rfl
    BstLean.Part268.WorldRow12497.product_lower (BstLean.Part268.WorldRow12497.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12497} (hw : c ∈ Hof BstLean.Part268.WorldRow12497.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12497) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12497) (by norm_num) BstLean.Part268.WorldRow12497.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12497} (hw : c ∈ Hof BstLean.Part268.WorldRow12497.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12497) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12497).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12497) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12497_eq : scalarRow12497.targetFrame = BstLean.Part268.agent12497.frame := by
  norm_num [scalarRow12497,BstLean.Part268.agent12497]

noncomputable def frameData12497 : BstLean.Part264b.FrameData 12497 :=
  BstLean.Part269.frameData_from_numerics (n := 12497) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12497.worldPackage rfl BstLean.Part268.WorldRow12497.product_lower (BstLean.Part268.WorldRow12497.producthi.2.trans (by norm_num))
    scalarRow12497 repair12497 covarianceInputs12497 (fun i hi => sourceNumerics12497 hi)
    BstLean.Part268.agent12497.frame targetFrame12497_eq


end BstLean.Part269.N12497

namespace BstLean.Part269.N12498
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12498 : scalarRow12498.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12498, BstLean.Part268.grid12498, BstLean.Part263.worldGrid]

theorem supplies12498 (j : Fin 43) : Supply 12498 (parameters j)
    (cellLower scalarRow12498.grid (sourceIndex j))
    (cellUpper scalarRow12498.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12498.grid grid_top_bounds12498 j

theorem radii12498 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12498.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12498 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12498 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12498.grid grid_top_bounds12498 j hθ

noncomputable def covarianceInputs12498 :
    BstLean.Part263.CovarianceInputs 12498 scalarRow12498.grid parameters (caps repair12498) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12498 grid_top_bounds12498 repair12498

noncomputable def covarianceEvent12498 : Set (AgFam 12498) :=
  BstLean.Part263.covarianceEvent 12498 scalarRow12498.grid parameters

theorem covarianceEvent12498_measurable : MeasurableSet covarianceEvent12498 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12498_payment :
    (retDist (paperDesignP 12498).toCentres).real
      (agentEv (paperDesignP 12498) covarianceEvent12498)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12498

theorem localCov12498 : BstLean.Part259.LocalCovarianceOn covarianceEvent12498
    (BstLean.Part263.cell scalarRow12498.grid) (caps repair12498) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12498

theorem covarianceGood12498_payment :
    (retDist (paperDesignP 12498).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12498)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12498_payment



end BstLean.Part269.N12498

namespace BstLean.Part269.N12498
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12498}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12498.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12498) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12498).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12498 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12498) (by norm_num) BstLean.Part268.WorldRow12498.worldPackage rfl
    BstLean.Part268.WorldRow12498.product_lower (BstLean.Part268.WorldRow12498.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12498} (hw : c ∈ Hof BstLean.Part268.WorldRow12498.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12498) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12498) (by norm_num) BstLean.Part268.WorldRow12498.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12498} (hw : c ∈ Hof BstLean.Part268.WorldRow12498.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12498) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12498).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12498) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12498_eq : scalarRow12498.targetFrame = BstLean.Part268.agent12498.frame := by
  norm_num [scalarRow12498,BstLean.Part268.agent12498]

noncomputable def frameData12498 : BstLean.Part264b.FrameData 12498 :=
  BstLean.Part269.frameData_from_numerics (n := 12498) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12498.worldPackage rfl BstLean.Part268.WorldRow12498.product_lower (BstLean.Part268.WorldRow12498.producthi.2.trans (by norm_num))
    scalarRow12498 repair12498 covarianceInputs12498 (fun i hi => sourceNumerics12498 hi)
    BstLean.Part268.agent12498.frame targetFrame12498_eq


end BstLean.Part269.N12498

namespace BstLean.Part269.N12499
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12499 : scalarRow12499.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12499, BstLean.Part268.grid12499, BstLean.Part263.worldGrid]

theorem supplies12499 (j : Fin 43) : Supply 12499 (parameters j)
    (cellLower scalarRow12499.grid (sourceIndex j))
    (cellUpper scalarRow12499.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12499.grid grid_top_bounds12499 j

theorem radii12499 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12499.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12499 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12499 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12499.grid grid_top_bounds12499 j hθ

noncomputable def covarianceInputs12499 :
    BstLean.Part263.CovarianceInputs 12499 scalarRow12499.grid parameters (caps repair12499) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12499 grid_top_bounds12499 repair12499

noncomputable def covarianceEvent12499 : Set (AgFam 12499) :=
  BstLean.Part263.covarianceEvent 12499 scalarRow12499.grid parameters

theorem covarianceEvent12499_measurable : MeasurableSet covarianceEvent12499 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12499_payment :
    (retDist (paperDesignP 12499).toCentres).real
      (agentEv (paperDesignP 12499) covarianceEvent12499)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12499

theorem localCov12499 : BstLean.Part259.LocalCovarianceOn covarianceEvent12499
    (BstLean.Part263.cell scalarRow12499.grid) (caps repair12499) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12499

theorem covarianceGood12499_payment :
    (retDist (paperDesignP 12499).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12499)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12499_payment



end BstLean.Part269.N12499

namespace BstLean.Part269.N12499
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12499}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12499.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12499) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12499).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12499 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12499) (by norm_num) BstLean.Part268.WorldRow12499.worldPackage rfl
    BstLean.Part268.WorldRow12499.product_lower (BstLean.Part268.WorldRow12499.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12499} (hw : c ∈ Hof BstLean.Part268.WorldRow12499.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12499) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12499) (by norm_num) BstLean.Part268.WorldRow12499.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12499} (hw : c ∈ Hof BstLean.Part268.WorldRow12499.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12499) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12499).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12499) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12499_eq : scalarRow12499.targetFrame = BstLean.Part268.agent12499.frame := by
  norm_num [scalarRow12499,BstLean.Part268.agent12499]

noncomputable def frameData12499 : BstLean.Part264b.FrameData 12499 :=
  BstLean.Part269.frameData_from_numerics (n := 12499) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12499.worldPackage rfl BstLean.Part268.WorldRow12499.product_lower (BstLean.Part268.WorldRow12499.producthi.2.trans (by norm_num))
    scalarRow12499 repair12499 covarianceInputs12499 (fun i hi => sourceNumerics12499 hi)
    BstLean.Part268.agent12499.frame targetFrame12499_eq


end BstLean.Part269.N12499
