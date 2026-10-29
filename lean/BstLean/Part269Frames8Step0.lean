import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World8Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs8
import BstLean.Part269Rows8
import BstLean.Part269Sources8
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12550
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12550 : scalarRow12550.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12550, BstLean.Part268.grid12550, BstLean.Part263.worldGrid]

theorem supplies12550 (j : Fin 43) : Supply 12550 (parameters j)
    (cellLower scalarRow12550.grid (sourceIndex j))
    (cellUpper scalarRow12550.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12550.grid grid_top_bounds12550 j

theorem radii12550 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12550.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12550 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12550 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12550.grid grid_top_bounds12550 j hθ

noncomputable def covarianceInputs12550 :
    BstLean.Part263.CovarianceInputs 12550 scalarRow12550.grid parameters (caps repair12550) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12550 grid_top_bounds12550 repair12550

noncomputable def covarianceEvent12550 : Set (AgFam 12550) :=
  BstLean.Part263.covarianceEvent 12550 scalarRow12550.grid parameters

theorem covarianceEvent12550_measurable : MeasurableSet covarianceEvent12550 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12550_payment :
    (retDist (paperDesignP 12550).toCentres).real
      (agentEv (paperDesignP 12550) covarianceEvent12550)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12550

theorem localCov12550 : BstLean.Part259.LocalCovarianceOn covarianceEvent12550
    (BstLean.Part263.cell scalarRow12550.grid) (caps repair12550) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12550

theorem covarianceGood12550_payment :
    (retDist (paperDesignP 12550).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12550)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12550_payment



end BstLean.Part269.N12550

namespace BstLean.Part269.N12550
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12550}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12550.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12550) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12550).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12550 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12550) (by norm_num) BstLean.Part268.WorldRow12550.worldPackage rfl
    BstLean.Part268.WorldRow12550.product_lower (BstLean.Part268.WorldRow12550.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12550} (hw : c ∈ Hof BstLean.Part268.WorldRow12550.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12550) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12550) (by norm_num) BstLean.Part268.WorldRow12550.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12550} (hw : c ∈ Hof BstLean.Part268.WorldRow12550.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12550) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12550).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12550) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12550_eq : scalarRow12550.targetFrame = BstLean.Part268.agent12550.frame := by
  norm_num [scalarRow12550,BstLean.Part268.agent12550]

noncomputable def frameData12550 : BstLean.Part264b.FrameData 12550 :=
  BstLean.Part269.frameData_from_numerics (n := 12550) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12550.worldPackage rfl BstLean.Part268.WorldRow12550.product_lower (BstLean.Part268.WorldRow12550.producthi.2.trans (by norm_num))
    scalarRow12550 repair12550 covarianceInputs12550 (fun i hi => sourceNumerics12550 hi)
    BstLean.Part268.agent12550.frame targetFrame12550_eq


end BstLean.Part269.N12550

namespace BstLean.Part269.N12551
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12551 : scalarRow12551.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12551, BstLean.Part268.grid12551, BstLean.Part263.worldGrid]

theorem supplies12551 (j : Fin 43) : Supply 12551 (parameters j)
    (cellLower scalarRow12551.grid (sourceIndex j))
    (cellUpper scalarRow12551.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12551.grid grid_top_bounds12551 j

theorem radii12551 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12551.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12551 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12551 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12551.grid grid_top_bounds12551 j hθ

noncomputable def covarianceInputs12551 :
    BstLean.Part263.CovarianceInputs 12551 scalarRow12551.grid parameters (caps repair12551) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12551 grid_top_bounds12551 repair12551

noncomputable def covarianceEvent12551 : Set (AgFam 12551) :=
  BstLean.Part263.covarianceEvent 12551 scalarRow12551.grid parameters

theorem covarianceEvent12551_measurable : MeasurableSet covarianceEvent12551 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12551_payment :
    (retDist (paperDesignP 12551).toCentres).real
      (agentEv (paperDesignP 12551) covarianceEvent12551)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12551

theorem localCov12551 : BstLean.Part259.LocalCovarianceOn covarianceEvent12551
    (BstLean.Part263.cell scalarRow12551.grid) (caps repair12551) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12551

theorem covarianceGood12551_payment :
    (retDist (paperDesignP 12551).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12551)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12551_payment



end BstLean.Part269.N12551

namespace BstLean.Part269.N12551
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12551}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12551.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12551) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12551).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12551 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12551) (by norm_num) BstLean.Part268.WorldRow12551.worldPackage rfl
    BstLean.Part268.WorldRow12551.product_lower (BstLean.Part268.WorldRow12551.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12551} (hw : c ∈ Hof BstLean.Part268.WorldRow12551.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12551) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12551) (by norm_num) BstLean.Part268.WorldRow12551.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12551} (hw : c ∈ Hof BstLean.Part268.WorldRow12551.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12551) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12551).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12551) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12551_eq : scalarRow12551.targetFrame = BstLean.Part268.agent12551.frame := by
  norm_num [scalarRow12551,BstLean.Part268.agent12551]

noncomputable def frameData12551 : BstLean.Part264b.FrameData 12551 :=
  BstLean.Part269.frameData_from_numerics (n := 12551) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12551.worldPackage rfl BstLean.Part268.WorldRow12551.product_lower (BstLean.Part268.WorldRow12551.producthi.2.trans (by norm_num))
    scalarRow12551 repair12551 covarianceInputs12551 (fun i hi => sourceNumerics12551 hi)
    BstLean.Part268.agent12551.frame targetFrame12551_eq


end BstLean.Part269.N12551

namespace BstLean.Part269.N12552
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12552 : scalarRow12552.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12552, BstLean.Part268.grid12552, BstLean.Part263.worldGrid]

theorem supplies12552 (j : Fin 43) : Supply 12552 (parameters j)
    (cellLower scalarRow12552.grid (sourceIndex j))
    (cellUpper scalarRow12552.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12552.grid grid_top_bounds12552 j

theorem radii12552 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12552.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12552 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12552 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12552.grid grid_top_bounds12552 j hθ

noncomputable def covarianceInputs12552 :
    BstLean.Part263.CovarianceInputs 12552 scalarRow12552.grid parameters (caps repair12552) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12552 grid_top_bounds12552 repair12552

noncomputable def covarianceEvent12552 : Set (AgFam 12552) :=
  BstLean.Part263.covarianceEvent 12552 scalarRow12552.grid parameters

theorem covarianceEvent12552_measurable : MeasurableSet covarianceEvent12552 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12552_payment :
    (retDist (paperDesignP 12552).toCentres).real
      (agentEv (paperDesignP 12552) covarianceEvent12552)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12552

theorem localCov12552 : BstLean.Part259.LocalCovarianceOn covarianceEvent12552
    (BstLean.Part263.cell scalarRow12552.grid) (caps repair12552) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12552

theorem covarianceGood12552_payment :
    (retDist (paperDesignP 12552).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12552)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12552_payment



end BstLean.Part269.N12552

namespace BstLean.Part269.N12552
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12552}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12552.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12552) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12552).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12552 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12552) (by norm_num) BstLean.Part268.WorldRow12552.worldPackage rfl
    BstLean.Part268.WorldRow12552.product_lower (BstLean.Part268.WorldRow12552.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12552} (hw : c ∈ Hof BstLean.Part268.WorldRow12552.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12552) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12552) (by norm_num) BstLean.Part268.WorldRow12552.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12552} (hw : c ∈ Hof BstLean.Part268.WorldRow12552.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12552) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12552).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12552) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12552_eq : scalarRow12552.targetFrame = BstLean.Part268.agent12552.frame := by
  norm_num [scalarRow12552,BstLean.Part268.agent12552]

noncomputable def frameData12552 : BstLean.Part264b.FrameData 12552 :=
  BstLean.Part269.frameData_from_numerics (n := 12552) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12552.worldPackage rfl BstLean.Part268.WorldRow12552.product_lower (BstLean.Part268.WorldRow12552.producthi.2.trans (by norm_num))
    scalarRow12552 repair12552 covarianceInputs12552 (fun i hi => sourceNumerics12552 hi)
    BstLean.Part268.agent12552.frame targetFrame12552_eq


end BstLean.Part269.N12552

namespace BstLean.Part269.N12553
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12553 : scalarRow12553.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12553, BstLean.Part268.grid12553, BstLean.Part263.worldGrid]

theorem supplies12553 (j : Fin 43) : Supply 12553 (parameters j)
    (cellLower scalarRow12553.grid (sourceIndex j))
    (cellUpper scalarRow12553.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12553.grid grid_top_bounds12553 j

theorem radii12553 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12553.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12553 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12553 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12553.grid grid_top_bounds12553 j hθ

noncomputable def covarianceInputs12553 :
    BstLean.Part263.CovarianceInputs 12553 scalarRow12553.grid parameters (caps repair12553) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12553 grid_top_bounds12553 repair12553

noncomputable def covarianceEvent12553 : Set (AgFam 12553) :=
  BstLean.Part263.covarianceEvent 12553 scalarRow12553.grid parameters

theorem covarianceEvent12553_measurable : MeasurableSet covarianceEvent12553 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12553_payment :
    (retDist (paperDesignP 12553).toCentres).real
      (agentEv (paperDesignP 12553) covarianceEvent12553)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12553

theorem localCov12553 : BstLean.Part259.LocalCovarianceOn covarianceEvent12553
    (BstLean.Part263.cell scalarRow12553.grid) (caps repair12553) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12553

theorem covarianceGood12553_payment :
    (retDist (paperDesignP 12553).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12553)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12553_payment



end BstLean.Part269.N12553

namespace BstLean.Part269.N12553
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12553}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12553.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12553) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12553).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12553 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12553) (by norm_num) BstLean.Part268.WorldRow12553.worldPackage rfl
    BstLean.Part268.WorldRow12553.product_lower (BstLean.Part268.WorldRow12553.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12553} (hw : c ∈ Hof BstLean.Part268.WorldRow12553.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12553) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12553) (by norm_num) BstLean.Part268.WorldRow12553.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12553} (hw : c ∈ Hof BstLean.Part268.WorldRow12553.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12553) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12553).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12553) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12553_eq : scalarRow12553.targetFrame = BstLean.Part268.agent12553.frame := by
  norm_num [scalarRow12553,BstLean.Part268.agent12553]

noncomputable def frameData12553 : BstLean.Part264b.FrameData 12553 :=
  BstLean.Part269.frameData_from_numerics (n := 12553) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12553.worldPackage rfl BstLean.Part268.WorldRow12553.product_lower (BstLean.Part268.WorldRow12553.producthi.2.trans (by norm_num))
    scalarRow12553 repair12553 covarianceInputs12553 (fun i hi => sourceNumerics12553 hi)
    BstLean.Part268.agent12553.frame targetFrame12553_eq


end BstLean.Part269.N12553

namespace BstLean.Part269.N12554
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12554 : scalarRow12554.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12554, BstLean.Part268.grid12554, BstLean.Part263.worldGrid]

theorem supplies12554 (j : Fin 43) : Supply 12554 (parameters j)
    (cellLower scalarRow12554.grid (sourceIndex j))
    (cellUpper scalarRow12554.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12554.grid grid_top_bounds12554 j

theorem radii12554 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12554.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12554 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12554 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12554.grid grid_top_bounds12554 j hθ

noncomputable def covarianceInputs12554 :
    BstLean.Part263.CovarianceInputs 12554 scalarRow12554.grid parameters (caps repair12554) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12554 grid_top_bounds12554 repair12554

noncomputable def covarianceEvent12554 : Set (AgFam 12554) :=
  BstLean.Part263.covarianceEvent 12554 scalarRow12554.grid parameters

theorem covarianceEvent12554_measurable : MeasurableSet covarianceEvent12554 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12554_payment :
    (retDist (paperDesignP 12554).toCentres).real
      (agentEv (paperDesignP 12554) covarianceEvent12554)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12554

theorem localCov12554 : BstLean.Part259.LocalCovarianceOn covarianceEvent12554
    (BstLean.Part263.cell scalarRow12554.grid) (caps repair12554) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12554

theorem covarianceGood12554_payment :
    (retDist (paperDesignP 12554).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12554)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12554_payment



end BstLean.Part269.N12554

namespace BstLean.Part269.N12554
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12554}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12554.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12554) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12554).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12554 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12554) (by norm_num) BstLean.Part268.WorldRow12554.worldPackage rfl
    BstLean.Part268.WorldRow12554.product_lower (BstLean.Part268.WorldRow12554.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12554} (hw : c ∈ Hof BstLean.Part268.WorldRow12554.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12554) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12554) (by norm_num) BstLean.Part268.WorldRow12554.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12554} (hw : c ∈ Hof BstLean.Part268.WorldRow12554.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12554) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12554).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12554) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12554_eq : scalarRow12554.targetFrame = BstLean.Part268.agent12554.frame := by
  norm_num [scalarRow12554,BstLean.Part268.agent12554]

noncomputable def frameData12554 : BstLean.Part264b.FrameData 12554 :=
  BstLean.Part269.frameData_from_numerics (n := 12554) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12554.worldPackage rfl BstLean.Part268.WorldRow12554.product_lower (BstLean.Part268.WorldRow12554.producthi.2.trans (by norm_num))
    scalarRow12554 repair12554 covarianceInputs12554 (fun i hi => sourceNumerics12554 hi)
    BstLean.Part268.agent12554.frame targetFrame12554_eq


end BstLean.Part269.N12554
