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

namespace BstLean.Part269.N12545
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12545 : scalarRow12545.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12545, BstLean.Part268.grid12545, BstLean.Part263.worldGrid]

theorem supplies12545 (j : Fin 43) : Supply 12545 (parameters j)
    (cellLower scalarRow12545.grid (sourceIndex j))
    (cellUpper scalarRow12545.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12545.grid grid_top_bounds12545 j

theorem radii12545 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12545.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12545 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12545 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12545.grid grid_top_bounds12545 j hθ

noncomputable def covarianceInputs12545 :
    BstLean.Part263.CovarianceInputs 12545 scalarRow12545.grid parameters (caps repair12545) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12545 grid_top_bounds12545 repair12545

noncomputable def covarianceEvent12545 : Set (AgFam 12545) :=
  BstLean.Part263.covarianceEvent 12545 scalarRow12545.grid parameters

theorem covarianceEvent12545_measurable : MeasurableSet covarianceEvent12545 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12545_payment :
    (retDist (paperDesignP 12545).toCentres).real
      (agentEv (paperDesignP 12545) covarianceEvent12545)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12545

theorem localCov12545 : BstLean.Part259.LocalCovarianceOn covarianceEvent12545
    (BstLean.Part263.cell scalarRow12545.grid) (caps repair12545) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12545

theorem covarianceGood12545_payment :
    (retDist (paperDesignP 12545).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12545)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12545_payment



end BstLean.Part269.N12545

namespace BstLean.Part269.N12545
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12545}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12545.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12545) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12545).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12545 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12545) (by norm_num) BstLean.Part268.WorldRow12545.worldPackage rfl
    BstLean.Part268.WorldRow12545.product_lower (BstLean.Part268.WorldRow12545.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12545} (hw : c ∈ Hof BstLean.Part268.WorldRow12545.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12545) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12545) (by norm_num) BstLean.Part268.WorldRow12545.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12545} (hw : c ∈ Hof BstLean.Part268.WorldRow12545.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12545) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12545).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12545) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12545_eq : scalarRow12545.targetFrame = BstLean.Part268.agent12545.frame := by
  norm_num [scalarRow12545,BstLean.Part268.agent12545]

noncomputable def frameData12545 : BstLean.Part264b.FrameData 12545 :=
  BstLean.Part269.frameData_from_numerics (n := 12545) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12545.worldPackage rfl BstLean.Part268.WorldRow12545.product_lower (BstLean.Part268.WorldRow12545.producthi.2.trans (by norm_num))
    scalarRow12545 repair12545 covarianceInputs12545 (fun i hi => sourceNumerics12545 hi)
    BstLean.Part268.agent12545.frame targetFrame12545_eq


end BstLean.Part269.N12545

namespace BstLean.Part269.N12546
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12546 : scalarRow12546.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12546, BstLean.Part268.grid12546, BstLean.Part263.worldGrid]

theorem supplies12546 (j : Fin 43) : Supply 12546 (parameters j)
    (cellLower scalarRow12546.grid (sourceIndex j))
    (cellUpper scalarRow12546.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12546.grid grid_top_bounds12546 j

theorem radii12546 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12546.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12546 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12546 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12546.grid grid_top_bounds12546 j hθ

noncomputable def covarianceInputs12546 :
    BstLean.Part263.CovarianceInputs 12546 scalarRow12546.grid parameters (caps repair12546) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12546 grid_top_bounds12546 repair12546

noncomputable def covarianceEvent12546 : Set (AgFam 12546) :=
  BstLean.Part263.covarianceEvent 12546 scalarRow12546.grid parameters

theorem covarianceEvent12546_measurable : MeasurableSet covarianceEvent12546 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12546_payment :
    (retDist (paperDesignP 12546).toCentres).real
      (agentEv (paperDesignP 12546) covarianceEvent12546)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12546

theorem localCov12546 : BstLean.Part259.LocalCovarianceOn covarianceEvent12546
    (BstLean.Part263.cell scalarRow12546.grid) (caps repair12546) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12546

theorem covarianceGood12546_payment :
    (retDist (paperDesignP 12546).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12546)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12546_payment



end BstLean.Part269.N12546

namespace BstLean.Part269.N12546
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12546}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12546.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12546) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12546).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12546 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12546) (by norm_num) BstLean.Part268.WorldRow12546.worldPackage rfl
    BstLean.Part268.WorldRow12546.product_lower (BstLean.Part268.WorldRow12546.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12546} (hw : c ∈ Hof BstLean.Part268.WorldRow12546.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12546) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12546) (by norm_num) BstLean.Part268.WorldRow12546.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12546} (hw : c ∈ Hof BstLean.Part268.WorldRow12546.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12546) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12546).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12546) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12546_eq : scalarRow12546.targetFrame = BstLean.Part268.agent12546.frame := by
  norm_num [scalarRow12546,BstLean.Part268.agent12546]

noncomputable def frameData12546 : BstLean.Part264b.FrameData 12546 :=
  BstLean.Part269.frameData_from_numerics (n := 12546) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12546.worldPackage rfl BstLean.Part268.WorldRow12546.product_lower (BstLean.Part268.WorldRow12546.producthi.2.trans (by norm_num))
    scalarRow12546 repair12546 covarianceInputs12546 (fun i hi => sourceNumerics12546 hi)
    BstLean.Part268.agent12546.frame targetFrame12546_eq


end BstLean.Part269.N12546

namespace BstLean.Part269.N12547
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12547 : scalarRow12547.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12547, BstLean.Part268.grid12547, BstLean.Part263.worldGrid]

theorem supplies12547 (j : Fin 43) : Supply 12547 (parameters j)
    (cellLower scalarRow12547.grid (sourceIndex j))
    (cellUpper scalarRow12547.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12547.grid grid_top_bounds12547 j

theorem radii12547 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12547.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12547 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12547 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12547.grid grid_top_bounds12547 j hθ

noncomputable def covarianceInputs12547 :
    BstLean.Part263.CovarianceInputs 12547 scalarRow12547.grid parameters (caps repair12547) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12547 grid_top_bounds12547 repair12547

noncomputable def covarianceEvent12547 : Set (AgFam 12547) :=
  BstLean.Part263.covarianceEvent 12547 scalarRow12547.grid parameters

theorem covarianceEvent12547_measurable : MeasurableSet covarianceEvent12547 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12547_payment :
    (retDist (paperDesignP 12547).toCentres).real
      (agentEv (paperDesignP 12547) covarianceEvent12547)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12547

theorem localCov12547 : BstLean.Part259.LocalCovarianceOn covarianceEvent12547
    (BstLean.Part263.cell scalarRow12547.grid) (caps repair12547) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12547

theorem covarianceGood12547_payment :
    (retDist (paperDesignP 12547).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12547)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12547_payment



end BstLean.Part269.N12547

namespace BstLean.Part269.N12547
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12547}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12547.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12547) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12547).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12547 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12547) (by norm_num) BstLean.Part268.WorldRow12547.worldPackage rfl
    BstLean.Part268.WorldRow12547.product_lower (BstLean.Part268.WorldRow12547.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12547} (hw : c ∈ Hof BstLean.Part268.WorldRow12547.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12547) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12547) (by norm_num) BstLean.Part268.WorldRow12547.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12547} (hw : c ∈ Hof BstLean.Part268.WorldRow12547.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12547) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12547).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12547) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12547_eq : scalarRow12547.targetFrame = BstLean.Part268.agent12547.frame := by
  norm_num [scalarRow12547,BstLean.Part268.agent12547]

noncomputable def frameData12547 : BstLean.Part264b.FrameData 12547 :=
  BstLean.Part269.frameData_from_numerics (n := 12547) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12547.worldPackage rfl BstLean.Part268.WorldRow12547.product_lower (BstLean.Part268.WorldRow12547.producthi.2.trans (by norm_num))
    scalarRow12547 repair12547 covarianceInputs12547 (fun i hi => sourceNumerics12547 hi)
    BstLean.Part268.agent12547.frame targetFrame12547_eq


end BstLean.Part269.N12547

namespace BstLean.Part269.N12548
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12548 : scalarRow12548.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12548, BstLean.Part268.grid12548, BstLean.Part263.worldGrid]

theorem supplies12548 (j : Fin 43) : Supply 12548 (parameters j)
    (cellLower scalarRow12548.grid (sourceIndex j))
    (cellUpper scalarRow12548.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12548.grid grid_top_bounds12548 j

theorem radii12548 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12548.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12548 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12548 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12548.grid grid_top_bounds12548 j hθ

noncomputable def covarianceInputs12548 :
    BstLean.Part263.CovarianceInputs 12548 scalarRow12548.grid parameters (caps repair12548) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12548 grid_top_bounds12548 repair12548

noncomputable def covarianceEvent12548 : Set (AgFam 12548) :=
  BstLean.Part263.covarianceEvent 12548 scalarRow12548.grid parameters

theorem covarianceEvent12548_measurable : MeasurableSet covarianceEvent12548 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12548_payment :
    (retDist (paperDesignP 12548).toCentres).real
      (agentEv (paperDesignP 12548) covarianceEvent12548)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12548

theorem localCov12548 : BstLean.Part259.LocalCovarianceOn covarianceEvent12548
    (BstLean.Part263.cell scalarRow12548.grid) (caps repair12548) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12548

theorem covarianceGood12548_payment :
    (retDist (paperDesignP 12548).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12548)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12548_payment



end BstLean.Part269.N12548

namespace BstLean.Part269.N12548
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12548}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12548.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12548) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12548).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12548 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12548) (by norm_num) BstLean.Part268.WorldRow12548.worldPackage rfl
    BstLean.Part268.WorldRow12548.product_lower (BstLean.Part268.WorldRow12548.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12548} (hw : c ∈ Hof BstLean.Part268.WorldRow12548.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12548) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12548) (by norm_num) BstLean.Part268.WorldRow12548.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12548} (hw : c ∈ Hof BstLean.Part268.WorldRow12548.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12548) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12548).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12548) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12548_eq : scalarRow12548.targetFrame = BstLean.Part268.agent12548.frame := by
  norm_num [scalarRow12548,BstLean.Part268.agent12548]

noncomputable def frameData12548 : BstLean.Part264b.FrameData 12548 :=
  BstLean.Part269.frameData_from_numerics (n := 12548) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12548.worldPackage rfl BstLean.Part268.WorldRow12548.product_lower (BstLean.Part268.WorldRow12548.producthi.2.trans (by norm_num))
    scalarRow12548 repair12548 covarianceInputs12548 (fun i hi => sourceNumerics12548 hi)
    BstLean.Part268.agent12548.frame targetFrame12548_eq


end BstLean.Part269.N12548

namespace BstLean.Part269.N12549
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12549 : scalarRow12549.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12549, BstLean.Part268.grid12549, BstLean.Part263.worldGrid]

theorem supplies12549 (j : Fin 43) : Supply 12549 (parameters j)
    (cellLower scalarRow12549.grid (sourceIndex j))
    (cellUpper scalarRow12549.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12549.grid grid_top_bounds12549 j

theorem radii12549 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12549.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12549 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12549 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12549.grid grid_top_bounds12549 j hθ

noncomputable def covarianceInputs12549 :
    BstLean.Part263.CovarianceInputs 12549 scalarRow12549.grid parameters (caps repair12549) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12549 grid_top_bounds12549 repair12549

noncomputable def covarianceEvent12549 : Set (AgFam 12549) :=
  BstLean.Part263.covarianceEvent 12549 scalarRow12549.grid parameters

theorem covarianceEvent12549_measurable : MeasurableSet covarianceEvent12549 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12549_payment :
    (retDist (paperDesignP 12549).toCentres).real
      (agentEv (paperDesignP 12549) covarianceEvent12549)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12549

theorem localCov12549 : BstLean.Part259.LocalCovarianceOn covarianceEvent12549
    (BstLean.Part263.cell scalarRow12549.grid) (caps repair12549) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12549

theorem covarianceGood12549_payment :
    (retDist (paperDesignP 12549).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12549)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12549_payment



end BstLean.Part269.N12549

namespace BstLean.Part269.N12549
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12549}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12549.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12549) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12549).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12549 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12549) (by norm_num) BstLean.Part268.WorldRow12549.worldPackage rfl
    BstLean.Part268.WorldRow12549.product_lower (BstLean.Part268.WorldRow12549.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12549} (hw : c ∈ Hof BstLean.Part268.WorldRow12549.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12549) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12549) (by norm_num) BstLean.Part268.WorldRow12549.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12549} (hw : c ∈ Hof BstLean.Part268.WorldRow12549.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12549) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12549).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12549) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12549_eq : scalarRow12549.targetFrame = BstLean.Part268.agent12549.frame := by
  norm_num [scalarRow12549,BstLean.Part268.agent12549]

noncomputable def frameData12549 : BstLean.Part264b.FrameData 12549 :=
  BstLean.Part269.frameData_from_numerics (n := 12549) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12549.worldPackage rfl BstLean.Part268.WorldRow12549.product_lower (BstLean.Part268.WorldRow12549.producthi.2.trans (by norm_num))
    scalarRow12549 repair12549 covarianceInputs12549 (fun i hi => sourceNumerics12549 hi)
    BstLean.Part268.agent12549.frame targetFrame12549_eq


end BstLean.Part269.N12549
