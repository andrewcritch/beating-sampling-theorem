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

namespace BstLean.Part269.N12475
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12475 : scalarRow12475.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12475, BstLean.Part268.grid12475, BstLean.Part263.worldGrid]

theorem supplies12475 (j : Fin 43) : Supply 12475 (parameters j)
    (cellLower scalarRow12475.grid (sourceIndex j))
    (cellUpper scalarRow12475.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12475.grid grid_top_bounds12475 j

theorem radii12475 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12475.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12475 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12475 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12475.grid grid_top_bounds12475 j hθ

noncomputable def covarianceInputs12475 :
    BstLean.Part263.CovarianceInputs 12475 scalarRow12475.grid parameters (caps repair12475) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12475 grid_top_bounds12475 repair12475

noncomputable def covarianceEvent12475 : Set (AgFam 12475) :=
  BstLean.Part263.covarianceEvent 12475 scalarRow12475.grid parameters

theorem covarianceEvent12475_measurable : MeasurableSet covarianceEvent12475 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12475_payment :
    (retDist (paperDesignP 12475).toCentres).real
      (agentEv (paperDesignP 12475) covarianceEvent12475)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12475

theorem localCov12475 : BstLean.Part259.LocalCovarianceOn covarianceEvent12475
    (BstLean.Part263.cell scalarRow12475.grid) (caps repair12475) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12475

theorem covarianceGood12475_payment :
    (retDist (paperDesignP 12475).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12475)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12475_payment



end BstLean.Part269.N12475

namespace BstLean.Part269.N12475
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12475}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12475.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12475) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12475).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12475 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12475) (by norm_num) BstLean.Part268.WorldRow12475.worldPackage rfl
    BstLean.Part268.WorldRow12475.product_lower (BstLean.Part268.WorldRow12475.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12475} (hw : c ∈ Hof BstLean.Part268.WorldRow12475.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12475) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12475) (by norm_num) BstLean.Part268.WorldRow12475.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12475} (hw : c ∈ Hof BstLean.Part268.WorldRow12475.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12475) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12475).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12475) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12475_eq : scalarRow12475.targetFrame = BstLean.Part268.agent12475.frame := by
  norm_num [scalarRow12475,BstLean.Part268.agent12475]

noncomputable def frameData12475 : BstLean.Part264b.FrameData 12475 :=
  BstLean.Part269.frameData_from_numerics (n := 12475) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12475.worldPackage rfl BstLean.Part268.WorldRow12475.product_lower (BstLean.Part268.WorldRow12475.producthi.2.trans (by norm_num))
    scalarRow12475 repair12475 covarianceInputs12475 (fun i hi => sourceNumerics12475 hi)
    BstLean.Part268.agent12475.frame targetFrame12475_eq


end BstLean.Part269.N12475

namespace BstLean.Part269.N12476
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12476 : scalarRow12476.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12476, BstLean.Part268.grid12476, BstLean.Part263.worldGrid]

theorem supplies12476 (j : Fin 43) : Supply 12476 (parameters j)
    (cellLower scalarRow12476.grid (sourceIndex j))
    (cellUpper scalarRow12476.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12476.grid grid_top_bounds12476 j

theorem radii12476 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12476.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12476 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12476 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12476.grid grid_top_bounds12476 j hθ

noncomputable def covarianceInputs12476 :
    BstLean.Part263.CovarianceInputs 12476 scalarRow12476.grid parameters (caps repair12476) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12476 grid_top_bounds12476 repair12476

noncomputable def covarianceEvent12476 : Set (AgFam 12476) :=
  BstLean.Part263.covarianceEvent 12476 scalarRow12476.grid parameters

theorem covarianceEvent12476_measurable : MeasurableSet covarianceEvent12476 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12476_payment :
    (retDist (paperDesignP 12476).toCentres).real
      (agentEv (paperDesignP 12476) covarianceEvent12476)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12476

theorem localCov12476 : BstLean.Part259.LocalCovarianceOn covarianceEvent12476
    (BstLean.Part263.cell scalarRow12476.grid) (caps repair12476) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12476

theorem covarianceGood12476_payment :
    (retDist (paperDesignP 12476).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12476)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12476_payment



end BstLean.Part269.N12476

namespace BstLean.Part269.N12476
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12476}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12476.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12476) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12476).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12476 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12476) (by norm_num) BstLean.Part268.WorldRow12476.worldPackage rfl
    BstLean.Part268.WorldRow12476.product_lower (BstLean.Part268.WorldRow12476.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12476} (hw : c ∈ Hof BstLean.Part268.WorldRow12476.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12476) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12476) (by norm_num) BstLean.Part268.WorldRow12476.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12476} (hw : c ∈ Hof BstLean.Part268.WorldRow12476.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12476) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12476).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12476) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12476_eq : scalarRow12476.targetFrame = BstLean.Part268.agent12476.frame := by
  norm_num [scalarRow12476,BstLean.Part268.agent12476]

noncomputable def frameData12476 : BstLean.Part264b.FrameData 12476 :=
  BstLean.Part269.frameData_from_numerics (n := 12476) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12476.worldPackage rfl BstLean.Part268.WorldRow12476.product_lower (BstLean.Part268.WorldRow12476.producthi.2.trans (by norm_num))
    scalarRow12476 repair12476 covarianceInputs12476 (fun i hi => sourceNumerics12476 hi)
    BstLean.Part268.agent12476.frame targetFrame12476_eq


end BstLean.Part269.N12476

namespace BstLean.Part269.N12477
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12477 : scalarRow12477.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12477, BstLean.Part268.grid12477, BstLean.Part263.worldGrid]

theorem supplies12477 (j : Fin 43) : Supply 12477 (parameters j)
    (cellLower scalarRow12477.grid (sourceIndex j))
    (cellUpper scalarRow12477.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12477.grid grid_top_bounds12477 j

theorem radii12477 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12477.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12477 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12477 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12477.grid grid_top_bounds12477 j hθ

noncomputable def covarianceInputs12477 :
    BstLean.Part263.CovarianceInputs 12477 scalarRow12477.grid parameters (caps repair12477) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12477 grid_top_bounds12477 repair12477

noncomputable def covarianceEvent12477 : Set (AgFam 12477) :=
  BstLean.Part263.covarianceEvent 12477 scalarRow12477.grid parameters

theorem covarianceEvent12477_measurable : MeasurableSet covarianceEvent12477 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12477_payment :
    (retDist (paperDesignP 12477).toCentres).real
      (agentEv (paperDesignP 12477) covarianceEvent12477)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12477

theorem localCov12477 : BstLean.Part259.LocalCovarianceOn covarianceEvent12477
    (BstLean.Part263.cell scalarRow12477.grid) (caps repair12477) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12477

theorem covarianceGood12477_payment :
    (retDist (paperDesignP 12477).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12477)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12477_payment



end BstLean.Part269.N12477

namespace BstLean.Part269.N12477
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12477}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12477.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12477) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12477).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12477 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12477) (by norm_num) BstLean.Part268.WorldRow12477.worldPackage rfl
    BstLean.Part268.WorldRow12477.product_lower (BstLean.Part268.WorldRow12477.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12477} (hw : c ∈ Hof BstLean.Part268.WorldRow12477.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12477) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12477) (by norm_num) BstLean.Part268.WorldRow12477.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12477} (hw : c ∈ Hof BstLean.Part268.WorldRow12477.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12477) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12477).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12477) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12477_eq : scalarRow12477.targetFrame = BstLean.Part268.agent12477.frame := by
  norm_num [scalarRow12477,BstLean.Part268.agent12477]

noncomputable def frameData12477 : BstLean.Part264b.FrameData 12477 :=
  BstLean.Part269.frameData_from_numerics (n := 12477) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12477.worldPackage rfl BstLean.Part268.WorldRow12477.product_lower (BstLean.Part268.WorldRow12477.producthi.2.trans (by norm_num))
    scalarRow12477 repair12477 covarianceInputs12477 (fun i hi => sourceNumerics12477 hi)
    BstLean.Part268.agent12477.frame targetFrame12477_eq


end BstLean.Part269.N12477

namespace BstLean.Part269.N12478
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12478 : scalarRow12478.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12478, BstLean.Part268.grid12478, BstLean.Part263.worldGrid]

theorem supplies12478 (j : Fin 43) : Supply 12478 (parameters j)
    (cellLower scalarRow12478.grid (sourceIndex j))
    (cellUpper scalarRow12478.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12478.grid grid_top_bounds12478 j

theorem radii12478 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12478.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12478 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12478 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12478.grid grid_top_bounds12478 j hθ

noncomputable def covarianceInputs12478 :
    BstLean.Part263.CovarianceInputs 12478 scalarRow12478.grid parameters (caps repair12478) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12478 grid_top_bounds12478 repair12478

noncomputable def covarianceEvent12478 : Set (AgFam 12478) :=
  BstLean.Part263.covarianceEvent 12478 scalarRow12478.grid parameters

theorem covarianceEvent12478_measurable : MeasurableSet covarianceEvent12478 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12478_payment :
    (retDist (paperDesignP 12478).toCentres).real
      (agentEv (paperDesignP 12478) covarianceEvent12478)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12478

theorem localCov12478 : BstLean.Part259.LocalCovarianceOn covarianceEvent12478
    (BstLean.Part263.cell scalarRow12478.grid) (caps repair12478) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12478

theorem covarianceGood12478_payment :
    (retDist (paperDesignP 12478).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12478)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12478_payment



end BstLean.Part269.N12478

namespace BstLean.Part269.N12478
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12478}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12478.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12478) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12478).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12478 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12478) (by norm_num) BstLean.Part268.WorldRow12478.worldPackage rfl
    BstLean.Part268.WorldRow12478.product_lower (BstLean.Part268.WorldRow12478.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12478} (hw : c ∈ Hof BstLean.Part268.WorldRow12478.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12478) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12478) (by norm_num) BstLean.Part268.WorldRow12478.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12478} (hw : c ∈ Hof BstLean.Part268.WorldRow12478.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12478) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12478).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12478) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12478_eq : scalarRow12478.targetFrame = BstLean.Part268.agent12478.frame := by
  norm_num [scalarRow12478,BstLean.Part268.agent12478]

noncomputable def frameData12478 : BstLean.Part264b.FrameData 12478 :=
  BstLean.Part269.frameData_from_numerics (n := 12478) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12478.worldPackage rfl BstLean.Part268.WorldRow12478.product_lower (BstLean.Part268.WorldRow12478.producthi.2.trans (by norm_num))
    scalarRow12478 repair12478 covarianceInputs12478 (fun i hi => sourceNumerics12478 hi)
    BstLean.Part268.agent12478.frame targetFrame12478_eq


end BstLean.Part269.N12478

namespace BstLean.Part269.N12479
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12479 : scalarRow12479.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12479, BstLean.Part268.grid12479, BstLean.Part263.worldGrid]

theorem supplies12479 (j : Fin 43) : Supply 12479 (parameters j)
    (cellLower scalarRow12479.grid (sourceIndex j))
    (cellUpper scalarRow12479.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12479.grid grid_top_bounds12479 j

theorem radii12479 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12479.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12479 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12479 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12479.grid grid_top_bounds12479 j hθ

noncomputable def covarianceInputs12479 :
    BstLean.Part263.CovarianceInputs 12479 scalarRow12479.grid parameters (caps repair12479) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12479 grid_top_bounds12479 repair12479

noncomputable def covarianceEvent12479 : Set (AgFam 12479) :=
  BstLean.Part263.covarianceEvent 12479 scalarRow12479.grid parameters

theorem covarianceEvent12479_measurable : MeasurableSet covarianceEvent12479 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12479_payment :
    (retDist (paperDesignP 12479).toCentres).real
      (agentEv (paperDesignP 12479) covarianceEvent12479)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12479

theorem localCov12479 : BstLean.Part259.LocalCovarianceOn covarianceEvent12479
    (BstLean.Part263.cell scalarRow12479.grid) (caps repair12479) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12479

theorem covarianceGood12479_payment :
    (retDist (paperDesignP 12479).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12479)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12479_payment



end BstLean.Part269.N12479

namespace BstLean.Part269.N12479
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12479}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12479.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12479) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12479).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12479 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12479) (by norm_num) BstLean.Part268.WorldRow12479.worldPackage rfl
    BstLean.Part268.WorldRow12479.product_lower (BstLean.Part268.WorldRow12479.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12479} (hw : c ∈ Hof BstLean.Part268.WorldRow12479.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12479) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12479) (by norm_num) BstLean.Part268.WorldRow12479.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12479} (hw : c ∈ Hof BstLean.Part268.WorldRow12479.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12479) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12479).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12479) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12479_eq : scalarRow12479.targetFrame = BstLean.Part268.agent12479.frame := by
  norm_num [scalarRow12479,BstLean.Part268.agent12479]

noncomputable def frameData12479 : BstLean.Part264b.FrameData 12479 :=
  BstLean.Part269.frameData_from_numerics (n := 12479) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12479.worldPackage rfl BstLean.Part268.WorldRow12479.product_lower (BstLean.Part268.WorldRow12479.producthi.2.trans (by norm_num))
    scalarRow12479 repair12479 covarianceInputs12479 (fun i hi => sourceNumerics12479 hi)
    BstLean.Part268.agent12479.frame targetFrame12479_eq


end BstLean.Part269.N12479
