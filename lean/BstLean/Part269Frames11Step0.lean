import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World11Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs11
import BstLean.Part269Rows11
import BstLean.Part269Sources11
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12625
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12625 : scalarRow12625.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12625, BstLean.Part268.grid12625, BstLean.Part263.worldGrid]

theorem supplies12625 (j : Fin 43) : Supply 12625 (parameters j)
    (cellLower scalarRow12625.grid (sourceIndex j))
    (cellUpper scalarRow12625.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12625.grid grid_top_bounds12625 j

theorem radii12625 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12625.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12625 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12625 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12625.grid grid_top_bounds12625 j hθ

noncomputable def covarianceInputs12625 :
    BstLean.Part263.CovarianceInputs 12625 scalarRow12625.grid parameters (caps repair12625) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12625 grid_top_bounds12625 repair12625

noncomputable def covarianceEvent12625 : Set (AgFam 12625) :=
  BstLean.Part263.covarianceEvent 12625 scalarRow12625.grid parameters

theorem covarianceEvent12625_measurable : MeasurableSet covarianceEvent12625 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12625_payment :
    (retDist (paperDesignP 12625).toCentres).real
      (agentEv (paperDesignP 12625) covarianceEvent12625)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12625

theorem localCov12625 : BstLean.Part259.LocalCovarianceOn covarianceEvent12625
    (BstLean.Part263.cell scalarRow12625.grid) (caps repair12625) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12625

theorem covarianceGood12625_payment :
    (retDist (paperDesignP 12625).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12625)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12625_payment



end BstLean.Part269.N12625

namespace BstLean.Part269.N12625
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12625}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12625.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12625) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12625).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12625 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12625) (by norm_num) BstLean.Part268.WorldRow12625.worldPackage rfl
    BstLean.Part268.WorldRow12625.product_lower (BstLean.Part268.WorldRow12625.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12625} (hw : c ∈ Hof BstLean.Part268.WorldRow12625.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12625) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12625) (by norm_num) BstLean.Part268.WorldRow12625.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12625} (hw : c ∈ Hof BstLean.Part268.WorldRow12625.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12625) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12625).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12625) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12625_eq : scalarRow12625.targetFrame = BstLean.Part268.agent12625.frame := by
  norm_num [scalarRow12625,BstLean.Part268.agent12625]

noncomputable def frameData12625 : BstLean.Part264b.FrameData 12625 :=
  BstLean.Part269.frameData_from_numerics (n := 12625) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12625.worldPackage rfl BstLean.Part268.WorldRow12625.product_lower (BstLean.Part268.WorldRow12625.producthi.2.trans (by norm_num))
    scalarRow12625 repair12625 covarianceInputs12625 (fun i hi => sourceNumerics12625 hi)
    BstLean.Part268.agent12625.frame targetFrame12625_eq


end BstLean.Part269.N12625

namespace BstLean.Part269.N12626
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12626 : scalarRow12626.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12626, BstLean.Part268.grid12626, BstLean.Part263.worldGrid]

theorem supplies12626 (j : Fin 43) : Supply 12626 (parameters j)
    (cellLower scalarRow12626.grid (sourceIndex j))
    (cellUpper scalarRow12626.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12626.grid grid_top_bounds12626 j

theorem radii12626 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12626.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12626 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12626 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12626.grid grid_top_bounds12626 j hθ

noncomputable def covarianceInputs12626 :
    BstLean.Part263.CovarianceInputs 12626 scalarRow12626.grid parameters (caps repair12626) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12626 grid_top_bounds12626 repair12626

noncomputable def covarianceEvent12626 : Set (AgFam 12626) :=
  BstLean.Part263.covarianceEvent 12626 scalarRow12626.grid parameters

theorem covarianceEvent12626_measurable : MeasurableSet covarianceEvent12626 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12626_payment :
    (retDist (paperDesignP 12626).toCentres).real
      (agentEv (paperDesignP 12626) covarianceEvent12626)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12626

theorem localCov12626 : BstLean.Part259.LocalCovarianceOn covarianceEvent12626
    (BstLean.Part263.cell scalarRow12626.grid) (caps repair12626) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12626

theorem covarianceGood12626_payment :
    (retDist (paperDesignP 12626).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12626)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12626_payment



end BstLean.Part269.N12626

namespace BstLean.Part269.N12626
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12626}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12626.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12626) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12626).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12626 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12626) (by norm_num) BstLean.Part268.WorldRow12626.worldPackage rfl
    BstLean.Part268.WorldRow12626.product_lower (BstLean.Part268.WorldRow12626.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12626} (hw : c ∈ Hof BstLean.Part268.WorldRow12626.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12626) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12626) (by norm_num) BstLean.Part268.WorldRow12626.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12626} (hw : c ∈ Hof BstLean.Part268.WorldRow12626.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12626) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12626).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12626) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12626_eq : scalarRow12626.targetFrame = BstLean.Part268.agent12626.frame := by
  norm_num [scalarRow12626,BstLean.Part268.agent12626]

noncomputable def frameData12626 : BstLean.Part264b.FrameData 12626 :=
  BstLean.Part269.frameData_from_numerics (n := 12626) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12626.worldPackage rfl BstLean.Part268.WorldRow12626.product_lower (BstLean.Part268.WorldRow12626.producthi.2.trans (by norm_num))
    scalarRow12626 repair12626 covarianceInputs12626 (fun i hi => sourceNumerics12626 hi)
    BstLean.Part268.agent12626.frame targetFrame12626_eq


end BstLean.Part269.N12626

namespace BstLean.Part269.N12627
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12627 : scalarRow12627.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12627, BstLean.Part268.grid12627, BstLean.Part263.worldGrid]

theorem supplies12627 (j : Fin 43) : Supply 12627 (parameters j)
    (cellLower scalarRow12627.grid (sourceIndex j))
    (cellUpper scalarRow12627.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12627.grid grid_top_bounds12627 j

theorem radii12627 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12627.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12627 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12627 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12627.grid grid_top_bounds12627 j hθ

noncomputable def covarianceInputs12627 :
    BstLean.Part263.CovarianceInputs 12627 scalarRow12627.grid parameters (caps repair12627) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12627 grid_top_bounds12627 repair12627

noncomputable def covarianceEvent12627 : Set (AgFam 12627) :=
  BstLean.Part263.covarianceEvent 12627 scalarRow12627.grid parameters

theorem covarianceEvent12627_measurable : MeasurableSet covarianceEvent12627 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12627_payment :
    (retDist (paperDesignP 12627).toCentres).real
      (agentEv (paperDesignP 12627) covarianceEvent12627)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12627

theorem localCov12627 : BstLean.Part259.LocalCovarianceOn covarianceEvent12627
    (BstLean.Part263.cell scalarRow12627.grid) (caps repair12627) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12627

theorem covarianceGood12627_payment :
    (retDist (paperDesignP 12627).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12627)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12627_payment



end BstLean.Part269.N12627

namespace BstLean.Part269.N12627
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12627}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12627.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12627) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12627).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12627 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12627) (by norm_num) BstLean.Part268.WorldRow12627.worldPackage rfl
    BstLean.Part268.WorldRow12627.product_lower (BstLean.Part268.WorldRow12627.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12627} (hw : c ∈ Hof BstLean.Part268.WorldRow12627.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12627) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12627) (by norm_num) BstLean.Part268.WorldRow12627.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12627} (hw : c ∈ Hof BstLean.Part268.WorldRow12627.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12627) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12627).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12627) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12627_eq : scalarRow12627.targetFrame = BstLean.Part268.agent12627.frame := by
  norm_num [scalarRow12627,BstLean.Part268.agent12627]

noncomputable def frameData12627 : BstLean.Part264b.FrameData 12627 :=
  BstLean.Part269.frameData_from_numerics (n := 12627) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12627.worldPackage rfl BstLean.Part268.WorldRow12627.product_lower (BstLean.Part268.WorldRow12627.producthi.2.trans (by norm_num))
    scalarRow12627 repair12627 covarianceInputs12627 (fun i hi => sourceNumerics12627 hi)
    BstLean.Part268.agent12627.frame targetFrame12627_eq


end BstLean.Part269.N12627

namespace BstLean.Part269.N12628
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12628 : scalarRow12628.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12628, BstLean.Part268.grid12628, BstLean.Part263.worldGrid]

theorem supplies12628 (j : Fin 43) : Supply 12628 (parameters j)
    (cellLower scalarRow12628.grid (sourceIndex j))
    (cellUpper scalarRow12628.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12628.grid grid_top_bounds12628 j

theorem radii12628 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12628.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12628 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12628 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12628.grid grid_top_bounds12628 j hθ

noncomputable def covarianceInputs12628 :
    BstLean.Part263.CovarianceInputs 12628 scalarRow12628.grid parameters (caps repair12628) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12628 grid_top_bounds12628 repair12628

noncomputable def covarianceEvent12628 : Set (AgFam 12628) :=
  BstLean.Part263.covarianceEvent 12628 scalarRow12628.grid parameters

theorem covarianceEvent12628_measurable : MeasurableSet covarianceEvent12628 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12628_payment :
    (retDist (paperDesignP 12628).toCentres).real
      (agentEv (paperDesignP 12628) covarianceEvent12628)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12628

theorem localCov12628 : BstLean.Part259.LocalCovarianceOn covarianceEvent12628
    (BstLean.Part263.cell scalarRow12628.grid) (caps repair12628) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12628

theorem covarianceGood12628_payment :
    (retDist (paperDesignP 12628).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12628)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12628_payment



end BstLean.Part269.N12628

namespace BstLean.Part269.N12628
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12628}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12628.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12628) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12628).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12628 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12628) (by norm_num) BstLean.Part268.WorldRow12628.worldPackage rfl
    BstLean.Part268.WorldRow12628.product_lower (BstLean.Part268.WorldRow12628.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12628} (hw : c ∈ Hof BstLean.Part268.WorldRow12628.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12628) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12628) (by norm_num) BstLean.Part268.WorldRow12628.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12628} (hw : c ∈ Hof BstLean.Part268.WorldRow12628.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12628) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12628).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12628) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12628_eq : scalarRow12628.targetFrame = BstLean.Part268.agent12628.frame := by
  norm_num [scalarRow12628,BstLean.Part268.agent12628]

noncomputable def frameData12628 : BstLean.Part264b.FrameData 12628 :=
  BstLean.Part269.frameData_from_numerics (n := 12628) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12628.worldPackage rfl BstLean.Part268.WorldRow12628.product_lower (BstLean.Part268.WorldRow12628.producthi.2.trans (by norm_num))
    scalarRow12628 repair12628 covarianceInputs12628 (fun i hi => sourceNumerics12628 hi)
    BstLean.Part268.agent12628.frame targetFrame12628_eq


end BstLean.Part269.N12628

namespace BstLean.Part269.N12629
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12629 : scalarRow12629.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12629, BstLean.Part268.grid12629, BstLean.Part263.worldGrid]

theorem supplies12629 (j : Fin 43) : Supply 12629 (parameters j)
    (cellLower scalarRow12629.grid (sourceIndex j))
    (cellUpper scalarRow12629.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12629.grid grid_top_bounds12629 j

theorem radii12629 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12629.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12629 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12629 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12629.grid grid_top_bounds12629 j hθ

noncomputable def covarianceInputs12629 :
    BstLean.Part263.CovarianceInputs 12629 scalarRow12629.grid parameters (caps repair12629) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12629 grid_top_bounds12629 repair12629

noncomputable def covarianceEvent12629 : Set (AgFam 12629) :=
  BstLean.Part263.covarianceEvent 12629 scalarRow12629.grid parameters

theorem covarianceEvent12629_measurable : MeasurableSet covarianceEvent12629 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12629_payment :
    (retDist (paperDesignP 12629).toCentres).real
      (agentEv (paperDesignP 12629) covarianceEvent12629)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12629

theorem localCov12629 : BstLean.Part259.LocalCovarianceOn covarianceEvent12629
    (BstLean.Part263.cell scalarRow12629.grid) (caps repair12629) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12629

theorem covarianceGood12629_payment :
    (retDist (paperDesignP 12629).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12629)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12629_payment



end BstLean.Part269.N12629

namespace BstLean.Part269.N12629
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12629}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12629.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12629) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12629).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12629 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12629) (by norm_num) BstLean.Part268.WorldRow12629.worldPackage rfl
    BstLean.Part268.WorldRow12629.product_lower (BstLean.Part268.WorldRow12629.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12629} (hw : c ∈ Hof BstLean.Part268.WorldRow12629.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12629) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12629) (by norm_num) BstLean.Part268.WorldRow12629.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12629} (hw : c ∈ Hof BstLean.Part268.WorldRow12629.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12629) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12629).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12629) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12629_eq : scalarRow12629.targetFrame = BstLean.Part268.agent12629.frame := by
  norm_num [scalarRow12629,BstLean.Part268.agent12629]

noncomputable def frameData12629 : BstLean.Part264b.FrameData 12629 :=
  BstLean.Part269.frameData_from_numerics (n := 12629) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12629.worldPackage rfl BstLean.Part268.WorldRow12629.product_lower (BstLean.Part268.WorldRow12629.producthi.2.trans (by norm_num))
    scalarRow12629 repair12629 covarianceInputs12629 (fun i hi => sourceNumerics12629 hi)
    BstLean.Part268.agent12629.frame targetFrame12629_eq


end BstLean.Part269.N12629
