import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World6Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs6
import BstLean.Part269Rows6
import BstLean.Part269Sources6
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12515
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12515 : scalarRow12515.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12515, BstLean.Part268.grid12515, BstLean.Part263.worldGrid]

theorem supplies12515 (j : Fin 43) : Supply 12515 (parameters j)
    (cellLower scalarRow12515.grid (sourceIndex j))
    (cellUpper scalarRow12515.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12515.grid grid_top_bounds12515 j

theorem radii12515 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12515.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12515 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12515 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12515.grid grid_top_bounds12515 j hθ

noncomputable def covarianceInputs12515 :
    BstLean.Part263.CovarianceInputs 12515 scalarRow12515.grid parameters (caps repair12515) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12515 grid_top_bounds12515 repair12515

noncomputable def covarianceEvent12515 : Set (AgFam 12515) :=
  BstLean.Part263.covarianceEvent 12515 scalarRow12515.grid parameters

theorem covarianceEvent12515_measurable : MeasurableSet covarianceEvent12515 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12515_payment :
    (retDist (paperDesignP 12515).toCentres).real
      (agentEv (paperDesignP 12515) covarianceEvent12515)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12515

theorem localCov12515 : BstLean.Part259.LocalCovarianceOn covarianceEvent12515
    (BstLean.Part263.cell scalarRow12515.grid) (caps repair12515) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12515

theorem covarianceGood12515_payment :
    (retDist (paperDesignP 12515).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12515)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12515_payment



end BstLean.Part269.N12515

namespace BstLean.Part269.N12515
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12515}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12515.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12515) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12515).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12515 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12515) (by norm_num) BstLean.Part268.WorldRow12515.worldPackage rfl
    BstLean.Part268.WorldRow12515.product_lower (BstLean.Part268.WorldRow12515.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12515} (hw : c ∈ Hof BstLean.Part268.WorldRow12515.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12515) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12515) (by norm_num) BstLean.Part268.WorldRow12515.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12515} (hw : c ∈ Hof BstLean.Part268.WorldRow12515.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12515) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12515).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12515) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12515_eq : scalarRow12515.targetFrame = BstLean.Part268.agent12515.frame := by
  norm_num [scalarRow12515,BstLean.Part268.agent12515]

noncomputable def frameData12515 : BstLean.Part264b.FrameData 12515 :=
  BstLean.Part269.frameData_from_numerics (n := 12515) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12515.worldPackage rfl BstLean.Part268.WorldRow12515.product_lower (BstLean.Part268.WorldRow12515.producthi.2.trans (by norm_num))
    scalarRow12515 repair12515 covarianceInputs12515 (fun i hi => sourceNumerics12515 hi)
    BstLean.Part268.agent12515.frame targetFrame12515_eq


end BstLean.Part269.N12515

namespace BstLean.Part269.N12516
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12516 : scalarRow12516.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12516, BstLean.Part268.grid12516, BstLean.Part263.worldGrid]

theorem supplies12516 (j : Fin 43) : Supply 12516 (parameters j)
    (cellLower scalarRow12516.grid (sourceIndex j))
    (cellUpper scalarRow12516.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12516.grid grid_top_bounds12516 j

theorem radii12516 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12516.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12516 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12516 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12516.grid grid_top_bounds12516 j hθ

noncomputable def covarianceInputs12516 :
    BstLean.Part263.CovarianceInputs 12516 scalarRow12516.grid parameters (caps repair12516) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12516 grid_top_bounds12516 repair12516

noncomputable def covarianceEvent12516 : Set (AgFam 12516) :=
  BstLean.Part263.covarianceEvent 12516 scalarRow12516.grid parameters

theorem covarianceEvent12516_measurable : MeasurableSet covarianceEvent12516 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12516_payment :
    (retDist (paperDesignP 12516).toCentres).real
      (agentEv (paperDesignP 12516) covarianceEvent12516)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12516

theorem localCov12516 : BstLean.Part259.LocalCovarianceOn covarianceEvent12516
    (BstLean.Part263.cell scalarRow12516.grid) (caps repair12516) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12516

theorem covarianceGood12516_payment :
    (retDist (paperDesignP 12516).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12516)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12516_payment



end BstLean.Part269.N12516

namespace BstLean.Part269.N12516
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12516}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12516.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12516) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12516).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12516 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12516) (by norm_num) BstLean.Part268.WorldRow12516.worldPackage rfl
    BstLean.Part268.WorldRow12516.product_lower (BstLean.Part268.WorldRow12516.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12516} (hw : c ∈ Hof BstLean.Part268.WorldRow12516.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12516) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12516) (by norm_num) BstLean.Part268.WorldRow12516.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12516} (hw : c ∈ Hof BstLean.Part268.WorldRow12516.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12516) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12516).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12516) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12516_eq : scalarRow12516.targetFrame = BstLean.Part268.agent12516.frame := by
  norm_num [scalarRow12516,BstLean.Part268.agent12516]

noncomputable def frameData12516 : BstLean.Part264b.FrameData 12516 :=
  BstLean.Part269.frameData_from_numerics (n := 12516) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12516.worldPackage rfl BstLean.Part268.WorldRow12516.product_lower (BstLean.Part268.WorldRow12516.producthi.2.trans (by norm_num))
    scalarRow12516 repair12516 covarianceInputs12516 (fun i hi => sourceNumerics12516 hi)
    BstLean.Part268.agent12516.frame targetFrame12516_eq


end BstLean.Part269.N12516

namespace BstLean.Part269.N12517
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12517 : scalarRow12517.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12517, BstLean.Part268.grid12517, BstLean.Part263.worldGrid]

theorem supplies12517 (j : Fin 43) : Supply 12517 (parameters j)
    (cellLower scalarRow12517.grid (sourceIndex j))
    (cellUpper scalarRow12517.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12517.grid grid_top_bounds12517 j

theorem radii12517 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12517.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12517 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12517 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12517.grid grid_top_bounds12517 j hθ

noncomputable def covarianceInputs12517 :
    BstLean.Part263.CovarianceInputs 12517 scalarRow12517.grid parameters (caps repair12517) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12517 grid_top_bounds12517 repair12517

noncomputable def covarianceEvent12517 : Set (AgFam 12517) :=
  BstLean.Part263.covarianceEvent 12517 scalarRow12517.grid parameters

theorem covarianceEvent12517_measurable : MeasurableSet covarianceEvent12517 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12517_payment :
    (retDist (paperDesignP 12517).toCentres).real
      (agentEv (paperDesignP 12517) covarianceEvent12517)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12517

theorem localCov12517 : BstLean.Part259.LocalCovarianceOn covarianceEvent12517
    (BstLean.Part263.cell scalarRow12517.grid) (caps repair12517) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12517

theorem covarianceGood12517_payment :
    (retDist (paperDesignP 12517).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12517)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12517_payment



end BstLean.Part269.N12517

namespace BstLean.Part269.N12517
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12517}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12517.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12517) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12517).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12517 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12517) (by norm_num) BstLean.Part268.WorldRow12517.worldPackage rfl
    BstLean.Part268.WorldRow12517.product_lower (BstLean.Part268.WorldRow12517.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12517} (hw : c ∈ Hof BstLean.Part268.WorldRow12517.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12517) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12517) (by norm_num) BstLean.Part268.WorldRow12517.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12517} (hw : c ∈ Hof BstLean.Part268.WorldRow12517.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12517) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12517).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12517) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12517_eq : scalarRow12517.targetFrame = BstLean.Part268.agent12517.frame := by
  norm_num [scalarRow12517,BstLean.Part268.agent12517]

noncomputable def frameData12517 : BstLean.Part264b.FrameData 12517 :=
  BstLean.Part269.frameData_from_numerics (n := 12517) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12517.worldPackage rfl BstLean.Part268.WorldRow12517.product_lower (BstLean.Part268.WorldRow12517.producthi.2.trans (by norm_num))
    scalarRow12517 repair12517 covarianceInputs12517 (fun i hi => sourceNumerics12517 hi)
    BstLean.Part268.agent12517.frame targetFrame12517_eq


end BstLean.Part269.N12517

namespace BstLean.Part269.N12518
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12518 : scalarRow12518.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12518, BstLean.Part268.grid12518, BstLean.Part263.worldGrid]

theorem supplies12518 (j : Fin 43) : Supply 12518 (parameters j)
    (cellLower scalarRow12518.grid (sourceIndex j))
    (cellUpper scalarRow12518.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12518.grid grid_top_bounds12518 j

theorem radii12518 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12518.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12518 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12518 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12518.grid grid_top_bounds12518 j hθ

noncomputable def covarianceInputs12518 :
    BstLean.Part263.CovarianceInputs 12518 scalarRow12518.grid parameters (caps repair12518) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12518 grid_top_bounds12518 repair12518

noncomputable def covarianceEvent12518 : Set (AgFam 12518) :=
  BstLean.Part263.covarianceEvent 12518 scalarRow12518.grid parameters

theorem covarianceEvent12518_measurable : MeasurableSet covarianceEvent12518 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12518_payment :
    (retDist (paperDesignP 12518).toCentres).real
      (agentEv (paperDesignP 12518) covarianceEvent12518)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12518

theorem localCov12518 : BstLean.Part259.LocalCovarianceOn covarianceEvent12518
    (BstLean.Part263.cell scalarRow12518.grid) (caps repair12518) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12518

theorem covarianceGood12518_payment :
    (retDist (paperDesignP 12518).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12518)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12518_payment



end BstLean.Part269.N12518

namespace BstLean.Part269.N12518
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12518}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12518.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12518) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12518).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12518 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12518) (by norm_num) BstLean.Part268.WorldRow12518.worldPackage rfl
    BstLean.Part268.WorldRow12518.product_lower (BstLean.Part268.WorldRow12518.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12518} (hw : c ∈ Hof BstLean.Part268.WorldRow12518.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12518) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12518) (by norm_num) BstLean.Part268.WorldRow12518.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12518} (hw : c ∈ Hof BstLean.Part268.WorldRow12518.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12518) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12518).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12518) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12518_eq : scalarRow12518.targetFrame = BstLean.Part268.agent12518.frame := by
  norm_num [scalarRow12518,BstLean.Part268.agent12518]

noncomputable def frameData12518 : BstLean.Part264b.FrameData 12518 :=
  BstLean.Part269.frameData_from_numerics (n := 12518) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12518.worldPackage rfl BstLean.Part268.WorldRow12518.product_lower (BstLean.Part268.WorldRow12518.producthi.2.trans (by norm_num))
    scalarRow12518 repair12518 covarianceInputs12518 (fun i hi => sourceNumerics12518 hi)
    BstLean.Part268.agent12518.frame targetFrame12518_eq


end BstLean.Part269.N12518

namespace BstLean.Part269.N12519
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12519 : scalarRow12519.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12519, BstLean.Part268.grid12519, BstLean.Part263.worldGrid]

theorem supplies12519 (j : Fin 43) : Supply 12519 (parameters j)
    (cellLower scalarRow12519.grid (sourceIndex j))
    (cellUpper scalarRow12519.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12519.grid grid_top_bounds12519 j

theorem radii12519 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12519.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12519 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12519 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12519.grid grid_top_bounds12519 j hθ

noncomputable def covarianceInputs12519 :
    BstLean.Part263.CovarianceInputs 12519 scalarRow12519.grid parameters (caps repair12519) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12519 grid_top_bounds12519 repair12519

noncomputable def covarianceEvent12519 : Set (AgFam 12519) :=
  BstLean.Part263.covarianceEvent 12519 scalarRow12519.grid parameters

theorem covarianceEvent12519_measurable : MeasurableSet covarianceEvent12519 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12519_payment :
    (retDist (paperDesignP 12519).toCentres).real
      (agentEv (paperDesignP 12519) covarianceEvent12519)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12519

theorem localCov12519 : BstLean.Part259.LocalCovarianceOn covarianceEvent12519
    (BstLean.Part263.cell scalarRow12519.grid) (caps repair12519) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12519

theorem covarianceGood12519_payment :
    (retDist (paperDesignP 12519).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12519)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12519_payment



end BstLean.Part269.N12519

namespace BstLean.Part269.N12519
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12519}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12519.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12519) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12519).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12519 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12519) (by norm_num) BstLean.Part268.WorldRow12519.worldPackage rfl
    BstLean.Part268.WorldRow12519.product_lower (BstLean.Part268.WorldRow12519.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12519} (hw : c ∈ Hof BstLean.Part268.WorldRow12519.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12519) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12519) (by norm_num) BstLean.Part268.WorldRow12519.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12519} (hw : c ∈ Hof BstLean.Part268.WorldRow12519.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12519) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12519).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12519) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12519_eq : scalarRow12519.targetFrame = BstLean.Part268.agent12519.frame := by
  norm_num [scalarRow12519,BstLean.Part268.agent12519]

noncomputable def frameData12519 : BstLean.Part264b.FrameData 12519 :=
  BstLean.Part269.frameData_from_numerics (n := 12519) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12519.worldPackage rfl BstLean.Part268.WorldRow12519.product_lower (BstLean.Part268.WorldRow12519.producthi.2.trans (by norm_num))
    scalarRow12519 repair12519 covarianceInputs12519 (fun i hi => sourceNumerics12519 hi)
    BstLean.Part268.agent12519.frame targetFrame12519_eq


end BstLean.Part269.N12519
