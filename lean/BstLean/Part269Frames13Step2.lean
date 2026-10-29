import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World13Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs13
import BstLean.Part269Rows13
import BstLean.Part269Sources13
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12685
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12685 : scalarRow12685.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12685, BstLean.Part268.grid12685, BstLean.Part263.worldGrid]

theorem supplies12685 (j : Fin 43) : Supply 12685 (parameters j)
    (cellLower scalarRow12685.grid (sourceIndex j))
    (cellUpper scalarRow12685.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12685.grid grid_top_bounds12685 j

theorem radii12685 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12685.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12685 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12685 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12685.grid grid_top_bounds12685 j hθ

noncomputable def covarianceInputs12685 :
    BstLean.Part263.CovarianceInputs 12685 scalarRow12685.grid parameters (caps repair12685) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12685 grid_top_bounds12685 repair12685

noncomputable def covarianceEvent12685 : Set (AgFam 12685) :=
  BstLean.Part263.covarianceEvent 12685 scalarRow12685.grid parameters

theorem covarianceEvent12685_measurable : MeasurableSet covarianceEvent12685 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12685_payment :
    (retDist (paperDesignP 12685).toCentres).real
      (agentEv (paperDesignP 12685) covarianceEvent12685)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12685

theorem localCov12685 : BstLean.Part259.LocalCovarianceOn covarianceEvent12685
    (BstLean.Part263.cell scalarRow12685.grid) (caps repair12685) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12685

theorem covarianceGood12685_payment :
    (retDist (paperDesignP 12685).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12685)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12685_payment



end BstLean.Part269.N12685

namespace BstLean.Part269.N12685
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12685}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12685.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12685) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12685).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12685 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12685) (by norm_num) BstLean.Part268.WorldRow12685.worldPackage rfl
    BstLean.Part268.WorldRow12685.product_lower (BstLean.Part268.WorldRow12685.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12685} (hw : c ∈ Hof BstLean.Part268.WorldRow12685.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12685) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12685) (by norm_num) BstLean.Part268.WorldRow12685.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12685} (hw : c ∈ Hof BstLean.Part268.WorldRow12685.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12685) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12685).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12685) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12685_eq : scalarRow12685.targetFrame = BstLean.Part268.agent12685.frame := by
  norm_num [scalarRow12685,BstLean.Part268.agent12685]

noncomputable def frameData12685 : BstLean.Part264b.FrameData 12685 :=
  BstLean.Part269.frameData_from_numerics (n := 12685) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12685.worldPackage rfl BstLean.Part268.WorldRow12685.product_lower (BstLean.Part268.WorldRow12685.producthi.2.trans (by norm_num))
    scalarRow12685 repair12685 covarianceInputs12685 (fun i hi => sourceNumerics12685 hi)
    BstLean.Part268.agent12685.frame targetFrame12685_eq


end BstLean.Part269.N12685

namespace BstLean.Part269.N12686
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12686 : scalarRow12686.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12686, BstLean.Part268.grid12686, BstLean.Part263.worldGrid]

theorem supplies12686 (j : Fin 43) : Supply 12686 (parameters j)
    (cellLower scalarRow12686.grid (sourceIndex j))
    (cellUpper scalarRow12686.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12686.grid grid_top_bounds12686 j

theorem radii12686 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12686.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12686 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12686 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12686.grid grid_top_bounds12686 j hθ

noncomputable def covarianceInputs12686 :
    BstLean.Part263.CovarianceInputs 12686 scalarRow12686.grid parameters (caps repair12686) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12686 grid_top_bounds12686 repair12686

noncomputable def covarianceEvent12686 : Set (AgFam 12686) :=
  BstLean.Part263.covarianceEvent 12686 scalarRow12686.grid parameters

theorem covarianceEvent12686_measurable : MeasurableSet covarianceEvent12686 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12686_payment :
    (retDist (paperDesignP 12686).toCentres).real
      (agentEv (paperDesignP 12686) covarianceEvent12686)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12686

theorem localCov12686 : BstLean.Part259.LocalCovarianceOn covarianceEvent12686
    (BstLean.Part263.cell scalarRow12686.grid) (caps repair12686) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12686

theorem covarianceGood12686_payment :
    (retDist (paperDesignP 12686).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12686)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12686_payment



end BstLean.Part269.N12686

namespace BstLean.Part269.N12686
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12686}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12686.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12686) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12686).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12686 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12686) (by norm_num) BstLean.Part268.WorldRow12686.worldPackage rfl
    BstLean.Part268.WorldRow12686.product_lower (BstLean.Part268.WorldRow12686.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12686} (hw : c ∈ Hof BstLean.Part268.WorldRow12686.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12686) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12686) (by norm_num) BstLean.Part268.WorldRow12686.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12686} (hw : c ∈ Hof BstLean.Part268.WorldRow12686.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12686) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12686).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12686) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12686_eq : scalarRow12686.targetFrame = BstLean.Part268.agent12686.frame := by
  norm_num [scalarRow12686,BstLean.Part268.agent12686]

noncomputable def frameData12686 : BstLean.Part264b.FrameData 12686 :=
  BstLean.Part269.frameData_from_numerics (n := 12686) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12686.worldPackage rfl BstLean.Part268.WorldRow12686.product_lower (BstLean.Part268.WorldRow12686.producthi.2.trans (by norm_num))
    scalarRow12686 repair12686 covarianceInputs12686 (fun i hi => sourceNumerics12686 hi)
    BstLean.Part268.agent12686.frame targetFrame12686_eq


end BstLean.Part269.N12686

namespace BstLean.Part269.N12687
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12687 : scalarRow12687.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12687, BstLean.Part268.grid12687, BstLean.Part263.worldGrid]

theorem supplies12687 (j : Fin 43) : Supply 12687 (parameters j)
    (cellLower scalarRow12687.grid (sourceIndex j))
    (cellUpper scalarRow12687.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12687.grid grid_top_bounds12687 j

theorem radii12687 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12687.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12687 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12687 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12687.grid grid_top_bounds12687 j hθ

noncomputable def covarianceInputs12687 :
    BstLean.Part263.CovarianceInputs 12687 scalarRow12687.grid parameters (caps repair12687) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12687 grid_top_bounds12687 repair12687

noncomputable def covarianceEvent12687 : Set (AgFam 12687) :=
  BstLean.Part263.covarianceEvent 12687 scalarRow12687.grid parameters

theorem covarianceEvent12687_measurable : MeasurableSet covarianceEvent12687 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12687_payment :
    (retDist (paperDesignP 12687).toCentres).real
      (agentEv (paperDesignP 12687) covarianceEvent12687)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12687

theorem localCov12687 : BstLean.Part259.LocalCovarianceOn covarianceEvent12687
    (BstLean.Part263.cell scalarRow12687.grid) (caps repair12687) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12687

theorem covarianceGood12687_payment :
    (retDist (paperDesignP 12687).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12687)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12687_payment



end BstLean.Part269.N12687

namespace BstLean.Part269.N12687
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12687}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12687.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12687) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12687).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12687 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12687) (by norm_num) BstLean.Part268.WorldRow12687.worldPackage rfl
    BstLean.Part268.WorldRow12687.product_lower (BstLean.Part268.WorldRow12687.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12687} (hw : c ∈ Hof BstLean.Part268.WorldRow12687.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12687) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12687) (by norm_num) BstLean.Part268.WorldRow12687.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12687} (hw : c ∈ Hof BstLean.Part268.WorldRow12687.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12687) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12687).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12687) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12687_eq : scalarRow12687.targetFrame = BstLean.Part268.agent12687.frame := by
  norm_num [scalarRow12687,BstLean.Part268.agent12687]

noncomputable def frameData12687 : BstLean.Part264b.FrameData 12687 :=
  BstLean.Part269.frameData_from_numerics (n := 12687) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12687.worldPackage rfl BstLean.Part268.WorldRow12687.product_lower (BstLean.Part268.WorldRow12687.producthi.2.trans (by norm_num))
    scalarRow12687 repair12687 covarianceInputs12687 (fun i hi => sourceNumerics12687 hi)
    BstLean.Part268.agent12687.frame targetFrame12687_eq


end BstLean.Part269.N12687

namespace BstLean.Part269.N12688
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12688 : scalarRow12688.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12688, BstLean.Part268.grid12688, BstLean.Part263.worldGrid]

theorem supplies12688 (j : Fin 43) : Supply 12688 (parameters j)
    (cellLower scalarRow12688.grid (sourceIndex j))
    (cellUpper scalarRow12688.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12688.grid grid_top_bounds12688 j

theorem radii12688 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12688.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12688 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12688 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12688.grid grid_top_bounds12688 j hθ

noncomputable def covarianceInputs12688 :
    BstLean.Part263.CovarianceInputs 12688 scalarRow12688.grid parameters (caps repair12688) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12688 grid_top_bounds12688 repair12688

noncomputable def covarianceEvent12688 : Set (AgFam 12688) :=
  BstLean.Part263.covarianceEvent 12688 scalarRow12688.grid parameters

theorem covarianceEvent12688_measurable : MeasurableSet covarianceEvent12688 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12688_payment :
    (retDist (paperDesignP 12688).toCentres).real
      (agentEv (paperDesignP 12688) covarianceEvent12688)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12688

theorem localCov12688 : BstLean.Part259.LocalCovarianceOn covarianceEvent12688
    (BstLean.Part263.cell scalarRow12688.grid) (caps repair12688) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12688

theorem covarianceGood12688_payment :
    (retDist (paperDesignP 12688).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12688)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12688_payment



end BstLean.Part269.N12688

namespace BstLean.Part269.N12688
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12688}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12688.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12688) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12688).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12688 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12688) (by norm_num) BstLean.Part268.WorldRow12688.worldPackage rfl
    BstLean.Part268.WorldRow12688.product_lower (BstLean.Part268.WorldRow12688.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12688} (hw : c ∈ Hof BstLean.Part268.WorldRow12688.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12688) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12688) (by norm_num) BstLean.Part268.WorldRow12688.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12688} (hw : c ∈ Hof BstLean.Part268.WorldRow12688.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12688) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12688).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12688) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12688_eq : scalarRow12688.targetFrame = BstLean.Part268.agent12688.frame := by
  norm_num [scalarRow12688,BstLean.Part268.agent12688]

noncomputable def frameData12688 : BstLean.Part264b.FrameData 12688 :=
  BstLean.Part269.frameData_from_numerics (n := 12688) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12688.worldPackage rfl BstLean.Part268.WorldRow12688.product_lower (BstLean.Part268.WorldRow12688.producthi.2.trans (by norm_num))
    scalarRow12688 repair12688 covarianceInputs12688 (fun i hi => sourceNumerics12688 hi)
    BstLean.Part268.agent12688.frame targetFrame12688_eq


end BstLean.Part269.N12688

namespace BstLean.Part269.N12689
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12689 : scalarRow12689.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12689, BstLean.Part268.grid12689, BstLean.Part263.worldGrid]

theorem supplies12689 (j : Fin 43) : Supply 12689 (parameters j)
    (cellLower scalarRow12689.grid (sourceIndex j))
    (cellUpper scalarRow12689.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12689.grid grid_top_bounds12689 j

theorem radii12689 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12689.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12689 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12689 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12689.grid grid_top_bounds12689 j hθ

noncomputable def covarianceInputs12689 :
    BstLean.Part263.CovarianceInputs 12689 scalarRow12689.grid parameters (caps repair12689) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12689 grid_top_bounds12689 repair12689

noncomputable def covarianceEvent12689 : Set (AgFam 12689) :=
  BstLean.Part263.covarianceEvent 12689 scalarRow12689.grid parameters

theorem covarianceEvent12689_measurable : MeasurableSet covarianceEvent12689 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12689_payment :
    (retDist (paperDesignP 12689).toCentres).real
      (agentEv (paperDesignP 12689) covarianceEvent12689)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12689

theorem localCov12689 : BstLean.Part259.LocalCovarianceOn covarianceEvent12689
    (BstLean.Part263.cell scalarRow12689.grid) (caps repair12689) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12689

theorem covarianceGood12689_payment :
    (retDist (paperDesignP 12689).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12689)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12689_payment



end BstLean.Part269.N12689

namespace BstLean.Part269.N12689
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12689}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12689.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12689) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12689).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12689 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12689) (by norm_num) BstLean.Part268.WorldRow12689.worldPackage rfl
    BstLean.Part268.WorldRow12689.product_lower (BstLean.Part268.WorldRow12689.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12689} (hw : c ∈ Hof BstLean.Part268.WorldRow12689.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12689) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12689) (by norm_num) BstLean.Part268.WorldRow12689.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12689} (hw : c ∈ Hof BstLean.Part268.WorldRow12689.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12689) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12689).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12689) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12689_eq : scalarRow12689.targetFrame = BstLean.Part268.agent12689.frame := by
  norm_num [scalarRow12689,BstLean.Part268.agent12689]

noncomputable def frameData12689 : BstLean.Part264b.FrameData 12689 :=
  BstLean.Part269.frameData_from_numerics (n := 12689) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12689.worldPackage rfl BstLean.Part268.WorldRow12689.product_lower (BstLean.Part268.WorldRow12689.producthi.2.trans (by norm_num))
    scalarRow12689 repair12689 covarianceInputs12689 (fun i hi => sourceNumerics12689 hi)
    BstLean.Part268.agent12689.frame targetFrame12689_eq


end BstLean.Part269.N12689
