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

namespace BstLean.Part269.N12615
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12615 : scalarRow12615.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12615, BstLean.Part268.grid12615, BstLean.Part263.worldGrid]

theorem supplies12615 (j : Fin 43) : Supply 12615 (parameters j)
    (cellLower scalarRow12615.grid (sourceIndex j))
    (cellUpper scalarRow12615.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12615.grid grid_top_bounds12615 j

theorem radii12615 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12615.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12615 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12615 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12615.grid grid_top_bounds12615 j hθ

noncomputable def covarianceInputs12615 :
    BstLean.Part263.CovarianceInputs 12615 scalarRow12615.grid parameters (caps repair12615) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12615 grid_top_bounds12615 repair12615

noncomputable def covarianceEvent12615 : Set (AgFam 12615) :=
  BstLean.Part263.covarianceEvent 12615 scalarRow12615.grid parameters

theorem covarianceEvent12615_measurable : MeasurableSet covarianceEvent12615 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12615_payment :
    (retDist (paperDesignP 12615).toCentres).real
      (agentEv (paperDesignP 12615) covarianceEvent12615)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12615

theorem localCov12615 : BstLean.Part259.LocalCovarianceOn covarianceEvent12615
    (BstLean.Part263.cell scalarRow12615.grid) (caps repair12615) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12615

theorem covarianceGood12615_payment :
    (retDist (paperDesignP 12615).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12615)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12615_payment



end BstLean.Part269.N12615

namespace BstLean.Part269.N12615
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12615}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12615.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12615) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12615).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12615 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12615) (by norm_num) BstLean.Part268.WorldRow12615.worldPackage rfl
    BstLean.Part268.WorldRow12615.product_lower (BstLean.Part268.WorldRow12615.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12615} (hw : c ∈ Hof BstLean.Part268.WorldRow12615.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12615) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12615) (by norm_num) BstLean.Part268.WorldRow12615.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12615} (hw : c ∈ Hof BstLean.Part268.WorldRow12615.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12615) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12615).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12615) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12615_eq : scalarRow12615.targetFrame = BstLean.Part268.agent12615.frame := by
  norm_num [scalarRow12615,BstLean.Part268.agent12615]

noncomputable def frameData12615 : BstLean.Part264b.FrameData 12615 :=
  BstLean.Part269.frameData_from_numerics (n := 12615) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12615.worldPackage rfl BstLean.Part268.WorldRow12615.product_lower (BstLean.Part268.WorldRow12615.producthi.2.trans (by norm_num))
    scalarRow12615 repair12615 covarianceInputs12615 (fun i hi => sourceNumerics12615 hi)
    BstLean.Part268.agent12615.frame targetFrame12615_eq


end BstLean.Part269.N12615

namespace BstLean.Part269.N12616
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12616 : scalarRow12616.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12616, BstLean.Part268.grid12616, BstLean.Part263.worldGrid]

theorem supplies12616 (j : Fin 43) : Supply 12616 (parameters j)
    (cellLower scalarRow12616.grid (sourceIndex j))
    (cellUpper scalarRow12616.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12616.grid grid_top_bounds12616 j

theorem radii12616 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12616.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12616 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12616 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12616.grid grid_top_bounds12616 j hθ

noncomputable def covarianceInputs12616 :
    BstLean.Part263.CovarianceInputs 12616 scalarRow12616.grid parameters (caps repair12616) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12616 grid_top_bounds12616 repair12616

noncomputable def covarianceEvent12616 : Set (AgFam 12616) :=
  BstLean.Part263.covarianceEvent 12616 scalarRow12616.grid parameters

theorem covarianceEvent12616_measurable : MeasurableSet covarianceEvent12616 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12616_payment :
    (retDist (paperDesignP 12616).toCentres).real
      (agentEv (paperDesignP 12616) covarianceEvent12616)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12616

theorem localCov12616 : BstLean.Part259.LocalCovarianceOn covarianceEvent12616
    (BstLean.Part263.cell scalarRow12616.grid) (caps repair12616) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12616

theorem covarianceGood12616_payment :
    (retDist (paperDesignP 12616).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12616)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12616_payment



end BstLean.Part269.N12616

namespace BstLean.Part269.N12616
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12616}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12616.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12616) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12616).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12616 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12616) (by norm_num) BstLean.Part268.WorldRow12616.worldPackage rfl
    BstLean.Part268.WorldRow12616.product_lower (BstLean.Part268.WorldRow12616.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12616} (hw : c ∈ Hof BstLean.Part268.WorldRow12616.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12616) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12616) (by norm_num) BstLean.Part268.WorldRow12616.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12616} (hw : c ∈ Hof BstLean.Part268.WorldRow12616.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12616) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12616).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12616) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12616_eq : scalarRow12616.targetFrame = BstLean.Part268.agent12616.frame := by
  norm_num [scalarRow12616,BstLean.Part268.agent12616]

noncomputable def frameData12616 : BstLean.Part264b.FrameData 12616 :=
  BstLean.Part269.frameData_from_numerics (n := 12616) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12616.worldPackage rfl BstLean.Part268.WorldRow12616.product_lower (BstLean.Part268.WorldRow12616.producthi.2.trans (by norm_num))
    scalarRow12616 repair12616 covarianceInputs12616 (fun i hi => sourceNumerics12616 hi)
    BstLean.Part268.agent12616.frame targetFrame12616_eq


end BstLean.Part269.N12616

namespace BstLean.Part269.N12617
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12617 : scalarRow12617.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12617, BstLean.Part268.grid12617, BstLean.Part263.worldGrid]

theorem supplies12617 (j : Fin 43) : Supply 12617 (parameters j)
    (cellLower scalarRow12617.grid (sourceIndex j))
    (cellUpper scalarRow12617.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12617.grid grid_top_bounds12617 j

theorem radii12617 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12617.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12617 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12617 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12617.grid grid_top_bounds12617 j hθ

noncomputable def covarianceInputs12617 :
    BstLean.Part263.CovarianceInputs 12617 scalarRow12617.grid parameters (caps repair12617) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12617 grid_top_bounds12617 repair12617

noncomputable def covarianceEvent12617 : Set (AgFam 12617) :=
  BstLean.Part263.covarianceEvent 12617 scalarRow12617.grid parameters

theorem covarianceEvent12617_measurable : MeasurableSet covarianceEvent12617 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12617_payment :
    (retDist (paperDesignP 12617).toCentres).real
      (agentEv (paperDesignP 12617) covarianceEvent12617)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12617

theorem localCov12617 : BstLean.Part259.LocalCovarianceOn covarianceEvent12617
    (BstLean.Part263.cell scalarRow12617.grid) (caps repair12617) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12617

theorem covarianceGood12617_payment :
    (retDist (paperDesignP 12617).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12617)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12617_payment



end BstLean.Part269.N12617

namespace BstLean.Part269.N12617
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12617}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12617.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12617) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12617).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12617 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12617) (by norm_num) BstLean.Part268.WorldRow12617.worldPackage rfl
    BstLean.Part268.WorldRow12617.product_lower (BstLean.Part268.WorldRow12617.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12617} (hw : c ∈ Hof BstLean.Part268.WorldRow12617.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12617) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12617) (by norm_num) BstLean.Part268.WorldRow12617.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12617} (hw : c ∈ Hof BstLean.Part268.WorldRow12617.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12617) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12617).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12617) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12617_eq : scalarRow12617.targetFrame = BstLean.Part268.agent12617.frame := by
  norm_num [scalarRow12617,BstLean.Part268.agent12617]

noncomputable def frameData12617 : BstLean.Part264b.FrameData 12617 :=
  BstLean.Part269.frameData_from_numerics (n := 12617) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12617.worldPackage rfl BstLean.Part268.WorldRow12617.product_lower (BstLean.Part268.WorldRow12617.producthi.2.trans (by norm_num))
    scalarRow12617 repair12617 covarianceInputs12617 (fun i hi => sourceNumerics12617 hi)
    BstLean.Part268.agent12617.frame targetFrame12617_eq


end BstLean.Part269.N12617

namespace BstLean.Part269.N12618
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12618 : scalarRow12618.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12618, BstLean.Part268.grid12618, BstLean.Part263.worldGrid]

theorem supplies12618 (j : Fin 43) : Supply 12618 (parameters j)
    (cellLower scalarRow12618.grid (sourceIndex j))
    (cellUpper scalarRow12618.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12618.grid grid_top_bounds12618 j

theorem radii12618 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12618.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12618 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12618 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12618.grid grid_top_bounds12618 j hθ

noncomputable def covarianceInputs12618 :
    BstLean.Part263.CovarianceInputs 12618 scalarRow12618.grid parameters (caps repair12618) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12618 grid_top_bounds12618 repair12618

noncomputable def covarianceEvent12618 : Set (AgFam 12618) :=
  BstLean.Part263.covarianceEvent 12618 scalarRow12618.grid parameters

theorem covarianceEvent12618_measurable : MeasurableSet covarianceEvent12618 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12618_payment :
    (retDist (paperDesignP 12618).toCentres).real
      (agentEv (paperDesignP 12618) covarianceEvent12618)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12618

theorem localCov12618 : BstLean.Part259.LocalCovarianceOn covarianceEvent12618
    (BstLean.Part263.cell scalarRow12618.grid) (caps repair12618) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12618

theorem covarianceGood12618_payment :
    (retDist (paperDesignP 12618).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12618)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12618_payment



end BstLean.Part269.N12618

namespace BstLean.Part269.N12618
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12618}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12618.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12618) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12618).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12618 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12618) (by norm_num) BstLean.Part268.WorldRow12618.worldPackage rfl
    BstLean.Part268.WorldRow12618.product_lower (BstLean.Part268.WorldRow12618.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12618} (hw : c ∈ Hof BstLean.Part268.WorldRow12618.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12618) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12618) (by norm_num) BstLean.Part268.WorldRow12618.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12618} (hw : c ∈ Hof BstLean.Part268.WorldRow12618.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12618) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12618).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12618) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12618_eq : scalarRow12618.targetFrame = BstLean.Part268.agent12618.frame := by
  norm_num [scalarRow12618,BstLean.Part268.agent12618]

noncomputable def frameData12618 : BstLean.Part264b.FrameData 12618 :=
  BstLean.Part269.frameData_from_numerics (n := 12618) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12618.worldPackage rfl BstLean.Part268.WorldRow12618.product_lower (BstLean.Part268.WorldRow12618.producthi.2.trans (by norm_num))
    scalarRow12618 repair12618 covarianceInputs12618 (fun i hi => sourceNumerics12618 hi)
    BstLean.Part268.agent12618.frame targetFrame12618_eq


end BstLean.Part269.N12618

namespace BstLean.Part269.N12619
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12619 : scalarRow12619.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12619, BstLean.Part268.grid12619, BstLean.Part263.worldGrid]

theorem supplies12619 (j : Fin 43) : Supply 12619 (parameters j)
    (cellLower scalarRow12619.grid (sourceIndex j))
    (cellUpper scalarRow12619.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12619.grid grid_top_bounds12619 j

theorem radii12619 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12619.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12619 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12619 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12619.grid grid_top_bounds12619 j hθ

noncomputable def covarianceInputs12619 :
    BstLean.Part263.CovarianceInputs 12619 scalarRow12619.grid parameters (caps repair12619) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12619 grid_top_bounds12619 repair12619

noncomputable def covarianceEvent12619 : Set (AgFam 12619) :=
  BstLean.Part263.covarianceEvent 12619 scalarRow12619.grid parameters

theorem covarianceEvent12619_measurable : MeasurableSet covarianceEvent12619 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12619_payment :
    (retDist (paperDesignP 12619).toCentres).real
      (agentEv (paperDesignP 12619) covarianceEvent12619)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12619

theorem localCov12619 : BstLean.Part259.LocalCovarianceOn covarianceEvent12619
    (BstLean.Part263.cell scalarRow12619.grid) (caps repair12619) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12619

theorem covarianceGood12619_payment :
    (retDist (paperDesignP 12619).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12619)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12619_payment



end BstLean.Part269.N12619

namespace BstLean.Part269.N12619
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12619}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12619.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12619) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12619).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12619 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12619) (by norm_num) BstLean.Part268.WorldRow12619.worldPackage rfl
    BstLean.Part268.WorldRow12619.product_lower (BstLean.Part268.WorldRow12619.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12619} (hw : c ∈ Hof BstLean.Part268.WorldRow12619.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12619) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12619) (by norm_num) BstLean.Part268.WorldRow12619.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12619} (hw : c ∈ Hof BstLean.Part268.WorldRow12619.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12619) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12619).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12619) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12619_eq : scalarRow12619.targetFrame = BstLean.Part268.agent12619.frame := by
  norm_num [scalarRow12619,BstLean.Part268.agent12619]

noncomputable def frameData12619 : BstLean.Part264b.FrameData 12619 :=
  BstLean.Part269.frameData_from_numerics (n := 12619) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12619.worldPackage rfl BstLean.Part268.WorldRow12619.product_lower (BstLean.Part268.WorldRow12619.producthi.2.trans (by norm_num))
    scalarRow12619 repair12619 covarianceInputs12619 (fun i hi => sourceNumerics12619 hi)
    BstLean.Part268.agent12619.frame targetFrame12619_eq


end BstLean.Part269.N12619
