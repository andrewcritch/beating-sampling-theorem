import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World16Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs16
import BstLean.Part269Rows16
import BstLean.Part269Sources16
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12765
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12765 : scalarRow12765.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12765, BstLean.Part268.grid12765, BstLean.Part263.worldGrid]

theorem supplies12765 (j : Fin 43) : Supply 12765 (parameters j)
    (cellLower scalarRow12765.grid (sourceIndex j))
    (cellUpper scalarRow12765.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12765.grid grid_top_bounds12765 j

theorem radii12765 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12765.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12765 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12765 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12765.grid grid_top_bounds12765 j hθ

noncomputable def covarianceInputs12765 :
    BstLean.Part263.CovarianceInputs 12765 scalarRow12765.grid parameters (caps repair12765) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12765 grid_top_bounds12765 repair12765

noncomputable def covarianceEvent12765 : Set (AgFam 12765) :=
  BstLean.Part263.covarianceEvent 12765 scalarRow12765.grid parameters

theorem covarianceEvent12765_measurable : MeasurableSet covarianceEvent12765 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12765_payment :
    (retDist (paperDesignP 12765).toCentres).real
      (agentEv (paperDesignP 12765) covarianceEvent12765)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12765

theorem localCov12765 : BstLean.Part259.LocalCovarianceOn covarianceEvent12765
    (BstLean.Part263.cell scalarRow12765.grid) (caps repair12765) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12765

theorem covarianceGood12765_payment :
    (retDist (paperDesignP 12765).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12765)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12765_payment



end BstLean.Part269.N12765

namespace BstLean.Part269.N12765
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12765}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12765.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12765) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12765).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12765 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12765) (by norm_num) BstLean.Part268.WorldRow12765.worldPackage rfl
    BstLean.Part268.WorldRow12765.product_lower (BstLean.Part268.WorldRow12765.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12765} (hw : c ∈ Hof BstLean.Part268.WorldRow12765.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12765) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12765) (by norm_num) BstLean.Part268.WorldRow12765.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12765} (hw : c ∈ Hof BstLean.Part268.WorldRow12765.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12765) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12765).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12765) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12765_eq : scalarRow12765.targetFrame = BstLean.Part268.agent12765.frame := by
  norm_num [scalarRow12765,BstLean.Part268.agent12765]

noncomputable def frameData12765 : BstLean.Part264b.FrameData 12765 :=
  BstLean.Part269.frameData_from_numerics (n := 12765) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12765.worldPackage rfl BstLean.Part268.WorldRow12765.product_lower (BstLean.Part268.WorldRow12765.producthi.2.trans (by norm_num))
    scalarRow12765 repair12765 covarianceInputs12765 (fun i hi => sourceNumerics12765 hi)
    BstLean.Part268.agent12765.frame targetFrame12765_eq


end BstLean.Part269.N12765

namespace BstLean.Part269.N12766
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12766 : scalarRow12766.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12766, BstLean.Part268.grid12766, BstLean.Part263.worldGrid]

theorem supplies12766 (j : Fin 43) : Supply 12766 (parameters j)
    (cellLower scalarRow12766.grid (sourceIndex j))
    (cellUpper scalarRow12766.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12766.grid grid_top_bounds12766 j

theorem radii12766 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12766.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12766 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12766 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12766.grid grid_top_bounds12766 j hθ

noncomputable def covarianceInputs12766 :
    BstLean.Part263.CovarianceInputs 12766 scalarRow12766.grid parameters (caps repair12766) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12766 grid_top_bounds12766 repair12766

noncomputable def covarianceEvent12766 : Set (AgFam 12766) :=
  BstLean.Part263.covarianceEvent 12766 scalarRow12766.grid parameters

theorem covarianceEvent12766_measurable : MeasurableSet covarianceEvent12766 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12766_payment :
    (retDist (paperDesignP 12766).toCentres).real
      (agentEv (paperDesignP 12766) covarianceEvent12766)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12766

theorem localCov12766 : BstLean.Part259.LocalCovarianceOn covarianceEvent12766
    (BstLean.Part263.cell scalarRow12766.grid) (caps repair12766) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12766

theorem covarianceGood12766_payment :
    (retDist (paperDesignP 12766).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12766)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12766_payment



end BstLean.Part269.N12766

namespace BstLean.Part269.N12766
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12766}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12766.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12766) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12766).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12766 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12766) (by norm_num) BstLean.Part268.WorldRow12766.worldPackage rfl
    BstLean.Part268.WorldRow12766.product_lower (BstLean.Part268.WorldRow12766.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12766} (hw : c ∈ Hof BstLean.Part268.WorldRow12766.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12766) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12766) (by norm_num) BstLean.Part268.WorldRow12766.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12766} (hw : c ∈ Hof BstLean.Part268.WorldRow12766.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12766) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12766).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12766) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12766_eq : scalarRow12766.targetFrame = BstLean.Part268.agent12766.frame := by
  norm_num [scalarRow12766,BstLean.Part268.agent12766]

noncomputable def frameData12766 : BstLean.Part264b.FrameData 12766 :=
  BstLean.Part269.frameData_from_numerics (n := 12766) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12766.worldPackage rfl BstLean.Part268.WorldRow12766.product_lower (BstLean.Part268.WorldRow12766.producthi.2.trans (by norm_num))
    scalarRow12766 repair12766 covarianceInputs12766 (fun i hi => sourceNumerics12766 hi)
    BstLean.Part268.agent12766.frame targetFrame12766_eq


end BstLean.Part269.N12766

namespace BstLean.Part269.N12767
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12767 : scalarRow12767.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12767, BstLean.Part268.grid12767, BstLean.Part263.worldGrid]

theorem supplies12767 (j : Fin 43) : Supply 12767 (parameters j)
    (cellLower scalarRow12767.grid (sourceIndex j))
    (cellUpper scalarRow12767.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12767.grid grid_top_bounds12767 j

theorem radii12767 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12767.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12767 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12767 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12767.grid grid_top_bounds12767 j hθ

noncomputable def covarianceInputs12767 :
    BstLean.Part263.CovarianceInputs 12767 scalarRow12767.grid parameters (caps repair12767) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12767 grid_top_bounds12767 repair12767

noncomputable def covarianceEvent12767 : Set (AgFam 12767) :=
  BstLean.Part263.covarianceEvent 12767 scalarRow12767.grid parameters

theorem covarianceEvent12767_measurable : MeasurableSet covarianceEvent12767 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12767_payment :
    (retDist (paperDesignP 12767).toCentres).real
      (agentEv (paperDesignP 12767) covarianceEvent12767)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12767

theorem localCov12767 : BstLean.Part259.LocalCovarianceOn covarianceEvent12767
    (BstLean.Part263.cell scalarRow12767.grid) (caps repair12767) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12767

theorem covarianceGood12767_payment :
    (retDist (paperDesignP 12767).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12767)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12767_payment



end BstLean.Part269.N12767

namespace BstLean.Part269.N12767
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12767}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12767.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12767) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12767).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12767 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12767) (by norm_num) BstLean.Part268.WorldRow12767.worldPackage rfl
    BstLean.Part268.WorldRow12767.product_lower (BstLean.Part268.WorldRow12767.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12767} (hw : c ∈ Hof BstLean.Part268.WorldRow12767.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12767) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12767) (by norm_num) BstLean.Part268.WorldRow12767.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12767} (hw : c ∈ Hof BstLean.Part268.WorldRow12767.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12767) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12767).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12767) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12767_eq : scalarRow12767.targetFrame = BstLean.Part268.agent12767.frame := by
  norm_num [scalarRow12767,BstLean.Part268.agent12767]

noncomputable def frameData12767 : BstLean.Part264b.FrameData 12767 :=
  BstLean.Part269.frameData_from_numerics (n := 12767) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12767.worldPackage rfl BstLean.Part268.WorldRow12767.product_lower (BstLean.Part268.WorldRow12767.producthi.2.trans (by norm_num))
    scalarRow12767 repair12767 covarianceInputs12767 (fun i hi => sourceNumerics12767 hi)
    BstLean.Part268.agent12767.frame targetFrame12767_eq


end BstLean.Part269.N12767

namespace BstLean.Part269.N12768
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12768 : scalarRow12768.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12768, BstLean.Part268.grid12768, BstLean.Part263.worldGrid]

theorem supplies12768 (j : Fin 43) : Supply 12768 (parameters j)
    (cellLower scalarRow12768.grid (sourceIndex j))
    (cellUpper scalarRow12768.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12768.grid grid_top_bounds12768 j

theorem radii12768 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12768.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12768 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12768 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12768.grid grid_top_bounds12768 j hθ

noncomputable def covarianceInputs12768 :
    BstLean.Part263.CovarianceInputs 12768 scalarRow12768.grid parameters (caps repair12768) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12768 grid_top_bounds12768 repair12768

noncomputable def covarianceEvent12768 : Set (AgFam 12768) :=
  BstLean.Part263.covarianceEvent 12768 scalarRow12768.grid parameters

theorem covarianceEvent12768_measurable : MeasurableSet covarianceEvent12768 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12768_payment :
    (retDist (paperDesignP 12768).toCentres).real
      (agentEv (paperDesignP 12768) covarianceEvent12768)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12768

theorem localCov12768 : BstLean.Part259.LocalCovarianceOn covarianceEvent12768
    (BstLean.Part263.cell scalarRow12768.grid) (caps repair12768) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12768

theorem covarianceGood12768_payment :
    (retDist (paperDesignP 12768).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12768)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12768_payment



end BstLean.Part269.N12768

namespace BstLean.Part269.N12768
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12768}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12768.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12768) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12768).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12768 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12768) (by norm_num) BstLean.Part268.WorldRow12768.worldPackage rfl
    BstLean.Part268.WorldRow12768.product_lower (BstLean.Part268.WorldRow12768.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12768} (hw : c ∈ Hof BstLean.Part268.WorldRow12768.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12768) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12768) (by norm_num) BstLean.Part268.WorldRow12768.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12768} (hw : c ∈ Hof BstLean.Part268.WorldRow12768.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12768) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12768).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12768) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12768_eq : scalarRow12768.targetFrame = BstLean.Part268.agent12768.frame := by
  norm_num [scalarRow12768,BstLean.Part268.agent12768]

noncomputable def frameData12768 : BstLean.Part264b.FrameData 12768 :=
  BstLean.Part269.frameData_from_numerics (n := 12768) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12768.worldPackage rfl BstLean.Part268.WorldRow12768.product_lower (BstLean.Part268.WorldRow12768.producthi.2.trans (by norm_num))
    scalarRow12768 repair12768 covarianceInputs12768 (fun i hi => sourceNumerics12768 hi)
    BstLean.Part268.agent12768.frame targetFrame12768_eq


end BstLean.Part269.N12768

namespace BstLean.Part269.N12769
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12769 : scalarRow12769.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12769, BstLean.Part268.grid12769, BstLean.Part263.worldGrid]

theorem supplies12769 (j : Fin 43) : Supply 12769 (parameters j)
    (cellLower scalarRow12769.grid (sourceIndex j))
    (cellUpper scalarRow12769.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12769.grid grid_top_bounds12769 j

theorem radii12769 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12769.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12769 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12769 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12769.grid grid_top_bounds12769 j hθ

noncomputable def covarianceInputs12769 :
    BstLean.Part263.CovarianceInputs 12769 scalarRow12769.grid parameters (caps repair12769) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12769 grid_top_bounds12769 repair12769

noncomputable def covarianceEvent12769 : Set (AgFam 12769) :=
  BstLean.Part263.covarianceEvent 12769 scalarRow12769.grid parameters

theorem covarianceEvent12769_measurable : MeasurableSet covarianceEvent12769 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12769_payment :
    (retDist (paperDesignP 12769).toCentres).real
      (agentEv (paperDesignP 12769) covarianceEvent12769)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12769

theorem localCov12769 : BstLean.Part259.LocalCovarianceOn covarianceEvent12769
    (BstLean.Part263.cell scalarRow12769.grid) (caps repair12769) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12769

theorem covarianceGood12769_payment :
    (retDist (paperDesignP 12769).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12769)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12769_payment



end BstLean.Part269.N12769

namespace BstLean.Part269.N12769
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12769}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12769.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12769) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12769).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12769 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12769) (by norm_num) BstLean.Part268.WorldRow12769.worldPackage rfl
    BstLean.Part268.WorldRow12769.product_lower (BstLean.Part268.WorldRow12769.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12769} (hw : c ∈ Hof BstLean.Part268.WorldRow12769.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12769) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12769) (by norm_num) BstLean.Part268.WorldRow12769.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12769} (hw : c ∈ Hof BstLean.Part268.WorldRow12769.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12769) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12769).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12769) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12769_eq : scalarRow12769.targetFrame = BstLean.Part268.agent12769.frame := by
  norm_num [scalarRow12769,BstLean.Part268.agent12769]

noncomputable def frameData12769 : BstLean.Part264b.FrameData 12769 :=
  BstLean.Part269.frameData_from_numerics (n := 12769) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12769.worldPackage rfl BstLean.Part268.WorldRow12769.product_lower (BstLean.Part268.WorldRow12769.producthi.2.trans (by norm_num))
    scalarRow12769 repair12769 covarianceInputs12769 (fun i hi => sourceNumerics12769 hi)
    BstLean.Part268.agent12769.frame targetFrame12769_eq


end BstLean.Part269.N12769
