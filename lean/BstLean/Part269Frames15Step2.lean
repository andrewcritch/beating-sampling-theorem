import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World15Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs15
import BstLean.Part269Rows15
import BstLean.Part269Sources15
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12735
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12735 : scalarRow12735.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12735, BstLean.Part268.grid12735, BstLean.Part263.worldGrid]

theorem supplies12735 (j : Fin 43) : Supply 12735 (parameters j)
    (cellLower scalarRow12735.grid (sourceIndex j))
    (cellUpper scalarRow12735.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12735.grid grid_top_bounds12735 j

theorem radii12735 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12735.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12735 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12735 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12735.grid grid_top_bounds12735 j hθ

noncomputable def covarianceInputs12735 :
    BstLean.Part263.CovarianceInputs 12735 scalarRow12735.grid parameters (caps repair12735) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12735 grid_top_bounds12735 repair12735

noncomputable def covarianceEvent12735 : Set (AgFam 12735) :=
  BstLean.Part263.covarianceEvent 12735 scalarRow12735.grid parameters

theorem covarianceEvent12735_measurable : MeasurableSet covarianceEvent12735 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12735_payment :
    (retDist (paperDesignP 12735).toCentres).real
      (agentEv (paperDesignP 12735) covarianceEvent12735)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12735

theorem localCov12735 : BstLean.Part259.LocalCovarianceOn covarianceEvent12735
    (BstLean.Part263.cell scalarRow12735.grid) (caps repair12735) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12735

theorem covarianceGood12735_payment :
    (retDist (paperDesignP 12735).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12735)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12735_payment



end BstLean.Part269.N12735

namespace BstLean.Part269.N12735
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12735}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12735.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12735) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12735).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12735 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12735) (by norm_num) BstLean.Part268.WorldRow12735.worldPackage rfl
    BstLean.Part268.WorldRow12735.product_lower (BstLean.Part268.WorldRow12735.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12735} (hw : c ∈ Hof BstLean.Part268.WorldRow12735.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12735) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12735) (by norm_num) BstLean.Part268.WorldRow12735.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12735} (hw : c ∈ Hof BstLean.Part268.WorldRow12735.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12735) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12735).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12735) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12735_eq : scalarRow12735.targetFrame = BstLean.Part268.agent12735.frame := by
  norm_num [scalarRow12735,BstLean.Part268.agent12735]

noncomputable def frameData12735 : BstLean.Part264b.FrameData 12735 :=
  BstLean.Part269.frameData_from_numerics (n := 12735) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12735.worldPackage rfl BstLean.Part268.WorldRow12735.product_lower (BstLean.Part268.WorldRow12735.producthi.2.trans (by norm_num))
    scalarRow12735 repair12735 covarianceInputs12735 (fun i hi => sourceNumerics12735 hi)
    BstLean.Part268.agent12735.frame targetFrame12735_eq


end BstLean.Part269.N12735

namespace BstLean.Part269.N12736
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12736 : scalarRow12736.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12736, BstLean.Part268.grid12736, BstLean.Part263.worldGrid]

theorem supplies12736 (j : Fin 43) : Supply 12736 (parameters j)
    (cellLower scalarRow12736.grid (sourceIndex j))
    (cellUpper scalarRow12736.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12736.grid grid_top_bounds12736 j

theorem radii12736 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12736.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12736 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12736 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12736.grid grid_top_bounds12736 j hθ

noncomputable def covarianceInputs12736 :
    BstLean.Part263.CovarianceInputs 12736 scalarRow12736.grid parameters (caps repair12736) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12736 grid_top_bounds12736 repair12736

noncomputable def covarianceEvent12736 : Set (AgFam 12736) :=
  BstLean.Part263.covarianceEvent 12736 scalarRow12736.grid parameters

theorem covarianceEvent12736_measurable : MeasurableSet covarianceEvent12736 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12736_payment :
    (retDist (paperDesignP 12736).toCentres).real
      (agentEv (paperDesignP 12736) covarianceEvent12736)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12736

theorem localCov12736 : BstLean.Part259.LocalCovarianceOn covarianceEvent12736
    (BstLean.Part263.cell scalarRow12736.grid) (caps repair12736) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12736

theorem covarianceGood12736_payment :
    (retDist (paperDesignP 12736).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12736)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12736_payment



end BstLean.Part269.N12736

namespace BstLean.Part269.N12736
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12736}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12736.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12736) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12736).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12736 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12736) (by norm_num) BstLean.Part268.WorldRow12736.worldPackage rfl
    BstLean.Part268.WorldRow12736.product_lower (BstLean.Part268.WorldRow12736.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12736} (hw : c ∈ Hof BstLean.Part268.WorldRow12736.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12736) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12736) (by norm_num) BstLean.Part268.WorldRow12736.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12736} (hw : c ∈ Hof BstLean.Part268.WorldRow12736.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12736) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12736).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12736) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12736_eq : scalarRow12736.targetFrame = BstLean.Part268.agent12736.frame := by
  norm_num [scalarRow12736,BstLean.Part268.agent12736]

noncomputable def frameData12736 : BstLean.Part264b.FrameData 12736 :=
  BstLean.Part269.frameData_from_numerics (n := 12736) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12736.worldPackage rfl BstLean.Part268.WorldRow12736.product_lower (BstLean.Part268.WorldRow12736.producthi.2.trans (by norm_num))
    scalarRow12736 repair12736 covarianceInputs12736 (fun i hi => sourceNumerics12736 hi)
    BstLean.Part268.agent12736.frame targetFrame12736_eq


end BstLean.Part269.N12736

namespace BstLean.Part269.N12737
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12737 : scalarRow12737.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12737, BstLean.Part268.grid12737, BstLean.Part263.worldGrid]

theorem supplies12737 (j : Fin 43) : Supply 12737 (parameters j)
    (cellLower scalarRow12737.grid (sourceIndex j))
    (cellUpper scalarRow12737.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12737.grid grid_top_bounds12737 j

theorem radii12737 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12737.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12737 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12737 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12737.grid grid_top_bounds12737 j hθ

noncomputable def covarianceInputs12737 :
    BstLean.Part263.CovarianceInputs 12737 scalarRow12737.grid parameters (caps repair12737) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12737 grid_top_bounds12737 repair12737

noncomputable def covarianceEvent12737 : Set (AgFam 12737) :=
  BstLean.Part263.covarianceEvent 12737 scalarRow12737.grid parameters

theorem covarianceEvent12737_measurable : MeasurableSet covarianceEvent12737 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12737_payment :
    (retDist (paperDesignP 12737).toCentres).real
      (agentEv (paperDesignP 12737) covarianceEvent12737)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12737

theorem localCov12737 : BstLean.Part259.LocalCovarianceOn covarianceEvent12737
    (BstLean.Part263.cell scalarRow12737.grid) (caps repair12737) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12737

theorem covarianceGood12737_payment :
    (retDist (paperDesignP 12737).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12737)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12737_payment



end BstLean.Part269.N12737

namespace BstLean.Part269.N12737
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12737}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12737.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12737) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12737).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12737 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12737) (by norm_num) BstLean.Part268.WorldRow12737.worldPackage rfl
    BstLean.Part268.WorldRow12737.product_lower (BstLean.Part268.WorldRow12737.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12737} (hw : c ∈ Hof BstLean.Part268.WorldRow12737.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12737) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12737) (by norm_num) BstLean.Part268.WorldRow12737.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12737} (hw : c ∈ Hof BstLean.Part268.WorldRow12737.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12737) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12737).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12737) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12737_eq : scalarRow12737.targetFrame = BstLean.Part268.agent12737.frame := by
  norm_num [scalarRow12737,BstLean.Part268.agent12737]

noncomputable def frameData12737 : BstLean.Part264b.FrameData 12737 :=
  BstLean.Part269.frameData_from_numerics (n := 12737) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12737.worldPackage rfl BstLean.Part268.WorldRow12737.product_lower (BstLean.Part268.WorldRow12737.producthi.2.trans (by norm_num))
    scalarRow12737 repair12737 covarianceInputs12737 (fun i hi => sourceNumerics12737 hi)
    BstLean.Part268.agent12737.frame targetFrame12737_eq


end BstLean.Part269.N12737

namespace BstLean.Part269.N12738
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12738 : scalarRow12738.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12738, BstLean.Part268.grid12738, BstLean.Part263.worldGrid]

theorem supplies12738 (j : Fin 43) : Supply 12738 (parameters j)
    (cellLower scalarRow12738.grid (sourceIndex j))
    (cellUpper scalarRow12738.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12738.grid grid_top_bounds12738 j

theorem radii12738 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12738.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12738 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12738 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12738.grid grid_top_bounds12738 j hθ

noncomputable def covarianceInputs12738 :
    BstLean.Part263.CovarianceInputs 12738 scalarRow12738.grid parameters (caps repair12738) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12738 grid_top_bounds12738 repair12738

noncomputable def covarianceEvent12738 : Set (AgFam 12738) :=
  BstLean.Part263.covarianceEvent 12738 scalarRow12738.grid parameters

theorem covarianceEvent12738_measurable : MeasurableSet covarianceEvent12738 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12738_payment :
    (retDist (paperDesignP 12738).toCentres).real
      (agentEv (paperDesignP 12738) covarianceEvent12738)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12738

theorem localCov12738 : BstLean.Part259.LocalCovarianceOn covarianceEvent12738
    (BstLean.Part263.cell scalarRow12738.grid) (caps repair12738) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12738

theorem covarianceGood12738_payment :
    (retDist (paperDesignP 12738).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12738)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12738_payment



end BstLean.Part269.N12738

namespace BstLean.Part269.N12738
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12738}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12738.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12738) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12738).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12738 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12738) (by norm_num) BstLean.Part268.WorldRow12738.worldPackage rfl
    BstLean.Part268.WorldRow12738.product_lower (BstLean.Part268.WorldRow12738.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12738} (hw : c ∈ Hof BstLean.Part268.WorldRow12738.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12738) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12738) (by norm_num) BstLean.Part268.WorldRow12738.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12738} (hw : c ∈ Hof BstLean.Part268.WorldRow12738.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12738) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12738).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12738) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12738_eq : scalarRow12738.targetFrame = BstLean.Part268.agent12738.frame := by
  norm_num [scalarRow12738,BstLean.Part268.agent12738]

noncomputable def frameData12738 : BstLean.Part264b.FrameData 12738 :=
  BstLean.Part269.frameData_from_numerics (n := 12738) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12738.worldPackage rfl BstLean.Part268.WorldRow12738.product_lower (BstLean.Part268.WorldRow12738.producthi.2.trans (by norm_num))
    scalarRow12738 repair12738 covarianceInputs12738 (fun i hi => sourceNumerics12738 hi)
    BstLean.Part268.agent12738.frame targetFrame12738_eq


end BstLean.Part269.N12738

namespace BstLean.Part269.N12739
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12739 : scalarRow12739.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12739, BstLean.Part268.grid12739, BstLean.Part263.worldGrid]

theorem supplies12739 (j : Fin 43) : Supply 12739 (parameters j)
    (cellLower scalarRow12739.grid (sourceIndex j))
    (cellUpper scalarRow12739.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12739.grid grid_top_bounds12739 j

theorem radii12739 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12739.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12739 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12739 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12739.grid grid_top_bounds12739 j hθ

noncomputable def covarianceInputs12739 :
    BstLean.Part263.CovarianceInputs 12739 scalarRow12739.grid parameters (caps repair12739) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12739 grid_top_bounds12739 repair12739

noncomputable def covarianceEvent12739 : Set (AgFam 12739) :=
  BstLean.Part263.covarianceEvent 12739 scalarRow12739.grid parameters

theorem covarianceEvent12739_measurable : MeasurableSet covarianceEvent12739 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12739_payment :
    (retDist (paperDesignP 12739).toCentres).real
      (agentEv (paperDesignP 12739) covarianceEvent12739)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12739

theorem localCov12739 : BstLean.Part259.LocalCovarianceOn covarianceEvent12739
    (BstLean.Part263.cell scalarRow12739.grid) (caps repair12739) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12739

theorem covarianceGood12739_payment :
    (retDist (paperDesignP 12739).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12739)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12739_payment



end BstLean.Part269.N12739

namespace BstLean.Part269.N12739
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12739}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12739.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12739) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12739).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12739 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12739) (by norm_num) BstLean.Part268.WorldRow12739.worldPackage rfl
    BstLean.Part268.WorldRow12739.product_lower (BstLean.Part268.WorldRow12739.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12739} (hw : c ∈ Hof BstLean.Part268.WorldRow12739.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12739) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12739) (by norm_num) BstLean.Part268.WorldRow12739.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12739} (hw : c ∈ Hof BstLean.Part268.WorldRow12739.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12739) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12739).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12739) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12739_eq : scalarRow12739.targetFrame = BstLean.Part268.agent12739.frame := by
  norm_num [scalarRow12739,BstLean.Part268.agent12739]

noncomputable def frameData12739 : BstLean.Part264b.FrameData 12739 :=
  BstLean.Part269.frameData_from_numerics (n := 12739) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12739.worldPackage rfl BstLean.Part268.WorldRow12739.product_lower (BstLean.Part268.WorldRow12739.producthi.2.trans (by norm_num))
    scalarRow12739 repair12739 covarianceInputs12739 (fun i hi => sourceNumerics12739 hi)
    BstLean.Part268.agent12739.frame targetFrame12739_eq


end BstLean.Part269.N12739
