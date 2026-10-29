import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World17Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs17
import BstLean.Part269Rows17
import BstLean.Part269Sources17
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12780
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12780 : scalarRow12780.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12780, BstLean.Part268.grid12780, BstLean.Part263.worldGrid]

theorem supplies12780 (j : Fin 43) : Supply 12780 (parameters j)
    (cellLower scalarRow12780.grid (sourceIndex j))
    (cellUpper scalarRow12780.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12780.grid grid_top_bounds12780 j

theorem radii12780 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12780.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12780 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12780 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12780.grid grid_top_bounds12780 j hθ

noncomputable def covarianceInputs12780 :
    BstLean.Part263.CovarianceInputs 12780 scalarRow12780.grid parameters (caps repair12780) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12780 grid_top_bounds12780 repair12780

noncomputable def covarianceEvent12780 : Set (AgFam 12780) :=
  BstLean.Part263.covarianceEvent 12780 scalarRow12780.grid parameters

theorem covarianceEvent12780_measurable : MeasurableSet covarianceEvent12780 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12780_payment :
    (retDist (paperDesignP 12780).toCentres).real
      (agentEv (paperDesignP 12780) covarianceEvent12780)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12780

theorem localCov12780 : BstLean.Part259.LocalCovarianceOn covarianceEvent12780
    (BstLean.Part263.cell scalarRow12780.grid) (caps repair12780) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12780

theorem covarianceGood12780_payment :
    (retDist (paperDesignP 12780).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12780)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12780_payment



end BstLean.Part269.N12780

namespace BstLean.Part269.N12780
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12780}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12780.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12780) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12780).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12780 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12780) (by norm_num) BstLean.Part268.WorldRow12780.worldPackage rfl
    BstLean.Part268.WorldRow12780.product_lower (BstLean.Part268.WorldRow12780.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12780} (hw : c ∈ Hof BstLean.Part268.WorldRow12780.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12780) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12780) (by norm_num) BstLean.Part268.WorldRow12780.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12780} (hw : c ∈ Hof BstLean.Part268.WorldRow12780.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12780) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12780).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12780) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12780_eq : scalarRow12780.targetFrame = BstLean.Part268.agent12780.frame := by
  norm_num [scalarRow12780,BstLean.Part268.agent12780]

noncomputable def frameData12780 : BstLean.Part264b.FrameData 12780 :=
  BstLean.Part269.frameData_from_numerics (n := 12780) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12780.worldPackage rfl BstLean.Part268.WorldRow12780.product_lower (BstLean.Part268.WorldRow12780.producthi.2.trans (by norm_num))
    scalarRow12780 repair12780 covarianceInputs12780 (fun i hi => sourceNumerics12780 hi)
    BstLean.Part268.agent12780.frame targetFrame12780_eq


end BstLean.Part269.N12780

namespace BstLean.Part269.N12781
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12781 : scalarRow12781.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12781, BstLean.Part268.grid12781, BstLean.Part263.worldGrid]

theorem supplies12781 (j : Fin 43) : Supply 12781 (parameters j)
    (cellLower scalarRow12781.grid (sourceIndex j))
    (cellUpper scalarRow12781.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12781.grid grid_top_bounds12781 j

theorem radii12781 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12781.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12781 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12781 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12781.grid grid_top_bounds12781 j hθ

noncomputable def covarianceInputs12781 :
    BstLean.Part263.CovarianceInputs 12781 scalarRow12781.grid parameters (caps repair12781) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12781 grid_top_bounds12781 repair12781

noncomputable def covarianceEvent12781 : Set (AgFam 12781) :=
  BstLean.Part263.covarianceEvent 12781 scalarRow12781.grid parameters

theorem covarianceEvent12781_measurable : MeasurableSet covarianceEvent12781 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12781_payment :
    (retDist (paperDesignP 12781).toCentres).real
      (agentEv (paperDesignP 12781) covarianceEvent12781)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12781

theorem localCov12781 : BstLean.Part259.LocalCovarianceOn covarianceEvent12781
    (BstLean.Part263.cell scalarRow12781.grid) (caps repair12781) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12781

theorem covarianceGood12781_payment :
    (retDist (paperDesignP 12781).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12781)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12781_payment



end BstLean.Part269.N12781

namespace BstLean.Part269.N12781
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12781}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12781.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12781) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12781).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12781 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12781) (by norm_num) BstLean.Part268.WorldRow12781.worldPackage rfl
    BstLean.Part268.WorldRow12781.product_lower (BstLean.Part268.WorldRow12781.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12781} (hw : c ∈ Hof BstLean.Part268.WorldRow12781.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12781) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12781) (by norm_num) BstLean.Part268.WorldRow12781.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12781} (hw : c ∈ Hof BstLean.Part268.WorldRow12781.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12781) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12781).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12781) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12781_eq : scalarRow12781.targetFrame = BstLean.Part268.agent12781.frame := by
  norm_num [scalarRow12781,BstLean.Part268.agent12781]

noncomputable def frameData12781 : BstLean.Part264b.FrameData 12781 :=
  BstLean.Part269.frameData_from_numerics (n := 12781) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12781.worldPackage rfl BstLean.Part268.WorldRow12781.product_lower (BstLean.Part268.WorldRow12781.producthi.2.trans (by norm_num))
    scalarRow12781 repair12781 covarianceInputs12781 (fun i hi => sourceNumerics12781 hi)
    BstLean.Part268.agent12781.frame targetFrame12781_eq


end BstLean.Part269.N12781

namespace BstLean.Part269.N12782
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12782 : scalarRow12782.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12782, BstLean.Part268.grid12782, BstLean.Part263.worldGrid]

theorem supplies12782 (j : Fin 43) : Supply 12782 (parameters j)
    (cellLower scalarRow12782.grid (sourceIndex j))
    (cellUpper scalarRow12782.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12782.grid grid_top_bounds12782 j

theorem radii12782 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12782.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12782 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12782 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12782.grid grid_top_bounds12782 j hθ

noncomputable def covarianceInputs12782 :
    BstLean.Part263.CovarianceInputs 12782 scalarRow12782.grid parameters (caps repair12782) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12782 grid_top_bounds12782 repair12782

noncomputable def covarianceEvent12782 : Set (AgFam 12782) :=
  BstLean.Part263.covarianceEvent 12782 scalarRow12782.grid parameters

theorem covarianceEvent12782_measurable : MeasurableSet covarianceEvent12782 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12782_payment :
    (retDist (paperDesignP 12782).toCentres).real
      (agentEv (paperDesignP 12782) covarianceEvent12782)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12782

theorem localCov12782 : BstLean.Part259.LocalCovarianceOn covarianceEvent12782
    (BstLean.Part263.cell scalarRow12782.grid) (caps repair12782) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12782

theorem covarianceGood12782_payment :
    (retDist (paperDesignP 12782).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12782)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12782_payment



end BstLean.Part269.N12782

namespace BstLean.Part269.N12782
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12782}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12782.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12782) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12782).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12782 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12782) (by norm_num) BstLean.Part268.WorldRow12782.worldPackage rfl
    BstLean.Part268.WorldRow12782.product_lower (BstLean.Part268.WorldRow12782.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12782} (hw : c ∈ Hof BstLean.Part268.WorldRow12782.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12782) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12782) (by norm_num) BstLean.Part268.WorldRow12782.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12782} (hw : c ∈ Hof BstLean.Part268.WorldRow12782.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12782) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12782).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12782) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12782_eq : scalarRow12782.targetFrame = BstLean.Part268.agent12782.frame := by
  norm_num [scalarRow12782,BstLean.Part268.agent12782]

noncomputable def frameData12782 : BstLean.Part264b.FrameData 12782 :=
  BstLean.Part269.frameData_from_numerics (n := 12782) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12782.worldPackage rfl BstLean.Part268.WorldRow12782.product_lower (BstLean.Part268.WorldRow12782.producthi.2.trans (by norm_num))
    scalarRow12782 repair12782 covarianceInputs12782 (fun i hi => sourceNumerics12782 hi)
    BstLean.Part268.agent12782.frame targetFrame12782_eq


end BstLean.Part269.N12782

namespace BstLean.Part269.N12783
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12783 : scalarRow12783.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12783, BstLean.Part268.grid12783, BstLean.Part263.worldGrid]

theorem supplies12783 (j : Fin 43) : Supply 12783 (parameters j)
    (cellLower scalarRow12783.grid (sourceIndex j))
    (cellUpper scalarRow12783.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12783.grid grid_top_bounds12783 j

theorem radii12783 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12783.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12783 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12783 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12783.grid grid_top_bounds12783 j hθ

noncomputable def covarianceInputs12783 :
    BstLean.Part263.CovarianceInputs 12783 scalarRow12783.grid parameters (caps repair12783) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12783 grid_top_bounds12783 repair12783

noncomputable def covarianceEvent12783 : Set (AgFam 12783) :=
  BstLean.Part263.covarianceEvent 12783 scalarRow12783.grid parameters

theorem covarianceEvent12783_measurable : MeasurableSet covarianceEvent12783 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12783_payment :
    (retDist (paperDesignP 12783).toCentres).real
      (agentEv (paperDesignP 12783) covarianceEvent12783)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12783

theorem localCov12783 : BstLean.Part259.LocalCovarianceOn covarianceEvent12783
    (BstLean.Part263.cell scalarRow12783.grid) (caps repair12783) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12783

theorem covarianceGood12783_payment :
    (retDist (paperDesignP 12783).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12783)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12783_payment



end BstLean.Part269.N12783

namespace BstLean.Part269.N12783
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12783}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12783.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12783) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12783).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12783 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12783) (by norm_num) BstLean.Part268.WorldRow12783.worldPackage rfl
    BstLean.Part268.WorldRow12783.product_lower (BstLean.Part268.WorldRow12783.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12783} (hw : c ∈ Hof BstLean.Part268.WorldRow12783.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12783) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12783) (by norm_num) BstLean.Part268.WorldRow12783.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12783} (hw : c ∈ Hof BstLean.Part268.WorldRow12783.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12783) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12783).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12783) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12783_eq : scalarRow12783.targetFrame = BstLean.Part268.agent12783.frame := by
  norm_num [scalarRow12783,BstLean.Part268.agent12783]

noncomputable def frameData12783 : BstLean.Part264b.FrameData 12783 :=
  BstLean.Part269.frameData_from_numerics (n := 12783) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12783.worldPackage rfl BstLean.Part268.WorldRow12783.product_lower (BstLean.Part268.WorldRow12783.producthi.2.trans (by norm_num))
    scalarRow12783 repair12783 covarianceInputs12783 (fun i hi => sourceNumerics12783 hi)
    BstLean.Part268.agent12783.frame targetFrame12783_eq


end BstLean.Part269.N12783

namespace BstLean.Part269.N12784
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12784 : scalarRow12784.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12784, BstLean.Part268.grid12784, BstLean.Part263.worldGrid]

theorem supplies12784 (j : Fin 43) : Supply 12784 (parameters j)
    (cellLower scalarRow12784.grid (sourceIndex j))
    (cellUpper scalarRow12784.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12784.grid grid_top_bounds12784 j

theorem radii12784 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12784.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12784 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12784 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12784.grid grid_top_bounds12784 j hθ

noncomputable def covarianceInputs12784 :
    BstLean.Part263.CovarianceInputs 12784 scalarRow12784.grid parameters (caps repair12784) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12784 grid_top_bounds12784 repair12784

noncomputable def covarianceEvent12784 : Set (AgFam 12784) :=
  BstLean.Part263.covarianceEvent 12784 scalarRow12784.grid parameters

theorem covarianceEvent12784_measurable : MeasurableSet covarianceEvent12784 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12784_payment :
    (retDist (paperDesignP 12784).toCentres).real
      (agentEv (paperDesignP 12784) covarianceEvent12784)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12784

theorem localCov12784 : BstLean.Part259.LocalCovarianceOn covarianceEvent12784
    (BstLean.Part263.cell scalarRow12784.grid) (caps repair12784) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12784

theorem covarianceGood12784_payment :
    (retDist (paperDesignP 12784).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12784)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12784_payment



end BstLean.Part269.N12784

namespace BstLean.Part269.N12784
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12784}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12784.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12784) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12784).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12784 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12784) (by norm_num) BstLean.Part268.WorldRow12784.worldPackage rfl
    BstLean.Part268.WorldRow12784.product_lower (BstLean.Part268.WorldRow12784.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12784} (hw : c ∈ Hof BstLean.Part268.WorldRow12784.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12784) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12784) (by norm_num) BstLean.Part268.WorldRow12784.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12784} (hw : c ∈ Hof BstLean.Part268.WorldRow12784.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12784) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12784).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12784) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12784_eq : scalarRow12784.targetFrame = BstLean.Part268.agent12784.frame := by
  norm_num [scalarRow12784,BstLean.Part268.agent12784]

noncomputable def frameData12784 : BstLean.Part264b.FrameData 12784 :=
  BstLean.Part269.frameData_from_numerics (n := 12784) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12784.worldPackage rfl BstLean.Part268.WorldRow12784.product_lower (BstLean.Part268.WorldRow12784.producthi.2.trans (by norm_num))
    scalarRow12784 repair12784 covarianceInputs12784 (fun i hi => sourceNumerics12784 hi)
    BstLean.Part268.agent12784.frame targetFrame12784_eq


end BstLean.Part269.N12784
