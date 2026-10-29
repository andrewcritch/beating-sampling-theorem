import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World3Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs3
import BstLean.Part269Rows3
import BstLean.Part269Sources3
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12440
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12440 : scalarRow12440.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12440, BstLean.Part268.grid12440, BstLean.Part263.worldGrid]

theorem supplies12440 (j : Fin 43) : Supply 12440 (parameters j)
    (cellLower scalarRow12440.grid (sourceIndex j))
    (cellUpper scalarRow12440.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12440.grid grid_top_bounds12440 j

theorem radii12440 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12440.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12440 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12440 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12440.grid grid_top_bounds12440 j hθ

noncomputable def covarianceInputs12440 :
    BstLean.Part263.CovarianceInputs 12440 scalarRow12440.grid parameters (caps repair12440) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12440 grid_top_bounds12440 repair12440

noncomputable def covarianceEvent12440 : Set (AgFam 12440) :=
  BstLean.Part263.covarianceEvent 12440 scalarRow12440.grid parameters

theorem covarianceEvent12440_measurable : MeasurableSet covarianceEvent12440 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12440_payment :
    (retDist (paperDesignP 12440).toCentres).real
      (agentEv (paperDesignP 12440) covarianceEvent12440)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12440

theorem localCov12440 : BstLean.Part259.LocalCovarianceOn covarianceEvent12440
    (BstLean.Part263.cell scalarRow12440.grid) (caps repair12440) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12440

theorem covarianceGood12440_payment :
    (retDist (paperDesignP 12440).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12440)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12440_payment



end BstLean.Part269.N12440

namespace BstLean.Part269.N12440
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12440}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12440.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12440) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12440).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12440 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12440) (by norm_num) BstLean.Part268.WorldRow12440.worldPackage rfl
    BstLean.Part268.WorldRow12440.product_lower (BstLean.Part268.WorldRow12440.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12440} (hw : c ∈ Hof BstLean.Part268.WorldRow12440.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12440) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12440) (by norm_num) BstLean.Part268.WorldRow12440.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12440} (hw : c ∈ Hof BstLean.Part268.WorldRow12440.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12440) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12440).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12440) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12440_eq : scalarRow12440.targetFrame = BstLean.Part268.agent12440.frame := by
  norm_num [scalarRow12440,BstLean.Part268.agent12440]

noncomputable def frameData12440 : BstLean.Part264b.FrameData 12440 :=
  BstLean.Part269.frameData_from_numerics (n := 12440) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12440.worldPackage rfl BstLean.Part268.WorldRow12440.product_lower (BstLean.Part268.WorldRow12440.producthi.2.trans (by norm_num))
    scalarRow12440 repair12440 covarianceInputs12440 (fun i hi => sourceNumerics12440 hi)
    BstLean.Part268.agent12440.frame targetFrame12440_eq


end BstLean.Part269.N12440

namespace BstLean.Part269.N12441
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12441 : scalarRow12441.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12441, BstLean.Part268.grid12441, BstLean.Part263.worldGrid]

theorem supplies12441 (j : Fin 43) : Supply 12441 (parameters j)
    (cellLower scalarRow12441.grid (sourceIndex j))
    (cellUpper scalarRow12441.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12441.grid grid_top_bounds12441 j

theorem radii12441 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12441.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12441 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12441 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12441.grid grid_top_bounds12441 j hθ

noncomputable def covarianceInputs12441 :
    BstLean.Part263.CovarianceInputs 12441 scalarRow12441.grid parameters (caps repair12441) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12441 grid_top_bounds12441 repair12441

noncomputable def covarianceEvent12441 : Set (AgFam 12441) :=
  BstLean.Part263.covarianceEvent 12441 scalarRow12441.grid parameters

theorem covarianceEvent12441_measurable : MeasurableSet covarianceEvent12441 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12441_payment :
    (retDist (paperDesignP 12441).toCentres).real
      (agentEv (paperDesignP 12441) covarianceEvent12441)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12441

theorem localCov12441 : BstLean.Part259.LocalCovarianceOn covarianceEvent12441
    (BstLean.Part263.cell scalarRow12441.grid) (caps repair12441) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12441

theorem covarianceGood12441_payment :
    (retDist (paperDesignP 12441).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12441)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12441_payment



end BstLean.Part269.N12441

namespace BstLean.Part269.N12441
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12441}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12441.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12441) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12441).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12441 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12441) (by norm_num) BstLean.Part268.WorldRow12441.worldPackage rfl
    BstLean.Part268.WorldRow12441.product_lower (BstLean.Part268.WorldRow12441.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12441} (hw : c ∈ Hof BstLean.Part268.WorldRow12441.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12441) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12441) (by norm_num) BstLean.Part268.WorldRow12441.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12441} (hw : c ∈ Hof BstLean.Part268.WorldRow12441.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12441) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12441).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12441) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12441_eq : scalarRow12441.targetFrame = BstLean.Part268.agent12441.frame := by
  norm_num [scalarRow12441,BstLean.Part268.agent12441]

noncomputable def frameData12441 : BstLean.Part264b.FrameData 12441 :=
  BstLean.Part269.frameData_from_numerics (n := 12441) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12441.worldPackage rfl BstLean.Part268.WorldRow12441.product_lower (BstLean.Part268.WorldRow12441.producthi.2.trans (by norm_num))
    scalarRow12441 repair12441 covarianceInputs12441 (fun i hi => sourceNumerics12441 hi)
    BstLean.Part268.agent12441.frame targetFrame12441_eq


end BstLean.Part269.N12441

namespace BstLean.Part269.N12442
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12442 : scalarRow12442.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12442, BstLean.Part268.grid12442, BstLean.Part263.worldGrid]

theorem supplies12442 (j : Fin 43) : Supply 12442 (parameters j)
    (cellLower scalarRow12442.grid (sourceIndex j))
    (cellUpper scalarRow12442.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12442.grid grid_top_bounds12442 j

theorem radii12442 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12442.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12442 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12442 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12442.grid grid_top_bounds12442 j hθ

noncomputable def covarianceInputs12442 :
    BstLean.Part263.CovarianceInputs 12442 scalarRow12442.grid parameters (caps repair12442) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12442 grid_top_bounds12442 repair12442

noncomputable def covarianceEvent12442 : Set (AgFam 12442) :=
  BstLean.Part263.covarianceEvent 12442 scalarRow12442.grid parameters

theorem covarianceEvent12442_measurable : MeasurableSet covarianceEvent12442 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12442_payment :
    (retDist (paperDesignP 12442).toCentres).real
      (agentEv (paperDesignP 12442) covarianceEvent12442)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12442

theorem localCov12442 : BstLean.Part259.LocalCovarianceOn covarianceEvent12442
    (BstLean.Part263.cell scalarRow12442.grid) (caps repair12442) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12442

theorem covarianceGood12442_payment :
    (retDist (paperDesignP 12442).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12442)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12442_payment



end BstLean.Part269.N12442

namespace BstLean.Part269.N12442
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12442}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12442.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12442) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12442).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12442 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12442) (by norm_num) BstLean.Part268.WorldRow12442.worldPackage rfl
    BstLean.Part268.WorldRow12442.product_lower (BstLean.Part268.WorldRow12442.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12442} (hw : c ∈ Hof BstLean.Part268.WorldRow12442.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12442) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12442) (by norm_num) BstLean.Part268.WorldRow12442.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12442} (hw : c ∈ Hof BstLean.Part268.WorldRow12442.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12442) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12442).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12442) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12442_eq : scalarRow12442.targetFrame = BstLean.Part268.agent12442.frame := by
  norm_num [scalarRow12442,BstLean.Part268.agent12442]

noncomputable def frameData12442 : BstLean.Part264b.FrameData 12442 :=
  BstLean.Part269.frameData_from_numerics (n := 12442) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12442.worldPackage rfl BstLean.Part268.WorldRow12442.product_lower (BstLean.Part268.WorldRow12442.producthi.2.trans (by norm_num))
    scalarRow12442 repair12442 covarianceInputs12442 (fun i hi => sourceNumerics12442 hi)
    BstLean.Part268.agent12442.frame targetFrame12442_eq


end BstLean.Part269.N12442

namespace BstLean.Part269.N12443
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12443 : scalarRow12443.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12443, BstLean.Part268.grid12443, BstLean.Part263.worldGrid]

theorem supplies12443 (j : Fin 43) : Supply 12443 (parameters j)
    (cellLower scalarRow12443.grid (sourceIndex j))
    (cellUpper scalarRow12443.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12443.grid grid_top_bounds12443 j

theorem radii12443 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12443.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12443 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12443 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12443.grid grid_top_bounds12443 j hθ

noncomputable def covarianceInputs12443 :
    BstLean.Part263.CovarianceInputs 12443 scalarRow12443.grid parameters (caps repair12443) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12443 grid_top_bounds12443 repair12443

noncomputable def covarianceEvent12443 : Set (AgFam 12443) :=
  BstLean.Part263.covarianceEvent 12443 scalarRow12443.grid parameters

theorem covarianceEvent12443_measurable : MeasurableSet covarianceEvent12443 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12443_payment :
    (retDist (paperDesignP 12443).toCentres).real
      (agentEv (paperDesignP 12443) covarianceEvent12443)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12443

theorem localCov12443 : BstLean.Part259.LocalCovarianceOn covarianceEvent12443
    (BstLean.Part263.cell scalarRow12443.grid) (caps repair12443) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12443

theorem covarianceGood12443_payment :
    (retDist (paperDesignP 12443).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12443)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12443_payment



end BstLean.Part269.N12443

namespace BstLean.Part269.N12443
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12443}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12443.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12443) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12443).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12443 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12443) (by norm_num) BstLean.Part268.WorldRow12443.worldPackage rfl
    BstLean.Part268.WorldRow12443.product_lower (BstLean.Part268.WorldRow12443.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12443} (hw : c ∈ Hof BstLean.Part268.WorldRow12443.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12443) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12443) (by norm_num) BstLean.Part268.WorldRow12443.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12443} (hw : c ∈ Hof BstLean.Part268.WorldRow12443.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12443) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12443).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12443) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12443_eq : scalarRow12443.targetFrame = BstLean.Part268.agent12443.frame := by
  norm_num [scalarRow12443,BstLean.Part268.agent12443]

noncomputable def frameData12443 : BstLean.Part264b.FrameData 12443 :=
  BstLean.Part269.frameData_from_numerics (n := 12443) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12443.worldPackage rfl BstLean.Part268.WorldRow12443.product_lower (BstLean.Part268.WorldRow12443.producthi.2.trans (by norm_num))
    scalarRow12443 repair12443 covarianceInputs12443 (fun i hi => sourceNumerics12443 hi)
    BstLean.Part268.agent12443.frame targetFrame12443_eq


end BstLean.Part269.N12443

namespace BstLean.Part269.N12444
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12444 : scalarRow12444.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12444, BstLean.Part268.grid12444, BstLean.Part263.worldGrid]

theorem supplies12444 (j : Fin 43) : Supply 12444 (parameters j)
    (cellLower scalarRow12444.grid (sourceIndex j))
    (cellUpper scalarRow12444.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12444.grid grid_top_bounds12444 j

theorem radii12444 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12444.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12444 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12444 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12444.grid grid_top_bounds12444 j hθ

noncomputable def covarianceInputs12444 :
    BstLean.Part263.CovarianceInputs 12444 scalarRow12444.grid parameters (caps repair12444) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12444 grid_top_bounds12444 repair12444

noncomputable def covarianceEvent12444 : Set (AgFam 12444) :=
  BstLean.Part263.covarianceEvent 12444 scalarRow12444.grid parameters

theorem covarianceEvent12444_measurable : MeasurableSet covarianceEvent12444 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12444_payment :
    (retDist (paperDesignP 12444).toCentres).real
      (agentEv (paperDesignP 12444) covarianceEvent12444)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12444

theorem localCov12444 : BstLean.Part259.LocalCovarianceOn covarianceEvent12444
    (BstLean.Part263.cell scalarRow12444.grid) (caps repair12444) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12444

theorem covarianceGood12444_payment :
    (retDist (paperDesignP 12444).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12444)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12444_payment



end BstLean.Part269.N12444

namespace BstLean.Part269.N12444
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12444}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12444.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12444) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12444).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12444 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12444) (by norm_num) BstLean.Part268.WorldRow12444.worldPackage rfl
    BstLean.Part268.WorldRow12444.product_lower (BstLean.Part268.WorldRow12444.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12444} (hw : c ∈ Hof BstLean.Part268.WorldRow12444.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12444) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12444) (by norm_num) BstLean.Part268.WorldRow12444.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12444} (hw : c ∈ Hof BstLean.Part268.WorldRow12444.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12444) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12444).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12444) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12444_eq : scalarRow12444.targetFrame = BstLean.Part268.agent12444.frame := by
  norm_num [scalarRow12444,BstLean.Part268.agent12444]

noncomputable def frameData12444 : BstLean.Part264b.FrameData 12444 :=
  BstLean.Part269.frameData_from_numerics (n := 12444) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12444.worldPackage rfl BstLean.Part268.WorldRow12444.product_lower (BstLean.Part268.WorldRow12444.producthi.2.trans (by norm_num))
    scalarRow12444 repair12444 covarianceInputs12444 (fun i hi => sourceNumerics12444 hi)
    BstLean.Part268.agent12444.frame targetFrame12444_eq


end BstLean.Part269.N12444
