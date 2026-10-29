import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World1Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs1
import BstLean.Part269Rows1
import BstLean.Part269Sources1
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12390
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12390 : scalarRow12390.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12390, BstLean.Part268.grid12390, BstLean.Part263.worldGrid]

theorem supplies12390 (j : Fin 43) : Supply 12390 (parameters j)
    (cellLower scalarRow12390.grid (sourceIndex j))
    (cellUpper scalarRow12390.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12390.grid grid_top_bounds12390 j

theorem radii12390 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12390.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12390 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12390 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12390.grid grid_top_bounds12390 j hθ

noncomputable def covarianceInputs12390 :
    BstLean.Part263.CovarianceInputs 12390 scalarRow12390.grid parameters (caps repair12390) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12390 grid_top_bounds12390 repair12390

noncomputable def covarianceEvent12390 : Set (AgFam 12390) :=
  BstLean.Part263.covarianceEvent 12390 scalarRow12390.grid parameters

theorem covarianceEvent12390_measurable : MeasurableSet covarianceEvent12390 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12390_payment :
    (retDist (paperDesignP 12390).toCentres).real
      (agentEv (paperDesignP 12390) covarianceEvent12390)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12390

theorem localCov12390 : BstLean.Part259.LocalCovarianceOn covarianceEvent12390
    (BstLean.Part263.cell scalarRow12390.grid) (caps repair12390) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12390

theorem covarianceGood12390_payment :
    (retDist (paperDesignP 12390).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12390)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12390_payment



end BstLean.Part269.N12390

namespace BstLean.Part269.N12390
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12390}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12390.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12390) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12390).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12390 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12390) (by norm_num) BstLean.Part268.WorldRow12390.worldPackage rfl
    BstLean.Part268.WorldRow12390.product_lower (BstLean.Part268.WorldRow12390.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12390} (hw : c ∈ Hof BstLean.Part268.WorldRow12390.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12390) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12390) (by norm_num) BstLean.Part268.WorldRow12390.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12390} (hw : c ∈ Hof BstLean.Part268.WorldRow12390.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12390) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12390).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12390) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12390_eq : scalarRow12390.targetFrame = BstLean.Part268.agent12390.frame := by
  norm_num [scalarRow12390,BstLean.Part268.agent12390]

noncomputable def frameData12390 : BstLean.Part264b.FrameData 12390 :=
  BstLean.Part269.frameData_from_numerics (n := 12390) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12390.worldPackage rfl BstLean.Part268.WorldRow12390.product_lower (BstLean.Part268.WorldRow12390.producthi.2.trans (by norm_num))
    scalarRow12390 repair12390 covarianceInputs12390 (fun i hi => sourceNumerics12390 hi)
    BstLean.Part268.agent12390.frame targetFrame12390_eq


end BstLean.Part269.N12390

namespace BstLean.Part269.N12391
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12391 : scalarRow12391.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12391, BstLean.Part268.grid12391, BstLean.Part263.worldGrid]

theorem supplies12391 (j : Fin 43) : Supply 12391 (parameters j)
    (cellLower scalarRow12391.grid (sourceIndex j))
    (cellUpper scalarRow12391.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12391.grid grid_top_bounds12391 j

theorem radii12391 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12391.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12391 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12391 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12391.grid grid_top_bounds12391 j hθ

noncomputable def covarianceInputs12391 :
    BstLean.Part263.CovarianceInputs 12391 scalarRow12391.grid parameters (caps repair12391) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12391 grid_top_bounds12391 repair12391

noncomputable def covarianceEvent12391 : Set (AgFam 12391) :=
  BstLean.Part263.covarianceEvent 12391 scalarRow12391.grid parameters

theorem covarianceEvent12391_measurable : MeasurableSet covarianceEvent12391 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12391_payment :
    (retDist (paperDesignP 12391).toCentres).real
      (agentEv (paperDesignP 12391) covarianceEvent12391)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12391

theorem localCov12391 : BstLean.Part259.LocalCovarianceOn covarianceEvent12391
    (BstLean.Part263.cell scalarRow12391.grid) (caps repair12391) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12391

theorem covarianceGood12391_payment :
    (retDist (paperDesignP 12391).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12391)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12391_payment



end BstLean.Part269.N12391

namespace BstLean.Part269.N12391
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12391}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12391.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12391) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12391).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12391 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12391) (by norm_num) BstLean.Part268.WorldRow12391.worldPackage rfl
    BstLean.Part268.WorldRow12391.product_lower (BstLean.Part268.WorldRow12391.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12391} (hw : c ∈ Hof BstLean.Part268.WorldRow12391.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12391) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12391) (by norm_num) BstLean.Part268.WorldRow12391.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12391} (hw : c ∈ Hof BstLean.Part268.WorldRow12391.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12391) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12391).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12391) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12391_eq : scalarRow12391.targetFrame = BstLean.Part268.agent12391.frame := by
  norm_num [scalarRow12391,BstLean.Part268.agent12391]

noncomputable def frameData12391 : BstLean.Part264b.FrameData 12391 :=
  BstLean.Part269.frameData_from_numerics (n := 12391) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12391.worldPackage rfl BstLean.Part268.WorldRow12391.product_lower (BstLean.Part268.WorldRow12391.producthi.2.trans (by norm_num))
    scalarRow12391 repair12391 covarianceInputs12391 (fun i hi => sourceNumerics12391 hi)
    BstLean.Part268.agent12391.frame targetFrame12391_eq


end BstLean.Part269.N12391

namespace BstLean.Part269.N12392
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12392 : scalarRow12392.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12392, BstLean.Part268.grid12392, BstLean.Part263.worldGrid]

theorem supplies12392 (j : Fin 43) : Supply 12392 (parameters j)
    (cellLower scalarRow12392.grid (sourceIndex j))
    (cellUpper scalarRow12392.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12392.grid grid_top_bounds12392 j

theorem radii12392 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12392.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12392 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12392 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12392.grid grid_top_bounds12392 j hθ

noncomputable def covarianceInputs12392 :
    BstLean.Part263.CovarianceInputs 12392 scalarRow12392.grid parameters (caps repair12392) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12392 grid_top_bounds12392 repair12392

noncomputable def covarianceEvent12392 : Set (AgFam 12392) :=
  BstLean.Part263.covarianceEvent 12392 scalarRow12392.grid parameters

theorem covarianceEvent12392_measurable : MeasurableSet covarianceEvent12392 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12392_payment :
    (retDist (paperDesignP 12392).toCentres).real
      (agentEv (paperDesignP 12392) covarianceEvent12392)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12392

theorem localCov12392 : BstLean.Part259.LocalCovarianceOn covarianceEvent12392
    (BstLean.Part263.cell scalarRow12392.grid) (caps repair12392) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12392

theorem covarianceGood12392_payment :
    (retDist (paperDesignP 12392).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12392)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12392_payment



end BstLean.Part269.N12392

namespace BstLean.Part269.N12392
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12392}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12392.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12392) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12392).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12392 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12392) (by norm_num) BstLean.Part268.WorldRow12392.worldPackage rfl
    BstLean.Part268.WorldRow12392.product_lower (BstLean.Part268.WorldRow12392.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12392} (hw : c ∈ Hof BstLean.Part268.WorldRow12392.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12392) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12392) (by norm_num) BstLean.Part268.WorldRow12392.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12392} (hw : c ∈ Hof BstLean.Part268.WorldRow12392.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12392) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12392).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12392) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12392_eq : scalarRow12392.targetFrame = BstLean.Part268.agent12392.frame := by
  norm_num [scalarRow12392,BstLean.Part268.agent12392]

noncomputable def frameData12392 : BstLean.Part264b.FrameData 12392 :=
  BstLean.Part269.frameData_from_numerics (n := 12392) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12392.worldPackage rfl BstLean.Part268.WorldRow12392.product_lower (BstLean.Part268.WorldRow12392.producthi.2.trans (by norm_num))
    scalarRow12392 repair12392 covarianceInputs12392 (fun i hi => sourceNumerics12392 hi)
    BstLean.Part268.agent12392.frame targetFrame12392_eq


end BstLean.Part269.N12392

namespace BstLean.Part269.N12393
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12393 : scalarRow12393.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12393, BstLean.Part268.grid12393, BstLean.Part263.worldGrid]

theorem supplies12393 (j : Fin 43) : Supply 12393 (parameters j)
    (cellLower scalarRow12393.grid (sourceIndex j))
    (cellUpper scalarRow12393.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12393.grid grid_top_bounds12393 j

theorem radii12393 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12393.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12393 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12393 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12393.grid grid_top_bounds12393 j hθ

noncomputable def covarianceInputs12393 :
    BstLean.Part263.CovarianceInputs 12393 scalarRow12393.grid parameters (caps repair12393) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12393 grid_top_bounds12393 repair12393

noncomputable def covarianceEvent12393 : Set (AgFam 12393) :=
  BstLean.Part263.covarianceEvent 12393 scalarRow12393.grid parameters

theorem covarianceEvent12393_measurable : MeasurableSet covarianceEvent12393 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12393_payment :
    (retDist (paperDesignP 12393).toCentres).real
      (agentEv (paperDesignP 12393) covarianceEvent12393)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12393

theorem localCov12393 : BstLean.Part259.LocalCovarianceOn covarianceEvent12393
    (BstLean.Part263.cell scalarRow12393.grid) (caps repair12393) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12393

theorem covarianceGood12393_payment :
    (retDist (paperDesignP 12393).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12393)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12393_payment



end BstLean.Part269.N12393

namespace BstLean.Part269.N12393
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12393}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12393.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12393) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12393).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12393 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12393) (by norm_num) BstLean.Part268.WorldRow12393.worldPackage rfl
    BstLean.Part268.WorldRow12393.product_lower (BstLean.Part268.WorldRow12393.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12393} (hw : c ∈ Hof BstLean.Part268.WorldRow12393.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12393) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12393) (by norm_num) BstLean.Part268.WorldRow12393.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12393} (hw : c ∈ Hof BstLean.Part268.WorldRow12393.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12393) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12393).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12393) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12393_eq : scalarRow12393.targetFrame = BstLean.Part268.agent12393.frame := by
  norm_num [scalarRow12393,BstLean.Part268.agent12393]

noncomputable def frameData12393 : BstLean.Part264b.FrameData 12393 :=
  BstLean.Part269.frameData_from_numerics (n := 12393) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12393.worldPackage rfl BstLean.Part268.WorldRow12393.product_lower (BstLean.Part268.WorldRow12393.producthi.2.trans (by norm_num))
    scalarRow12393 repair12393 covarianceInputs12393 (fun i hi => sourceNumerics12393 hi)
    BstLean.Part268.agent12393.frame targetFrame12393_eq


end BstLean.Part269.N12393

namespace BstLean.Part269.N12394
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12394 : scalarRow12394.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12394, BstLean.Part268.grid12394, BstLean.Part263.worldGrid]

theorem supplies12394 (j : Fin 43) : Supply 12394 (parameters j)
    (cellLower scalarRow12394.grid (sourceIndex j))
    (cellUpper scalarRow12394.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12394.grid grid_top_bounds12394 j

theorem radii12394 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12394.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12394 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12394 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12394.grid grid_top_bounds12394 j hθ

noncomputable def covarianceInputs12394 :
    BstLean.Part263.CovarianceInputs 12394 scalarRow12394.grid parameters (caps repair12394) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12394 grid_top_bounds12394 repair12394

noncomputable def covarianceEvent12394 : Set (AgFam 12394) :=
  BstLean.Part263.covarianceEvent 12394 scalarRow12394.grid parameters

theorem covarianceEvent12394_measurable : MeasurableSet covarianceEvent12394 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12394_payment :
    (retDist (paperDesignP 12394).toCentres).real
      (agentEv (paperDesignP 12394) covarianceEvent12394)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12394

theorem localCov12394 : BstLean.Part259.LocalCovarianceOn covarianceEvent12394
    (BstLean.Part263.cell scalarRow12394.grid) (caps repair12394) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12394

theorem covarianceGood12394_payment :
    (retDist (paperDesignP 12394).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12394)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12394_payment



end BstLean.Part269.N12394

namespace BstLean.Part269.N12394
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12394}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12394.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12394) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12394).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12394 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12394) (by norm_num) BstLean.Part268.WorldRow12394.worldPackage rfl
    BstLean.Part268.WorldRow12394.product_lower (BstLean.Part268.WorldRow12394.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12394} (hw : c ∈ Hof BstLean.Part268.WorldRow12394.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12394) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12394) (by norm_num) BstLean.Part268.WorldRow12394.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12394} (hw : c ∈ Hof BstLean.Part268.WorldRow12394.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12394) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12394).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12394) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12394_eq : scalarRow12394.targetFrame = BstLean.Part268.agent12394.frame := by
  norm_num [scalarRow12394,BstLean.Part268.agent12394]

noncomputable def frameData12394 : BstLean.Part264b.FrameData 12394 :=
  BstLean.Part269.frameData_from_numerics (n := 12394) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12394.worldPackage rfl BstLean.Part268.WorldRow12394.product_lower (BstLean.Part268.WorldRow12394.producthi.2.trans (by norm_num))
    scalarRow12394 repair12394 covarianceInputs12394 (fun i hi => sourceNumerics12394 hi)
    BstLean.Part268.agent12394.frame targetFrame12394_eq


end BstLean.Part269.N12394
