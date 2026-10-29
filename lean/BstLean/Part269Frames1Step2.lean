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

namespace BstLean.Part269.N12385
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12385 : scalarRow12385.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12385, BstLean.Part268.grid12385, BstLean.Part263.worldGrid]

theorem supplies12385 (j : Fin 43) : Supply 12385 (parameters j)
    (cellLower scalarRow12385.grid (sourceIndex j))
    (cellUpper scalarRow12385.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12385.grid grid_top_bounds12385 j

theorem radii12385 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12385.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12385 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12385 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12385.grid grid_top_bounds12385 j hθ

noncomputable def covarianceInputs12385 :
    BstLean.Part263.CovarianceInputs 12385 scalarRow12385.grid parameters (caps repair12385) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12385 grid_top_bounds12385 repair12385

noncomputable def covarianceEvent12385 : Set (AgFam 12385) :=
  BstLean.Part263.covarianceEvent 12385 scalarRow12385.grid parameters

theorem covarianceEvent12385_measurable : MeasurableSet covarianceEvent12385 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12385_payment :
    (retDist (paperDesignP 12385).toCentres).real
      (agentEv (paperDesignP 12385) covarianceEvent12385)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12385

theorem localCov12385 : BstLean.Part259.LocalCovarianceOn covarianceEvent12385
    (BstLean.Part263.cell scalarRow12385.grid) (caps repair12385) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12385

theorem covarianceGood12385_payment :
    (retDist (paperDesignP 12385).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12385)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12385_payment



end BstLean.Part269.N12385

namespace BstLean.Part269.N12385
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12385}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12385.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12385) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12385).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12385 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12385) (by norm_num) BstLean.Part268.WorldRow12385.worldPackage rfl
    BstLean.Part268.WorldRow12385.product_lower (BstLean.Part268.WorldRow12385.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12385} (hw : c ∈ Hof BstLean.Part268.WorldRow12385.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12385) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12385) (by norm_num) BstLean.Part268.WorldRow12385.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12385} (hw : c ∈ Hof BstLean.Part268.WorldRow12385.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12385) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12385).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12385) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12385_eq : scalarRow12385.targetFrame = BstLean.Part268.agent12385.frame := by
  norm_num [scalarRow12385,BstLean.Part268.agent12385]

noncomputable def frameData12385 : BstLean.Part264b.FrameData 12385 :=
  BstLean.Part269.frameData_from_numerics (n := 12385) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12385.worldPackage rfl BstLean.Part268.WorldRow12385.product_lower (BstLean.Part268.WorldRow12385.producthi.2.trans (by norm_num))
    scalarRow12385 repair12385 covarianceInputs12385 (fun i hi => sourceNumerics12385 hi)
    BstLean.Part268.agent12385.frame targetFrame12385_eq


end BstLean.Part269.N12385

namespace BstLean.Part269.N12386
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12386 : scalarRow12386.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12386, BstLean.Part268.grid12386, BstLean.Part263.worldGrid]

theorem supplies12386 (j : Fin 43) : Supply 12386 (parameters j)
    (cellLower scalarRow12386.grid (sourceIndex j))
    (cellUpper scalarRow12386.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12386.grid grid_top_bounds12386 j

theorem radii12386 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12386.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12386 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12386 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12386.grid grid_top_bounds12386 j hθ

noncomputable def covarianceInputs12386 :
    BstLean.Part263.CovarianceInputs 12386 scalarRow12386.grid parameters (caps repair12386) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12386 grid_top_bounds12386 repair12386

noncomputable def covarianceEvent12386 : Set (AgFam 12386) :=
  BstLean.Part263.covarianceEvent 12386 scalarRow12386.grid parameters

theorem covarianceEvent12386_measurable : MeasurableSet covarianceEvent12386 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12386_payment :
    (retDist (paperDesignP 12386).toCentres).real
      (agentEv (paperDesignP 12386) covarianceEvent12386)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12386

theorem localCov12386 : BstLean.Part259.LocalCovarianceOn covarianceEvent12386
    (BstLean.Part263.cell scalarRow12386.grid) (caps repair12386) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12386

theorem covarianceGood12386_payment :
    (retDist (paperDesignP 12386).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12386)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12386_payment



end BstLean.Part269.N12386

namespace BstLean.Part269.N12386
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12386}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12386.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12386) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12386).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12386 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12386) (by norm_num) BstLean.Part268.WorldRow12386.worldPackage rfl
    BstLean.Part268.WorldRow12386.product_lower (BstLean.Part268.WorldRow12386.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12386} (hw : c ∈ Hof BstLean.Part268.WorldRow12386.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12386) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12386) (by norm_num) BstLean.Part268.WorldRow12386.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12386} (hw : c ∈ Hof BstLean.Part268.WorldRow12386.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12386) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12386).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12386) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12386_eq : scalarRow12386.targetFrame = BstLean.Part268.agent12386.frame := by
  norm_num [scalarRow12386,BstLean.Part268.agent12386]

noncomputable def frameData12386 : BstLean.Part264b.FrameData 12386 :=
  BstLean.Part269.frameData_from_numerics (n := 12386) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12386.worldPackage rfl BstLean.Part268.WorldRow12386.product_lower (BstLean.Part268.WorldRow12386.producthi.2.trans (by norm_num))
    scalarRow12386 repair12386 covarianceInputs12386 (fun i hi => sourceNumerics12386 hi)
    BstLean.Part268.agent12386.frame targetFrame12386_eq


end BstLean.Part269.N12386

namespace BstLean.Part269.N12387
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12387 : scalarRow12387.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12387, BstLean.Part268.grid12387, BstLean.Part263.worldGrid]

theorem supplies12387 (j : Fin 43) : Supply 12387 (parameters j)
    (cellLower scalarRow12387.grid (sourceIndex j))
    (cellUpper scalarRow12387.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12387.grid grid_top_bounds12387 j

theorem radii12387 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12387.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12387 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12387 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12387.grid grid_top_bounds12387 j hθ

noncomputable def covarianceInputs12387 :
    BstLean.Part263.CovarianceInputs 12387 scalarRow12387.grid parameters (caps repair12387) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12387 grid_top_bounds12387 repair12387

noncomputable def covarianceEvent12387 : Set (AgFam 12387) :=
  BstLean.Part263.covarianceEvent 12387 scalarRow12387.grid parameters

theorem covarianceEvent12387_measurable : MeasurableSet covarianceEvent12387 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12387_payment :
    (retDist (paperDesignP 12387).toCentres).real
      (agentEv (paperDesignP 12387) covarianceEvent12387)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12387

theorem localCov12387 : BstLean.Part259.LocalCovarianceOn covarianceEvent12387
    (BstLean.Part263.cell scalarRow12387.grid) (caps repair12387) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12387

theorem covarianceGood12387_payment :
    (retDist (paperDesignP 12387).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12387)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12387_payment



end BstLean.Part269.N12387

namespace BstLean.Part269.N12387
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12387}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12387.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12387) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12387).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12387 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12387) (by norm_num) BstLean.Part268.WorldRow12387.worldPackage rfl
    BstLean.Part268.WorldRow12387.product_lower (BstLean.Part268.WorldRow12387.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12387} (hw : c ∈ Hof BstLean.Part268.WorldRow12387.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12387) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12387) (by norm_num) BstLean.Part268.WorldRow12387.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12387} (hw : c ∈ Hof BstLean.Part268.WorldRow12387.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12387) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12387).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12387) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12387_eq : scalarRow12387.targetFrame = BstLean.Part268.agent12387.frame := by
  norm_num [scalarRow12387,BstLean.Part268.agent12387]

noncomputable def frameData12387 : BstLean.Part264b.FrameData 12387 :=
  BstLean.Part269.frameData_from_numerics (n := 12387) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12387.worldPackage rfl BstLean.Part268.WorldRow12387.product_lower (BstLean.Part268.WorldRow12387.producthi.2.trans (by norm_num))
    scalarRow12387 repair12387 covarianceInputs12387 (fun i hi => sourceNumerics12387 hi)
    BstLean.Part268.agent12387.frame targetFrame12387_eq


end BstLean.Part269.N12387

namespace BstLean.Part269.N12388
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12388 : scalarRow12388.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12388, BstLean.Part268.grid12388, BstLean.Part263.worldGrid]

theorem supplies12388 (j : Fin 43) : Supply 12388 (parameters j)
    (cellLower scalarRow12388.grid (sourceIndex j))
    (cellUpper scalarRow12388.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12388.grid grid_top_bounds12388 j

theorem radii12388 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12388.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12388 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12388 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12388.grid grid_top_bounds12388 j hθ

noncomputable def covarianceInputs12388 :
    BstLean.Part263.CovarianceInputs 12388 scalarRow12388.grid parameters (caps repair12388) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12388 grid_top_bounds12388 repair12388

noncomputable def covarianceEvent12388 : Set (AgFam 12388) :=
  BstLean.Part263.covarianceEvent 12388 scalarRow12388.grid parameters

theorem covarianceEvent12388_measurable : MeasurableSet covarianceEvent12388 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12388_payment :
    (retDist (paperDesignP 12388).toCentres).real
      (agentEv (paperDesignP 12388) covarianceEvent12388)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12388

theorem localCov12388 : BstLean.Part259.LocalCovarianceOn covarianceEvent12388
    (BstLean.Part263.cell scalarRow12388.grid) (caps repair12388) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12388

theorem covarianceGood12388_payment :
    (retDist (paperDesignP 12388).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12388)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12388_payment



end BstLean.Part269.N12388

namespace BstLean.Part269.N12388
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12388}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12388.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12388) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12388).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12388 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12388) (by norm_num) BstLean.Part268.WorldRow12388.worldPackage rfl
    BstLean.Part268.WorldRow12388.product_lower (BstLean.Part268.WorldRow12388.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12388} (hw : c ∈ Hof BstLean.Part268.WorldRow12388.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12388) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12388) (by norm_num) BstLean.Part268.WorldRow12388.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12388} (hw : c ∈ Hof BstLean.Part268.WorldRow12388.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12388) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12388).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12388) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12388_eq : scalarRow12388.targetFrame = BstLean.Part268.agent12388.frame := by
  norm_num [scalarRow12388,BstLean.Part268.agent12388]

noncomputable def frameData12388 : BstLean.Part264b.FrameData 12388 :=
  BstLean.Part269.frameData_from_numerics (n := 12388) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12388.worldPackage rfl BstLean.Part268.WorldRow12388.product_lower (BstLean.Part268.WorldRow12388.producthi.2.trans (by norm_num))
    scalarRow12388 repair12388 covarianceInputs12388 (fun i hi => sourceNumerics12388 hi)
    BstLean.Part268.agent12388.frame targetFrame12388_eq


end BstLean.Part269.N12388

namespace BstLean.Part269.N12389
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12389 : scalarRow12389.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12389, BstLean.Part268.grid12389, BstLean.Part263.worldGrid]

theorem supplies12389 (j : Fin 43) : Supply 12389 (parameters j)
    (cellLower scalarRow12389.grid (sourceIndex j))
    (cellUpper scalarRow12389.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12389.grid grid_top_bounds12389 j

theorem radii12389 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12389.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12389 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12389 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12389.grid grid_top_bounds12389 j hθ

noncomputable def covarianceInputs12389 :
    BstLean.Part263.CovarianceInputs 12389 scalarRow12389.grid parameters (caps repair12389) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12389 grid_top_bounds12389 repair12389

noncomputable def covarianceEvent12389 : Set (AgFam 12389) :=
  BstLean.Part263.covarianceEvent 12389 scalarRow12389.grid parameters

theorem covarianceEvent12389_measurable : MeasurableSet covarianceEvent12389 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12389_payment :
    (retDist (paperDesignP 12389).toCentres).real
      (agentEv (paperDesignP 12389) covarianceEvent12389)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12389

theorem localCov12389 : BstLean.Part259.LocalCovarianceOn covarianceEvent12389
    (BstLean.Part263.cell scalarRow12389.grid) (caps repair12389) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12389

theorem covarianceGood12389_payment :
    (retDist (paperDesignP 12389).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12389)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12389_payment



end BstLean.Part269.N12389

namespace BstLean.Part269.N12389
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12389}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12389.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12389) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12389).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12389 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12389) (by norm_num) BstLean.Part268.WorldRow12389.worldPackage rfl
    BstLean.Part268.WorldRow12389.product_lower (BstLean.Part268.WorldRow12389.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12389} (hw : c ∈ Hof BstLean.Part268.WorldRow12389.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12389) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12389) (by norm_num) BstLean.Part268.WorldRow12389.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12389} (hw : c ∈ Hof BstLean.Part268.WorldRow12389.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12389) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12389).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12389) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12389_eq : scalarRow12389.targetFrame = BstLean.Part268.agent12389.frame := by
  norm_num [scalarRow12389,BstLean.Part268.agent12389]

noncomputable def frameData12389 : BstLean.Part264b.FrameData 12389 :=
  BstLean.Part269.frameData_from_numerics (n := 12389) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12389.worldPackage rfl BstLean.Part268.WorldRow12389.product_lower (BstLean.Part268.WorldRow12389.producthi.2.trans (by norm_num))
    scalarRow12389 repair12389 covarianceInputs12389 (fun i hi => sourceNumerics12389 hi)
    BstLean.Part268.agent12389.frame targetFrame12389_eq


end BstLean.Part269.N12389
