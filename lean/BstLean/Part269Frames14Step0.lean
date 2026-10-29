import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World14Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs14
import BstLean.Part269Rows14
import BstLean.Part269Sources14
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12700
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12700 : scalarRow12700.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12700, BstLean.Part268.grid12700, BstLean.Part263.worldGrid]

theorem supplies12700 (j : Fin 43) : Supply 12700 (parameters j)
    (cellLower scalarRow12700.grid (sourceIndex j))
    (cellUpper scalarRow12700.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12700.grid grid_top_bounds12700 j

theorem radii12700 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12700.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12700 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12700 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12700.grid grid_top_bounds12700 j hθ

noncomputable def covarianceInputs12700 :
    BstLean.Part263.CovarianceInputs 12700 scalarRow12700.grid parameters (caps repair12700) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12700 grid_top_bounds12700 repair12700

noncomputable def covarianceEvent12700 : Set (AgFam 12700) :=
  BstLean.Part263.covarianceEvent 12700 scalarRow12700.grid parameters

theorem covarianceEvent12700_measurable : MeasurableSet covarianceEvent12700 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12700_payment :
    (retDist (paperDesignP 12700).toCentres).real
      (agentEv (paperDesignP 12700) covarianceEvent12700)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12700

theorem localCov12700 : BstLean.Part259.LocalCovarianceOn covarianceEvent12700
    (BstLean.Part263.cell scalarRow12700.grid) (caps repair12700) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12700

theorem covarianceGood12700_payment :
    (retDist (paperDesignP 12700).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12700)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12700_payment



end BstLean.Part269.N12700

namespace BstLean.Part269.N12700
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12700}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12700.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12700) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12700).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12700 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12700) (by norm_num) BstLean.Part268.WorldRow12700.worldPackage rfl
    BstLean.Part268.WorldRow12700.product_lower (BstLean.Part268.WorldRow12700.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12700} (hw : c ∈ Hof BstLean.Part268.WorldRow12700.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12700) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12700) (by norm_num) BstLean.Part268.WorldRow12700.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12700} (hw : c ∈ Hof BstLean.Part268.WorldRow12700.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12700) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12700).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12700) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12700_eq : scalarRow12700.targetFrame = BstLean.Part268.agent12700.frame := by
  norm_num [scalarRow12700,BstLean.Part268.agent12700]

noncomputable def frameData12700 : BstLean.Part264b.FrameData 12700 :=
  BstLean.Part269.frameData_from_numerics (n := 12700) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12700.worldPackage rfl BstLean.Part268.WorldRow12700.product_lower (BstLean.Part268.WorldRow12700.producthi.2.trans (by norm_num))
    scalarRow12700 repair12700 covarianceInputs12700 (fun i hi => sourceNumerics12700 hi)
    BstLean.Part268.agent12700.frame targetFrame12700_eq


end BstLean.Part269.N12700

namespace BstLean.Part269.N12701
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12701 : scalarRow12701.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12701, BstLean.Part268.grid12701, BstLean.Part263.worldGrid]

theorem supplies12701 (j : Fin 43) : Supply 12701 (parameters j)
    (cellLower scalarRow12701.grid (sourceIndex j))
    (cellUpper scalarRow12701.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12701.grid grid_top_bounds12701 j

theorem radii12701 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12701.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12701 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12701 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12701.grid grid_top_bounds12701 j hθ

noncomputable def covarianceInputs12701 :
    BstLean.Part263.CovarianceInputs 12701 scalarRow12701.grid parameters (caps repair12701) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12701 grid_top_bounds12701 repair12701

noncomputable def covarianceEvent12701 : Set (AgFam 12701) :=
  BstLean.Part263.covarianceEvent 12701 scalarRow12701.grid parameters

theorem covarianceEvent12701_measurable : MeasurableSet covarianceEvent12701 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12701_payment :
    (retDist (paperDesignP 12701).toCentres).real
      (agentEv (paperDesignP 12701) covarianceEvent12701)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12701

theorem localCov12701 : BstLean.Part259.LocalCovarianceOn covarianceEvent12701
    (BstLean.Part263.cell scalarRow12701.grid) (caps repair12701) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12701

theorem covarianceGood12701_payment :
    (retDist (paperDesignP 12701).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12701)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12701_payment



end BstLean.Part269.N12701

namespace BstLean.Part269.N12701
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12701}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12701.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12701) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12701).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12701 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12701) (by norm_num) BstLean.Part268.WorldRow12701.worldPackage rfl
    BstLean.Part268.WorldRow12701.product_lower (BstLean.Part268.WorldRow12701.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12701} (hw : c ∈ Hof BstLean.Part268.WorldRow12701.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12701) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12701) (by norm_num) BstLean.Part268.WorldRow12701.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12701} (hw : c ∈ Hof BstLean.Part268.WorldRow12701.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12701) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12701).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12701) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12701_eq : scalarRow12701.targetFrame = BstLean.Part268.agent12701.frame := by
  norm_num [scalarRow12701,BstLean.Part268.agent12701]

noncomputable def frameData12701 : BstLean.Part264b.FrameData 12701 :=
  BstLean.Part269.frameData_from_numerics (n := 12701) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12701.worldPackage rfl BstLean.Part268.WorldRow12701.product_lower (BstLean.Part268.WorldRow12701.producthi.2.trans (by norm_num))
    scalarRow12701 repair12701 covarianceInputs12701 (fun i hi => sourceNumerics12701 hi)
    BstLean.Part268.agent12701.frame targetFrame12701_eq


end BstLean.Part269.N12701

namespace BstLean.Part269.N12702
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12702 : scalarRow12702.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12702, BstLean.Part268.grid12702, BstLean.Part263.worldGrid]

theorem supplies12702 (j : Fin 43) : Supply 12702 (parameters j)
    (cellLower scalarRow12702.grid (sourceIndex j))
    (cellUpper scalarRow12702.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12702.grid grid_top_bounds12702 j

theorem radii12702 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12702.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12702 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12702 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12702.grid grid_top_bounds12702 j hθ

noncomputable def covarianceInputs12702 :
    BstLean.Part263.CovarianceInputs 12702 scalarRow12702.grid parameters (caps repair12702) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12702 grid_top_bounds12702 repair12702

noncomputable def covarianceEvent12702 : Set (AgFam 12702) :=
  BstLean.Part263.covarianceEvent 12702 scalarRow12702.grid parameters

theorem covarianceEvent12702_measurable : MeasurableSet covarianceEvent12702 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12702_payment :
    (retDist (paperDesignP 12702).toCentres).real
      (agentEv (paperDesignP 12702) covarianceEvent12702)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12702

theorem localCov12702 : BstLean.Part259.LocalCovarianceOn covarianceEvent12702
    (BstLean.Part263.cell scalarRow12702.grid) (caps repair12702) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12702

theorem covarianceGood12702_payment :
    (retDist (paperDesignP 12702).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12702)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12702_payment



end BstLean.Part269.N12702

namespace BstLean.Part269.N12702
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12702}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12702.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12702) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12702).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12702 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12702) (by norm_num) BstLean.Part268.WorldRow12702.worldPackage rfl
    BstLean.Part268.WorldRow12702.product_lower (BstLean.Part268.WorldRow12702.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12702} (hw : c ∈ Hof BstLean.Part268.WorldRow12702.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12702) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12702) (by norm_num) BstLean.Part268.WorldRow12702.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12702} (hw : c ∈ Hof BstLean.Part268.WorldRow12702.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12702) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12702).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12702) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12702_eq : scalarRow12702.targetFrame = BstLean.Part268.agent12702.frame := by
  norm_num [scalarRow12702,BstLean.Part268.agent12702]

noncomputable def frameData12702 : BstLean.Part264b.FrameData 12702 :=
  BstLean.Part269.frameData_from_numerics (n := 12702) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12702.worldPackage rfl BstLean.Part268.WorldRow12702.product_lower (BstLean.Part268.WorldRow12702.producthi.2.trans (by norm_num))
    scalarRow12702 repair12702 covarianceInputs12702 (fun i hi => sourceNumerics12702 hi)
    BstLean.Part268.agent12702.frame targetFrame12702_eq


end BstLean.Part269.N12702

namespace BstLean.Part269.N12703
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12703 : scalarRow12703.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12703, BstLean.Part268.grid12703, BstLean.Part263.worldGrid]

theorem supplies12703 (j : Fin 43) : Supply 12703 (parameters j)
    (cellLower scalarRow12703.grid (sourceIndex j))
    (cellUpper scalarRow12703.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12703.grid grid_top_bounds12703 j

theorem radii12703 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12703.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12703 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12703 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12703.grid grid_top_bounds12703 j hθ

noncomputable def covarianceInputs12703 :
    BstLean.Part263.CovarianceInputs 12703 scalarRow12703.grid parameters (caps repair12703) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12703 grid_top_bounds12703 repair12703

noncomputable def covarianceEvent12703 : Set (AgFam 12703) :=
  BstLean.Part263.covarianceEvent 12703 scalarRow12703.grid parameters

theorem covarianceEvent12703_measurable : MeasurableSet covarianceEvent12703 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12703_payment :
    (retDist (paperDesignP 12703).toCentres).real
      (agentEv (paperDesignP 12703) covarianceEvent12703)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12703

theorem localCov12703 : BstLean.Part259.LocalCovarianceOn covarianceEvent12703
    (BstLean.Part263.cell scalarRow12703.grid) (caps repair12703) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12703

theorem covarianceGood12703_payment :
    (retDist (paperDesignP 12703).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12703)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12703_payment



end BstLean.Part269.N12703

namespace BstLean.Part269.N12703
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12703}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12703.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12703) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12703).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12703 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12703) (by norm_num) BstLean.Part268.WorldRow12703.worldPackage rfl
    BstLean.Part268.WorldRow12703.product_lower (BstLean.Part268.WorldRow12703.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12703} (hw : c ∈ Hof BstLean.Part268.WorldRow12703.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12703) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12703) (by norm_num) BstLean.Part268.WorldRow12703.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12703} (hw : c ∈ Hof BstLean.Part268.WorldRow12703.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12703) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12703).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12703) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12703_eq : scalarRow12703.targetFrame = BstLean.Part268.agent12703.frame := by
  norm_num [scalarRow12703,BstLean.Part268.agent12703]

noncomputable def frameData12703 : BstLean.Part264b.FrameData 12703 :=
  BstLean.Part269.frameData_from_numerics (n := 12703) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12703.worldPackage rfl BstLean.Part268.WorldRow12703.product_lower (BstLean.Part268.WorldRow12703.producthi.2.trans (by norm_num))
    scalarRow12703 repair12703 covarianceInputs12703 (fun i hi => sourceNumerics12703 hi)
    BstLean.Part268.agent12703.frame targetFrame12703_eq


end BstLean.Part269.N12703

namespace BstLean.Part269.N12704
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12704 : scalarRow12704.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12704, BstLean.Part268.grid12704, BstLean.Part263.worldGrid]

theorem supplies12704 (j : Fin 43) : Supply 12704 (parameters j)
    (cellLower scalarRow12704.grid (sourceIndex j))
    (cellUpper scalarRow12704.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12704.grid grid_top_bounds12704 j

theorem radii12704 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12704.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12704 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12704 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12704.grid grid_top_bounds12704 j hθ

noncomputable def covarianceInputs12704 :
    BstLean.Part263.CovarianceInputs 12704 scalarRow12704.grid parameters (caps repair12704) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12704 grid_top_bounds12704 repair12704

noncomputable def covarianceEvent12704 : Set (AgFam 12704) :=
  BstLean.Part263.covarianceEvent 12704 scalarRow12704.grid parameters

theorem covarianceEvent12704_measurable : MeasurableSet covarianceEvent12704 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12704_payment :
    (retDist (paperDesignP 12704).toCentres).real
      (agentEv (paperDesignP 12704) covarianceEvent12704)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12704

theorem localCov12704 : BstLean.Part259.LocalCovarianceOn covarianceEvent12704
    (BstLean.Part263.cell scalarRow12704.grid) (caps repair12704) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12704

theorem covarianceGood12704_payment :
    (retDist (paperDesignP 12704).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12704)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12704_payment



end BstLean.Part269.N12704

namespace BstLean.Part269.N12704
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12704}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12704.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12704) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12704).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12704 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12704) (by norm_num) BstLean.Part268.WorldRow12704.worldPackage rfl
    BstLean.Part268.WorldRow12704.product_lower (BstLean.Part268.WorldRow12704.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12704} (hw : c ∈ Hof BstLean.Part268.WorldRow12704.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12704) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12704) (by norm_num) BstLean.Part268.WorldRow12704.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12704} (hw : c ∈ Hof BstLean.Part268.WorldRow12704.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12704) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12704).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12704) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12704_eq : scalarRow12704.targetFrame = BstLean.Part268.agent12704.frame := by
  norm_num [scalarRow12704,BstLean.Part268.agent12704]

noncomputable def frameData12704 : BstLean.Part264b.FrameData 12704 :=
  BstLean.Part269.frameData_from_numerics (n := 12704) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12704.worldPackage rfl BstLean.Part268.WorldRow12704.product_lower (BstLean.Part268.WorldRow12704.producthi.2.trans (by norm_num))
    scalarRow12704 repair12704 covarianceInputs12704 (fun i hi => sourceNumerics12704 hi)
    BstLean.Part268.agent12704.frame targetFrame12704_eq


end BstLean.Part269.N12704
