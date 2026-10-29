import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World2Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs2
import BstLean.Part269Rows2
import BstLean.Part269Sources2
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12420
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12420 : scalarRow12420.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12420, BstLean.Part268.grid12420, BstLean.Part263.worldGrid]

theorem supplies12420 (j : Fin 43) : Supply 12420 (parameters j)
    (cellLower scalarRow12420.grid (sourceIndex j))
    (cellUpper scalarRow12420.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12420.grid grid_top_bounds12420 j

theorem radii12420 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12420.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12420 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12420 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12420.grid grid_top_bounds12420 j hθ

noncomputable def covarianceInputs12420 :
    BstLean.Part263.CovarianceInputs 12420 scalarRow12420.grid parameters (caps repair12420) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12420 grid_top_bounds12420 repair12420

noncomputable def covarianceEvent12420 : Set (AgFam 12420) :=
  BstLean.Part263.covarianceEvent 12420 scalarRow12420.grid parameters

theorem covarianceEvent12420_measurable : MeasurableSet covarianceEvent12420 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12420_payment :
    (retDist (paperDesignP 12420).toCentres).real
      (agentEv (paperDesignP 12420) covarianceEvent12420)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12420

theorem localCov12420 : BstLean.Part259.LocalCovarianceOn covarianceEvent12420
    (BstLean.Part263.cell scalarRow12420.grid) (caps repair12420) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12420

theorem covarianceGood12420_payment :
    (retDist (paperDesignP 12420).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12420)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12420_payment



end BstLean.Part269.N12420

namespace BstLean.Part269.N12420
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12420}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12420.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12420) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12420).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12420 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12420) (by norm_num) BstLean.Part268.WorldRow12420.worldPackage rfl
    BstLean.Part268.WorldRow12420.product_lower (BstLean.Part268.WorldRow12420.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12420} (hw : c ∈ Hof BstLean.Part268.WorldRow12420.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12420) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12420) (by norm_num) BstLean.Part268.WorldRow12420.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12420} (hw : c ∈ Hof BstLean.Part268.WorldRow12420.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12420) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12420).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12420) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12420_eq : scalarRow12420.targetFrame = BstLean.Part268.agent12420.frame := by
  norm_num [scalarRow12420,BstLean.Part268.agent12420]

noncomputable def frameData12420 : BstLean.Part264b.FrameData 12420 :=
  BstLean.Part269.frameData_from_numerics (n := 12420) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12420.worldPackage rfl BstLean.Part268.WorldRow12420.product_lower (BstLean.Part268.WorldRow12420.producthi.2.trans (by norm_num))
    scalarRow12420 repair12420 covarianceInputs12420 (fun i hi => sourceNumerics12420 hi)
    BstLean.Part268.agent12420.frame targetFrame12420_eq


end BstLean.Part269.N12420

namespace BstLean.Part269.N12421
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12421 : scalarRow12421.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12421, BstLean.Part268.grid12421, BstLean.Part263.worldGrid]

theorem supplies12421 (j : Fin 43) : Supply 12421 (parameters j)
    (cellLower scalarRow12421.grid (sourceIndex j))
    (cellUpper scalarRow12421.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12421.grid grid_top_bounds12421 j

theorem radii12421 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12421.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12421 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12421 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12421.grid grid_top_bounds12421 j hθ

noncomputable def covarianceInputs12421 :
    BstLean.Part263.CovarianceInputs 12421 scalarRow12421.grid parameters (caps repair12421) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12421 grid_top_bounds12421 repair12421

noncomputable def covarianceEvent12421 : Set (AgFam 12421) :=
  BstLean.Part263.covarianceEvent 12421 scalarRow12421.grid parameters

theorem covarianceEvent12421_measurable : MeasurableSet covarianceEvent12421 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12421_payment :
    (retDist (paperDesignP 12421).toCentres).real
      (agentEv (paperDesignP 12421) covarianceEvent12421)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12421

theorem localCov12421 : BstLean.Part259.LocalCovarianceOn covarianceEvent12421
    (BstLean.Part263.cell scalarRow12421.grid) (caps repair12421) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12421

theorem covarianceGood12421_payment :
    (retDist (paperDesignP 12421).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12421)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12421_payment



end BstLean.Part269.N12421

namespace BstLean.Part269.N12421
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12421}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12421.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12421) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12421).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12421 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12421) (by norm_num) BstLean.Part268.WorldRow12421.worldPackage rfl
    BstLean.Part268.WorldRow12421.product_lower (BstLean.Part268.WorldRow12421.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12421} (hw : c ∈ Hof BstLean.Part268.WorldRow12421.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12421) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12421) (by norm_num) BstLean.Part268.WorldRow12421.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12421} (hw : c ∈ Hof BstLean.Part268.WorldRow12421.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12421) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12421).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12421) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12421_eq : scalarRow12421.targetFrame = BstLean.Part268.agent12421.frame := by
  norm_num [scalarRow12421,BstLean.Part268.agent12421]

noncomputable def frameData12421 : BstLean.Part264b.FrameData 12421 :=
  BstLean.Part269.frameData_from_numerics (n := 12421) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12421.worldPackage rfl BstLean.Part268.WorldRow12421.product_lower (BstLean.Part268.WorldRow12421.producthi.2.trans (by norm_num))
    scalarRow12421 repair12421 covarianceInputs12421 (fun i hi => sourceNumerics12421 hi)
    BstLean.Part268.agent12421.frame targetFrame12421_eq


end BstLean.Part269.N12421

namespace BstLean.Part269.N12422
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12422 : scalarRow12422.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12422, BstLean.Part268.grid12422, BstLean.Part263.worldGrid]

theorem supplies12422 (j : Fin 43) : Supply 12422 (parameters j)
    (cellLower scalarRow12422.grid (sourceIndex j))
    (cellUpper scalarRow12422.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12422.grid grid_top_bounds12422 j

theorem radii12422 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12422.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12422 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12422 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12422.grid grid_top_bounds12422 j hθ

noncomputable def covarianceInputs12422 :
    BstLean.Part263.CovarianceInputs 12422 scalarRow12422.grid parameters (caps repair12422) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12422 grid_top_bounds12422 repair12422

noncomputable def covarianceEvent12422 : Set (AgFam 12422) :=
  BstLean.Part263.covarianceEvent 12422 scalarRow12422.grid parameters

theorem covarianceEvent12422_measurable : MeasurableSet covarianceEvent12422 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12422_payment :
    (retDist (paperDesignP 12422).toCentres).real
      (agentEv (paperDesignP 12422) covarianceEvent12422)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12422

theorem localCov12422 : BstLean.Part259.LocalCovarianceOn covarianceEvent12422
    (BstLean.Part263.cell scalarRow12422.grid) (caps repair12422) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12422

theorem covarianceGood12422_payment :
    (retDist (paperDesignP 12422).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12422)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12422_payment



end BstLean.Part269.N12422

namespace BstLean.Part269.N12422
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12422}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12422.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12422) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12422).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12422 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12422) (by norm_num) BstLean.Part268.WorldRow12422.worldPackage rfl
    BstLean.Part268.WorldRow12422.product_lower (BstLean.Part268.WorldRow12422.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12422} (hw : c ∈ Hof BstLean.Part268.WorldRow12422.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12422) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12422) (by norm_num) BstLean.Part268.WorldRow12422.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12422} (hw : c ∈ Hof BstLean.Part268.WorldRow12422.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12422) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12422).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12422) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12422_eq : scalarRow12422.targetFrame = BstLean.Part268.agent12422.frame := by
  norm_num [scalarRow12422,BstLean.Part268.agent12422]

noncomputable def frameData12422 : BstLean.Part264b.FrameData 12422 :=
  BstLean.Part269.frameData_from_numerics (n := 12422) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12422.worldPackage rfl BstLean.Part268.WorldRow12422.product_lower (BstLean.Part268.WorldRow12422.producthi.2.trans (by norm_num))
    scalarRow12422 repair12422 covarianceInputs12422 (fun i hi => sourceNumerics12422 hi)
    BstLean.Part268.agent12422.frame targetFrame12422_eq


end BstLean.Part269.N12422

namespace BstLean.Part269.N12423
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12423 : scalarRow12423.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12423, BstLean.Part268.grid12423, BstLean.Part263.worldGrid]

theorem supplies12423 (j : Fin 43) : Supply 12423 (parameters j)
    (cellLower scalarRow12423.grid (sourceIndex j))
    (cellUpper scalarRow12423.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12423.grid grid_top_bounds12423 j

theorem radii12423 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12423.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12423 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12423 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12423.grid grid_top_bounds12423 j hθ

noncomputable def covarianceInputs12423 :
    BstLean.Part263.CovarianceInputs 12423 scalarRow12423.grid parameters (caps repair12423) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12423 grid_top_bounds12423 repair12423

noncomputable def covarianceEvent12423 : Set (AgFam 12423) :=
  BstLean.Part263.covarianceEvent 12423 scalarRow12423.grid parameters

theorem covarianceEvent12423_measurable : MeasurableSet covarianceEvent12423 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12423_payment :
    (retDist (paperDesignP 12423).toCentres).real
      (agentEv (paperDesignP 12423) covarianceEvent12423)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12423

theorem localCov12423 : BstLean.Part259.LocalCovarianceOn covarianceEvent12423
    (BstLean.Part263.cell scalarRow12423.grid) (caps repair12423) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12423

theorem covarianceGood12423_payment :
    (retDist (paperDesignP 12423).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12423)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12423_payment



end BstLean.Part269.N12423

namespace BstLean.Part269.N12423
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12423}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12423.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12423) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12423).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12423 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12423) (by norm_num) BstLean.Part268.WorldRow12423.worldPackage rfl
    BstLean.Part268.WorldRow12423.product_lower (BstLean.Part268.WorldRow12423.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12423} (hw : c ∈ Hof BstLean.Part268.WorldRow12423.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12423) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12423) (by norm_num) BstLean.Part268.WorldRow12423.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12423} (hw : c ∈ Hof BstLean.Part268.WorldRow12423.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12423) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12423).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12423) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12423_eq : scalarRow12423.targetFrame = BstLean.Part268.agent12423.frame := by
  norm_num [scalarRow12423,BstLean.Part268.agent12423]

noncomputable def frameData12423 : BstLean.Part264b.FrameData 12423 :=
  BstLean.Part269.frameData_from_numerics (n := 12423) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12423.worldPackage rfl BstLean.Part268.WorldRow12423.product_lower (BstLean.Part268.WorldRow12423.producthi.2.trans (by norm_num))
    scalarRow12423 repair12423 covarianceInputs12423 (fun i hi => sourceNumerics12423 hi)
    BstLean.Part268.agent12423.frame targetFrame12423_eq


end BstLean.Part269.N12423

namespace BstLean.Part269.N12424
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12424 : scalarRow12424.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12424, BstLean.Part268.grid12424, BstLean.Part263.worldGrid]

theorem supplies12424 (j : Fin 43) : Supply 12424 (parameters j)
    (cellLower scalarRow12424.grid (sourceIndex j))
    (cellUpper scalarRow12424.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12424.grid grid_top_bounds12424 j

theorem radii12424 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12424.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12424 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12424 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12424.grid grid_top_bounds12424 j hθ

noncomputable def covarianceInputs12424 :
    BstLean.Part263.CovarianceInputs 12424 scalarRow12424.grid parameters (caps repair12424) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12424 grid_top_bounds12424 repair12424

noncomputable def covarianceEvent12424 : Set (AgFam 12424) :=
  BstLean.Part263.covarianceEvent 12424 scalarRow12424.grid parameters

theorem covarianceEvent12424_measurable : MeasurableSet covarianceEvent12424 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12424_payment :
    (retDist (paperDesignP 12424).toCentres).real
      (agentEv (paperDesignP 12424) covarianceEvent12424)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12424

theorem localCov12424 : BstLean.Part259.LocalCovarianceOn covarianceEvent12424
    (BstLean.Part263.cell scalarRow12424.grid) (caps repair12424) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12424

theorem covarianceGood12424_payment :
    (retDist (paperDesignP 12424).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12424)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12424_payment



end BstLean.Part269.N12424

namespace BstLean.Part269.N12424
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12424}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12424.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12424) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12424).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12424 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12424) (by norm_num) BstLean.Part268.WorldRow12424.worldPackage rfl
    BstLean.Part268.WorldRow12424.product_lower (BstLean.Part268.WorldRow12424.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12424} (hw : c ∈ Hof BstLean.Part268.WorldRow12424.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12424) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12424) (by norm_num) BstLean.Part268.WorldRow12424.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12424} (hw : c ∈ Hof BstLean.Part268.WorldRow12424.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12424) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12424).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12424) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12424_eq : scalarRow12424.targetFrame = BstLean.Part268.agent12424.frame := by
  norm_num [scalarRow12424,BstLean.Part268.agent12424]

noncomputable def frameData12424 : BstLean.Part264b.FrameData 12424 :=
  BstLean.Part269.frameData_from_numerics (n := 12424) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12424.worldPackage rfl BstLean.Part268.WorldRow12424.product_lower (BstLean.Part268.WorldRow12424.producthi.2.trans (by norm_num))
    scalarRow12424 repair12424 covarianceInputs12424 (fun i hi => sourceNumerics12424 hi)
    BstLean.Part268.agent12424.frame targetFrame12424_eq


end BstLean.Part269.N12424
