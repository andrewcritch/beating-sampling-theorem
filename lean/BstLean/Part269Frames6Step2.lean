import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World6Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs6
import BstLean.Part269Rows6
import BstLean.Part269Sources6
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12510
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12510 : scalarRow12510.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12510, BstLean.Part268.grid12510, BstLean.Part263.worldGrid]

theorem supplies12510 (j : Fin 43) : Supply 12510 (parameters j)
    (cellLower scalarRow12510.grid (sourceIndex j))
    (cellUpper scalarRow12510.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12510.grid grid_top_bounds12510 j

theorem radii12510 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12510.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12510 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12510 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12510.grid grid_top_bounds12510 j hθ

noncomputable def covarianceInputs12510 :
    BstLean.Part263.CovarianceInputs 12510 scalarRow12510.grid parameters (caps repair12510) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12510 grid_top_bounds12510 repair12510

noncomputable def covarianceEvent12510 : Set (AgFam 12510) :=
  BstLean.Part263.covarianceEvent 12510 scalarRow12510.grid parameters

theorem covarianceEvent12510_measurable : MeasurableSet covarianceEvent12510 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12510_payment :
    (retDist (paperDesignP 12510).toCentres).real
      (agentEv (paperDesignP 12510) covarianceEvent12510)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12510

theorem localCov12510 : BstLean.Part259.LocalCovarianceOn covarianceEvent12510
    (BstLean.Part263.cell scalarRow12510.grid) (caps repair12510) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12510

theorem covarianceGood12510_payment :
    (retDist (paperDesignP 12510).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12510)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12510_payment



end BstLean.Part269.N12510

namespace BstLean.Part269.N12510
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12510}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12510.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12510) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12510).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12510 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12510) (by norm_num) BstLean.Part268.WorldRow12510.worldPackage rfl
    BstLean.Part268.WorldRow12510.product_lower (BstLean.Part268.WorldRow12510.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12510} (hw : c ∈ Hof BstLean.Part268.WorldRow12510.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12510) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12510) (by norm_num) BstLean.Part268.WorldRow12510.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12510} (hw : c ∈ Hof BstLean.Part268.WorldRow12510.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12510) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12510).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12510) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12510_eq : scalarRow12510.targetFrame = BstLean.Part268.agent12510.frame := by
  norm_num [scalarRow12510,BstLean.Part268.agent12510]

noncomputable def frameData12510 : BstLean.Part264b.FrameData 12510 :=
  BstLean.Part269.frameData_from_numerics (n := 12510) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12510.worldPackage rfl BstLean.Part268.WorldRow12510.product_lower (BstLean.Part268.WorldRow12510.producthi.2.trans (by norm_num))
    scalarRow12510 repair12510 covarianceInputs12510 (fun i hi => sourceNumerics12510 hi)
    BstLean.Part268.agent12510.frame targetFrame12510_eq


end BstLean.Part269.N12510

namespace BstLean.Part269.N12511
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12511 : scalarRow12511.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12511, BstLean.Part268.grid12511, BstLean.Part263.worldGrid]

theorem supplies12511 (j : Fin 43) : Supply 12511 (parameters j)
    (cellLower scalarRow12511.grid (sourceIndex j))
    (cellUpper scalarRow12511.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12511.grid grid_top_bounds12511 j

theorem radii12511 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12511.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12511 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12511 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12511.grid grid_top_bounds12511 j hθ

noncomputable def covarianceInputs12511 :
    BstLean.Part263.CovarianceInputs 12511 scalarRow12511.grid parameters (caps repair12511) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12511 grid_top_bounds12511 repair12511

noncomputable def covarianceEvent12511 : Set (AgFam 12511) :=
  BstLean.Part263.covarianceEvent 12511 scalarRow12511.grid parameters

theorem covarianceEvent12511_measurable : MeasurableSet covarianceEvent12511 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12511_payment :
    (retDist (paperDesignP 12511).toCentres).real
      (agentEv (paperDesignP 12511) covarianceEvent12511)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12511

theorem localCov12511 : BstLean.Part259.LocalCovarianceOn covarianceEvent12511
    (BstLean.Part263.cell scalarRow12511.grid) (caps repair12511) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12511

theorem covarianceGood12511_payment :
    (retDist (paperDesignP 12511).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12511)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12511_payment



end BstLean.Part269.N12511

namespace BstLean.Part269.N12511
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12511}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12511.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12511) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12511).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12511 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12511) (by norm_num) BstLean.Part268.WorldRow12511.worldPackage rfl
    BstLean.Part268.WorldRow12511.product_lower (BstLean.Part268.WorldRow12511.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12511} (hw : c ∈ Hof BstLean.Part268.WorldRow12511.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12511) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12511) (by norm_num) BstLean.Part268.WorldRow12511.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12511} (hw : c ∈ Hof BstLean.Part268.WorldRow12511.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12511) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12511).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12511) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12511_eq : scalarRow12511.targetFrame = BstLean.Part268.agent12511.frame := by
  norm_num [scalarRow12511,BstLean.Part268.agent12511]

noncomputable def frameData12511 : BstLean.Part264b.FrameData 12511 :=
  BstLean.Part269.frameData_from_numerics (n := 12511) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12511.worldPackage rfl BstLean.Part268.WorldRow12511.product_lower (BstLean.Part268.WorldRow12511.producthi.2.trans (by norm_num))
    scalarRow12511 repair12511 covarianceInputs12511 (fun i hi => sourceNumerics12511 hi)
    BstLean.Part268.agent12511.frame targetFrame12511_eq


end BstLean.Part269.N12511

namespace BstLean.Part269.N12512
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12512 : scalarRow12512.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12512, BstLean.Part268.grid12512, BstLean.Part263.worldGrid]

theorem supplies12512 (j : Fin 43) : Supply 12512 (parameters j)
    (cellLower scalarRow12512.grid (sourceIndex j))
    (cellUpper scalarRow12512.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12512.grid grid_top_bounds12512 j

theorem radii12512 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12512.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12512 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12512 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12512.grid grid_top_bounds12512 j hθ

noncomputable def covarianceInputs12512 :
    BstLean.Part263.CovarianceInputs 12512 scalarRow12512.grid parameters (caps repair12512) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12512 grid_top_bounds12512 repair12512

noncomputable def covarianceEvent12512 : Set (AgFam 12512) :=
  BstLean.Part263.covarianceEvent 12512 scalarRow12512.grid parameters

theorem covarianceEvent12512_measurable : MeasurableSet covarianceEvent12512 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12512_payment :
    (retDist (paperDesignP 12512).toCentres).real
      (agentEv (paperDesignP 12512) covarianceEvent12512)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12512

theorem localCov12512 : BstLean.Part259.LocalCovarianceOn covarianceEvent12512
    (BstLean.Part263.cell scalarRow12512.grid) (caps repair12512) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12512

theorem covarianceGood12512_payment :
    (retDist (paperDesignP 12512).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12512)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12512_payment



end BstLean.Part269.N12512

namespace BstLean.Part269.N12512
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12512}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12512.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12512) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12512).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12512 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12512) (by norm_num) BstLean.Part268.WorldRow12512.worldPackage rfl
    BstLean.Part268.WorldRow12512.product_lower (BstLean.Part268.WorldRow12512.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12512} (hw : c ∈ Hof BstLean.Part268.WorldRow12512.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12512) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12512) (by norm_num) BstLean.Part268.WorldRow12512.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12512} (hw : c ∈ Hof BstLean.Part268.WorldRow12512.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12512) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12512).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12512) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12512_eq : scalarRow12512.targetFrame = BstLean.Part268.agent12512.frame := by
  norm_num [scalarRow12512,BstLean.Part268.agent12512]

noncomputable def frameData12512 : BstLean.Part264b.FrameData 12512 :=
  BstLean.Part269.frameData_from_numerics (n := 12512) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12512.worldPackage rfl BstLean.Part268.WorldRow12512.product_lower (BstLean.Part268.WorldRow12512.producthi.2.trans (by norm_num))
    scalarRow12512 repair12512 covarianceInputs12512 (fun i hi => sourceNumerics12512 hi)
    BstLean.Part268.agent12512.frame targetFrame12512_eq


end BstLean.Part269.N12512

namespace BstLean.Part269.N12513
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12513 : scalarRow12513.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12513, BstLean.Part268.grid12513, BstLean.Part263.worldGrid]

theorem supplies12513 (j : Fin 43) : Supply 12513 (parameters j)
    (cellLower scalarRow12513.grid (sourceIndex j))
    (cellUpper scalarRow12513.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12513.grid grid_top_bounds12513 j

theorem radii12513 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12513.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12513 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12513 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12513.grid grid_top_bounds12513 j hθ

noncomputable def covarianceInputs12513 :
    BstLean.Part263.CovarianceInputs 12513 scalarRow12513.grid parameters (caps repair12513) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12513 grid_top_bounds12513 repair12513

noncomputable def covarianceEvent12513 : Set (AgFam 12513) :=
  BstLean.Part263.covarianceEvent 12513 scalarRow12513.grid parameters

theorem covarianceEvent12513_measurable : MeasurableSet covarianceEvent12513 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12513_payment :
    (retDist (paperDesignP 12513).toCentres).real
      (agentEv (paperDesignP 12513) covarianceEvent12513)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12513

theorem localCov12513 : BstLean.Part259.LocalCovarianceOn covarianceEvent12513
    (BstLean.Part263.cell scalarRow12513.grid) (caps repair12513) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12513

theorem covarianceGood12513_payment :
    (retDist (paperDesignP 12513).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12513)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12513_payment



end BstLean.Part269.N12513

namespace BstLean.Part269.N12513
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12513}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12513.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12513) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12513).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12513 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12513) (by norm_num) BstLean.Part268.WorldRow12513.worldPackage rfl
    BstLean.Part268.WorldRow12513.product_lower (BstLean.Part268.WorldRow12513.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12513} (hw : c ∈ Hof BstLean.Part268.WorldRow12513.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12513) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12513) (by norm_num) BstLean.Part268.WorldRow12513.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12513} (hw : c ∈ Hof BstLean.Part268.WorldRow12513.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12513) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12513).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12513) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12513_eq : scalarRow12513.targetFrame = BstLean.Part268.agent12513.frame := by
  norm_num [scalarRow12513,BstLean.Part268.agent12513]

noncomputable def frameData12513 : BstLean.Part264b.FrameData 12513 :=
  BstLean.Part269.frameData_from_numerics (n := 12513) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12513.worldPackage rfl BstLean.Part268.WorldRow12513.product_lower (BstLean.Part268.WorldRow12513.producthi.2.trans (by norm_num))
    scalarRow12513 repair12513 covarianceInputs12513 (fun i hi => sourceNumerics12513 hi)
    BstLean.Part268.agent12513.frame targetFrame12513_eq


end BstLean.Part269.N12513

namespace BstLean.Part269.N12514
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12514 : scalarRow12514.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12514, BstLean.Part268.grid12514, BstLean.Part263.worldGrid]

theorem supplies12514 (j : Fin 43) : Supply 12514 (parameters j)
    (cellLower scalarRow12514.grid (sourceIndex j))
    (cellUpper scalarRow12514.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12514.grid grid_top_bounds12514 j

theorem radii12514 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12514.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12514 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12514 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12514.grid grid_top_bounds12514 j hθ

noncomputable def covarianceInputs12514 :
    BstLean.Part263.CovarianceInputs 12514 scalarRow12514.grid parameters (caps repair12514) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12514 grid_top_bounds12514 repair12514

noncomputable def covarianceEvent12514 : Set (AgFam 12514) :=
  BstLean.Part263.covarianceEvent 12514 scalarRow12514.grid parameters

theorem covarianceEvent12514_measurable : MeasurableSet covarianceEvent12514 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12514_payment :
    (retDist (paperDesignP 12514).toCentres).real
      (agentEv (paperDesignP 12514) covarianceEvent12514)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12514

theorem localCov12514 : BstLean.Part259.LocalCovarianceOn covarianceEvent12514
    (BstLean.Part263.cell scalarRow12514.grid) (caps repair12514) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12514

theorem covarianceGood12514_payment :
    (retDist (paperDesignP 12514).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12514)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12514_payment



end BstLean.Part269.N12514

namespace BstLean.Part269.N12514
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12514}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12514.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12514) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12514).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12514 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12514) (by norm_num) BstLean.Part268.WorldRow12514.worldPackage rfl
    BstLean.Part268.WorldRow12514.product_lower (BstLean.Part268.WorldRow12514.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12514} (hw : c ∈ Hof BstLean.Part268.WorldRow12514.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12514) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12514) (by norm_num) BstLean.Part268.WorldRow12514.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12514} (hw : c ∈ Hof BstLean.Part268.WorldRow12514.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12514) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12514).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12514) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12514_eq : scalarRow12514.targetFrame = BstLean.Part268.agent12514.frame := by
  norm_num [scalarRow12514,BstLean.Part268.agent12514]

noncomputable def frameData12514 : BstLean.Part264b.FrameData 12514 :=
  BstLean.Part269.frameData_from_numerics (n := 12514) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12514.worldPackage rfl BstLean.Part268.WorldRow12514.product_lower (BstLean.Part268.WorldRow12514.producthi.2.trans (by norm_num))
    scalarRow12514 repair12514 covarianceInputs12514 (fun i hi => sourceNumerics12514 hi)
    BstLean.Part268.agent12514.frame targetFrame12514_eq


end BstLean.Part269.N12514
