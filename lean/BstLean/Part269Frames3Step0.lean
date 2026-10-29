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

namespace BstLean.Part269.N12425
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12425 : scalarRow12425.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12425, BstLean.Part268.grid12425, BstLean.Part263.worldGrid]

theorem supplies12425 (j : Fin 43) : Supply 12425 (parameters j)
    (cellLower scalarRow12425.grid (sourceIndex j))
    (cellUpper scalarRow12425.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12425.grid grid_top_bounds12425 j

theorem radii12425 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12425.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12425 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12425 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12425.grid grid_top_bounds12425 j hθ

noncomputable def covarianceInputs12425 :
    BstLean.Part263.CovarianceInputs 12425 scalarRow12425.grid parameters (caps repair12425) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12425 grid_top_bounds12425 repair12425

noncomputable def covarianceEvent12425 : Set (AgFam 12425) :=
  BstLean.Part263.covarianceEvent 12425 scalarRow12425.grid parameters

theorem covarianceEvent12425_measurable : MeasurableSet covarianceEvent12425 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12425_payment :
    (retDist (paperDesignP 12425).toCentres).real
      (agentEv (paperDesignP 12425) covarianceEvent12425)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12425

theorem localCov12425 : BstLean.Part259.LocalCovarianceOn covarianceEvent12425
    (BstLean.Part263.cell scalarRow12425.grid) (caps repair12425) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12425

theorem covarianceGood12425_payment :
    (retDist (paperDesignP 12425).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12425)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12425_payment



end BstLean.Part269.N12425

namespace BstLean.Part269.N12425
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12425}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12425.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12425) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12425).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12425 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12425) (by norm_num) BstLean.Part268.WorldRow12425.worldPackage rfl
    BstLean.Part268.WorldRow12425.product_lower (BstLean.Part268.WorldRow12425.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12425} (hw : c ∈ Hof BstLean.Part268.WorldRow12425.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12425) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12425) (by norm_num) BstLean.Part268.WorldRow12425.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12425} (hw : c ∈ Hof BstLean.Part268.WorldRow12425.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12425) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12425).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12425) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12425_eq : scalarRow12425.targetFrame = BstLean.Part268.agent12425.frame := by
  norm_num [scalarRow12425,BstLean.Part268.agent12425]

noncomputable def frameData12425 : BstLean.Part264b.FrameData 12425 :=
  BstLean.Part269.frameData_from_numerics (n := 12425) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12425.worldPackage rfl BstLean.Part268.WorldRow12425.product_lower (BstLean.Part268.WorldRow12425.producthi.2.trans (by norm_num))
    scalarRow12425 repair12425 covarianceInputs12425 (fun i hi => sourceNumerics12425 hi)
    BstLean.Part268.agent12425.frame targetFrame12425_eq


end BstLean.Part269.N12425

namespace BstLean.Part269.N12426
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12426 : scalarRow12426.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12426, BstLean.Part268.grid12426, BstLean.Part263.worldGrid]

theorem supplies12426 (j : Fin 43) : Supply 12426 (parameters j)
    (cellLower scalarRow12426.grid (sourceIndex j))
    (cellUpper scalarRow12426.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12426.grid grid_top_bounds12426 j

theorem radii12426 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12426.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12426 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12426 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12426.grid grid_top_bounds12426 j hθ

noncomputable def covarianceInputs12426 :
    BstLean.Part263.CovarianceInputs 12426 scalarRow12426.grid parameters (caps repair12426) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12426 grid_top_bounds12426 repair12426

noncomputable def covarianceEvent12426 : Set (AgFam 12426) :=
  BstLean.Part263.covarianceEvent 12426 scalarRow12426.grid parameters

theorem covarianceEvent12426_measurable : MeasurableSet covarianceEvent12426 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12426_payment :
    (retDist (paperDesignP 12426).toCentres).real
      (agentEv (paperDesignP 12426) covarianceEvent12426)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12426

theorem localCov12426 : BstLean.Part259.LocalCovarianceOn covarianceEvent12426
    (BstLean.Part263.cell scalarRow12426.grid) (caps repair12426) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12426

theorem covarianceGood12426_payment :
    (retDist (paperDesignP 12426).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12426)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12426_payment



end BstLean.Part269.N12426

namespace BstLean.Part269.N12426
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12426}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12426.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12426) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12426).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12426 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12426) (by norm_num) BstLean.Part268.WorldRow12426.worldPackage rfl
    BstLean.Part268.WorldRow12426.product_lower (BstLean.Part268.WorldRow12426.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12426} (hw : c ∈ Hof BstLean.Part268.WorldRow12426.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12426) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12426) (by norm_num) BstLean.Part268.WorldRow12426.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12426} (hw : c ∈ Hof BstLean.Part268.WorldRow12426.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12426) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12426).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12426) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12426_eq : scalarRow12426.targetFrame = BstLean.Part268.agent12426.frame := by
  norm_num [scalarRow12426,BstLean.Part268.agent12426]

noncomputable def frameData12426 : BstLean.Part264b.FrameData 12426 :=
  BstLean.Part269.frameData_from_numerics (n := 12426) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12426.worldPackage rfl BstLean.Part268.WorldRow12426.product_lower (BstLean.Part268.WorldRow12426.producthi.2.trans (by norm_num))
    scalarRow12426 repair12426 covarianceInputs12426 (fun i hi => sourceNumerics12426 hi)
    BstLean.Part268.agent12426.frame targetFrame12426_eq


end BstLean.Part269.N12426

namespace BstLean.Part269.N12427
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12427 : scalarRow12427.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12427, BstLean.Part268.grid12427, BstLean.Part263.worldGrid]

theorem supplies12427 (j : Fin 43) : Supply 12427 (parameters j)
    (cellLower scalarRow12427.grid (sourceIndex j))
    (cellUpper scalarRow12427.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12427.grid grid_top_bounds12427 j

theorem radii12427 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12427.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12427 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12427 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12427.grid grid_top_bounds12427 j hθ

noncomputable def covarianceInputs12427 :
    BstLean.Part263.CovarianceInputs 12427 scalarRow12427.grid parameters (caps repair12427) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12427 grid_top_bounds12427 repair12427

noncomputable def covarianceEvent12427 : Set (AgFam 12427) :=
  BstLean.Part263.covarianceEvent 12427 scalarRow12427.grid parameters

theorem covarianceEvent12427_measurable : MeasurableSet covarianceEvent12427 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12427_payment :
    (retDist (paperDesignP 12427).toCentres).real
      (agentEv (paperDesignP 12427) covarianceEvent12427)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12427

theorem localCov12427 : BstLean.Part259.LocalCovarianceOn covarianceEvent12427
    (BstLean.Part263.cell scalarRow12427.grid) (caps repair12427) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12427

theorem covarianceGood12427_payment :
    (retDist (paperDesignP 12427).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12427)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12427_payment



end BstLean.Part269.N12427

namespace BstLean.Part269.N12427
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12427}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12427.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12427) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12427).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12427 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12427) (by norm_num) BstLean.Part268.WorldRow12427.worldPackage rfl
    BstLean.Part268.WorldRow12427.product_lower (BstLean.Part268.WorldRow12427.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12427} (hw : c ∈ Hof BstLean.Part268.WorldRow12427.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12427) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12427) (by norm_num) BstLean.Part268.WorldRow12427.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12427} (hw : c ∈ Hof BstLean.Part268.WorldRow12427.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12427) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12427).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12427) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12427_eq : scalarRow12427.targetFrame = BstLean.Part268.agent12427.frame := by
  norm_num [scalarRow12427,BstLean.Part268.agent12427]

noncomputable def frameData12427 : BstLean.Part264b.FrameData 12427 :=
  BstLean.Part269.frameData_from_numerics (n := 12427) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12427.worldPackage rfl BstLean.Part268.WorldRow12427.product_lower (BstLean.Part268.WorldRow12427.producthi.2.trans (by norm_num))
    scalarRow12427 repair12427 covarianceInputs12427 (fun i hi => sourceNumerics12427 hi)
    BstLean.Part268.agent12427.frame targetFrame12427_eq


end BstLean.Part269.N12427

namespace BstLean.Part269.N12428
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12428 : scalarRow12428.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12428, BstLean.Part268.grid12428, BstLean.Part263.worldGrid]

theorem supplies12428 (j : Fin 43) : Supply 12428 (parameters j)
    (cellLower scalarRow12428.grid (sourceIndex j))
    (cellUpper scalarRow12428.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12428.grid grid_top_bounds12428 j

theorem radii12428 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12428.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12428 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12428 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12428.grid grid_top_bounds12428 j hθ

noncomputable def covarianceInputs12428 :
    BstLean.Part263.CovarianceInputs 12428 scalarRow12428.grid parameters (caps repair12428) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12428 grid_top_bounds12428 repair12428

noncomputable def covarianceEvent12428 : Set (AgFam 12428) :=
  BstLean.Part263.covarianceEvent 12428 scalarRow12428.grid parameters

theorem covarianceEvent12428_measurable : MeasurableSet covarianceEvent12428 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12428_payment :
    (retDist (paperDesignP 12428).toCentres).real
      (agentEv (paperDesignP 12428) covarianceEvent12428)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12428

theorem localCov12428 : BstLean.Part259.LocalCovarianceOn covarianceEvent12428
    (BstLean.Part263.cell scalarRow12428.grid) (caps repair12428) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12428

theorem covarianceGood12428_payment :
    (retDist (paperDesignP 12428).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12428)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12428_payment



end BstLean.Part269.N12428

namespace BstLean.Part269.N12428
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12428}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12428.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12428) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12428).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12428 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12428) (by norm_num) BstLean.Part268.WorldRow12428.worldPackage rfl
    BstLean.Part268.WorldRow12428.product_lower (BstLean.Part268.WorldRow12428.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12428} (hw : c ∈ Hof BstLean.Part268.WorldRow12428.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12428) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12428) (by norm_num) BstLean.Part268.WorldRow12428.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12428} (hw : c ∈ Hof BstLean.Part268.WorldRow12428.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12428) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12428).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12428) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12428_eq : scalarRow12428.targetFrame = BstLean.Part268.agent12428.frame := by
  norm_num [scalarRow12428,BstLean.Part268.agent12428]

noncomputable def frameData12428 : BstLean.Part264b.FrameData 12428 :=
  BstLean.Part269.frameData_from_numerics (n := 12428) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12428.worldPackage rfl BstLean.Part268.WorldRow12428.product_lower (BstLean.Part268.WorldRow12428.producthi.2.trans (by norm_num))
    scalarRow12428 repair12428 covarianceInputs12428 (fun i hi => sourceNumerics12428 hi)
    BstLean.Part268.agent12428.frame targetFrame12428_eq


end BstLean.Part269.N12428

namespace BstLean.Part269.N12429
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12429 : scalarRow12429.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12429, BstLean.Part268.grid12429, BstLean.Part263.worldGrid]

theorem supplies12429 (j : Fin 43) : Supply 12429 (parameters j)
    (cellLower scalarRow12429.grid (sourceIndex j))
    (cellUpper scalarRow12429.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12429.grid grid_top_bounds12429 j

theorem radii12429 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12429.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12429 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12429 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12429.grid grid_top_bounds12429 j hθ

noncomputable def covarianceInputs12429 :
    BstLean.Part263.CovarianceInputs 12429 scalarRow12429.grid parameters (caps repair12429) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12429 grid_top_bounds12429 repair12429

noncomputable def covarianceEvent12429 : Set (AgFam 12429) :=
  BstLean.Part263.covarianceEvent 12429 scalarRow12429.grid parameters

theorem covarianceEvent12429_measurable : MeasurableSet covarianceEvent12429 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12429_payment :
    (retDist (paperDesignP 12429).toCentres).real
      (agentEv (paperDesignP 12429) covarianceEvent12429)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12429

theorem localCov12429 : BstLean.Part259.LocalCovarianceOn covarianceEvent12429
    (BstLean.Part263.cell scalarRow12429.grid) (caps repair12429) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12429

theorem covarianceGood12429_payment :
    (retDist (paperDesignP 12429).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12429)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12429_payment



end BstLean.Part269.N12429

namespace BstLean.Part269.N12429
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12429}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12429.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12429) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12429).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12429 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12429) (by norm_num) BstLean.Part268.WorldRow12429.worldPackage rfl
    BstLean.Part268.WorldRow12429.product_lower (BstLean.Part268.WorldRow12429.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12429} (hw : c ∈ Hof BstLean.Part268.WorldRow12429.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12429) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12429) (by norm_num) BstLean.Part268.WorldRow12429.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12429} (hw : c ∈ Hof BstLean.Part268.WorldRow12429.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12429) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12429).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12429) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12429_eq : scalarRow12429.targetFrame = BstLean.Part268.agent12429.frame := by
  norm_num [scalarRow12429,BstLean.Part268.agent12429]

noncomputable def frameData12429 : BstLean.Part264b.FrameData 12429 :=
  BstLean.Part269.frameData_from_numerics (n := 12429) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12429.worldPackage rfl BstLean.Part268.WorldRow12429.product_lower (BstLean.Part268.WorldRow12429.producthi.2.trans (by norm_num))
    scalarRow12429 repair12429 covarianceInputs12429 (fun i hi => sourceNumerics12429 hi)
    BstLean.Part268.agent12429.frame targetFrame12429_eq


end BstLean.Part269.N12429
