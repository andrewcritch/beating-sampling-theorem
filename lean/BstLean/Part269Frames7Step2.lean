import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World7Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs7
import BstLean.Part269Rows7
import BstLean.Part269Sources7
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12535
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12535 : scalarRow12535.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12535, BstLean.Part268.grid12535, BstLean.Part263.worldGrid]

theorem supplies12535 (j : Fin 43) : Supply 12535 (parameters j)
    (cellLower scalarRow12535.grid (sourceIndex j))
    (cellUpper scalarRow12535.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12535.grid grid_top_bounds12535 j

theorem radii12535 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12535.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12535 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12535 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12535.grid grid_top_bounds12535 j hθ

noncomputable def covarianceInputs12535 :
    BstLean.Part263.CovarianceInputs 12535 scalarRow12535.grid parameters (caps repair12535) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12535 grid_top_bounds12535 repair12535

noncomputable def covarianceEvent12535 : Set (AgFam 12535) :=
  BstLean.Part263.covarianceEvent 12535 scalarRow12535.grid parameters

theorem covarianceEvent12535_measurable : MeasurableSet covarianceEvent12535 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12535_payment :
    (retDist (paperDesignP 12535).toCentres).real
      (agentEv (paperDesignP 12535) covarianceEvent12535)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12535

theorem localCov12535 : BstLean.Part259.LocalCovarianceOn covarianceEvent12535
    (BstLean.Part263.cell scalarRow12535.grid) (caps repair12535) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12535

theorem covarianceGood12535_payment :
    (retDist (paperDesignP 12535).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12535)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12535_payment



end BstLean.Part269.N12535

namespace BstLean.Part269.N12535
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12535}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12535.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12535) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12535).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12535 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12535) (by norm_num) BstLean.Part268.WorldRow12535.worldPackage rfl
    BstLean.Part268.WorldRow12535.product_lower (BstLean.Part268.WorldRow12535.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12535} (hw : c ∈ Hof BstLean.Part268.WorldRow12535.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12535) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12535) (by norm_num) BstLean.Part268.WorldRow12535.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12535} (hw : c ∈ Hof BstLean.Part268.WorldRow12535.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12535) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12535).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12535) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12535_eq : scalarRow12535.targetFrame = BstLean.Part268.agent12535.frame := by
  norm_num [scalarRow12535,BstLean.Part268.agent12535]

noncomputable def frameData12535 : BstLean.Part264b.FrameData 12535 :=
  BstLean.Part269.frameData_from_numerics (n := 12535) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12535.worldPackage rfl BstLean.Part268.WorldRow12535.product_lower (BstLean.Part268.WorldRow12535.producthi.2.trans (by norm_num))
    scalarRow12535 repair12535 covarianceInputs12535 (fun i hi => sourceNumerics12535 hi)
    BstLean.Part268.agent12535.frame targetFrame12535_eq


end BstLean.Part269.N12535

namespace BstLean.Part269.N12536
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12536 : scalarRow12536.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12536, BstLean.Part268.grid12536, BstLean.Part263.worldGrid]

theorem supplies12536 (j : Fin 43) : Supply 12536 (parameters j)
    (cellLower scalarRow12536.grid (sourceIndex j))
    (cellUpper scalarRow12536.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12536.grid grid_top_bounds12536 j

theorem radii12536 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12536.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12536 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12536 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12536.grid grid_top_bounds12536 j hθ

noncomputable def covarianceInputs12536 :
    BstLean.Part263.CovarianceInputs 12536 scalarRow12536.grid parameters (caps repair12536) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12536 grid_top_bounds12536 repair12536

noncomputable def covarianceEvent12536 : Set (AgFam 12536) :=
  BstLean.Part263.covarianceEvent 12536 scalarRow12536.grid parameters

theorem covarianceEvent12536_measurable : MeasurableSet covarianceEvent12536 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12536_payment :
    (retDist (paperDesignP 12536).toCentres).real
      (agentEv (paperDesignP 12536) covarianceEvent12536)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12536

theorem localCov12536 : BstLean.Part259.LocalCovarianceOn covarianceEvent12536
    (BstLean.Part263.cell scalarRow12536.grid) (caps repair12536) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12536

theorem covarianceGood12536_payment :
    (retDist (paperDesignP 12536).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12536)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12536_payment



end BstLean.Part269.N12536

namespace BstLean.Part269.N12536
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12536}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12536.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12536) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12536).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12536 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12536) (by norm_num) BstLean.Part268.WorldRow12536.worldPackage rfl
    BstLean.Part268.WorldRow12536.product_lower (BstLean.Part268.WorldRow12536.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12536} (hw : c ∈ Hof BstLean.Part268.WorldRow12536.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12536) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12536) (by norm_num) BstLean.Part268.WorldRow12536.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12536} (hw : c ∈ Hof BstLean.Part268.WorldRow12536.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12536) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12536).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12536) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12536_eq : scalarRow12536.targetFrame = BstLean.Part268.agent12536.frame := by
  norm_num [scalarRow12536,BstLean.Part268.agent12536]

noncomputable def frameData12536 : BstLean.Part264b.FrameData 12536 :=
  BstLean.Part269.frameData_from_numerics (n := 12536) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12536.worldPackage rfl BstLean.Part268.WorldRow12536.product_lower (BstLean.Part268.WorldRow12536.producthi.2.trans (by norm_num))
    scalarRow12536 repair12536 covarianceInputs12536 (fun i hi => sourceNumerics12536 hi)
    BstLean.Part268.agent12536.frame targetFrame12536_eq


end BstLean.Part269.N12536

namespace BstLean.Part269.N12537
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12537 : scalarRow12537.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12537, BstLean.Part268.grid12537, BstLean.Part263.worldGrid]

theorem supplies12537 (j : Fin 43) : Supply 12537 (parameters j)
    (cellLower scalarRow12537.grid (sourceIndex j))
    (cellUpper scalarRow12537.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12537.grid grid_top_bounds12537 j

theorem radii12537 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12537.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12537 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12537 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12537.grid grid_top_bounds12537 j hθ

noncomputable def covarianceInputs12537 :
    BstLean.Part263.CovarianceInputs 12537 scalarRow12537.grid parameters (caps repair12537) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12537 grid_top_bounds12537 repair12537

noncomputable def covarianceEvent12537 : Set (AgFam 12537) :=
  BstLean.Part263.covarianceEvent 12537 scalarRow12537.grid parameters

theorem covarianceEvent12537_measurable : MeasurableSet covarianceEvent12537 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12537_payment :
    (retDist (paperDesignP 12537).toCentres).real
      (agentEv (paperDesignP 12537) covarianceEvent12537)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12537

theorem localCov12537 : BstLean.Part259.LocalCovarianceOn covarianceEvent12537
    (BstLean.Part263.cell scalarRow12537.grid) (caps repair12537) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12537

theorem covarianceGood12537_payment :
    (retDist (paperDesignP 12537).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12537)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12537_payment



end BstLean.Part269.N12537

namespace BstLean.Part269.N12537
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12537}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12537.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12537) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12537).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12537 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12537) (by norm_num) BstLean.Part268.WorldRow12537.worldPackage rfl
    BstLean.Part268.WorldRow12537.product_lower (BstLean.Part268.WorldRow12537.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12537} (hw : c ∈ Hof BstLean.Part268.WorldRow12537.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12537) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12537) (by norm_num) BstLean.Part268.WorldRow12537.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12537} (hw : c ∈ Hof BstLean.Part268.WorldRow12537.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12537) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12537).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12537) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12537_eq : scalarRow12537.targetFrame = BstLean.Part268.agent12537.frame := by
  norm_num [scalarRow12537,BstLean.Part268.agent12537]

noncomputable def frameData12537 : BstLean.Part264b.FrameData 12537 :=
  BstLean.Part269.frameData_from_numerics (n := 12537) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12537.worldPackage rfl BstLean.Part268.WorldRow12537.product_lower (BstLean.Part268.WorldRow12537.producthi.2.trans (by norm_num))
    scalarRow12537 repair12537 covarianceInputs12537 (fun i hi => sourceNumerics12537 hi)
    BstLean.Part268.agent12537.frame targetFrame12537_eq


end BstLean.Part269.N12537

namespace BstLean.Part269.N12538
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12538 : scalarRow12538.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12538, BstLean.Part268.grid12538, BstLean.Part263.worldGrid]

theorem supplies12538 (j : Fin 43) : Supply 12538 (parameters j)
    (cellLower scalarRow12538.grid (sourceIndex j))
    (cellUpper scalarRow12538.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12538.grid grid_top_bounds12538 j

theorem radii12538 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12538.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12538 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12538 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12538.grid grid_top_bounds12538 j hθ

noncomputable def covarianceInputs12538 :
    BstLean.Part263.CovarianceInputs 12538 scalarRow12538.grid parameters (caps repair12538) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12538 grid_top_bounds12538 repair12538

noncomputable def covarianceEvent12538 : Set (AgFam 12538) :=
  BstLean.Part263.covarianceEvent 12538 scalarRow12538.grid parameters

theorem covarianceEvent12538_measurable : MeasurableSet covarianceEvent12538 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12538_payment :
    (retDist (paperDesignP 12538).toCentres).real
      (agentEv (paperDesignP 12538) covarianceEvent12538)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12538

theorem localCov12538 : BstLean.Part259.LocalCovarianceOn covarianceEvent12538
    (BstLean.Part263.cell scalarRow12538.grid) (caps repair12538) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12538

theorem covarianceGood12538_payment :
    (retDist (paperDesignP 12538).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12538)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12538_payment



end BstLean.Part269.N12538

namespace BstLean.Part269.N12538
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12538}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12538.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12538) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12538).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12538 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12538) (by norm_num) BstLean.Part268.WorldRow12538.worldPackage rfl
    BstLean.Part268.WorldRow12538.product_lower (BstLean.Part268.WorldRow12538.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12538} (hw : c ∈ Hof BstLean.Part268.WorldRow12538.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12538) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12538) (by norm_num) BstLean.Part268.WorldRow12538.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12538} (hw : c ∈ Hof BstLean.Part268.WorldRow12538.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12538) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12538).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12538) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12538_eq : scalarRow12538.targetFrame = BstLean.Part268.agent12538.frame := by
  norm_num [scalarRow12538,BstLean.Part268.agent12538]

noncomputable def frameData12538 : BstLean.Part264b.FrameData 12538 :=
  BstLean.Part269.frameData_from_numerics (n := 12538) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12538.worldPackage rfl BstLean.Part268.WorldRow12538.product_lower (BstLean.Part268.WorldRow12538.producthi.2.trans (by norm_num))
    scalarRow12538 repair12538 covarianceInputs12538 (fun i hi => sourceNumerics12538 hi)
    BstLean.Part268.agent12538.frame targetFrame12538_eq


end BstLean.Part269.N12538

namespace BstLean.Part269.N12539
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12539 : scalarRow12539.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12539, BstLean.Part268.grid12539, BstLean.Part263.worldGrid]

theorem supplies12539 (j : Fin 43) : Supply 12539 (parameters j)
    (cellLower scalarRow12539.grid (sourceIndex j))
    (cellUpper scalarRow12539.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12539.grid grid_top_bounds12539 j

theorem radii12539 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12539.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12539 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12539 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12539.grid grid_top_bounds12539 j hθ

noncomputable def covarianceInputs12539 :
    BstLean.Part263.CovarianceInputs 12539 scalarRow12539.grid parameters (caps repair12539) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12539 grid_top_bounds12539 repair12539

noncomputable def covarianceEvent12539 : Set (AgFam 12539) :=
  BstLean.Part263.covarianceEvent 12539 scalarRow12539.grid parameters

theorem covarianceEvent12539_measurable : MeasurableSet covarianceEvent12539 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12539_payment :
    (retDist (paperDesignP 12539).toCentres).real
      (agentEv (paperDesignP 12539) covarianceEvent12539)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12539

theorem localCov12539 : BstLean.Part259.LocalCovarianceOn covarianceEvent12539
    (BstLean.Part263.cell scalarRow12539.grid) (caps repair12539) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12539

theorem covarianceGood12539_payment :
    (retDist (paperDesignP 12539).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12539)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12539_payment



end BstLean.Part269.N12539

namespace BstLean.Part269.N12539
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12539}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12539.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12539) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12539).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12539 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12539) (by norm_num) BstLean.Part268.WorldRow12539.worldPackage rfl
    BstLean.Part268.WorldRow12539.product_lower (BstLean.Part268.WorldRow12539.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12539} (hw : c ∈ Hof BstLean.Part268.WorldRow12539.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12539) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12539) (by norm_num) BstLean.Part268.WorldRow12539.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12539} (hw : c ∈ Hof BstLean.Part268.WorldRow12539.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12539) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12539).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12539) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12539_eq : scalarRow12539.targetFrame = BstLean.Part268.agent12539.frame := by
  norm_num [scalarRow12539,BstLean.Part268.agent12539]

noncomputable def frameData12539 : BstLean.Part264b.FrameData 12539 :=
  BstLean.Part269.frameData_from_numerics (n := 12539) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12539.worldPackage rfl BstLean.Part268.WorldRow12539.product_lower (BstLean.Part268.WorldRow12539.producthi.2.trans (by norm_num))
    scalarRow12539 repair12539 covarianceInputs12539 (fun i hi => sourceNumerics12539 hi)
    BstLean.Part268.agent12539.frame targetFrame12539_eq


end BstLean.Part269.N12539
