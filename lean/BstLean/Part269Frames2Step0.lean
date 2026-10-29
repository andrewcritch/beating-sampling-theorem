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

namespace BstLean.Part269.N12400
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12400 : scalarRow12400.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12400, BstLean.Part268.grid12400, BstLean.Part263.worldGrid]

theorem supplies12400 (j : Fin 43) : Supply 12400 (parameters j)
    (cellLower scalarRow12400.grid (sourceIndex j))
    (cellUpper scalarRow12400.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12400.grid grid_top_bounds12400 j

theorem radii12400 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12400.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12400 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12400 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12400.grid grid_top_bounds12400 j hθ

noncomputable def covarianceInputs12400 :
    BstLean.Part263.CovarianceInputs 12400 scalarRow12400.grid parameters (caps repair12400) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12400 grid_top_bounds12400 repair12400

noncomputable def covarianceEvent12400 : Set (AgFam 12400) :=
  BstLean.Part263.covarianceEvent 12400 scalarRow12400.grid parameters

theorem covarianceEvent12400_measurable : MeasurableSet covarianceEvent12400 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12400_payment :
    (retDist (paperDesignP 12400).toCentres).real
      (agentEv (paperDesignP 12400) covarianceEvent12400)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12400

theorem localCov12400 : BstLean.Part259.LocalCovarianceOn covarianceEvent12400
    (BstLean.Part263.cell scalarRow12400.grid) (caps repair12400) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12400

theorem covarianceGood12400_payment :
    (retDist (paperDesignP 12400).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12400)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12400_payment



end BstLean.Part269.N12400

namespace BstLean.Part269.N12400
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12400}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12400.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12400) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12400).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12400 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12400) (by norm_num) BstLean.Part268.WorldRow12400.worldPackage rfl
    BstLean.Part268.WorldRow12400.product_lower (BstLean.Part268.WorldRow12400.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12400} (hw : c ∈ Hof BstLean.Part268.WorldRow12400.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12400) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12400) (by norm_num) BstLean.Part268.WorldRow12400.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12400} (hw : c ∈ Hof BstLean.Part268.WorldRow12400.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12400) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12400).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12400) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12400_eq : scalarRow12400.targetFrame = BstLean.Part268.agent12400.frame := by
  norm_num [scalarRow12400,BstLean.Part268.agent12400]

noncomputable def frameData12400 : BstLean.Part264b.FrameData 12400 :=
  BstLean.Part269.frameData_from_numerics (n := 12400) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12400.worldPackage rfl BstLean.Part268.WorldRow12400.product_lower (BstLean.Part268.WorldRow12400.producthi.2.trans (by norm_num))
    scalarRow12400 repair12400 covarianceInputs12400 (fun i hi => sourceNumerics12400 hi)
    BstLean.Part268.agent12400.frame targetFrame12400_eq


end BstLean.Part269.N12400

namespace BstLean.Part269.N12401
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12401 : scalarRow12401.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12401, BstLean.Part268.grid12401, BstLean.Part263.worldGrid]

theorem supplies12401 (j : Fin 43) : Supply 12401 (parameters j)
    (cellLower scalarRow12401.grid (sourceIndex j))
    (cellUpper scalarRow12401.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12401.grid grid_top_bounds12401 j

theorem radii12401 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12401.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12401 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12401 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12401.grid grid_top_bounds12401 j hθ

noncomputable def covarianceInputs12401 :
    BstLean.Part263.CovarianceInputs 12401 scalarRow12401.grid parameters (caps repair12401) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12401 grid_top_bounds12401 repair12401

noncomputable def covarianceEvent12401 : Set (AgFam 12401) :=
  BstLean.Part263.covarianceEvent 12401 scalarRow12401.grid parameters

theorem covarianceEvent12401_measurable : MeasurableSet covarianceEvent12401 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12401_payment :
    (retDist (paperDesignP 12401).toCentres).real
      (agentEv (paperDesignP 12401) covarianceEvent12401)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12401

theorem localCov12401 : BstLean.Part259.LocalCovarianceOn covarianceEvent12401
    (BstLean.Part263.cell scalarRow12401.grid) (caps repair12401) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12401

theorem covarianceGood12401_payment :
    (retDist (paperDesignP 12401).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12401)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12401_payment



end BstLean.Part269.N12401

namespace BstLean.Part269.N12401
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12401}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12401.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12401) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12401).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12401 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12401) (by norm_num) BstLean.Part268.WorldRow12401.worldPackage rfl
    BstLean.Part268.WorldRow12401.product_lower (BstLean.Part268.WorldRow12401.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12401} (hw : c ∈ Hof BstLean.Part268.WorldRow12401.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12401) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12401) (by norm_num) BstLean.Part268.WorldRow12401.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12401} (hw : c ∈ Hof BstLean.Part268.WorldRow12401.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12401) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12401).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12401) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12401_eq : scalarRow12401.targetFrame = BstLean.Part268.agent12401.frame := by
  norm_num [scalarRow12401,BstLean.Part268.agent12401]

noncomputable def frameData12401 : BstLean.Part264b.FrameData 12401 :=
  BstLean.Part269.frameData_from_numerics (n := 12401) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12401.worldPackage rfl BstLean.Part268.WorldRow12401.product_lower (BstLean.Part268.WorldRow12401.producthi.2.trans (by norm_num))
    scalarRow12401 repair12401 covarianceInputs12401 (fun i hi => sourceNumerics12401 hi)
    BstLean.Part268.agent12401.frame targetFrame12401_eq


end BstLean.Part269.N12401

namespace BstLean.Part269.N12402
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12402 : scalarRow12402.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12402, BstLean.Part268.grid12402, BstLean.Part263.worldGrid]

theorem supplies12402 (j : Fin 43) : Supply 12402 (parameters j)
    (cellLower scalarRow12402.grid (sourceIndex j))
    (cellUpper scalarRow12402.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12402.grid grid_top_bounds12402 j

theorem radii12402 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12402.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12402 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12402 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12402.grid grid_top_bounds12402 j hθ

noncomputable def covarianceInputs12402 :
    BstLean.Part263.CovarianceInputs 12402 scalarRow12402.grid parameters (caps repair12402) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12402 grid_top_bounds12402 repair12402

noncomputable def covarianceEvent12402 : Set (AgFam 12402) :=
  BstLean.Part263.covarianceEvent 12402 scalarRow12402.grid parameters

theorem covarianceEvent12402_measurable : MeasurableSet covarianceEvent12402 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12402_payment :
    (retDist (paperDesignP 12402).toCentres).real
      (agentEv (paperDesignP 12402) covarianceEvent12402)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12402

theorem localCov12402 : BstLean.Part259.LocalCovarianceOn covarianceEvent12402
    (BstLean.Part263.cell scalarRow12402.grid) (caps repair12402) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12402

theorem covarianceGood12402_payment :
    (retDist (paperDesignP 12402).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12402)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12402_payment



end BstLean.Part269.N12402

namespace BstLean.Part269.N12402
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12402}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12402.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12402) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12402).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12402 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12402) (by norm_num) BstLean.Part268.WorldRow12402.worldPackage rfl
    BstLean.Part268.WorldRow12402.product_lower (BstLean.Part268.WorldRow12402.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12402} (hw : c ∈ Hof BstLean.Part268.WorldRow12402.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12402) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12402) (by norm_num) BstLean.Part268.WorldRow12402.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12402} (hw : c ∈ Hof BstLean.Part268.WorldRow12402.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12402) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12402).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12402) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12402_eq : scalarRow12402.targetFrame = BstLean.Part268.agent12402.frame := by
  norm_num [scalarRow12402,BstLean.Part268.agent12402]

noncomputable def frameData12402 : BstLean.Part264b.FrameData 12402 :=
  BstLean.Part269.frameData_from_numerics (n := 12402) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12402.worldPackage rfl BstLean.Part268.WorldRow12402.product_lower (BstLean.Part268.WorldRow12402.producthi.2.trans (by norm_num))
    scalarRow12402 repair12402 covarianceInputs12402 (fun i hi => sourceNumerics12402 hi)
    BstLean.Part268.agent12402.frame targetFrame12402_eq


end BstLean.Part269.N12402

namespace BstLean.Part269.N12403
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12403 : scalarRow12403.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12403, BstLean.Part268.grid12403, BstLean.Part263.worldGrid]

theorem supplies12403 (j : Fin 43) : Supply 12403 (parameters j)
    (cellLower scalarRow12403.grid (sourceIndex j))
    (cellUpper scalarRow12403.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12403.grid grid_top_bounds12403 j

theorem radii12403 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12403.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12403 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12403 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12403.grid grid_top_bounds12403 j hθ

noncomputable def covarianceInputs12403 :
    BstLean.Part263.CovarianceInputs 12403 scalarRow12403.grid parameters (caps repair12403) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12403 grid_top_bounds12403 repair12403

noncomputable def covarianceEvent12403 : Set (AgFam 12403) :=
  BstLean.Part263.covarianceEvent 12403 scalarRow12403.grid parameters

theorem covarianceEvent12403_measurable : MeasurableSet covarianceEvent12403 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12403_payment :
    (retDist (paperDesignP 12403).toCentres).real
      (agentEv (paperDesignP 12403) covarianceEvent12403)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12403

theorem localCov12403 : BstLean.Part259.LocalCovarianceOn covarianceEvent12403
    (BstLean.Part263.cell scalarRow12403.grid) (caps repair12403) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12403

theorem covarianceGood12403_payment :
    (retDist (paperDesignP 12403).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12403)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12403_payment



end BstLean.Part269.N12403

namespace BstLean.Part269.N12403
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12403}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12403.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12403) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12403).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12403 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12403) (by norm_num) BstLean.Part268.WorldRow12403.worldPackage rfl
    BstLean.Part268.WorldRow12403.product_lower (BstLean.Part268.WorldRow12403.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12403} (hw : c ∈ Hof BstLean.Part268.WorldRow12403.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12403) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12403) (by norm_num) BstLean.Part268.WorldRow12403.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12403} (hw : c ∈ Hof BstLean.Part268.WorldRow12403.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12403) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12403).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12403) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12403_eq : scalarRow12403.targetFrame = BstLean.Part268.agent12403.frame := by
  norm_num [scalarRow12403,BstLean.Part268.agent12403]

noncomputable def frameData12403 : BstLean.Part264b.FrameData 12403 :=
  BstLean.Part269.frameData_from_numerics (n := 12403) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12403.worldPackage rfl BstLean.Part268.WorldRow12403.product_lower (BstLean.Part268.WorldRow12403.producthi.2.trans (by norm_num))
    scalarRow12403 repair12403 covarianceInputs12403 (fun i hi => sourceNumerics12403 hi)
    BstLean.Part268.agent12403.frame targetFrame12403_eq


end BstLean.Part269.N12403

namespace BstLean.Part269.N12404
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12404 : scalarRow12404.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12404, BstLean.Part268.grid12404, BstLean.Part263.worldGrid]

theorem supplies12404 (j : Fin 43) : Supply 12404 (parameters j)
    (cellLower scalarRow12404.grid (sourceIndex j))
    (cellUpper scalarRow12404.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12404.grid grid_top_bounds12404 j

theorem radii12404 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12404.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12404 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12404 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12404.grid grid_top_bounds12404 j hθ

noncomputable def covarianceInputs12404 :
    BstLean.Part263.CovarianceInputs 12404 scalarRow12404.grid parameters (caps repair12404) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12404 grid_top_bounds12404 repair12404

noncomputable def covarianceEvent12404 : Set (AgFam 12404) :=
  BstLean.Part263.covarianceEvent 12404 scalarRow12404.grid parameters

theorem covarianceEvent12404_measurable : MeasurableSet covarianceEvent12404 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12404_payment :
    (retDist (paperDesignP 12404).toCentres).real
      (agentEv (paperDesignP 12404) covarianceEvent12404)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12404

theorem localCov12404 : BstLean.Part259.LocalCovarianceOn covarianceEvent12404
    (BstLean.Part263.cell scalarRow12404.grid) (caps repair12404) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12404

theorem covarianceGood12404_payment :
    (retDist (paperDesignP 12404).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12404)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12404_payment



end BstLean.Part269.N12404

namespace BstLean.Part269.N12404
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12404}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12404.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12404) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12404).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12404 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12404) (by norm_num) BstLean.Part268.WorldRow12404.worldPackage rfl
    BstLean.Part268.WorldRow12404.product_lower (BstLean.Part268.WorldRow12404.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12404} (hw : c ∈ Hof BstLean.Part268.WorldRow12404.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12404) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12404) (by norm_num) BstLean.Part268.WorldRow12404.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12404} (hw : c ∈ Hof BstLean.Part268.WorldRow12404.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12404) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12404).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12404) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12404_eq : scalarRow12404.targetFrame = BstLean.Part268.agent12404.frame := by
  norm_num [scalarRow12404,BstLean.Part268.agent12404]

noncomputable def frameData12404 : BstLean.Part264b.FrameData 12404 :=
  BstLean.Part269.frameData_from_numerics (n := 12404) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12404.worldPackage rfl BstLean.Part268.WorldRow12404.product_lower (BstLean.Part268.WorldRow12404.producthi.2.trans (by norm_num))
    scalarRow12404 repair12404 covarianceInputs12404 (fun i hi => sourceNumerics12404 hi)
    BstLean.Part268.agent12404.frame targetFrame12404_eq


end BstLean.Part269.N12404
