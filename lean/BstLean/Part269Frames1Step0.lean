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

namespace BstLean.Part269.N12375
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12375 : scalarRow12375.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12375, BstLean.Part268.grid12375, BstLean.Part263.worldGrid]

theorem supplies12375 (j : Fin 43) : Supply 12375 (parameters j)
    (cellLower scalarRow12375.grid (sourceIndex j))
    (cellUpper scalarRow12375.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12375.grid grid_top_bounds12375 j

theorem radii12375 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12375.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12375 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12375 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12375.grid grid_top_bounds12375 j hθ

noncomputable def covarianceInputs12375 :
    BstLean.Part263.CovarianceInputs 12375 scalarRow12375.grid parameters (caps repair12375) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12375 grid_top_bounds12375 repair12375

noncomputable def covarianceEvent12375 : Set (AgFam 12375) :=
  BstLean.Part263.covarianceEvent 12375 scalarRow12375.grid parameters

theorem covarianceEvent12375_measurable : MeasurableSet covarianceEvent12375 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12375_payment :
    (retDist (paperDesignP 12375).toCentres).real
      (agentEv (paperDesignP 12375) covarianceEvent12375)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12375

theorem localCov12375 : BstLean.Part259.LocalCovarianceOn covarianceEvent12375
    (BstLean.Part263.cell scalarRow12375.grid) (caps repair12375) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12375

theorem covarianceGood12375_payment :
    (retDist (paperDesignP 12375).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12375)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12375_payment



end BstLean.Part269.N12375

namespace BstLean.Part269.N12375
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12375}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12375.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12375) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12375).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12375 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12375) (by norm_num) BstLean.Part268.WorldRow12375.worldPackage rfl
    BstLean.Part268.WorldRow12375.product_lower (BstLean.Part268.WorldRow12375.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12375} (hw : c ∈ Hof BstLean.Part268.WorldRow12375.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12375) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12375) (by norm_num) BstLean.Part268.WorldRow12375.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12375} (hw : c ∈ Hof BstLean.Part268.WorldRow12375.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12375) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12375).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12375) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12375_eq : scalarRow12375.targetFrame = BstLean.Part268.agent12375.frame := by
  norm_num [scalarRow12375,BstLean.Part268.agent12375]

noncomputable def frameData12375 : BstLean.Part264b.FrameData 12375 :=
  BstLean.Part269.frameData_from_numerics (n := 12375) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12375.worldPackage rfl BstLean.Part268.WorldRow12375.product_lower (BstLean.Part268.WorldRow12375.producthi.2.trans (by norm_num))
    scalarRow12375 repair12375 covarianceInputs12375 (fun i hi => sourceNumerics12375 hi)
    BstLean.Part268.agent12375.frame targetFrame12375_eq


end BstLean.Part269.N12375

namespace BstLean.Part269.N12376
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12376 : scalarRow12376.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12376, BstLean.Part268.grid12376, BstLean.Part263.worldGrid]

theorem supplies12376 (j : Fin 43) : Supply 12376 (parameters j)
    (cellLower scalarRow12376.grid (sourceIndex j))
    (cellUpper scalarRow12376.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12376.grid grid_top_bounds12376 j

theorem radii12376 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12376.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12376 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12376 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12376.grid grid_top_bounds12376 j hθ

noncomputable def covarianceInputs12376 :
    BstLean.Part263.CovarianceInputs 12376 scalarRow12376.grid parameters (caps repair12376) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12376 grid_top_bounds12376 repair12376

noncomputable def covarianceEvent12376 : Set (AgFam 12376) :=
  BstLean.Part263.covarianceEvent 12376 scalarRow12376.grid parameters

theorem covarianceEvent12376_measurable : MeasurableSet covarianceEvent12376 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12376_payment :
    (retDist (paperDesignP 12376).toCentres).real
      (agentEv (paperDesignP 12376) covarianceEvent12376)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12376

theorem localCov12376 : BstLean.Part259.LocalCovarianceOn covarianceEvent12376
    (BstLean.Part263.cell scalarRow12376.grid) (caps repair12376) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12376

theorem covarianceGood12376_payment :
    (retDist (paperDesignP 12376).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12376)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12376_payment



end BstLean.Part269.N12376

namespace BstLean.Part269.N12376
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12376}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12376.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12376) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12376).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12376 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12376) (by norm_num) BstLean.Part268.WorldRow12376.worldPackage rfl
    BstLean.Part268.WorldRow12376.product_lower (BstLean.Part268.WorldRow12376.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12376} (hw : c ∈ Hof BstLean.Part268.WorldRow12376.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12376) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12376) (by norm_num) BstLean.Part268.WorldRow12376.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12376} (hw : c ∈ Hof BstLean.Part268.WorldRow12376.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12376) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12376).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12376) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12376_eq : scalarRow12376.targetFrame = BstLean.Part268.agent12376.frame := by
  norm_num [scalarRow12376,BstLean.Part268.agent12376]

noncomputable def frameData12376 : BstLean.Part264b.FrameData 12376 :=
  BstLean.Part269.frameData_from_numerics (n := 12376) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12376.worldPackage rfl BstLean.Part268.WorldRow12376.product_lower (BstLean.Part268.WorldRow12376.producthi.2.trans (by norm_num))
    scalarRow12376 repair12376 covarianceInputs12376 (fun i hi => sourceNumerics12376 hi)
    BstLean.Part268.agent12376.frame targetFrame12376_eq


end BstLean.Part269.N12376

namespace BstLean.Part269.N12377
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12377 : scalarRow12377.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12377, BstLean.Part268.grid12377, BstLean.Part263.worldGrid]

theorem supplies12377 (j : Fin 43) : Supply 12377 (parameters j)
    (cellLower scalarRow12377.grid (sourceIndex j))
    (cellUpper scalarRow12377.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12377.grid grid_top_bounds12377 j

theorem radii12377 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12377.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12377 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12377 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12377.grid grid_top_bounds12377 j hθ

noncomputable def covarianceInputs12377 :
    BstLean.Part263.CovarianceInputs 12377 scalarRow12377.grid parameters (caps repair12377) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12377 grid_top_bounds12377 repair12377

noncomputable def covarianceEvent12377 : Set (AgFam 12377) :=
  BstLean.Part263.covarianceEvent 12377 scalarRow12377.grid parameters

theorem covarianceEvent12377_measurable : MeasurableSet covarianceEvent12377 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12377_payment :
    (retDist (paperDesignP 12377).toCentres).real
      (agentEv (paperDesignP 12377) covarianceEvent12377)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12377

theorem localCov12377 : BstLean.Part259.LocalCovarianceOn covarianceEvent12377
    (BstLean.Part263.cell scalarRow12377.grid) (caps repair12377) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12377

theorem covarianceGood12377_payment :
    (retDist (paperDesignP 12377).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12377)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12377_payment



end BstLean.Part269.N12377

namespace BstLean.Part269.N12377
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12377}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12377.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12377) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12377).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12377 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12377) (by norm_num) BstLean.Part268.WorldRow12377.worldPackage rfl
    BstLean.Part268.WorldRow12377.product_lower (BstLean.Part268.WorldRow12377.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12377} (hw : c ∈ Hof BstLean.Part268.WorldRow12377.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12377) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12377) (by norm_num) BstLean.Part268.WorldRow12377.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12377} (hw : c ∈ Hof BstLean.Part268.WorldRow12377.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12377) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12377).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12377) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12377_eq : scalarRow12377.targetFrame = BstLean.Part268.agent12377.frame := by
  norm_num [scalarRow12377,BstLean.Part268.agent12377]

noncomputable def frameData12377 : BstLean.Part264b.FrameData 12377 :=
  BstLean.Part269.frameData_from_numerics (n := 12377) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12377.worldPackage rfl BstLean.Part268.WorldRow12377.product_lower (BstLean.Part268.WorldRow12377.producthi.2.trans (by norm_num))
    scalarRow12377 repair12377 covarianceInputs12377 (fun i hi => sourceNumerics12377 hi)
    BstLean.Part268.agent12377.frame targetFrame12377_eq


end BstLean.Part269.N12377

namespace BstLean.Part269.N12378
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12378 : scalarRow12378.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12378, BstLean.Part268.grid12378, BstLean.Part263.worldGrid]

theorem supplies12378 (j : Fin 43) : Supply 12378 (parameters j)
    (cellLower scalarRow12378.grid (sourceIndex j))
    (cellUpper scalarRow12378.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12378.grid grid_top_bounds12378 j

theorem radii12378 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12378.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12378 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12378 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12378.grid grid_top_bounds12378 j hθ

noncomputable def covarianceInputs12378 :
    BstLean.Part263.CovarianceInputs 12378 scalarRow12378.grid parameters (caps repair12378) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12378 grid_top_bounds12378 repair12378

noncomputable def covarianceEvent12378 : Set (AgFam 12378) :=
  BstLean.Part263.covarianceEvent 12378 scalarRow12378.grid parameters

theorem covarianceEvent12378_measurable : MeasurableSet covarianceEvent12378 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12378_payment :
    (retDist (paperDesignP 12378).toCentres).real
      (agentEv (paperDesignP 12378) covarianceEvent12378)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12378

theorem localCov12378 : BstLean.Part259.LocalCovarianceOn covarianceEvent12378
    (BstLean.Part263.cell scalarRow12378.grid) (caps repair12378) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12378

theorem covarianceGood12378_payment :
    (retDist (paperDesignP 12378).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12378)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12378_payment



end BstLean.Part269.N12378

namespace BstLean.Part269.N12378
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12378}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12378.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12378) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12378).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12378 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12378) (by norm_num) BstLean.Part268.WorldRow12378.worldPackage rfl
    BstLean.Part268.WorldRow12378.product_lower (BstLean.Part268.WorldRow12378.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12378} (hw : c ∈ Hof BstLean.Part268.WorldRow12378.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12378) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12378) (by norm_num) BstLean.Part268.WorldRow12378.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12378} (hw : c ∈ Hof BstLean.Part268.WorldRow12378.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12378) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12378).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12378) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12378_eq : scalarRow12378.targetFrame = BstLean.Part268.agent12378.frame := by
  norm_num [scalarRow12378,BstLean.Part268.agent12378]

noncomputable def frameData12378 : BstLean.Part264b.FrameData 12378 :=
  BstLean.Part269.frameData_from_numerics (n := 12378) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12378.worldPackage rfl BstLean.Part268.WorldRow12378.product_lower (BstLean.Part268.WorldRow12378.producthi.2.trans (by norm_num))
    scalarRow12378 repair12378 covarianceInputs12378 (fun i hi => sourceNumerics12378 hi)
    BstLean.Part268.agent12378.frame targetFrame12378_eq


end BstLean.Part269.N12378

namespace BstLean.Part269.N12379
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12379 : scalarRow12379.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12379, BstLean.Part268.grid12379, BstLean.Part263.worldGrid]

theorem supplies12379 (j : Fin 43) : Supply 12379 (parameters j)
    (cellLower scalarRow12379.grid (sourceIndex j))
    (cellUpper scalarRow12379.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12379.grid grid_top_bounds12379 j

theorem radii12379 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12379.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12379 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12379 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12379.grid grid_top_bounds12379 j hθ

noncomputable def covarianceInputs12379 :
    BstLean.Part263.CovarianceInputs 12379 scalarRow12379.grid parameters (caps repair12379) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12379 grid_top_bounds12379 repair12379

noncomputable def covarianceEvent12379 : Set (AgFam 12379) :=
  BstLean.Part263.covarianceEvent 12379 scalarRow12379.grid parameters

theorem covarianceEvent12379_measurable : MeasurableSet covarianceEvent12379 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12379_payment :
    (retDist (paperDesignP 12379).toCentres).real
      (agentEv (paperDesignP 12379) covarianceEvent12379)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12379

theorem localCov12379 : BstLean.Part259.LocalCovarianceOn covarianceEvent12379
    (BstLean.Part263.cell scalarRow12379.grid) (caps repair12379) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12379

theorem covarianceGood12379_payment :
    (retDist (paperDesignP 12379).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12379)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12379_payment



end BstLean.Part269.N12379

namespace BstLean.Part269.N12379
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12379}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12379.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12379) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12379).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12379 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12379) (by norm_num) BstLean.Part268.WorldRow12379.worldPackage rfl
    BstLean.Part268.WorldRow12379.product_lower (BstLean.Part268.WorldRow12379.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12379} (hw : c ∈ Hof BstLean.Part268.WorldRow12379.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12379) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12379) (by norm_num) BstLean.Part268.WorldRow12379.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12379} (hw : c ∈ Hof BstLean.Part268.WorldRow12379.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12379) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12379).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12379) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12379_eq : scalarRow12379.targetFrame = BstLean.Part268.agent12379.frame := by
  norm_num [scalarRow12379,BstLean.Part268.agent12379]

noncomputable def frameData12379 : BstLean.Part264b.FrameData 12379 :=
  BstLean.Part269.frameData_from_numerics (n := 12379) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12379.worldPackage rfl BstLean.Part268.WorldRow12379.product_lower (BstLean.Part268.WorldRow12379.producthi.2.trans (by norm_num))
    scalarRow12379 repair12379 covarianceInputs12379 (fun i hi => sourceNumerics12379 hi)
    BstLean.Part268.agent12379.frame targetFrame12379_eq


end BstLean.Part269.N12379
