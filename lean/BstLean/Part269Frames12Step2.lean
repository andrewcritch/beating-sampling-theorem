import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World12Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs12
import BstLean.Part269Rows12
import BstLean.Part269Sources12
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12660
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12660 : scalarRow12660.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12660, BstLean.Part268.grid12660, BstLean.Part263.worldGrid]

theorem supplies12660 (j : Fin 43) : Supply 12660 (parameters j)
    (cellLower scalarRow12660.grid (sourceIndex j))
    (cellUpper scalarRow12660.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12660.grid grid_top_bounds12660 j

theorem radii12660 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12660.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12660 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12660 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12660.grid grid_top_bounds12660 j hθ

noncomputable def covarianceInputs12660 :
    BstLean.Part263.CovarianceInputs 12660 scalarRow12660.grid parameters (caps repair12660) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12660 grid_top_bounds12660 repair12660

noncomputable def covarianceEvent12660 : Set (AgFam 12660) :=
  BstLean.Part263.covarianceEvent 12660 scalarRow12660.grid parameters

theorem covarianceEvent12660_measurable : MeasurableSet covarianceEvent12660 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12660_payment :
    (retDist (paperDesignP 12660).toCentres).real
      (agentEv (paperDesignP 12660) covarianceEvent12660)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12660

theorem localCov12660 : BstLean.Part259.LocalCovarianceOn covarianceEvent12660
    (BstLean.Part263.cell scalarRow12660.grid) (caps repair12660) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12660

theorem covarianceGood12660_payment :
    (retDist (paperDesignP 12660).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12660)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12660_payment



end BstLean.Part269.N12660

namespace BstLean.Part269.N12660
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12660}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12660.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12660) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12660).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12660 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12660) (by norm_num) BstLean.Part268.WorldRow12660.worldPackage rfl
    BstLean.Part268.WorldRow12660.product_lower (BstLean.Part268.WorldRow12660.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12660} (hw : c ∈ Hof BstLean.Part268.WorldRow12660.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12660) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12660) (by norm_num) BstLean.Part268.WorldRow12660.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12660} (hw : c ∈ Hof BstLean.Part268.WorldRow12660.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12660) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12660).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12660) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12660_eq : scalarRow12660.targetFrame = BstLean.Part268.agent12660.frame := by
  norm_num [scalarRow12660,BstLean.Part268.agent12660]

noncomputable def frameData12660 : BstLean.Part264b.FrameData 12660 :=
  BstLean.Part269.frameData_from_numerics (n := 12660) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12660.worldPackage rfl BstLean.Part268.WorldRow12660.product_lower (BstLean.Part268.WorldRow12660.producthi.2.trans (by norm_num))
    scalarRow12660 repair12660 covarianceInputs12660 (fun i hi => sourceNumerics12660 hi)
    BstLean.Part268.agent12660.frame targetFrame12660_eq


end BstLean.Part269.N12660

namespace BstLean.Part269.N12661
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12661 : scalarRow12661.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12661, BstLean.Part268.grid12661, BstLean.Part263.worldGrid]

theorem supplies12661 (j : Fin 43) : Supply 12661 (parameters j)
    (cellLower scalarRow12661.grid (sourceIndex j))
    (cellUpper scalarRow12661.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12661.grid grid_top_bounds12661 j

theorem radii12661 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12661.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12661 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12661 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12661.grid grid_top_bounds12661 j hθ

noncomputable def covarianceInputs12661 :
    BstLean.Part263.CovarianceInputs 12661 scalarRow12661.grid parameters (caps repair12661) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12661 grid_top_bounds12661 repair12661

noncomputable def covarianceEvent12661 : Set (AgFam 12661) :=
  BstLean.Part263.covarianceEvent 12661 scalarRow12661.grid parameters

theorem covarianceEvent12661_measurable : MeasurableSet covarianceEvent12661 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12661_payment :
    (retDist (paperDesignP 12661).toCentres).real
      (agentEv (paperDesignP 12661) covarianceEvent12661)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12661

theorem localCov12661 : BstLean.Part259.LocalCovarianceOn covarianceEvent12661
    (BstLean.Part263.cell scalarRow12661.grid) (caps repair12661) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12661

theorem covarianceGood12661_payment :
    (retDist (paperDesignP 12661).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12661)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12661_payment



end BstLean.Part269.N12661

namespace BstLean.Part269.N12661
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12661}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12661.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12661) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12661).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12661 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12661) (by norm_num) BstLean.Part268.WorldRow12661.worldPackage rfl
    BstLean.Part268.WorldRow12661.product_lower (BstLean.Part268.WorldRow12661.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12661} (hw : c ∈ Hof BstLean.Part268.WorldRow12661.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12661) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12661) (by norm_num) BstLean.Part268.WorldRow12661.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12661} (hw : c ∈ Hof BstLean.Part268.WorldRow12661.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12661) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12661).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12661) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12661_eq : scalarRow12661.targetFrame = BstLean.Part268.agent12661.frame := by
  norm_num [scalarRow12661,BstLean.Part268.agent12661]

noncomputable def frameData12661 : BstLean.Part264b.FrameData 12661 :=
  BstLean.Part269.frameData_from_numerics (n := 12661) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12661.worldPackage rfl BstLean.Part268.WorldRow12661.product_lower (BstLean.Part268.WorldRow12661.producthi.2.trans (by norm_num))
    scalarRow12661 repair12661 covarianceInputs12661 (fun i hi => sourceNumerics12661 hi)
    BstLean.Part268.agent12661.frame targetFrame12661_eq


end BstLean.Part269.N12661

namespace BstLean.Part269.N12662
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12662 : scalarRow12662.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12662, BstLean.Part268.grid12662, BstLean.Part263.worldGrid]

theorem supplies12662 (j : Fin 43) : Supply 12662 (parameters j)
    (cellLower scalarRow12662.grid (sourceIndex j))
    (cellUpper scalarRow12662.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12662.grid grid_top_bounds12662 j

theorem radii12662 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12662.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12662 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12662 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12662.grid grid_top_bounds12662 j hθ

noncomputable def covarianceInputs12662 :
    BstLean.Part263.CovarianceInputs 12662 scalarRow12662.grid parameters (caps repair12662) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12662 grid_top_bounds12662 repair12662

noncomputable def covarianceEvent12662 : Set (AgFam 12662) :=
  BstLean.Part263.covarianceEvent 12662 scalarRow12662.grid parameters

theorem covarianceEvent12662_measurable : MeasurableSet covarianceEvent12662 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12662_payment :
    (retDist (paperDesignP 12662).toCentres).real
      (agentEv (paperDesignP 12662) covarianceEvent12662)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12662

theorem localCov12662 : BstLean.Part259.LocalCovarianceOn covarianceEvent12662
    (BstLean.Part263.cell scalarRow12662.grid) (caps repair12662) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12662

theorem covarianceGood12662_payment :
    (retDist (paperDesignP 12662).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12662)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12662_payment



end BstLean.Part269.N12662

namespace BstLean.Part269.N12662
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12662}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12662.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12662) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12662).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12662 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12662) (by norm_num) BstLean.Part268.WorldRow12662.worldPackage rfl
    BstLean.Part268.WorldRow12662.product_lower (BstLean.Part268.WorldRow12662.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12662} (hw : c ∈ Hof BstLean.Part268.WorldRow12662.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12662) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12662) (by norm_num) BstLean.Part268.WorldRow12662.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12662} (hw : c ∈ Hof BstLean.Part268.WorldRow12662.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12662) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12662).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12662) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12662_eq : scalarRow12662.targetFrame = BstLean.Part268.agent12662.frame := by
  norm_num [scalarRow12662,BstLean.Part268.agent12662]

noncomputable def frameData12662 : BstLean.Part264b.FrameData 12662 :=
  BstLean.Part269.frameData_from_numerics (n := 12662) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12662.worldPackage rfl BstLean.Part268.WorldRow12662.product_lower (BstLean.Part268.WorldRow12662.producthi.2.trans (by norm_num))
    scalarRow12662 repair12662 covarianceInputs12662 (fun i hi => sourceNumerics12662 hi)
    BstLean.Part268.agent12662.frame targetFrame12662_eq


end BstLean.Part269.N12662

namespace BstLean.Part269.N12663
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12663 : scalarRow12663.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12663, BstLean.Part268.grid12663, BstLean.Part263.worldGrid]

theorem supplies12663 (j : Fin 43) : Supply 12663 (parameters j)
    (cellLower scalarRow12663.grid (sourceIndex j))
    (cellUpper scalarRow12663.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12663.grid grid_top_bounds12663 j

theorem radii12663 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12663.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12663 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12663 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12663.grid grid_top_bounds12663 j hθ

noncomputable def covarianceInputs12663 :
    BstLean.Part263.CovarianceInputs 12663 scalarRow12663.grid parameters (caps repair12663) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12663 grid_top_bounds12663 repair12663

noncomputable def covarianceEvent12663 : Set (AgFam 12663) :=
  BstLean.Part263.covarianceEvent 12663 scalarRow12663.grid parameters

theorem covarianceEvent12663_measurable : MeasurableSet covarianceEvent12663 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12663_payment :
    (retDist (paperDesignP 12663).toCentres).real
      (agentEv (paperDesignP 12663) covarianceEvent12663)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12663

theorem localCov12663 : BstLean.Part259.LocalCovarianceOn covarianceEvent12663
    (BstLean.Part263.cell scalarRow12663.grid) (caps repair12663) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12663

theorem covarianceGood12663_payment :
    (retDist (paperDesignP 12663).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12663)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12663_payment



end BstLean.Part269.N12663

namespace BstLean.Part269.N12663
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12663}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12663.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12663) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12663).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12663 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12663) (by norm_num) BstLean.Part268.WorldRow12663.worldPackage rfl
    BstLean.Part268.WorldRow12663.product_lower (BstLean.Part268.WorldRow12663.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12663} (hw : c ∈ Hof BstLean.Part268.WorldRow12663.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12663) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12663) (by norm_num) BstLean.Part268.WorldRow12663.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12663} (hw : c ∈ Hof BstLean.Part268.WorldRow12663.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12663) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12663).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12663) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12663_eq : scalarRow12663.targetFrame = BstLean.Part268.agent12663.frame := by
  norm_num [scalarRow12663,BstLean.Part268.agent12663]

noncomputable def frameData12663 : BstLean.Part264b.FrameData 12663 :=
  BstLean.Part269.frameData_from_numerics (n := 12663) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12663.worldPackage rfl BstLean.Part268.WorldRow12663.product_lower (BstLean.Part268.WorldRow12663.producthi.2.trans (by norm_num))
    scalarRow12663 repair12663 covarianceInputs12663 (fun i hi => sourceNumerics12663 hi)
    BstLean.Part268.agent12663.frame targetFrame12663_eq


end BstLean.Part269.N12663

namespace BstLean.Part269.N12664
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12664 : scalarRow12664.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12664, BstLean.Part268.grid12664, BstLean.Part263.worldGrid]

theorem supplies12664 (j : Fin 43) : Supply 12664 (parameters j)
    (cellLower scalarRow12664.grid (sourceIndex j))
    (cellUpper scalarRow12664.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12664.grid grid_top_bounds12664 j

theorem radii12664 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12664.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12664 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12664 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12664.grid grid_top_bounds12664 j hθ

noncomputable def covarianceInputs12664 :
    BstLean.Part263.CovarianceInputs 12664 scalarRow12664.grid parameters (caps repair12664) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12664 grid_top_bounds12664 repair12664

noncomputable def covarianceEvent12664 : Set (AgFam 12664) :=
  BstLean.Part263.covarianceEvent 12664 scalarRow12664.grid parameters

theorem covarianceEvent12664_measurable : MeasurableSet covarianceEvent12664 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12664_payment :
    (retDist (paperDesignP 12664).toCentres).real
      (agentEv (paperDesignP 12664) covarianceEvent12664)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12664

theorem localCov12664 : BstLean.Part259.LocalCovarianceOn covarianceEvent12664
    (BstLean.Part263.cell scalarRow12664.grid) (caps repair12664) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12664

theorem covarianceGood12664_payment :
    (retDist (paperDesignP 12664).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12664)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12664_payment



end BstLean.Part269.N12664

namespace BstLean.Part269.N12664
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12664}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12664.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12664) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12664).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12664 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12664) (by norm_num) BstLean.Part268.WorldRow12664.worldPackage rfl
    BstLean.Part268.WorldRow12664.product_lower (BstLean.Part268.WorldRow12664.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12664} (hw : c ∈ Hof BstLean.Part268.WorldRow12664.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12664) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12664) (by norm_num) BstLean.Part268.WorldRow12664.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12664} (hw : c ∈ Hof BstLean.Part268.WorldRow12664.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12664) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12664).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12664) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12664_eq : scalarRow12664.targetFrame = BstLean.Part268.agent12664.frame := by
  norm_num [scalarRow12664,BstLean.Part268.agent12664]

noncomputable def frameData12664 : BstLean.Part264b.FrameData 12664 :=
  BstLean.Part269.frameData_from_numerics (n := 12664) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12664.worldPackage rfl BstLean.Part268.WorldRow12664.product_lower (BstLean.Part268.WorldRow12664.producthi.2.trans (by norm_num))
    scalarRow12664 repair12664 covarianceInputs12664 (fun i hi => sourceNumerics12664 hi)
    BstLean.Part268.agent12664.frame targetFrame12664_eq


end BstLean.Part269.N12664
