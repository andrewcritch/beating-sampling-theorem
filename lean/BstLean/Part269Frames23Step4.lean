import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World23Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs23
import BstLean.Part269Rows23
import BstLean.Part269Sources23
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12945
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12945 : scalarRow12945.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12945, BstLean.Part268.grid12945, BstLean.Part263.worldGrid]

theorem supplies12945 (j : Fin 43) : Supply 12945 (parameters j)
    (cellLower scalarRow12945.grid (sourceIndex j))
    (cellUpper scalarRow12945.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12945.grid grid_top_bounds12945 j

theorem radii12945 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12945.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12945 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12945 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12945.grid grid_top_bounds12945 j hθ

noncomputable def covarianceInputs12945 :
    BstLean.Part263.CovarianceInputs 12945 scalarRow12945.grid parameters (caps repair12945) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12945 grid_top_bounds12945 repair12945

noncomputable def covarianceEvent12945 : Set (AgFam 12945) :=
  BstLean.Part263.covarianceEvent 12945 scalarRow12945.grid parameters

theorem covarianceEvent12945_measurable : MeasurableSet covarianceEvent12945 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12945_payment :
    (retDist (paperDesignP 12945).toCentres).real
      (agentEv (paperDesignP 12945) covarianceEvent12945)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12945

theorem localCov12945 : BstLean.Part259.LocalCovarianceOn covarianceEvent12945
    (BstLean.Part263.cell scalarRow12945.grid) (caps repair12945) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12945

theorem covarianceGood12945_payment :
    (retDist (paperDesignP 12945).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12945)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12945_payment



end BstLean.Part269.N12945

namespace BstLean.Part269.N12945
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12945}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12945.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12945) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12945).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12945 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12945) (by norm_num) BstLean.Part268.WorldRow12945.worldPackage rfl
    BstLean.Part268.WorldRow12945.product_lower (BstLean.Part268.WorldRow12945.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12945} (hw : c ∈ Hof BstLean.Part268.WorldRow12945.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12945) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12945) (by norm_num) BstLean.Part268.WorldRow12945.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12945} (hw : c ∈ Hof BstLean.Part268.WorldRow12945.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12945) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12945).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12945) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12945_eq : scalarRow12945.targetFrame = BstLean.Part268.agent12945.frame := by
  norm_num [scalarRow12945,BstLean.Part268.agent12945]

noncomputable def frameData12945 : BstLean.Part264b.FrameData 12945 :=
  BstLean.Part269.frameData_from_numerics (n := 12945) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12945.worldPackage rfl BstLean.Part268.WorldRow12945.product_lower (BstLean.Part268.WorldRow12945.producthi.2.trans (by norm_num))
    scalarRow12945 repair12945 covarianceInputs12945 (fun i hi => sourceNumerics12945 hi)
    BstLean.Part268.agent12945.frame targetFrame12945_eq


end BstLean.Part269.N12945

namespace BstLean.Part269.N12946
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12946 : scalarRow12946.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12946, BstLean.Part268.grid12946, BstLean.Part263.worldGrid]

theorem supplies12946 (j : Fin 43) : Supply 12946 (parameters j)
    (cellLower scalarRow12946.grid (sourceIndex j))
    (cellUpper scalarRow12946.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12946.grid grid_top_bounds12946 j

theorem radii12946 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12946.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12946 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12946 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12946.grid grid_top_bounds12946 j hθ

noncomputable def covarianceInputs12946 :
    BstLean.Part263.CovarianceInputs 12946 scalarRow12946.grid parameters (caps repair12946) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12946 grid_top_bounds12946 repair12946

noncomputable def covarianceEvent12946 : Set (AgFam 12946) :=
  BstLean.Part263.covarianceEvent 12946 scalarRow12946.grid parameters

theorem covarianceEvent12946_measurable : MeasurableSet covarianceEvent12946 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12946_payment :
    (retDist (paperDesignP 12946).toCentres).real
      (agentEv (paperDesignP 12946) covarianceEvent12946)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12946

theorem localCov12946 : BstLean.Part259.LocalCovarianceOn covarianceEvent12946
    (BstLean.Part263.cell scalarRow12946.grid) (caps repair12946) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12946

theorem covarianceGood12946_payment :
    (retDist (paperDesignP 12946).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12946)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12946_payment



end BstLean.Part269.N12946

namespace BstLean.Part269.N12946
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12946}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12946.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12946) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12946).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12946 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12946) (by norm_num) BstLean.Part268.WorldRow12946.worldPackage rfl
    BstLean.Part268.WorldRow12946.product_lower (BstLean.Part268.WorldRow12946.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12946} (hw : c ∈ Hof BstLean.Part268.WorldRow12946.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12946) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12946) (by norm_num) BstLean.Part268.WorldRow12946.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12946} (hw : c ∈ Hof BstLean.Part268.WorldRow12946.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12946) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12946).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12946) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12946_eq : scalarRow12946.targetFrame = BstLean.Part268.agent12946.frame := by
  norm_num [scalarRow12946,BstLean.Part268.agent12946]

noncomputable def frameData12946 : BstLean.Part264b.FrameData 12946 :=
  BstLean.Part269.frameData_from_numerics (n := 12946) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12946.worldPackage rfl BstLean.Part268.WorldRow12946.product_lower (BstLean.Part268.WorldRow12946.producthi.2.trans (by norm_num))
    scalarRow12946 repair12946 covarianceInputs12946 (fun i hi => sourceNumerics12946 hi)
    BstLean.Part268.agent12946.frame targetFrame12946_eq


end BstLean.Part269.N12946

namespace BstLean.Part269.N12947
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12947 : scalarRow12947.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12947, BstLean.Part268.grid12947, BstLean.Part263.worldGrid]

theorem supplies12947 (j : Fin 43) : Supply 12947 (parameters j)
    (cellLower scalarRow12947.grid (sourceIndex j))
    (cellUpper scalarRow12947.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12947.grid grid_top_bounds12947 j

theorem radii12947 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12947.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12947 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12947 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12947.grid grid_top_bounds12947 j hθ

noncomputable def covarianceInputs12947 :
    BstLean.Part263.CovarianceInputs 12947 scalarRow12947.grid parameters (caps repair12947) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12947 grid_top_bounds12947 repair12947

noncomputable def covarianceEvent12947 : Set (AgFam 12947) :=
  BstLean.Part263.covarianceEvent 12947 scalarRow12947.grid parameters

theorem covarianceEvent12947_measurable : MeasurableSet covarianceEvent12947 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12947_payment :
    (retDist (paperDesignP 12947).toCentres).real
      (agentEv (paperDesignP 12947) covarianceEvent12947)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12947

theorem localCov12947 : BstLean.Part259.LocalCovarianceOn covarianceEvent12947
    (BstLean.Part263.cell scalarRow12947.grid) (caps repair12947) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12947

theorem covarianceGood12947_payment :
    (retDist (paperDesignP 12947).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12947)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12947_payment



end BstLean.Part269.N12947

namespace BstLean.Part269.N12947
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12947}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12947.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12947) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12947).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12947 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12947) (by norm_num) BstLean.Part268.WorldRow12947.worldPackage rfl
    BstLean.Part268.WorldRow12947.product_lower (BstLean.Part268.WorldRow12947.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12947} (hw : c ∈ Hof BstLean.Part268.WorldRow12947.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12947) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12947) (by norm_num) BstLean.Part268.WorldRow12947.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12947} (hw : c ∈ Hof BstLean.Part268.WorldRow12947.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12947) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12947).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12947) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12947_eq : scalarRow12947.targetFrame = BstLean.Part268.agent12947.frame := by
  norm_num [scalarRow12947,BstLean.Part268.agent12947]

noncomputable def frameData12947 : BstLean.Part264b.FrameData 12947 :=
  BstLean.Part269.frameData_from_numerics (n := 12947) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12947.worldPackage rfl BstLean.Part268.WorldRow12947.product_lower (BstLean.Part268.WorldRow12947.producthi.2.trans (by norm_num))
    scalarRow12947 repair12947 covarianceInputs12947 (fun i hi => sourceNumerics12947 hi)
    BstLean.Part268.agent12947.frame targetFrame12947_eq


end BstLean.Part269.N12947

namespace BstLean.Part269.N12948
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12948 : scalarRow12948.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12948, BstLean.Part268.grid12948, BstLean.Part263.worldGrid]

theorem supplies12948 (j : Fin 43) : Supply 12948 (parameters j)
    (cellLower scalarRow12948.grid (sourceIndex j))
    (cellUpper scalarRow12948.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12948.grid grid_top_bounds12948 j

theorem radii12948 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12948.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12948 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12948 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12948.grid grid_top_bounds12948 j hθ

noncomputable def covarianceInputs12948 :
    BstLean.Part263.CovarianceInputs 12948 scalarRow12948.grid parameters (caps repair12948) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12948 grid_top_bounds12948 repair12948

noncomputable def covarianceEvent12948 : Set (AgFam 12948) :=
  BstLean.Part263.covarianceEvent 12948 scalarRow12948.grid parameters

theorem covarianceEvent12948_measurable : MeasurableSet covarianceEvent12948 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12948_payment :
    (retDist (paperDesignP 12948).toCentres).real
      (agentEv (paperDesignP 12948) covarianceEvent12948)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12948

theorem localCov12948 : BstLean.Part259.LocalCovarianceOn covarianceEvent12948
    (BstLean.Part263.cell scalarRow12948.grid) (caps repair12948) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12948

theorem covarianceGood12948_payment :
    (retDist (paperDesignP 12948).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12948)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12948_payment



end BstLean.Part269.N12948

namespace BstLean.Part269.N12948
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12948}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12948.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12948) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12948).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12948 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12948) (by norm_num) BstLean.Part268.WorldRow12948.worldPackage rfl
    BstLean.Part268.WorldRow12948.product_lower (BstLean.Part268.WorldRow12948.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12948} (hw : c ∈ Hof BstLean.Part268.WorldRow12948.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12948) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12948) (by norm_num) BstLean.Part268.WorldRow12948.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12948} (hw : c ∈ Hof BstLean.Part268.WorldRow12948.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12948) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12948).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12948) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12948_eq : scalarRow12948.targetFrame = BstLean.Part268.agent12948.frame := by
  norm_num [scalarRow12948,BstLean.Part268.agent12948]

noncomputable def frameData12948 : BstLean.Part264b.FrameData 12948 :=
  BstLean.Part269.frameData_from_numerics (n := 12948) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12948.worldPackage rfl BstLean.Part268.WorldRow12948.product_lower (BstLean.Part268.WorldRow12948.producthi.2.trans (by norm_num))
    scalarRow12948 repair12948 covarianceInputs12948 (fun i hi => sourceNumerics12948 hi)
    BstLean.Part268.agent12948.frame targetFrame12948_eq


end BstLean.Part269.N12948

namespace BstLean.Part269.N12949
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12949 : scalarRow12949.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12949, BstLean.Part268.grid12949, BstLean.Part263.worldGrid]

theorem supplies12949 (j : Fin 43) : Supply 12949 (parameters j)
    (cellLower scalarRow12949.grid (sourceIndex j))
    (cellUpper scalarRow12949.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12949.grid grid_top_bounds12949 j

theorem radii12949 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12949.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12949 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12949 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12949.grid grid_top_bounds12949 j hθ

noncomputable def covarianceInputs12949 :
    BstLean.Part263.CovarianceInputs 12949 scalarRow12949.grid parameters (caps repair12949) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12949 grid_top_bounds12949 repair12949

noncomputable def covarianceEvent12949 : Set (AgFam 12949) :=
  BstLean.Part263.covarianceEvent 12949 scalarRow12949.grid parameters

theorem covarianceEvent12949_measurable : MeasurableSet covarianceEvent12949 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12949_payment :
    (retDist (paperDesignP 12949).toCentres).real
      (agentEv (paperDesignP 12949) covarianceEvent12949)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12949

theorem localCov12949 : BstLean.Part259.LocalCovarianceOn covarianceEvent12949
    (BstLean.Part263.cell scalarRow12949.grid) (caps repair12949) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12949

theorem covarianceGood12949_payment :
    (retDist (paperDesignP 12949).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12949)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12949_payment



end BstLean.Part269.N12949

namespace BstLean.Part269.N12949
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12949}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12949.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12949) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12949).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12949 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12949) (by norm_num) BstLean.Part268.WorldRow12949.worldPackage rfl
    BstLean.Part268.WorldRow12949.product_lower (BstLean.Part268.WorldRow12949.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12949} (hw : c ∈ Hof BstLean.Part268.WorldRow12949.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12949) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12949) (by norm_num) BstLean.Part268.WorldRow12949.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12949} (hw : c ∈ Hof BstLean.Part268.WorldRow12949.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12949) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12949).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12949) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12949_eq : scalarRow12949.targetFrame = BstLean.Part268.agent12949.frame := by
  norm_num [scalarRow12949,BstLean.Part268.agent12949]

noncomputable def frameData12949 : BstLean.Part264b.FrameData 12949 :=
  BstLean.Part269.frameData_from_numerics (n := 12949) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12949.worldPackage rfl BstLean.Part268.WorldRow12949.product_lower (BstLean.Part268.WorldRow12949.producthi.2.trans (by norm_num))
    scalarRow12949 repair12949 covarianceInputs12949 (fun i hi => sourceNumerics12949 hi)
    BstLean.Part268.agent12949.frame targetFrame12949_eq


end BstLean.Part269.N12949
