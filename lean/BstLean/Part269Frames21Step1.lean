import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World21Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs21
import BstLean.Part269Rows21
import BstLean.Part269Sources21
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12880
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12880 : scalarRow12880.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12880, BstLean.Part268.grid12880, BstLean.Part263.worldGrid]

theorem supplies12880 (j : Fin 43) : Supply 12880 (parameters j)
    (cellLower scalarRow12880.grid (sourceIndex j))
    (cellUpper scalarRow12880.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12880.grid grid_top_bounds12880 j

theorem radii12880 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12880.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12880 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12880 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12880.grid grid_top_bounds12880 j hθ

noncomputable def covarianceInputs12880 :
    BstLean.Part263.CovarianceInputs 12880 scalarRow12880.grid parameters (caps repair12880) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12880 grid_top_bounds12880 repair12880

noncomputable def covarianceEvent12880 : Set (AgFam 12880) :=
  BstLean.Part263.covarianceEvent 12880 scalarRow12880.grid parameters

theorem covarianceEvent12880_measurable : MeasurableSet covarianceEvent12880 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12880_payment :
    (retDist (paperDesignP 12880).toCentres).real
      (agentEv (paperDesignP 12880) covarianceEvent12880)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12880

theorem localCov12880 : BstLean.Part259.LocalCovarianceOn covarianceEvent12880
    (BstLean.Part263.cell scalarRow12880.grid) (caps repair12880) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12880

theorem covarianceGood12880_payment :
    (retDist (paperDesignP 12880).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12880)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12880_payment



end BstLean.Part269.N12880

namespace BstLean.Part269.N12880
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12880}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12880.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12880) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12880).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12880 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12880) (by norm_num) BstLean.Part268.WorldRow12880.worldPackage rfl
    BstLean.Part268.WorldRow12880.product_lower (BstLean.Part268.WorldRow12880.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12880} (hw : c ∈ Hof BstLean.Part268.WorldRow12880.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12880) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12880) (by norm_num) BstLean.Part268.WorldRow12880.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12880} (hw : c ∈ Hof BstLean.Part268.WorldRow12880.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12880) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12880).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12880) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12880_eq : scalarRow12880.targetFrame = BstLean.Part268.agent12880.frame := by
  norm_num [scalarRow12880,BstLean.Part268.agent12880]

noncomputable def frameData12880 : BstLean.Part264b.FrameData 12880 :=
  BstLean.Part269.frameData_from_numerics (n := 12880) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12880.worldPackage rfl BstLean.Part268.WorldRow12880.product_lower (BstLean.Part268.WorldRow12880.producthi.2.trans (by norm_num))
    scalarRow12880 repair12880 covarianceInputs12880 (fun i hi => sourceNumerics12880 hi)
    BstLean.Part268.agent12880.frame targetFrame12880_eq


end BstLean.Part269.N12880

namespace BstLean.Part269.N12881
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12881 : scalarRow12881.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12881, BstLean.Part268.grid12881, BstLean.Part263.worldGrid]

theorem supplies12881 (j : Fin 43) : Supply 12881 (parameters j)
    (cellLower scalarRow12881.grid (sourceIndex j))
    (cellUpper scalarRow12881.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12881.grid grid_top_bounds12881 j

theorem radii12881 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12881.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12881 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12881 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12881.grid grid_top_bounds12881 j hθ

noncomputable def covarianceInputs12881 :
    BstLean.Part263.CovarianceInputs 12881 scalarRow12881.grid parameters (caps repair12881) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12881 grid_top_bounds12881 repair12881

noncomputable def covarianceEvent12881 : Set (AgFam 12881) :=
  BstLean.Part263.covarianceEvent 12881 scalarRow12881.grid parameters

theorem covarianceEvent12881_measurable : MeasurableSet covarianceEvent12881 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12881_payment :
    (retDist (paperDesignP 12881).toCentres).real
      (agentEv (paperDesignP 12881) covarianceEvent12881)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12881

theorem localCov12881 : BstLean.Part259.LocalCovarianceOn covarianceEvent12881
    (BstLean.Part263.cell scalarRow12881.grid) (caps repair12881) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12881

theorem covarianceGood12881_payment :
    (retDist (paperDesignP 12881).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12881)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12881_payment



end BstLean.Part269.N12881

namespace BstLean.Part269.N12881
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12881}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12881.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12881) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12881).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12881 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12881) (by norm_num) BstLean.Part268.WorldRow12881.worldPackage rfl
    BstLean.Part268.WorldRow12881.product_lower (BstLean.Part268.WorldRow12881.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12881} (hw : c ∈ Hof BstLean.Part268.WorldRow12881.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12881) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12881) (by norm_num) BstLean.Part268.WorldRow12881.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12881} (hw : c ∈ Hof BstLean.Part268.WorldRow12881.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12881) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12881).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12881) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12881_eq : scalarRow12881.targetFrame = BstLean.Part268.agent12881.frame := by
  norm_num [scalarRow12881,BstLean.Part268.agent12881]

noncomputable def frameData12881 : BstLean.Part264b.FrameData 12881 :=
  BstLean.Part269.frameData_from_numerics (n := 12881) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12881.worldPackage rfl BstLean.Part268.WorldRow12881.product_lower (BstLean.Part268.WorldRow12881.producthi.2.trans (by norm_num))
    scalarRow12881 repair12881 covarianceInputs12881 (fun i hi => sourceNumerics12881 hi)
    BstLean.Part268.agent12881.frame targetFrame12881_eq


end BstLean.Part269.N12881

namespace BstLean.Part269.N12882
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12882 : scalarRow12882.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12882, BstLean.Part268.grid12882, BstLean.Part263.worldGrid]

theorem supplies12882 (j : Fin 43) : Supply 12882 (parameters j)
    (cellLower scalarRow12882.grid (sourceIndex j))
    (cellUpper scalarRow12882.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12882.grid grid_top_bounds12882 j

theorem radii12882 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12882.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12882 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12882 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12882.grid grid_top_bounds12882 j hθ

noncomputable def covarianceInputs12882 :
    BstLean.Part263.CovarianceInputs 12882 scalarRow12882.grid parameters (caps repair12882) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12882 grid_top_bounds12882 repair12882

noncomputable def covarianceEvent12882 : Set (AgFam 12882) :=
  BstLean.Part263.covarianceEvent 12882 scalarRow12882.grid parameters

theorem covarianceEvent12882_measurable : MeasurableSet covarianceEvent12882 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12882_payment :
    (retDist (paperDesignP 12882).toCentres).real
      (agentEv (paperDesignP 12882) covarianceEvent12882)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12882

theorem localCov12882 : BstLean.Part259.LocalCovarianceOn covarianceEvent12882
    (BstLean.Part263.cell scalarRow12882.grid) (caps repair12882) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12882

theorem covarianceGood12882_payment :
    (retDist (paperDesignP 12882).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12882)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12882_payment



end BstLean.Part269.N12882

namespace BstLean.Part269.N12882
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12882}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12882.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12882) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12882).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12882 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12882) (by norm_num) BstLean.Part268.WorldRow12882.worldPackage rfl
    BstLean.Part268.WorldRow12882.product_lower (BstLean.Part268.WorldRow12882.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12882} (hw : c ∈ Hof BstLean.Part268.WorldRow12882.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12882) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12882) (by norm_num) BstLean.Part268.WorldRow12882.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12882} (hw : c ∈ Hof BstLean.Part268.WorldRow12882.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12882) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12882).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12882) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12882_eq : scalarRow12882.targetFrame = BstLean.Part268.agent12882.frame := by
  norm_num [scalarRow12882,BstLean.Part268.agent12882]

noncomputable def frameData12882 : BstLean.Part264b.FrameData 12882 :=
  BstLean.Part269.frameData_from_numerics (n := 12882) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12882.worldPackage rfl BstLean.Part268.WorldRow12882.product_lower (BstLean.Part268.WorldRow12882.producthi.2.trans (by norm_num))
    scalarRow12882 repair12882 covarianceInputs12882 (fun i hi => sourceNumerics12882 hi)
    BstLean.Part268.agent12882.frame targetFrame12882_eq


end BstLean.Part269.N12882

namespace BstLean.Part269.N12883
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12883 : scalarRow12883.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12883, BstLean.Part268.grid12883, BstLean.Part263.worldGrid]

theorem supplies12883 (j : Fin 43) : Supply 12883 (parameters j)
    (cellLower scalarRow12883.grid (sourceIndex j))
    (cellUpper scalarRow12883.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12883.grid grid_top_bounds12883 j

theorem radii12883 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12883.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12883 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12883 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12883.grid grid_top_bounds12883 j hθ

noncomputable def covarianceInputs12883 :
    BstLean.Part263.CovarianceInputs 12883 scalarRow12883.grid parameters (caps repair12883) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12883 grid_top_bounds12883 repair12883

noncomputable def covarianceEvent12883 : Set (AgFam 12883) :=
  BstLean.Part263.covarianceEvent 12883 scalarRow12883.grid parameters

theorem covarianceEvent12883_measurable : MeasurableSet covarianceEvent12883 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12883_payment :
    (retDist (paperDesignP 12883).toCentres).real
      (agentEv (paperDesignP 12883) covarianceEvent12883)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12883

theorem localCov12883 : BstLean.Part259.LocalCovarianceOn covarianceEvent12883
    (BstLean.Part263.cell scalarRow12883.grid) (caps repair12883) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12883

theorem covarianceGood12883_payment :
    (retDist (paperDesignP 12883).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12883)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12883_payment



end BstLean.Part269.N12883

namespace BstLean.Part269.N12883
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12883}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12883.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12883) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12883).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12883 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12883) (by norm_num) BstLean.Part268.WorldRow12883.worldPackage rfl
    BstLean.Part268.WorldRow12883.product_lower (BstLean.Part268.WorldRow12883.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12883} (hw : c ∈ Hof BstLean.Part268.WorldRow12883.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12883) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12883) (by norm_num) BstLean.Part268.WorldRow12883.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12883} (hw : c ∈ Hof BstLean.Part268.WorldRow12883.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12883) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12883).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12883) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12883_eq : scalarRow12883.targetFrame = BstLean.Part268.agent12883.frame := by
  norm_num [scalarRow12883,BstLean.Part268.agent12883]

noncomputable def frameData12883 : BstLean.Part264b.FrameData 12883 :=
  BstLean.Part269.frameData_from_numerics (n := 12883) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12883.worldPackage rfl BstLean.Part268.WorldRow12883.product_lower (BstLean.Part268.WorldRow12883.producthi.2.trans (by norm_num))
    scalarRow12883 repair12883 covarianceInputs12883 (fun i hi => sourceNumerics12883 hi)
    BstLean.Part268.agent12883.frame targetFrame12883_eq


end BstLean.Part269.N12883

namespace BstLean.Part269.N12884
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12884 : scalarRow12884.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12884, BstLean.Part268.grid12884, BstLean.Part263.worldGrid]

theorem supplies12884 (j : Fin 43) : Supply 12884 (parameters j)
    (cellLower scalarRow12884.grid (sourceIndex j))
    (cellUpper scalarRow12884.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12884.grid grid_top_bounds12884 j

theorem radii12884 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12884.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12884 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12884 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12884.grid grid_top_bounds12884 j hθ

noncomputable def covarianceInputs12884 :
    BstLean.Part263.CovarianceInputs 12884 scalarRow12884.grid parameters (caps repair12884) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12884 grid_top_bounds12884 repair12884

noncomputable def covarianceEvent12884 : Set (AgFam 12884) :=
  BstLean.Part263.covarianceEvent 12884 scalarRow12884.grid parameters

theorem covarianceEvent12884_measurable : MeasurableSet covarianceEvent12884 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12884_payment :
    (retDist (paperDesignP 12884).toCentres).real
      (agentEv (paperDesignP 12884) covarianceEvent12884)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12884

theorem localCov12884 : BstLean.Part259.LocalCovarianceOn covarianceEvent12884
    (BstLean.Part263.cell scalarRow12884.grid) (caps repair12884) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12884

theorem covarianceGood12884_payment :
    (retDist (paperDesignP 12884).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12884)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12884_payment



end BstLean.Part269.N12884

namespace BstLean.Part269.N12884
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12884}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12884.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12884) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12884).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12884 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12884) (by norm_num) BstLean.Part268.WorldRow12884.worldPackage rfl
    BstLean.Part268.WorldRow12884.product_lower (BstLean.Part268.WorldRow12884.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12884} (hw : c ∈ Hof BstLean.Part268.WorldRow12884.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12884) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12884) (by norm_num) BstLean.Part268.WorldRow12884.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12884} (hw : c ∈ Hof BstLean.Part268.WorldRow12884.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12884) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12884).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12884) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12884_eq : scalarRow12884.targetFrame = BstLean.Part268.agent12884.frame := by
  norm_num [scalarRow12884,BstLean.Part268.agent12884]

noncomputable def frameData12884 : BstLean.Part264b.FrameData 12884 :=
  BstLean.Part269.frameData_from_numerics (n := 12884) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12884.worldPackage rfl BstLean.Part268.WorldRow12884.product_lower (BstLean.Part268.WorldRow12884.producthi.2.trans (by norm_num))
    scalarRow12884 repair12884 covarianceInputs12884 (fun i hi => sourceNumerics12884 hi)
    BstLean.Part268.agent12884.frame targetFrame12884_eq


end BstLean.Part269.N12884
