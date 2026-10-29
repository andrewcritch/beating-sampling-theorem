import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World20Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs20
import BstLean.Part269Rows20
import BstLean.Part269Sources20
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12870
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12870 : scalarRow12870.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12870, BstLean.Part268.grid12870, BstLean.Part263.worldGrid]

theorem supplies12870 (j : Fin 43) : Supply 12870 (parameters j)
    (cellLower scalarRow12870.grid (sourceIndex j))
    (cellUpper scalarRow12870.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12870.grid grid_top_bounds12870 j

theorem radii12870 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12870.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12870 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12870 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12870.grid grid_top_bounds12870 j hθ

noncomputable def covarianceInputs12870 :
    BstLean.Part263.CovarianceInputs 12870 scalarRow12870.grid parameters (caps repair12870) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12870 grid_top_bounds12870 repair12870

noncomputable def covarianceEvent12870 : Set (AgFam 12870) :=
  BstLean.Part263.covarianceEvent 12870 scalarRow12870.grid parameters

theorem covarianceEvent12870_measurable : MeasurableSet covarianceEvent12870 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12870_payment :
    (retDist (paperDesignP 12870).toCentres).real
      (agentEv (paperDesignP 12870) covarianceEvent12870)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12870

theorem localCov12870 : BstLean.Part259.LocalCovarianceOn covarianceEvent12870
    (BstLean.Part263.cell scalarRow12870.grid) (caps repair12870) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12870

theorem covarianceGood12870_payment :
    (retDist (paperDesignP 12870).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12870)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12870_payment



end BstLean.Part269.N12870

namespace BstLean.Part269.N12870
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12870}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12870.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12870) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12870).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12870 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12870) (by norm_num) BstLean.Part268.WorldRow12870.worldPackage rfl
    BstLean.Part268.WorldRow12870.product_lower (BstLean.Part268.WorldRow12870.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12870} (hw : c ∈ Hof BstLean.Part268.WorldRow12870.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12870) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12870) (by norm_num) BstLean.Part268.WorldRow12870.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12870} (hw : c ∈ Hof BstLean.Part268.WorldRow12870.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12870) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12870).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12870) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12870_eq : scalarRow12870.targetFrame = BstLean.Part268.agent12870.frame := by
  norm_num [scalarRow12870,BstLean.Part268.agent12870]

noncomputable def frameData12870 : BstLean.Part264b.FrameData 12870 :=
  BstLean.Part269.frameData_from_numerics (n := 12870) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12870.worldPackage rfl BstLean.Part268.WorldRow12870.product_lower (BstLean.Part268.WorldRow12870.producthi.2.trans (by norm_num))
    scalarRow12870 repair12870 covarianceInputs12870 (fun i hi => sourceNumerics12870 hi)
    BstLean.Part268.agent12870.frame targetFrame12870_eq


end BstLean.Part269.N12870

namespace BstLean.Part269.N12871
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12871 : scalarRow12871.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12871, BstLean.Part268.grid12871, BstLean.Part263.worldGrid]

theorem supplies12871 (j : Fin 43) : Supply 12871 (parameters j)
    (cellLower scalarRow12871.grid (sourceIndex j))
    (cellUpper scalarRow12871.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12871.grid grid_top_bounds12871 j

theorem radii12871 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12871.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12871 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12871 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12871.grid grid_top_bounds12871 j hθ

noncomputable def covarianceInputs12871 :
    BstLean.Part263.CovarianceInputs 12871 scalarRow12871.grid parameters (caps repair12871) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12871 grid_top_bounds12871 repair12871

noncomputable def covarianceEvent12871 : Set (AgFam 12871) :=
  BstLean.Part263.covarianceEvent 12871 scalarRow12871.grid parameters

theorem covarianceEvent12871_measurable : MeasurableSet covarianceEvent12871 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12871_payment :
    (retDist (paperDesignP 12871).toCentres).real
      (agentEv (paperDesignP 12871) covarianceEvent12871)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12871

theorem localCov12871 : BstLean.Part259.LocalCovarianceOn covarianceEvent12871
    (BstLean.Part263.cell scalarRow12871.grid) (caps repair12871) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12871

theorem covarianceGood12871_payment :
    (retDist (paperDesignP 12871).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12871)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12871_payment



end BstLean.Part269.N12871

namespace BstLean.Part269.N12871
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12871}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12871.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12871) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12871).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12871 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12871) (by norm_num) BstLean.Part268.WorldRow12871.worldPackage rfl
    BstLean.Part268.WorldRow12871.product_lower (BstLean.Part268.WorldRow12871.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12871} (hw : c ∈ Hof BstLean.Part268.WorldRow12871.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12871) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12871) (by norm_num) BstLean.Part268.WorldRow12871.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12871} (hw : c ∈ Hof BstLean.Part268.WorldRow12871.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12871) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12871).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12871) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12871_eq : scalarRow12871.targetFrame = BstLean.Part268.agent12871.frame := by
  norm_num [scalarRow12871,BstLean.Part268.agent12871]

noncomputable def frameData12871 : BstLean.Part264b.FrameData 12871 :=
  BstLean.Part269.frameData_from_numerics (n := 12871) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12871.worldPackage rfl BstLean.Part268.WorldRow12871.product_lower (BstLean.Part268.WorldRow12871.producthi.2.trans (by norm_num))
    scalarRow12871 repair12871 covarianceInputs12871 (fun i hi => sourceNumerics12871 hi)
    BstLean.Part268.agent12871.frame targetFrame12871_eq


end BstLean.Part269.N12871

namespace BstLean.Part269.N12872
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12872 : scalarRow12872.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12872, BstLean.Part268.grid12872, BstLean.Part263.worldGrid]

theorem supplies12872 (j : Fin 43) : Supply 12872 (parameters j)
    (cellLower scalarRow12872.grid (sourceIndex j))
    (cellUpper scalarRow12872.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12872.grid grid_top_bounds12872 j

theorem radii12872 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12872.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12872 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12872 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12872.grid grid_top_bounds12872 j hθ

noncomputable def covarianceInputs12872 :
    BstLean.Part263.CovarianceInputs 12872 scalarRow12872.grid parameters (caps repair12872) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12872 grid_top_bounds12872 repair12872

noncomputable def covarianceEvent12872 : Set (AgFam 12872) :=
  BstLean.Part263.covarianceEvent 12872 scalarRow12872.grid parameters

theorem covarianceEvent12872_measurable : MeasurableSet covarianceEvent12872 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12872_payment :
    (retDist (paperDesignP 12872).toCentres).real
      (agentEv (paperDesignP 12872) covarianceEvent12872)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12872

theorem localCov12872 : BstLean.Part259.LocalCovarianceOn covarianceEvent12872
    (BstLean.Part263.cell scalarRow12872.grid) (caps repair12872) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12872

theorem covarianceGood12872_payment :
    (retDist (paperDesignP 12872).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12872)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12872_payment



end BstLean.Part269.N12872

namespace BstLean.Part269.N12872
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12872}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12872.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12872) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12872).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12872 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12872) (by norm_num) BstLean.Part268.WorldRow12872.worldPackage rfl
    BstLean.Part268.WorldRow12872.product_lower (BstLean.Part268.WorldRow12872.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12872} (hw : c ∈ Hof BstLean.Part268.WorldRow12872.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12872) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12872) (by norm_num) BstLean.Part268.WorldRow12872.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12872} (hw : c ∈ Hof BstLean.Part268.WorldRow12872.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12872) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12872).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12872) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12872_eq : scalarRow12872.targetFrame = BstLean.Part268.agent12872.frame := by
  norm_num [scalarRow12872,BstLean.Part268.agent12872]

noncomputable def frameData12872 : BstLean.Part264b.FrameData 12872 :=
  BstLean.Part269.frameData_from_numerics (n := 12872) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12872.worldPackage rfl BstLean.Part268.WorldRow12872.product_lower (BstLean.Part268.WorldRow12872.producthi.2.trans (by norm_num))
    scalarRow12872 repair12872 covarianceInputs12872 (fun i hi => sourceNumerics12872 hi)
    BstLean.Part268.agent12872.frame targetFrame12872_eq


end BstLean.Part269.N12872

namespace BstLean.Part269.N12873
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12873 : scalarRow12873.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12873, BstLean.Part268.grid12873, BstLean.Part263.worldGrid]

theorem supplies12873 (j : Fin 43) : Supply 12873 (parameters j)
    (cellLower scalarRow12873.grid (sourceIndex j))
    (cellUpper scalarRow12873.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12873.grid grid_top_bounds12873 j

theorem radii12873 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12873.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12873 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12873 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12873.grid grid_top_bounds12873 j hθ

noncomputable def covarianceInputs12873 :
    BstLean.Part263.CovarianceInputs 12873 scalarRow12873.grid parameters (caps repair12873) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12873 grid_top_bounds12873 repair12873

noncomputable def covarianceEvent12873 : Set (AgFam 12873) :=
  BstLean.Part263.covarianceEvent 12873 scalarRow12873.grid parameters

theorem covarianceEvent12873_measurable : MeasurableSet covarianceEvent12873 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12873_payment :
    (retDist (paperDesignP 12873).toCentres).real
      (agentEv (paperDesignP 12873) covarianceEvent12873)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12873

theorem localCov12873 : BstLean.Part259.LocalCovarianceOn covarianceEvent12873
    (BstLean.Part263.cell scalarRow12873.grid) (caps repair12873) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12873

theorem covarianceGood12873_payment :
    (retDist (paperDesignP 12873).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12873)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12873_payment



end BstLean.Part269.N12873

namespace BstLean.Part269.N12873
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12873}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12873.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12873) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12873).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12873 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12873) (by norm_num) BstLean.Part268.WorldRow12873.worldPackage rfl
    BstLean.Part268.WorldRow12873.product_lower (BstLean.Part268.WorldRow12873.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12873} (hw : c ∈ Hof BstLean.Part268.WorldRow12873.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12873) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12873) (by norm_num) BstLean.Part268.WorldRow12873.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12873} (hw : c ∈ Hof BstLean.Part268.WorldRow12873.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12873) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12873).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12873) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12873_eq : scalarRow12873.targetFrame = BstLean.Part268.agent12873.frame := by
  norm_num [scalarRow12873,BstLean.Part268.agent12873]

noncomputable def frameData12873 : BstLean.Part264b.FrameData 12873 :=
  BstLean.Part269.frameData_from_numerics (n := 12873) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12873.worldPackage rfl BstLean.Part268.WorldRow12873.product_lower (BstLean.Part268.WorldRow12873.producthi.2.trans (by norm_num))
    scalarRow12873 repair12873 covarianceInputs12873 (fun i hi => sourceNumerics12873 hi)
    BstLean.Part268.agent12873.frame targetFrame12873_eq


end BstLean.Part269.N12873

namespace BstLean.Part269.N12874
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12874 : scalarRow12874.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12874, BstLean.Part268.grid12874, BstLean.Part263.worldGrid]

theorem supplies12874 (j : Fin 43) : Supply 12874 (parameters j)
    (cellLower scalarRow12874.grid (sourceIndex j))
    (cellUpper scalarRow12874.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12874.grid grid_top_bounds12874 j

theorem radii12874 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12874.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12874 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12874 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12874.grid grid_top_bounds12874 j hθ

noncomputable def covarianceInputs12874 :
    BstLean.Part263.CovarianceInputs 12874 scalarRow12874.grid parameters (caps repair12874) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12874 grid_top_bounds12874 repair12874

noncomputable def covarianceEvent12874 : Set (AgFam 12874) :=
  BstLean.Part263.covarianceEvent 12874 scalarRow12874.grid parameters

theorem covarianceEvent12874_measurable : MeasurableSet covarianceEvent12874 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12874_payment :
    (retDist (paperDesignP 12874).toCentres).real
      (agentEv (paperDesignP 12874) covarianceEvent12874)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12874

theorem localCov12874 : BstLean.Part259.LocalCovarianceOn covarianceEvent12874
    (BstLean.Part263.cell scalarRow12874.grid) (caps repair12874) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12874

theorem covarianceGood12874_payment :
    (retDist (paperDesignP 12874).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12874)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12874_payment



end BstLean.Part269.N12874

namespace BstLean.Part269.N12874
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12874}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12874.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12874) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12874).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12874 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12874) (by norm_num) BstLean.Part268.WorldRow12874.worldPackage rfl
    BstLean.Part268.WorldRow12874.product_lower (BstLean.Part268.WorldRow12874.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12874} (hw : c ∈ Hof BstLean.Part268.WorldRow12874.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12874) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12874) (by norm_num) BstLean.Part268.WorldRow12874.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12874} (hw : c ∈ Hof BstLean.Part268.WorldRow12874.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12874) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12874).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12874) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12874_eq : scalarRow12874.targetFrame = BstLean.Part268.agent12874.frame := by
  norm_num [scalarRow12874,BstLean.Part268.agent12874]

noncomputable def frameData12874 : BstLean.Part264b.FrameData 12874 :=
  BstLean.Part269.frameData_from_numerics (n := 12874) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12874.worldPackage rfl BstLean.Part268.WorldRow12874.product_lower (BstLean.Part268.WorldRow12874.producthi.2.trans (by norm_num))
    scalarRow12874 repair12874 covarianceInputs12874 (fun i hi => sourceNumerics12874 hi)
    BstLean.Part268.agent12874.frame targetFrame12874_eq


end BstLean.Part269.N12874
