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

namespace BstLean.Part269.N12865
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12865 : scalarRow12865.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12865, BstLean.Part268.grid12865, BstLean.Part263.worldGrid]

theorem supplies12865 (j : Fin 43) : Supply 12865 (parameters j)
    (cellLower scalarRow12865.grid (sourceIndex j))
    (cellUpper scalarRow12865.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12865.grid grid_top_bounds12865 j

theorem radii12865 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12865.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12865 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12865 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12865.grid grid_top_bounds12865 j hθ

noncomputable def covarianceInputs12865 :
    BstLean.Part263.CovarianceInputs 12865 scalarRow12865.grid parameters (caps repair12865) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12865 grid_top_bounds12865 repair12865

noncomputable def covarianceEvent12865 : Set (AgFam 12865) :=
  BstLean.Part263.covarianceEvent 12865 scalarRow12865.grid parameters

theorem covarianceEvent12865_measurable : MeasurableSet covarianceEvent12865 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12865_payment :
    (retDist (paperDesignP 12865).toCentres).real
      (agentEv (paperDesignP 12865) covarianceEvent12865)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12865

theorem localCov12865 : BstLean.Part259.LocalCovarianceOn covarianceEvent12865
    (BstLean.Part263.cell scalarRow12865.grid) (caps repair12865) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12865

theorem covarianceGood12865_payment :
    (retDist (paperDesignP 12865).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12865)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12865_payment



end BstLean.Part269.N12865

namespace BstLean.Part269.N12865
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12865}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12865.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12865) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12865).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12865 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12865) (by norm_num) BstLean.Part268.WorldRow12865.worldPackage rfl
    BstLean.Part268.WorldRow12865.product_lower (BstLean.Part268.WorldRow12865.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12865} (hw : c ∈ Hof BstLean.Part268.WorldRow12865.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12865) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12865) (by norm_num) BstLean.Part268.WorldRow12865.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12865} (hw : c ∈ Hof BstLean.Part268.WorldRow12865.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12865) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12865).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12865) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12865_eq : scalarRow12865.targetFrame = BstLean.Part268.agent12865.frame := by
  norm_num [scalarRow12865,BstLean.Part268.agent12865]

noncomputable def frameData12865 : BstLean.Part264b.FrameData 12865 :=
  BstLean.Part269.frameData_from_numerics (n := 12865) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12865.worldPackage rfl BstLean.Part268.WorldRow12865.product_lower (BstLean.Part268.WorldRow12865.producthi.2.trans (by norm_num))
    scalarRow12865 repair12865 covarianceInputs12865 (fun i hi => sourceNumerics12865 hi)
    BstLean.Part268.agent12865.frame targetFrame12865_eq


end BstLean.Part269.N12865

namespace BstLean.Part269.N12866
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12866 : scalarRow12866.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12866, BstLean.Part268.grid12866, BstLean.Part263.worldGrid]

theorem supplies12866 (j : Fin 43) : Supply 12866 (parameters j)
    (cellLower scalarRow12866.grid (sourceIndex j))
    (cellUpper scalarRow12866.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12866.grid grid_top_bounds12866 j

theorem radii12866 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12866.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12866 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12866 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12866.grid grid_top_bounds12866 j hθ

noncomputable def covarianceInputs12866 :
    BstLean.Part263.CovarianceInputs 12866 scalarRow12866.grid parameters (caps repair12866) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12866 grid_top_bounds12866 repair12866

noncomputable def covarianceEvent12866 : Set (AgFam 12866) :=
  BstLean.Part263.covarianceEvent 12866 scalarRow12866.grid parameters

theorem covarianceEvent12866_measurable : MeasurableSet covarianceEvent12866 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12866_payment :
    (retDist (paperDesignP 12866).toCentres).real
      (agentEv (paperDesignP 12866) covarianceEvent12866)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12866

theorem localCov12866 : BstLean.Part259.LocalCovarianceOn covarianceEvent12866
    (BstLean.Part263.cell scalarRow12866.grid) (caps repair12866) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12866

theorem covarianceGood12866_payment :
    (retDist (paperDesignP 12866).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12866)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12866_payment



end BstLean.Part269.N12866

namespace BstLean.Part269.N12866
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12866}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12866.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12866) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12866).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12866 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12866) (by norm_num) BstLean.Part268.WorldRow12866.worldPackage rfl
    BstLean.Part268.WorldRow12866.product_lower (BstLean.Part268.WorldRow12866.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12866} (hw : c ∈ Hof BstLean.Part268.WorldRow12866.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12866) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12866) (by norm_num) BstLean.Part268.WorldRow12866.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12866} (hw : c ∈ Hof BstLean.Part268.WorldRow12866.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12866) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12866).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12866) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12866_eq : scalarRow12866.targetFrame = BstLean.Part268.agent12866.frame := by
  norm_num [scalarRow12866,BstLean.Part268.agent12866]

noncomputable def frameData12866 : BstLean.Part264b.FrameData 12866 :=
  BstLean.Part269.frameData_from_numerics (n := 12866) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12866.worldPackage rfl BstLean.Part268.WorldRow12866.product_lower (BstLean.Part268.WorldRow12866.producthi.2.trans (by norm_num))
    scalarRow12866 repair12866 covarianceInputs12866 (fun i hi => sourceNumerics12866 hi)
    BstLean.Part268.agent12866.frame targetFrame12866_eq


end BstLean.Part269.N12866

namespace BstLean.Part269.N12867
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12867 : scalarRow12867.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12867, BstLean.Part268.grid12867, BstLean.Part263.worldGrid]

theorem supplies12867 (j : Fin 43) : Supply 12867 (parameters j)
    (cellLower scalarRow12867.grid (sourceIndex j))
    (cellUpper scalarRow12867.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12867.grid grid_top_bounds12867 j

theorem radii12867 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12867.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12867 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12867 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12867.grid grid_top_bounds12867 j hθ

noncomputable def covarianceInputs12867 :
    BstLean.Part263.CovarianceInputs 12867 scalarRow12867.grid parameters (caps repair12867) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12867 grid_top_bounds12867 repair12867

noncomputable def covarianceEvent12867 : Set (AgFam 12867) :=
  BstLean.Part263.covarianceEvent 12867 scalarRow12867.grid parameters

theorem covarianceEvent12867_measurable : MeasurableSet covarianceEvent12867 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12867_payment :
    (retDist (paperDesignP 12867).toCentres).real
      (agentEv (paperDesignP 12867) covarianceEvent12867)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12867

theorem localCov12867 : BstLean.Part259.LocalCovarianceOn covarianceEvent12867
    (BstLean.Part263.cell scalarRow12867.grid) (caps repair12867) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12867

theorem covarianceGood12867_payment :
    (retDist (paperDesignP 12867).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12867)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12867_payment



end BstLean.Part269.N12867

namespace BstLean.Part269.N12867
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12867}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12867.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12867) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12867).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12867 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12867) (by norm_num) BstLean.Part268.WorldRow12867.worldPackage rfl
    BstLean.Part268.WorldRow12867.product_lower (BstLean.Part268.WorldRow12867.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12867} (hw : c ∈ Hof BstLean.Part268.WorldRow12867.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12867) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12867) (by norm_num) BstLean.Part268.WorldRow12867.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12867} (hw : c ∈ Hof BstLean.Part268.WorldRow12867.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12867) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12867).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12867) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12867_eq : scalarRow12867.targetFrame = BstLean.Part268.agent12867.frame := by
  norm_num [scalarRow12867,BstLean.Part268.agent12867]

noncomputable def frameData12867 : BstLean.Part264b.FrameData 12867 :=
  BstLean.Part269.frameData_from_numerics (n := 12867) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12867.worldPackage rfl BstLean.Part268.WorldRow12867.product_lower (BstLean.Part268.WorldRow12867.producthi.2.trans (by norm_num))
    scalarRow12867 repair12867 covarianceInputs12867 (fun i hi => sourceNumerics12867 hi)
    BstLean.Part268.agent12867.frame targetFrame12867_eq


end BstLean.Part269.N12867

namespace BstLean.Part269.N12868
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12868 : scalarRow12868.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12868, BstLean.Part268.grid12868, BstLean.Part263.worldGrid]

theorem supplies12868 (j : Fin 43) : Supply 12868 (parameters j)
    (cellLower scalarRow12868.grid (sourceIndex j))
    (cellUpper scalarRow12868.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12868.grid grid_top_bounds12868 j

theorem radii12868 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12868.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12868 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12868 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12868.grid grid_top_bounds12868 j hθ

noncomputable def covarianceInputs12868 :
    BstLean.Part263.CovarianceInputs 12868 scalarRow12868.grid parameters (caps repair12868) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12868 grid_top_bounds12868 repair12868

noncomputable def covarianceEvent12868 : Set (AgFam 12868) :=
  BstLean.Part263.covarianceEvent 12868 scalarRow12868.grid parameters

theorem covarianceEvent12868_measurable : MeasurableSet covarianceEvent12868 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12868_payment :
    (retDist (paperDesignP 12868).toCentres).real
      (agentEv (paperDesignP 12868) covarianceEvent12868)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12868

theorem localCov12868 : BstLean.Part259.LocalCovarianceOn covarianceEvent12868
    (BstLean.Part263.cell scalarRow12868.grid) (caps repair12868) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12868

theorem covarianceGood12868_payment :
    (retDist (paperDesignP 12868).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12868)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12868_payment



end BstLean.Part269.N12868

namespace BstLean.Part269.N12868
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12868}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12868.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12868) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12868).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12868 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12868) (by norm_num) BstLean.Part268.WorldRow12868.worldPackage rfl
    BstLean.Part268.WorldRow12868.product_lower (BstLean.Part268.WorldRow12868.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12868} (hw : c ∈ Hof BstLean.Part268.WorldRow12868.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12868) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12868) (by norm_num) BstLean.Part268.WorldRow12868.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12868} (hw : c ∈ Hof BstLean.Part268.WorldRow12868.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12868) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12868).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12868) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12868_eq : scalarRow12868.targetFrame = BstLean.Part268.agent12868.frame := by
  norm_num [scalarRow12868,BstLean.Part268.agent12868]

noncomputable def frameData12868 : BstLean.Part264b.FrameData 12868 :=
  BstLean.Part269.frameData_from_numerics (n := 12868) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12868.worldPackage rfl BstLean.Part268.WorldRow12868.product_lower (BstLean.Part268.WorldRow12868.producthi.2.trans (by norm_num))
    scalarRow12868 repair12868 covarianceInputs12868 (fun i hi => sourceNumerics12868 hi)
    BstLean.Part268.agent12868.frame targetFrame12868_eq


end BstLean.Part269.N12868

namespace BstLean.Part269.N12869
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12869 : scalarRow12869.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12869, BstLean.Part268.grid12869, BstLean.Part263.worldGrid]

theorem supplies12869 (j : Fin 43) : Supply 12869 (parameters j)
    (cellLower scalarRow12869.grid (sourceIndex j))
    (cellUpper scalarRow12869.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12869.grid grid_top_bounds12869 j

theorem radii12869 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12869.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12869 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12869 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12869.grid grid_top_bounds12869 j hθ

noncomputable def covarianceInputs12869 :
    BstLean.Part263.CovarianceInputs 12869 scalarRow12869.grid parameters (caps repair12869) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12869 grid_top_bounds12869 repair12869

noncomputable def covarianceEvent12869 : Set (AgFam 12869) :=
  BstLean.Part263.covarianceEvent 12869 scalarRow12869.grid parameters

theorem covarianceEvent12869_measurable : MeasurableSet covarianceEvent12869 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12869_payment :
    (retDist (paperDesignP 12869).toCentres).real
      (agentEv (paperDesignP 12869) covarianceEvent12869)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12869

theorem localCov12869 : BstLean.Part259.LocalCovarianceOn covarianceEvent12869
    (BstLean.Part263.cell scalarRow12869.grid) (caps repair12869) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12869

theorem covarianceGood12869_payment :
    (retDist (paperDesignP 12869).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12869)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12869_payment



end BstLean.Part269.N12869

namespace BstLean.Part269.N12869
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12869}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12869.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12869) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12869).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12869 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12869) (by norm_num) BstLean.Part268.WorldRow12869.worldPackage rfl
    BstLean.Part268.WorldRow12869.product_lower (BstLean.Part268.WorldRow12869.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12869} (hw : c ∈ Hof BstLean.Part268.WorldRow12869.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12869) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12869) (by norm_num) BstLean.Part268.WorldRow12869.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12869} (hw : c ∈ Hof BstLean.Part268.WorldRow12869.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12869) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12869).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12869) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12869_eq : scalarRow12869.targetFrame = BstLean.Part268.agent12869.frame := by
  norm_num [scalarRow12869,BstLean.Part268.agent12869]

noncomputable def frameData12869 : BstLean.Part264b.FrameData 12869 :=
  BstLean.Part269.frameData_from_numerics (n := 12869) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12869.worldPackage rfl BstLean.Part268.WorldRow12869.product_lower (BstLean.Part268.WorldRow12869.producthi.2.trans (by norm_num))
    scalarRow12869 repair12869 covarianceInputs12869 (fun i hi => sourceNumerics12869 hi)
    BstLean.Part268.agent12869.frame targetFrame12869_eq


end BstLean.Part269.N12869
