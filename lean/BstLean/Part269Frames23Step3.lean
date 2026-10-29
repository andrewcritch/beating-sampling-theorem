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

namespace BstLean.Part269.N12940
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12940 : scalarRow12940.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12940, BstLean.Part268.grid12940, BstLean.Part263.worldGrid]

theorem supplies12940 (j : Fin 43) : Supply 12940 (parameters j)
    (cellLower scalarRow12940.grid (sourceIndex j))
    (cellUpper scalarRow12940.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12940.grid grid_top_bounds12940 j

theorem radii12940 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12940.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12940 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12940 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12940.grid grid_top_bounds12940 j hθ

noncomputable def covarianceInputs12940 :
    BstLean.Part263.CovarianceInputs 12940 scalarRow12940.grid parameters (caps repair12940) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12940 grid_top_bounds12940 repair12940

noncomputable def covarianceEvent12940 : Set (AgFam 12940) :=
  BstLean.Part263.covarianceEvent 12940 scalarRow12940.grid parameters

theorem covarianceEvent12940_measurable : MeasurableSet covarianceEvent12940 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12940_payment :
    (retDist (paperDesignP 12940).toCentres).real
      (agentEv (paperDesignP 12940) covarianceEvent12940)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12940

theorem localCov12940 : BstLean.Part259.LocalCovarianceOn covarianceEvent12940
    (BstLean.Part263.cell scalarRow12940.grid) (caps repair12940) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12940

theorem covarianceGood12940_payment :
    (retDist (paperDesignP 12940).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12940)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12940_payment



end BstLean.Part269.N12940

namespace BstLean.Part269.N12940
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12940}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12940.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12940) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12940).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12940 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12940) (by norm_num) BstLean.Part268.WorldRow12940.worldPackage rfl
    BstLean.Part268.WorldRow12940.product_lower (BstLean.Part268.WorldRow12940.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12940} (hw : c ∈ Hof BstLean.Part268.WorldRow12940.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12940) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12940) (by norm_num) BstLean.Part268.WorldRow12940.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12940} (hw : c ∈ Hof BstLean.Part268.WorldRow12940.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12940) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12940).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12940) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12940_eq : scalarRow12940.targetFrame = BstLean.Part268.agent12940.frame := by
  norm_num [scalarRow12940,BstLean.Part268.agent12940]

noncomputable def frameData12940 : BstLean.Part264b.FrameData 12940 :=
  BstLean.Part269.frameData_from_numerics (n := 12940) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12940.worldPackage rfl BstLean.Part268.WorldRow12940.product_lower (BstLean.Part268.WorldRow12940.producthi.2.trans (by norm_num))
    scalarRow12940 repair12940 covarianceInputs12940 (fun i hi => sourceNumerics12940 hi)
    BstLean.Part268.agent12940.frame targetFrame12940_eq


end BstLean.Part269.N12940

namespace BstLean.Part269.N12941
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12941 : scalarRow12941.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12941, BstLean.Part268.grid12941, BstLean.Part263.worldGrid]

theorem supplies12941 (j : Fin 43) : Supply 12941 (parameters j)
    (cellLower scalarRow12941.grid (sourceIndex j))
    (cellUpper scalarRow12941.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12941.grid grid_top_bounds12941 j

theorem radii12941 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12941.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12941 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12941 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12941.grid grid_top_bounds12941 j hθ

noncomputable def covarianceInputs12941 :
    BstLean.Part263.CovarianceInputs 12941 scalarRow12941.grid parameters (caps repair12941) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12941 grid_top_bounds12941 repair12941

noncomputable def covarianceEvent12941 : Set (AgFam 12941) :=
  BstLean.Part263.covarianceEvent 12941 scalarRow12941.grid parameters

theorem covarianceEvent12941_measurable : MeasurableSet covarianceEvent12941 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12941_payment :
    (retDist (paperDesignP 12941).toCentres).real
      (agentEv (paperDesignP 12941) covarianceEvent12941)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12941

theorem localCov12941 : BstLean.Part259.LocalCovarianceOn covarianceEvent12941
    (BstLean.Part263.cell scalarRow12941.grid) (caps repair12941) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12941

theorem covarianceGood12941_payment :
    (retDist (paperDesignP 12941).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12941)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12941_payment



end BstLean.Part269.N12941

namespace BstLean.Part269.N12941
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12941}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12941.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12941) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12941).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12941 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12941) (by norm_num) BstLean.Part268.WorldRow12941.worldPackage rfl
    BstLean.Part268.WorldRow12941.product_lower (BstLean.Part268.WorldRow12941.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12941} (hw : c ∈ Hof BstLean.Part268.WorldRow12941.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12941) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12941) (by norm_num) BstLean.Part268.WorldRow12941.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12941} (hw : c ∈ Hof BstLean.Part268.WorldRow12941.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12941) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12941).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12941) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12941_eq : scalarRow12941.targetFrame = BstLean.Part268.agent12941.frame := by
  norm_num [scalarRow12941,BstLean.Part268.agent12941]

noncomputable def frameData12941 : BstLean.Part264b.FrameData 12941 :=
  BstLean.Part269.frameData_from_numerics (n := 12941) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12941.worldPackage rfl BstLean.Part268.WorldRow12941.product_lower (BstLean.Part268.WorldRow12941.producthi.2.trans (by norm_num))
    scalarRow12941 repair12941 covarianceInputs12941 (fun i hi => sourceNumerics12941 hi)
    BstLean.Part268.agent12941.frame targetFrame12941_eq


end BstLean.Part269.N12941

namespace BstLean.Part269.N12942
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12942 : scalarRow12942.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12942, BstLean.Part268.grid12942, BstLean.Part263.worldGrid]

theorem supplies12942 (j : Fin 43) : Supply 12942 (parameters j)
    (cellLower scalarRow12942.grid (sourceIndex j))
    (cellUpper scalarRow12942.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12942.grid grid_top_bounds12942 j

theorem radii12942 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12942.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12942 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12942 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12942.grid grid_top_bounds12942 j hθ

noncomputable def covarianceInputs12942 :
    BstLean.Part263.CovarianceInputs 12942 scalarRow12942.grid parameters (caps repair12942) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12942 grid_top_bounds12942 repair12942

noncomputable def covarianceEvent12942 : Set (AgFam 12942) :=
  BstLean.Part263.covarianceEvent 12942 scalarRow12942.grid parameters

theorem covarianceEvent12942_measurable : MeasurableSet covarianceEvent12942 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12942_payment :
    (retDist (paperDesignP 12942).toCentres).real
      (agentEv (paperDesignP 12942) covarianceEvent12942)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12942

theorem localCov12942 : BstLean.Part259.LocalCovarianceOn covarianceEvent12942
    (BstLean.Part263.cell scalarRow12942.grid) (caps repair12942) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12942

theorem covarianceGood12942_payment :
    (retDist (paperDesignP 12942).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12942)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12942_payment



end BstLean.Part269.N12942

namespace BstLean.Part269.N12942
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12942}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12942.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12942) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12942).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12942 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12942) (by norm_num) BstLean.Part268.WorldRow12942.worldPackage rfl
    BstLean.Part268.WorldRow12942.product_lower (BstLean.Part268.WorldRow12942.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12942} (hw : c ∈ Hof BstLean.Part268.WorldRow12942.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12942) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12942) (by norm_num) BstLean.Part268.WorldRow12942.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12942} (hw : c ∈ Hof BstLean.Part268.WorldRow12942.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12942) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12942).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12942) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12942_eq : scalarRow12942.targetFrame = BstLean.Part268.agent12942.frame := by
  norm_num [scalarRow12942,BstLean.Part268.agent12942]

noncomputable def frameData12942 : BstLean.Part264b.FrameData 12942 :=
  BstLean.Part269.frameData_from_numerics (n := 12942) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12942.worldPackage rfl BstLean.Part268.WorldRow12942.product_lower (BstLean.Part268.WorldRow12942.producthi.2.trans (by norm_num))
    scalarRow12942 repair12942 covarianceInputs12942 (fun i hi => sourceNumerics12942 hi)
    BstLean.Part268.agent12942.frame targetFrame12942_eq


end BstLean.Part269.N12942

namespace BstLean.Part269.N12943
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12943 : scalarRow12943.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12943, BstLean.Part268.grid12943, BstLean.Part263.worldGrid]

theorem supplies12943 (j : Fin 43) : Supply 12943 (parameters j)
    (cellLower scalarRow12943.grid (sourceIndex j))
    (cellUpper scalarRow12943.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12943.grid grid_top_bounds12943 j

theorem radii12943 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12943.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12943 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12943 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12943.grid grid_top_bounds12943 j hθ

noncomputable def covarianceInputs12943 :
    BstLean.Part263.CovarianceInputs 12943 scalarRow12943.grid parameters (caps repair12943) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12943 grid_top_bounds12943 repair12943

noncomputable def covarianceEvent12943 : Set (AgFam 12943) :=
  BstLean.Part263.covarianceEvent 12943 scalarRow12943.grid parameters

theorem covarianceEvent12943_measurable : MeasurableSet covarianceEvent12943 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12943_payment :
    (retDist (paperDesignP 12943).toCentres).real
      (agentEv (paperDesignP 12943) covarianceEvent12943)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12943

theorem localCov12943 : BstLean.Part259.LocalCovarianceOn covarianceEvent12943
    (BstLean.Part263.cell scalarRow12943.grid) (caps repair12943) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12943

theorem covarianceGood12943_payment :
    (retDist (paperDesignP 12943).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12943)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12943_payment



end BstLean.Part269.N12943

namespace BstLean.Part269.N12943
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12943}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12943.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12943) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12943).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12943 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12943) (by norm_num) BstLean.Part268.WorldRow12943.worldPackage rfl
    BstLean.Part268.WorldRow12943.product_lower (BstLean.Part268.WorldRow12943.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12943} (hw : c ∈ Hof BstLean.Part268.WorldRow12943.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12943) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12943) (by norm_num) BstLean.Part268.WorldRow12943.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12943} (hw : c ∈ Hof BstLean.Part268.WorldRow12943.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12943) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12943).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12943) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12943_eq : scalarRow12943.targetFrame = BstLean.Part268.agent12943.frame := by
  norm_num [scalarRow12943,BstLean.Part268.agent12943]

noncomputable def frameData12943 : BstLean.Part264b.FrameData 12943 :=
  BstLean.Part269.frameData_from_numerics (n := 12943) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12943.worldPackage rfl BstLean.Part268.WorldRow12943.product_lower (BstLean.Part268.WorldRow12943.producthi.2.trans (by norm_num))
    scalarRow12943 repair12943 covarianceInputs12943 (fun i hi => sourceNumerics12943 hi)
    BstLean.Part268.agent12943.frame targetFrame12943_eq


end BstLean.Part269.N12943

namespace BstLean.Part269.N12944
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12944 : scalarRow12944.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12944, BstLean.Part268.grid12944, BstLean.Part263.worldGrid]

theorem supplies12944 (j : Fin 43) : Supply 12944 (parameters j)
    (cellLower scalarRow12944.grid (sourceIndex j))
    (cellUpper scalarRow12944.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12944.grid grid_top_bounds12944 j

theorem radii12944 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12944.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12944 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12944 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12944.grid grid_top_bounds12944 j hθ

noncomputable def covarianceInputs12944 :
    BstLean.Part263.CovarianceInputs 12944 scalarRow12944.grid parameters (caps repair12944) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12944 grid_top_bounds12944 repair12944

noncomputable def covarianceEvent12944 : Set (AgFam 12944) :=
  BstLean.Part263.covarianceEvent 12944 scalarRow12944.grid parameters

theorem covarianceEvent12944_measurable : MeasurableSet covarianceEvent12944 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12944_payment :
    (retDist (paperDesignP 12944).toCentres).real
      (agentEv (paperDesignP 12944) covarianceEvent12944)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12944

theorem localCov12944 : BstLean.Part259.LocalCovarianceOn covarianceEvent12944
    (BstLean.Part263.cell scalarRow12944.grid) (caps repair12944) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12944

theorem covarianceGood12944_payment :
    (retDist (paperDesignP 12944).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12944)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12944_payment



end BstLean.Part269.N12944

namespace BstLean.Part269.N12944
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12944}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12944.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12944) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12944).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12944 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12944) (by norm_num) BstLean.Part268.WorldRow12944.worldPackage rfl
    BstLean.Part268.WorldRow12944.product_lower (BstLean.Part268.WorldRow12944.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12944} (hw : c ∈ Hof BstLean.Part268.WorldRow12944.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12944) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12944) (by norm_num) BstLean.Part268.WorldRow12944.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12944} (hw : c ∈ Hof BstLean.Part268.WorldRow12944.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12944) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12944).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12944) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12944_eq : scalarRow12944.targetFrame = BstLean.Part268.agent12944.frame := by
  norm_num [scalarRow12944,BstLean.Part268.agent12944]

noncomputable def frameData12944 : BstLean.Part264b.FrameData 12944 :=
  BstLean.Part269.frameData_from_numerics (n := 12944) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12944.worldPackage rfl BstLean.Part268.WorldRow12944.product_lower (BstLean.Part268.WorldRow12944.producthi.2.trans (by norm_num))
    scalarRow12944 repair12944 covarianceInputs12944 (fun i hi => sourceNumerics12944 hi)
    BstLean.Part268.agent12944.frame targetFrame12944_eq


end BstLean.Part269.N12944
