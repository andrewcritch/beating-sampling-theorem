import BstLean.Part269FrameAdapter
import BstLean.Part269Covariance13224
import BstLean.Part269N13224Source
import BstLean.Part268World34Step6
namespace BstLean.Part269.N13224
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13224}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13224.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13224) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13224).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13224 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13224) (by norm_num) BstLean.Part268.WorldRow13224.worldPackage rfl
    BstLean.Part268.WorldRow13224.product_lower (BstLean.Part268.WorldRow13224.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13224} (hw : c ∈ Hof BstLean.Part268.WorldRow13224.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13224) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13224) (by norm_num) BstLean.Part268.WorldRow13224.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13224} (hw : c ∈ Hof BstLean.Part268.WorldRow13224.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13224) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13224).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13224) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13224_eq : scalarRow13224.targetFrame = BstLean.Part268.agent13224.frame := by
  norm_num [scalarRow13224,BstLean.Part268.agent13224]

noncomputable def frameData13224 : BstLean.Part264b.FrameData 13224 :=
  BstLean.Part269.frameData_from_numerics (n := 13224) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13224.worldPackage rfl BstLean.Part268.WorldRow13224.product_lower (BstLean.Part268.WorldRow13224.producthi.2.trans (by norm_num))
    scalarRow13224 repair13224 covarianceInputs13224 (fun i hi => sourceNumerics13224 hi)
    BstLean.Part268.agent13224.frame targetFrame13224_eq

end BstLean.Part269.N13224

