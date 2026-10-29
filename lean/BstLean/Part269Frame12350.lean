import BstLean.Part269N12350Source
import BstLean.Part268World0Step6
import BstLean.Part269FrameAdapter
import BstLean.Part269Covariance12350
namespace BstLean.Part269.N12350
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12350}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12350.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12350) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12350).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12350 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12350) (by norm_num) BstLean.Part268.WorldRow12350.worldPackage rfl
    BstLean.Part268.WorldRow12350.product_lower (BstLean.Part268.WorldRow12350.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12350} (hw : c ∈ Hof BstLean.Part268.WorldRow12350.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12350) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12350) (by norm_num) BstLean.Part268.WorldRow12350.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12350} (hw : c ∈ Hof BstLean.Part268.WorldRow12350.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12350) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12350).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12350) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12350_eq : scalarRow12350.targetFrame = BstLean.Part268.agent12350.frame := by
  norm_num [scalarRow12350,BstLean.Part268.agent12350]

noncomputable def frameData12350 : BstLean.Part264b.FrameData 12350 :=
  BstLean.Part269.frameData_from_numerics (n := 12350) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12350.worldPackage rfl BstLean.Part268.WorldRow12350.product_lower (BstLean.Part268.WorldRow12350.producthi.2.trans (by norm_num))
    scalarRow12350 repair12350 covarianceInputs12350 (fun i hi => sourceNumerics12350 hi)
    BstLean.Part268.agent12350.frame targetFrame12350_eq

end BstLean.Part269.N12350

