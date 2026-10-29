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

namespace BstLean.Part269.N12885
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12885 : scalarRow12885.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12885, BstLean.Part268.grid12885, BstLean.Part263.worldGrid]

theorem supplies12885 (j : Fin 43) : Supply 12885 (parameters j)
    (cellLower scalarRow12885.grid (sourceIndex j))
    (cellUpper scalarRow12885.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12885.grid grid_top_bounds12885 j

theorem radii12885 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12885.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12885 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12885 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12885.grid grid_top_bounds12885 j hθ

noncomputable def covarianceInputs12885 :
    BstLean.Part263.CovarianceInputs 12885 scalarRow12885.grid parameters (caps repair12885) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12885 grid_top_bounds12885 repair12885

noncomputable def covarianceEvent12885 : Set (AgFam 12885) :=
  BstLean.Part263.covarianceEvent 12885 scalarRow12885.grid parameters

theorem covarianceEvent12885_measurable : MeasurableSet covarianceEvent12885 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12885_payment :
    (retDist (paperDesignP 12885).toCentres).real
      (agentEv (paperDesignP 12885) covarianceEvent12885)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12885

theorem localCov12885 : BstLean.Part259.LocalCovarianceOn covarianceEvent12885
    (BstLean.Part263.cell scalarRow12885.grid) (caps repair12885) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12885

theorem covarianceGood12885_payment :
    (retDist (paperDesignP 12885).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12885)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12885_payment



end BstLean.Part269.N12885

namespace BstLean.Part269.N12885
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12885}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12885.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12885) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12885).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12885 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12885) (by norm_num) BstLean.Part268.WorldRow12885.worldPackage rfl
    BstLean.Part268.WorldRow12885.product_lower (BstLean.Part268.WorldRow12885.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12885} (hw : c ∈ Hof BstLean.Part268.WorldRow12885.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12885) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12885) (by norm_num) BstLean.Part268.WorldRow12885.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12885} (hw : c ∈ Hof BstLean.Part268.WorldRow12885.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12885) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12885).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12885) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12885_eq : scalarRow12885.targetFrame = BstLean.Part268.agent12885.frame := by
  norm_num [scalarRow12885,BstLean.Part268.agent12885]

noncomputable def frameData12885 : BstLean.Part264b.FrameData 12885 :=
  BstLean.Part269.frameData_from_numerics (n := 12885) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12885.worldPackage rfl BstLean.Part268.WorldRow12885.product_lower (BstLean.Part268.WorldRow12885.producthi.2.trans (by norm_num))
    scalarRow12885 repair12885 covarianceInputs12885 (fun i hi => sourceNumerics12885 hi)
    BstLean.Part268.agent12885.frame targetFrame12885_eq


end BstLean.Part269.N12885

namespace BstLean.Part269.N12886
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12886 : scalarRow12886.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12886, BstLean.Part268.grid12886, BstLean.Part263.worldGrid]

theorem supplies12886 (j : Fin 43) : Supply 12886 (parameters j)
    (cellLower scalarRow12886.grid (sourceIndex j))
    (cellUpper scalarRow12886.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12886.grid grid_top_bounds12886 j

theorem radii12886 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12886.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12886 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12886 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12886.grid grid_top_bounds12886 j hθ

noncomputable def covarianceInputs12886 :
    BstLean.Part263.CovarianceInputs 12886 scalarRow12886.grid parameters (caps repair12886) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12886 grid_top_bounds12886 repair12886

noncomputable def covarianceEvent12886 : Set (AgFam 12886) :=
  BstLean.Part263.covarianceEvent 12886 scalarRow12886.grid parameters

theorem covarianceEvent12886_measurable : MeasurableSet covarianceEvent12886 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12886_payment :
    (retDist (paperDesignP 12886).toCentres).real
      (agentEv (paperDesignP 12886) covarianceEvent12886)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12886

theorem localCov12886 : BstLean.Part259.LocalCovarianceOn covarianceEvent12886
    (BstLean.Part263.cell scalarRow12886.grid) (caps repair12886) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12886

theorem covarianceGood12886_payment :
    (retDist (paperDesignP 12886).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12886)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12886_payment



end BstLean.Part269.N12886

namespace BstLean.Part269.N12886
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12886}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12886.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12886) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12886).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12886 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12886) (by norm_num) BstLean.Part268.WorldRow12886.worldPackage rfl
    BstLean.Part268.WorldRow12886.product_lower (BstLean.Part268.WorldRow12886.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12886} (hw : c ∈ Hof BstLean.Part268.WorldRow12886.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12886) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12886) (by norm_num) BstLean.Part268.WorldRow12886.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12886} (hw : c ∈ Hof BstLean.Part268.WorldRow12886.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12886) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12886).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12886) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12886_eq : scalarRow12886.targetFrame = BstLean.Part268.agent12886.frame := by
  norm_num [scalarRow12886,BstLean.Part268.agent12886]

noncomputable def frameData12886 : BstLean.Part264b.FrameData 12886 :=
  BstLean.Part269.frameData_from_numerics (n := 12886) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12886.worldPackage rfl BstLean.Part268.WorldRow12886.product_lower (BstLean.Part268.WorldRow12886.producthi.2.trans (by norm_num))
    scalarRow12886 repair12886 covarianceInputs12886 (fun i hi => sourceNumerics12886 hi)
    BstLean.Part268.agent12886.frame targetFrame12886_eq


end BstLean.Part269.N12886

namespace BstLean.Part269.N12887
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12887 : scalarRow12887.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12887, BstLean.Part268.grid12887, BstLean.Part263.worldGrid]

theorem supplies12887 (j : Fin 43) : Supply 12887 (parameters j)
    (cellLower scalarRow12887.grid (sourceIndex j))
    (cellUpper scalarRow12887.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12887.grid grid_top_bounds12887 j

theorem radii12887 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12887.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12887 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12887 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12887.grid grid_top_bounds12887 j hθ

noncomputable def covarianceInputs12887 :
    BstLean.Part263.CovarianceInputs 12887 scalarRow12887.grid parameters (caps repair12887) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12887 grid_top_bounds12887 repair12887

noncomputable def covarianceEvent12887 : Set (AgFam 12887) :=
  BstLean.Part263.covarianceEvent 12887 scalarRow12887.grid parameters

theorem covarianceEvent12887_measurable : MeasurableSet covarianceEvent12887 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12887_payment :
    (retDist (paperDesignP 12887).toCentres).real
      (agentEv (paperDesignP 12887) covarianceEvent12887)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12887

theorem localCov12887 : BstLean.Part259.LocalCovarianceOn covarianceEvent12887
    (BstLean.Part263.cell scalarRow12887.grid) (caps repair12887) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12887

theorem covarianceGood12887_payment :
    (retDist (paperDesignP 12887).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12887)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12887_payment



end BstLean.Part269.N12887

namespace BstLean.Part269.N12887
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12887}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12887.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12887) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12887).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12887 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12887) (by norm_num) BstLean.Part268.WorldRow12887.worldPackage rfl
    BstLean.Part268.WorldRow12887.product_lower (BstLean.Part268.WorldRow12887.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12887} (hw : c ∈ Hof BstLean.Part268.WorldRow12887.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12887) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12887) (by norm_num) BstLean.Part268.WorldRow12887.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12887} (hw : c ∈ Hof BstLean.Part268.WorldRow12887.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12887) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12887).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12887) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12887_eq : scalarRow12887.targetFrame = BstLean.Part268.agent12887.frame := by
  norm_num [scalarRow12887,BstLean.Part268.agent12887]

noncomputable def frameData12887 : BstLean.Part264b.FrameData 12887 :=
  BstLean.Part269.frameData_from_numerics (n := 12887) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12887.worldPackage rfl BstLean.Part268.WorldRow12887.product_lower (BstLean.Part268.WorldRow12887.producthi.2.trans (by norm_num))
    scalarRow12887 repair12887 covarianceInputs12887 (fun i hi => sourceNumerics12887 hi)
    BstLean.Part268.agent12887.frame targetFrame12887_eq


end BstLean.Part269.N12887

namespace BstLean.Part269.N12888
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12888 : scalarRow12888.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12888, BstLean.Part268.grid12888, BstLean.Part263.worldGrid]

theorem supplies12888 (j : Fin 43) : Supply 12888 (parameters j)
    (cellLower scalarRow12888.grid (sourceIndex j))
    (cellUpper scalarRow12888.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12888.grid grid_top_bounds12888 j

theorem radii12888 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12888.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12888 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12888 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12888.grid grid_top_bounds12888 j hθ

noncomputable def covarianceInputs12888 :
    BstLean.Part263.CovarianceInputs 12888 scalarRow12888.grid parameters (caps repair12888) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12888 grid_top_bounds12888 repair12888

noncomputable def covarianceEvent12888 : Set (AgFam 12888) :=
  BstLean.Part263.covarianceEvent 12888 scalarRow12888.grid parameters

theorem covarianceEvent12888_measurable : MeasurableSet covarianceEvent12888 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12888_payment :
    (retDist (paperDesignP 12888).toCentres).real
      (agentEv (paperDesignP 12888) covarianceEvent12888)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12888

theorem localCov12888 : BstLean.Part259.LocalCovarianceOn covarianceEvent12888
    (BstLean.Part263.cell scalarRow12888.grid) (caps repair12888) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12888

theorem covarianceGood12888_payment :
    (retDist (paperDesignP 12888).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12888)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12888_payment



end BstLean.Part269.N12888

namespace BstLean.Part269.N12888
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12888}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12888.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12888) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12888).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12888 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12888) (by norm_num) BstLean.Part268.WorldRow12888.worldPackage rfl
    BstLean.Part268.WorldRow12888.product_lower (BstLean.Part268.WorldRow12888.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12888} (hw : c ∈ Hof BstLean.Part268.WorldRow12888.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12888) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12888) (by norm_num) BstLean.Part268.WorldRow12888.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12888} (hw : c ∈ Hof BstLean.Part268.WorldRow12888.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12888) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12888).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12888) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12888_eq : scalarRow12888.targetFrame = BstLean.Part268.agent12888.frame := by
  norm_num [scalarRow12888,BstLean.Part268.agent12888]

noncomputable def frameData12888 : BstLean.Part264b.FrameData 12888 :=
  BstLean.Part269.frameData_from_numerics (n := 12888) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12888.worldPackage rfl BstLean.Part268.WorldRow12888.product_lower (BstLean.Part268.WorldRow12888.producthi.2.trans (by norm_num))
    scalarRow12888 repair12888 covarianceInputs12888 (fun i hi => sourceNumerics12888 hi)
    BstLean.Part268.agent12888.frame targetFrame12888_eq


end BstLean.Part269.N12888

namespace BstLean.Part269.N12889
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12889 : scalarRow12889.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12889, BstLean.Part268.grid12889, BstLean.Part263.worldGrid]

theorem supplies12889 (j : Fin 43) : Supply 12889 (parameters j)
    (cellLower scalarRow12889.grid (sourceIndex j))
    (cellUpper scalarRow12889.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12889.grid grid_top_bounds12889 j

theorem radii12889 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12889.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12889 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12889 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12889.grid grid_top_bounds12889 j hθ

noncomputable def covarianceInputs12889 :
    BstLean.Part263.CovarianceInputs 12889 scalarRow12889.grid parameters (caps repair12889) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12889 grid_top_bounds12889 repair12889

noncomputable def covarianceEvent12889 : Set (AgFam 12889) :=
  BstLean.Part263.covarianceEvent 12889 scalarRow12889.grid parameters

theorem covarianceEvent12889_measurable : MeasurableSet covarianceEvent12889 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12889_payment :
    (retDist (paperDesignP 12889).toCentres).real
      (agentEv (paperDesignP 12889) covarianceEvent12889)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12889

theorem localCov12889 : BstLean.Part259.LocalCovarianceOn covarianceEvent12889
    (BstLean.Part263.cell scalarRow12889.grid) (caps repair12889) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12889

theorem covarianceGood12889_payment :
    (retDist (paperDesignP 12889).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12889)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12889_payment



end BstLean.Part269.N12889

namespace BstLean.Part269.N12889
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12889}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12889.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12889) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12889).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12889 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12889) (by norm_num) BstLean.Part268.WorldRow12889.worldPackage rfl
    BstLean.Part268.WorldRow12889.product_lower (BstLean.Part268.WorldRow12889.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12889} (hw : c ∈ Hof BstLean.Part268.WorldRow12889.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12889) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12889) (by norm_num) BstLean.Part268.WorldRow12889.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12889} (hw : c ∈ Hof BstLean.Part268.WorldRow12889.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12889) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12889).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12889) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12889_eq : scalarRow12889.targetFrame = BstLean.Part268.agent12889.frame := by
  norm_num [scalarRow12889,BstLean.Part268.agent12889]

noncomputable def frameData12889 : BstLean.Part264b.FrameData 12889 :=
  BstLean.Part269.frameData_from_numerics (n := 12889) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12889.worldPackage rfl BstLean.Part268.WorldRow12889.product_lower (BstLean.Part268.WorldRow12889.producthi.2.trans (by norm_num))
    scalarRow12889 repair12889 covarianceInputs12889 (fun i hi => sourceNumerics12889 hi)
    BstLean.Part268.agent12889.frame targetFrame12889_eq


end BstLean.Part269.N12889
