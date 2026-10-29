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

namespace BstLean.Part269.N12875
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12875 : scalarRow12875.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12875, BstLean.Part268.grid12875, BstLean.Part263.worldGrid]

theorem supplies12875 (j : Fin 43) : Supply 12875 (parameters j)
    (cellLower scalarRow12875.grid (sourceIndex j))
    (cellUpper scalarRow12875.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12875.grid grid_top_bounds12875 j

theorem radii12875 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12875.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12875 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12875 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12875.grid grid_top_bounds12875 j hθ

noncomputable def covarianceInputs12875 :
    BstLean.Part263.CovarianceInputs 12875 scalarRow12875.grid parameters (caps repair12875) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12875 grid_top_bounds12875 repair12875

noncomputable def covarianceEvent12875 : Set (AgFam 12875) :=
  BstLean.Part263.covarianceEvent 12875 scalarRow12875.grid parameters

theorem covarianceEvent12875_measurable : MeasurableSet covarianceEvent12875 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12875_payment :
    (retDist (paperDesignP 12875).toCentres).real
      (agentEv (paperDesignP 12875) covarianceEvent12875)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12875

theorem localCov12875 : BstLean.Part259.LocalCovarianceOn covarianceEvent12875
    (BstLean.Part263.cell scalarRow12875.grid) (caps repair12875) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12875

theorem covarianceGood12875_payment :
    (retDist (paperDesignP 12875).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12875)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12875_payment



end BstLean.Part269.N12875

namespace BstLean.Part269.N12875
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12875}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12875.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12875) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12875).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12875 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12875) (by norm_num) BstLean.Part268.WorldRow12875.worldPackage rfl
    BstLean.Part268.WorldRow12875.product_lower (BstLean.Part268.WorldRow12875.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12875} (hw : c ∈ Hof BstLean.Part268.WorldRow12875.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12875) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12875) (by norm_num) BstLean.Part268.WorldRow12875.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12875} (hw : c ∈ Hof BstLean.Part268.WorldRow12875.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12875) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12875).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12875) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12875_eq : scalarRow12875.targetFrame = BstLean.Part268.agent12875.frame := by
  norm_num [scalarRow12875,BstLean.Part268.agent12875]

noncomputable def frameData12875 : BstLean.Part264b.FrameData 12875 :=
  BstLean.Part269.frameData_from_numerics (n := 12875) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12875.worldPackage rfl BstLean.Part268.WorldRow12875.product_lower (BstLean.Part268.WorldRow12875.producthi.2.trans (by norm_num))
    scalarRow12875 repair12875 covarianceInputs12875 (fun i hi => sourceNumerics12875 hi)
    BstLean.Part268.agent12875.frame targetFrame12875_eq


end BstLean.Part269.N12875

namespace BstLean.Part269.N12876
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12876 : scalarRow12876.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12876, BstLean.Part268.grid12876, BstLean.Part263.worldGrid]

theorem supplies12876 (j : Fin 43) : Supply 12876 (parameters j)
    (cellLower scalarRow12876.grid (sourceIndex j))
    (cellUpper scalarRow12876.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12876.grid grid_top_bounds12876 j

theorem radii12876 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12876.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12876 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12876 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12876.grid grid_top_bounds12876 j hθ

noncomputable def covarianceInputs12876 :
    BstLean.Part263.CovarianceInputs 12876 scalarRow12876.grid parameters (caps repair12876) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12876 grid_top_bounds12876 repair12876

noncomputable def covarianceEvent12876 : Set (AgFam 12876) :=
  BstLean.Part263.covarianceEvent 12876 scalarRow12876.grid parameters

theorem covarianceEvent12876_measurable : MeasurableSet covarianceEvent12876 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12876_payment :
    (retDist (paperDesignP 12876).toCentres).real
      (agentEv (paperDesignP 12876) covarianceEvent12876)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12876

theorem localCov12876 : BstLean.Part259.LocalCovarianceOn covarianceEvent12876
    (BstLean.Part263.cell scalarRow12876.grid) (caps repair12876) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12876

theorem covarianceGood12876_payment :
    (retDist (paperDesignP 12876).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12876)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12876_payment



end BstLean.Part269.N12876

namespace BstLean.Part269.N12876
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12876}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12876.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12876) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12876).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12876 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12876) (by norm_num) BstLean.Part268.WorldRow12876.worldPackage rfl
    BstLean.Part268.WorldRow12876.product_lower (BstLean.Part268.WorldRow12876.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12876} (hw : c ∈ Hof BstLean.Part268.WorldRow12876.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12876) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12876) (by norm_num) BstLean.Part268.WorldRow12876.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12876} (hw : c ∈ Hof BstLean.Part268.WorldRow12876.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12876) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12876).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12876) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12876_eq : scalarRow12876.targetFrame = BstLean.Part268.agent12876.frame := by
  norm_num [scalarRow12876,BstLean.Part268.agent12876]

noncomputable def frameData12876 : BstLean.Part264b.FrameData 12876 :=
  BstLean.Part269.frameData_from_numerics (n := 12876) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12876.worldPackage rfl BstLean.Part268.WorldRow12876.product_lower (BstLean.Part268.WorldRow12876.producthi.2.trans (by norm_num))
    scalarRow12876 repair12876 covarianceInputs12876 (fun i hi => sourceNumerics12876 hi)
    BstLean.Part268.agent12876.frame targetFrame12876_eq


end BstLean.Part269.N12876

namespace BstLean.Part269.N12877
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12877 : scalarRow12877.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12877, BstLean.Part268.grid12877, BstLean.Part263.worldGrid]

theorem supplies12877 (j : Fin 43) : Supply 12877 (parameters j)
    (cellLower scalarRow12877.grid (sourceIndex j))
    (cellUpper scalarRow12877.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12877.grid grid_top_bounds12877 j

theorem radii12877 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12877.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12877 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12877 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12877.grid grid_top_bounds12877 j hθ

noncomputable def covarianceInputs12877 :
    BstLean.Part263.CovarianceInputs 12877 scalarRow12877.grid parameters (caps repair12877) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12877 grid_top_bounds12877 repair12877

noncomputable def covarianceEvent12877 : Set (AgFam 12877) :=
  BstLean.Part263.covarianceEvent 12877 scalarRow12877.grid parameters

theorem covarianceEvent12877_measurable : MeasurableSet covarianceEvent12877 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12877_payment :
    (retDist (paperDesignP 12877).toCentres).real
      (agentEv (paperDesignP 12877) covarianceEvent12877)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12877

theorem localCov12877 : BstLean.Part259.LocalCovarianceOn covarianceEvent12877
    (BstLean.Part263.cell scalarRow12877.grid) (caps repair12877) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12877

theorem covarianceGood12877_payment :
    (retDist (paperDesignP 12877).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12877)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12877_payment



end BstLean.Part269.N12877

namespace BstLean.Part269.N12877
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12877}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12877.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12877) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12877).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12877 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12877) (by norm_num) BstLean.Part268.WorldRow12877.worldPackage rfl
    BstLean.Part268.WorldRow12877.product_lower (BstLean.Part268.WorldRow12877.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12877} (hw : c ∈ Hof BstLean.Part268.WorldRow12877.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12877) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12877) (by norm_num) BstLean.Part268.WorldRow12877.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12877} (hw : c ∈ Hof BstLean.Part268.WorldRow12877.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12877) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12877).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12877) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12877_eq : scalarRow12877.targetFrame = BstLean.Part268.agent12877.frame := by
  norm_num [scalarRow12877,BstLean.Part268.agent12877]

noncomputable def frameData12877 : BstLean.Part264b.FrameData 12877 :=
  BstLean.Part269.frameData_from_numerics (n := 12877) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12877.worldPackage rfl BstLean.Part268.WorldRow12877.product_lower (BstLean.Part268.WorldRow12877.producthi.2.trans (by norm_num))
    scalarRow12877 repair12877 covarianceInputs12877 (fun i hi => sourceNumerics12877 hi)
    BstLean.Part268.agent12877.frame targetFrame12877_eq


end BstLean.Part269.N12877

namespace BstLean.Part269.N12878
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12878 : scalarRow12878.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12878, BstLean.Part268.grid12878, BstLean.Part263.worldGrid]

theorem supplies12878 (j : Fin 43) : Supply 12878 (parameters j)
    (cellLower scalarRow12878.grid (sourceIndex j))
    (cellUpper scalarRow12878.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12878.grid grid_top_bounds12878 j

theorem radii12878 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12878.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12878 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12878 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12878.grid grid_top_bounds12878 j hθ

noncomputable def covarianceInputs12878 :
    BstLean.Part263.CovarianceInputs 12878 scalarRow12878.grid parameters (caps repair12878) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12878 grid_top_bounds12878 repair12878

noncomputable def covarianceEvent12878 : Set (AgFam 12878) :=
  BstLean.Part263.covarianceEvent 12878 scalarRow12878.grid parameters

theorem covarianceEvent12878_measurable : MeasurableSet covarianceEvent12878 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12878_payment :
    (retDist (paperDesignP 12878).toCentres).real
      (agentEv (paperDesignP 12878) covarianceEvent12878)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12878

theorem localCov12878 : BstLean.Part259.LocalCovarianceOn covarianceEvent12878
    (BstLean.Part263.cell scalarRow12878.grid) (caps repair12878) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12878

theorem covarianceGood12878_payment :
    (retDist (paperDesignP 12878).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12878)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12878_payment



end BstLean.Part269.N12878

namespace BstLean.Part269.N12878
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12878}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12878.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12878) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12878).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12878 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12878) (by norm_num) BstLean.Part268.WorldRow12878.worldPackage rfl
    BstLean.Part268.WorldRow12878.product_lower (BstLean.Part268.WorldRow12878.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12878} (hw : c ∈ Hof BstLean.Part268.WorldRow12878.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12878) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12878) (by norm_num) BstLean.Part268.WorldRow12878.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12878} (hw : c ∈ Hof BstLean.Part268.WorldRow12878.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12878) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12878).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12878) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12878_eq : scalarRow12878.targetFrame = BstLean.Part268.agent12878.frame := by
  norm_num [scalarRow12878,BstLean.Part268.agent12878]

noncomputable def frameData12878 : BstLean.Part264b.FrameData 12878 :=
  BstLean.Part269.frameData_from_numerics (n := 12878) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12878.worldPackage rfl BstLean.Part268.WorldRow12878.product_lower (BstLean.Part268.WorldRow12878.producthi.2.trans (by norm_num))
    scalarRow12878 repair12878 covarianceInputs12878 (fun i hi => sourceNumerics12878 hi)
    BstLean.Part268.agent12878.frame targetFrame12878_eq


end BstLean.Part269.N12878

namespace BstLean.Part269.N12879
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12879 : scalarRow12879.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12879, BstLean.Part268.grid12879, BstLean.Part263.worldGrid]

theorem supplies12879 (j : Fin 43) : Supply 12879 (parameters j)
    (cellLower scalarRow12879.grid (sourceIndex j))
    (cellUpper scalarRow12879.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12879.grid grid_top_bounds12879 j

theorem radii12879 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12879.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12879 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12879 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12879.grid grid_top_bounds12879 j hθ

noncomputable def covarianceInputs12879 :
    BstLean.Part263.CovarianceInputs 12879 scalarRow12879.grid parameters (caps repair12879) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12879 grid_top_bounds12879 repair12879

noncomputable def covarianceEvent12879 : Set (AgFam 12879) :=
  BstLean.Part263.covarianceEvent 12879 scalarRow12879.grid parameters

theorem covarianceEvent12879_measurable : MeasurableSet covarianceEvent12879 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12879_payment :
    (retDist (paperDesignP 12879).toCentres).real
      (agentEv (paperDesignP 12879) covarianceEvent12879)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12879

theorem localCov12879 : BstLean.Part259.LocalCovarianceOn covarianceEvent12879
    (BstLean.Part263.cell scalarRow12879.grid) (caps repair12879) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12879

theorem covarianceGood12879_payment :
    (retDist (paperDesignP 12879).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12879)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12879_payment



end BstLean.Part269.N12879

namespace BstLean.Part269.N12879
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12879}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12879.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12879) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12879).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12879 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12879) (by norm_num) BstLean.Part268.WorldRow12879.worldPackage rfl
    BstLean.Part268.WorldRow12879.product_lower (BstLean.Part268.WorldRow12879.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12879} (hw : c ∈ Hof BstLean.Part268.WorldRow12879.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12879) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12879) (by norm_num) BstLean.Part268.WorldRow12879.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12879} (hw : c ∈ Hof BstLean.Part268.WorldRow12879.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12879) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12879).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12879) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12879_eq : scalarRow12879.targetFrame = BstLean.Part268.agent12879.frame := by
  norm_num [scalarRow12879,BstLean.Part268.agent12879]

noncomputable def frameData12879 : BstLean.Part264b.FrameData 12879 :=
  BstLean.Part269.frameData_from_numerics (n := 12879) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12879.worldPackage rfl BstLean.Part268.WorldRow12879.product_lower (BstLean.Part268.WorldRow12879.producthi.2.trans (by norm_num))
    scalarRow12879 repair12879 covarianceInputs12879 (fun i hi => sourceNumerics12879 hi)
    BstLean.Part268.agent12879.frame targetFrame12879_eq


end BstLean.Part269.N12879
