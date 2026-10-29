import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World27Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs27
import BstLean.Part269Rows27
import BstLean.Part269Sources27
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13040
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13040 : scalarRow13040.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13040, BstLean.Part268.grid13040, BstLean.Part263.worldGrid]

theorem supplies13040 (j : Fin 43) : Supply 13040 (parameters j)
    (cellLower scalarRow13040.grid (sourceIndex j))
    (cellUpper scalarRow13040.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13040.grid grid_top_bounds13040 j

theorem radii13040 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13040.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13040 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13040 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13040.grid grid_top_bounds13040 j hθ

noncomputable def covarianceInputs13040 :
    BstLean.Part263.CovarianceInputs 13040 scalarRow13040.grid parameters (caps repair13040) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13040 grid_top_bounds13040 repair13040

noncomputable def covarianceEvent13040 : Set (AgFam 13040) :=
  BstLean.Part263.covarianceEvent 13040 scalarRow13040.grid parameters

theorem covarianceEvent13040_measurable : MeasurableSet covarianceEvent13040 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13040_payment :
    (retDist (paperDesignP 13040).toCentres).real
      (agentEv (paperDesignP 13040) covarianceEvent13040)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13040

theorem localCov13040 : BstLean.Part259.LocalCovarianceOn covarianceEvent13040
    (BstLean.Part263.cell scalarRow13040.grid) (caps repair13040) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13040

theorem covarianceGood13040_payment :
    (retDist (paperDesignP 13040).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13040)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13040_payment



end BstLean.Part269.N13040

namespace BstLean.Part269.N13040
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13040}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13040.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13040) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13040).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13040 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13040) (by norm_num) BstLean.Part268.WorldRow13040.worldPackage rfl
    BstLean.Part268.WorldRow13040.product_lower (BstLean.Part268.WorldRow13040.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13040} (hw : c ∈ Hof BstLean.Part268.WorldRow13040.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13040) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13040) (by norm_num) BstLean.Part268.WorldRow13040.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13040} (hw : c ∈ Hof BstLean.Part268.WorldRow13040.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13040) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13040).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13040) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13040_eq : scalarRow13040.targetFrame = BstLean.Part268.agent13040.frame := by
  norm_num [scalarRow13040,BstLean.Part268.agent13040]

noncomputable def frameData13040 : BstLean.Part264b.FrameData 13040 :=
  BstLean.Part269.frameData_from_numerics (n := 13040) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13040.worldPackage rfl BstLean.Part268.WorldRow13040.product_lower (BstLean.Part268.WorldRow13040.producthi.2.trans (by norm_num))
    scalarRow13040 repair13040 covarianceInputs13040 (fun i hi => sourceNumerics13040 hi)
    BstLean.Part268.agent13040.frame targetFrame13040_eq


end BstLean.Part269.N13040

namespace BstLean.Part269.N13041
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13041 : scalarRow13041.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13041, BstLean.Part268.grid13041, BstLean.Part263.worldGrid]

theorem supplies13041 (j : Fin 43) : Supply 13041 (parameters j)
    (cellLower scalarRow13041.grid (sourceIndex j))
    (cellUpper scalarRow13041.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13041.grid grid_top_bounds13041 j

theorem radii13041 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13041.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13041 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13041 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13041.grid grid_top_bounds13041 j hθ

noncomputable def covarianceInputs13041 :
    BstLean.Part263.CovarianceInputs 13041 scalarRow13041.grid parameters (caps repair13041) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13041 grid_top_bounds13041 repair13041

noncomputable def covarianceEvent13041 : Set (AgFam 13041) :=
  BstLean.Part263.covarianceEvent 13041 scalarRow13041.grid parameters

theorem covarianceEvent13041_measurable : MeasurableSet covarianceEvent13041 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13041_payment :
    (retDist (paperDesignP 13041).toCentres).real
      (agentEv (paperDesignP 13041) covarianceEvent13041)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13041

theorem localCov13041 : BstLean.Part259.LocalCovarianceOn covarianceEvent13041
    (BstLean.Part263.cell scalarRow13041.grid) (caps repair13041) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13041

theorem covarianceGood13041_payment :
    (retDist (paperDesignP 13041).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13041)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13041_payment



end BstLean.Part269.N13041

namespace BstLean.Part269.N13041
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13041}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13041.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13041) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13041).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13041 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13041) (by norm_num) BstLean.Part268.WorldRow13041.worldPackage rfl
    BstLean.Part268.WorldRow13041.product_lower (BstLean.Part268.WorldRow13041.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13041} (hw : c ∈ Hof BstLean.Part268.WorldRow13041.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13041) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13041) (by norm_num) BstLean.Part268.WorldRow13041.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13041} (hw : c ∈ Hof BstLean.Part268.WorldRow13041.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13041) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13041).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13041) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13041_eq : scalarRow13041.targetFrame = BstLean.Part268.agent13041.frame := by
  norm_num [scalarRow13041,BstLean.Part268.agent13041]

noncomputable def frameData13041 : BstLean.Part264b.FrameData 13041 :=
  BstLean.Part269.frameData_from_numerics (n := 13041) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13041.worldPackage rfl BstLean.Part268.WorldRow13041.product_lower (BstLean.Part268.WorldRow13041.producthi.2.trans (by norm_num))
    scalarRow13041 repair13041 covarianceInputs13041 (fun i hi => sourceNumerics13041 hi)
    BstLean.Part268.agent13041.frame targetFrame13041_eq


end BstLean.Part269.N13041

namespace BstLean.Part269.N13042
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13042 : scalarRow13042.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13042, BstLean.Part268.grid13042, BstLean.Part263.worldGrid]

theorem supplies13042 (j : Fin 43) : Supply 13042 (parameters j)
    (cellLower scalarRow13042.grid (sourceIndex j))
    (cellUpper scalarRow13042.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13042.grid grid_top_bounds13042 j

theorem radii13042 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13042.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13042 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13042 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13042.grid grid_top_bounds13042 j hθ

noncomputable def covarianceInputs13042 :
    BstLean.Part263.CovarianceInputs 13042 scalarRow13042.grid parameters (caps repair13042) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13042 grid_top_bounds13042 repair13042

noncomputable def covarianceEvent13042 : Set (AgFam 13042) :=
  BstLean.Part263.covarianceEvent 13042 scalarRow13042.grid parameters

theorem covarianceEvent13042_measurable : MeasurableSet covarianceEvent13042 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13042_payment :
    (retDist (paperDesignP 13042).toCentres).real
      (agentEv (paperDesignP 13042) covarianceEvent13042)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13042

theorem localCov13042 : BstLean.Part259.LocalCovarianceOn covarianceEvent13042
    (BstLean.Part263.cell scalarRow13042.grid) (caps repair13042) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13042

theorem covarianceGood13042_payment :
    (retDist (paperDesignP 13042).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13042)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13042_payment



end BstLean.Part269.N13042

namespace BstLean.Part269.N13042
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13042}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13042.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13042) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13042).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13042 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13042) (by norm_num) BstLean.Part268.WorldRow13042.worldPackage rfl
    BstLean.Part268.WorldRow13042.product_lower (BstLean.Part268.WorldRow13042.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13042} (hw : c ∈ Hof BstLean.Part268.WorldRow13042.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13042) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13042) (by norm_num) BstLean.Part268.WorldRow13042.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13042} (hw : c ∈ Hof BstLean.Part268.WorldRow13042.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13042) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13042).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13042) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13042_eq : scalarRow13042.targetFrame = BstLean.Part268.agent13042.frame := by
  norm_num [scalarRow13042,BstLean.Part268.agent13042]

noncomputable def frameData13042 : BstLean.Part264b.FrameData 13042 :=
  BstLean.Part269.frameData_from_numerics (n := 13042) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13042.worldPackage rfl BstLean.Part268.WorldRow13042.product_lower (BstLean.Part268.WorldRow13042.producthi.2.trans (by norm_num))
    scalarRow13042 repair13042 covarianceInputs13042 (fun i hi => sourceNumerics13042 hi)
    BstLean.Part268.agent13042.frame targetFrame13042_eq


end BstLean.Part269.N13042

namespace BstLean.Part269.N13043
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13043 : scalarRow13043.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13043, BstLean.Part268.grid13043, BstLean.Part263.worldGrid]

theorem supplies13043 (j : Fin 43) : Supply 13043 (parameters j)
    (cellLower scalarRow13043.grid (sourceIndex j))
    (cellUpper scalarRow13043.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13043.grid grid_top_bounds13043 j

theorem radii13043 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13043.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13043 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13043 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13043.grid grid_top_bounds13043 j hθ

noncomputable def covarianceInputs13043 :
    BstLean.Part263.CovarianceInputs 13043 scalarRow13043.grid parameters (caps repair13043) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13043 grid_top_bounds13043 repair13043

noncomputable def covarianceEvent13043 : Set (AgFam 13043) :=
  BstLean.Part263.covarianceEvent 13043 scalarRow13043.grid parameters

theorem covarianceEvent13043_measurable : MeasurableSet covarianceEvent13043 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13043_payment :
    (retDist (paperDesignP 13043).toCentres).real
      (agentEv (paperDesignP 13043) covarianceEvent13043)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13043

theorem localCov13043 : BstLean.Part259.LocalCovarianceOn covarianceEvent13043
    (BstLean.Part263.cell scalarRow13043.grid) (caps repair13043) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13043

theorem covarianceGood13043_payment :
    (retDist (paperDesignP 13043).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13043)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13043_payment



end BstLean.Part269.N13043

namespace BstLean.Part269.N13043
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13043}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13043.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13043) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13043).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13043 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13043) (by norm_num) BstLean.Part268.WorldRow13043.worldPackage rfl
    BstLean.Part268.WorldRow13043.product_lower (BstLean.Part268.WorldRow13043.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13043} (hw : c ∈ Hof BstLean.Part268.WorldRow13043.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13043) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13043) (by norm_num) BstLean.Part268.WorldRow13043.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13043} (hw : c ∈ Hof BstLean.Part268.WorldRow13043.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13043) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13043).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13043) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13043_eq : scalarRow13043.targetFrame = BstLean.Part268.agent13043.frame := by
  norm_num [scalarRow13043,BstLean.Part268.agent13043]

noncomputable def frameData13043 : BstLean.Part264b.FrameData 13043 :=
  BstLean.Part269.frameData_from_numerics (n := 13043) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13043.worldPackage rfl BstLean.Part268.WorldRow13043.product_lower (BstLean.Part268.WorldRow13043.producthi.2.trans (by norm_num))
    scalarRow13043 repair13043 covarianceInputs13043 (fun i hi => sourceNumerics13043 hi)
    BstLean.Part268.agent13043.frame targetFrame13043_eq


end BstLean.Part269.N13043

namespace BstLean.Part269.N13044
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13044 : scalarRow13044.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13044, BstLean.Part268.grid13044, BstLean.Part263.worldGrid]

theorem supplies13044 (j : Fin 43) : Supply 13044 (parameters j)
    (cellLower scalarRow13044.grid (sourceIndex j))
    (cellUpper scalarRow13044.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13044.grid grid_top_bounds13044 j

theorem radii13044 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13044.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13044 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13044 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13044.grid grid_top_bounds13044 j hθ

noncomputable def covarianceInputs13044 :
    BstLean.Part263.CovarianceInputs 13044 scalarRow13044.grid parameters (caps repair13044) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13044 grid_top_bounds13044 repair13044

noncomputable def covarianceEvent13044 : Set (AgFam 13044) :=
  BstLean.Part263.covarianceEvent 13044 scalarRow13044.grid parameters

theorem covarianceEvent13044_measurable : MeasurableSet covarianceEvent13044 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13044_payment :
    (retDist (paperDesignP 13044).toCentres).real
      (agentEv (paperDesignP 13044) covarianceEvent13044)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13044

theorem localCov13044 : BstLean.Part259.LocalCovarianceOn covarianceEvent13044
    (BstLean.Part263.cell scalarRow13044.grid) (caps repair13044) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13044

theorem covarianceGood13044_payment :
    (retDist (paperDesignP 13044).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13044)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13044_payment



end BstLean.Part269.N13044

namespace BstLean.Part269.N13044
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13044}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13044.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13044) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13044).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13044 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13044) (by norm_num) BstLean.Part268.WorldRow13044.worldPackage rfl
    BstLean.Part268.WorldRow13044.product_lower (BstLean.Part268.WorldRow13044.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13044} (hw : c ∈ Hof BstLean.Part268.WorldRow13044.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13044) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13044) (by norm_num) BstLean.Part268.WorldRow13044.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13044} (hw : c ∈ Hof BstLean.Part268.WorldRow13044.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13044) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13044).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13044) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13044_eq : scalarRow13044.targetFrame = BstLean.Part268.agent13044.frame := by
  norm_num [scalarRow13044,BstLean.Part268.agent13044]

noncomputable def frameData13044 : BstLean.Part264b.FrameData 13044 :=
  BstLean.Part269.frameData_from_numerics (n := 13044) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13044.worldPackage rfl BstLean.Part268.WorldRow13044.product_lower (BstLean.Part268.WorldRow13044.producthi.2.trans (by norm_num))
    scalarRow13044 repair13044 covarianceInputs13044 (fun i hi => sourceNumerics13044 hi)
    BstLean.Part268.agent13044.frame targetFrame13044_eq


end BstLean.Part269.N13044
