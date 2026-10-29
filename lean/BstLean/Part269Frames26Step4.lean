import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World26Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs26
import BstLean.Part269Rows26
import BstLean.Part269Sources26
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13020
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13020 : scalarRow13020.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13020, BstLean.Part268.grid13020, BstLean.Part263.worldGrid]

theorem supplies13020 (j : Fin 43) : Supply 13020 (parameters j)
    (cellLower scalarRow13020.grid (sourceIndex j))
    (cellUpper scalarRow13020.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13020.grid grid_top_bounds13020 j

theorem radii13020 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13020.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13020 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13020 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13020.grid grid_top_bounds13020 j hθ

noncomputable def covarianceInputs13020 :
    BstLean.Part263.CovarianceInputs 13020 scalarRow13020.grid parameters (caps repair13020) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13020 grid_top_bounds13020 repair13020

noncomputable def covarianceEvent13020 : Set (AgFam 13020) :=
  BstLean.Part263.covarianceEvent 13020 scalarRow13020.grid parameters

theorem covarianceEvent13020_measurable : MeasurableSet covarianceEvent13020 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13020_payment :
    (retDist (paperDesignP 13020).toCentres).real
      (agentEv (paperDesignP 13020) covarianceEvent13020)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13020

theorem localCov13020 : BstLean.Part259.LocalCovarianceOn covarianceEvent13020
    (BstLean.Part263.cell scalarRow13020.grid) (caps repair13020) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13020

theorem covarianceGood13020_payment :
    (retDist (paperDesignP 13020).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13020)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13020_payment



end BstLean.Part269.N13020

namespace BstLean.Part269.N13020
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13020}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13020.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13020) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13020).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13020 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13020) (by norm_num) BstLean.Part268.WorldRow13020.worldPackage rfl
    BstLean.Part268.WorldRow13020.product_lower (BstLean.Part268.WorldRow13020.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13020} (hw : c ∈ Hof BstLean.Part268.WorldRow13020.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13020) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13020) (by norm_num) BstLean.Part268.WorldRow13020.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13020} (hw : c ∈ Hof BstLean.Part268.WorldRow13020.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13020) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13020).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13020) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13020_eq : scalarRow13020.targetFrame = BstLean.Part268.agent13020.frame := by
  norm_num [scalarRow13020,BstLean.Part268.agent13020]

noncomputable def frameData13020 : BstLean.Part264b.FrameData 13020 :=
  BstLean.Part269.frameData_from_numerics (n := 13020) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13020.worldPackage rfl BstLean.Part268.WorldRow13020.product_lower (BstLean.Part268.WorldRow13020.producthi.2.trans (by norm_num))
    scalarRow13020 repair13020 covarianceInputs13020 (fun i hi => sourceNumerics13020 hi)
    BstLean.Part268.agent13020.frame targetFrame13020_eq


end BstLean.Part269.N13020

namespace BstLean.Part269.N13021
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13021 : scalarRow13021.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13021, BstLean.Part268.grid13021, BstLean.Part263.worldGrid]

theorem supplies13021 (j : Fin 43) : Supply 13021 (parameters j)
    (cellLower scalarRow13021.grid (sourceIndex j))
    (cellUpper scalarRow13021.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13021.grid grid_top_bounds13021 j

theorem radii13021 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13021.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13021 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13021 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13021.grid grid_top_bounds13021 j hθ

noncomputable def covarianceInputs13021 :
    BstLean.Part263.CovarianceInputs 13021 scalarRow13021.grid parameters (caps repair13021) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13021 grid_top_bounds13021 repair13021

noncomputable def covarianceEvent13021 : Set (AgFam 13021) :=
  BstLean.Part263.covarianceEvent 13021 scalarRow13021.grid parameters

theorem covarianceEvent13021_measurable : MeasurableSet covarianceEvent13021 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13021_payment :
    (retDist (paperDesignP 13021).toCentres).real
      (agentEv (paperDesignP 13021) covarianceEvent13021)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13021

theorem localCov13021 : BstLean.Part259.LocalCovarianceOn covarianceEvent13021
    (BstLean.Part263.cell scalarRow13021.grid) (caps repair13021) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13021

theorem covarianceGood13021_payment :
    (retDist (paperDesignP 13021).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13021)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13021_payment



end BstLean.Part269.N13021

namespace BstLean.Part269.N13021
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13021}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13021.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13021) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13021).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13021 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13021) (by norm_num) BstLean.Part268.WorldRow13021.worldPackage rfl
    BstLean.Part268.WorldRow13021.product_lower (BstLean.Part268.WorldRow13021.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13021} (hw : c ∈ Hof BstLean.Part268.WorldRow13021.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13021) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13021) (by norm_num) BstLean.Part268.WorldRow13021.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13021} (hw : c ∈ Hof BstLean.Part268.WorldRow13021.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13021) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13021).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13021) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13021_eq : scalarRow13021.targetFrame = BstLean.Part268.agent13021.frame := by
  norm_num [scalarRow13021,BstLean.Part268.agent13021]

noncomputable def frameData13021 : BstLean.Part264b.FrameData 13021 :=
  BstLean.Part269.frameData_from_numerics (n := 13021) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13021.worldPackage rfl BstLean.Part268.WorldRow13021.product_lower (BstLean.Part268.WorldRow13021.producthi.2.trans (by norm_num))
    scalarRow13021 repair13021 covarianceInputs13021 (fun i hi => sourceNumerics13021 hi)
    BstLean.Part268.agent13021.frame targetFrame13021_eq


end BstLean.Part269.N13021

namespace BstLean.Part269.N13022
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13022 : scalarRow13022.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13022, BstLean.Part268.grid13022, BstLean.Part263.worldGrid]

theorem supplies13022 (j : Fin 43) : Supply 13022 (parameters j)
    (cellLower scalarRow13022.grid (sourceIndex j))
    (cellUpper scalarRow13022.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13022.grid grid_top_bounds13022 j

theorem radii13022 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13022.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13022 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13022 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13022.grid grid_top_bounds13022 j hθ

noncomputable def covarianceInputs13022 :
    BstLean.Part263.CovarianceInputs 13022 scalarRow13022.grid parameters (caps repair13022) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13022 grid_top_bounds13022 repair13022

noncomputable def covarianceEvent13022 : Set (AgFam 13022) :=
  BstLean.Part263.covarianceEvent 13022 scalarRow13022.grid parameters

theorem covarianceEvent13022_measurable : MeasurableSet covarianceEvent13022 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13022_payment :
    (retDist (paperDesignP 13022).toCentres).real
      (agentEv (paperDesignP 13022) covarianceEvent13022)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13022

theorem localCov13022 : BstLean.Part259.LocalCovarianceOn covarianceEvent13022
    (BstLean.Part263.cell scalarRow13022.grid) (caps repair13022) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13022

theorem covarianceGood13022_payment :
    (retDist (paperDesignP 13022).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13022)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13022_payment



end BstLean.Part269.N13022

namespace BstLean.Part269.N13022
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13022}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13022.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13022) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13022).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13022 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13022) (by norm_num) BstLean.Part268.WorldRow13022.worldPackage rfl
    BstLean.Part268.WorldRow13022.product_lower (BstLean.Part268.WorldRow13022.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13022} (hw : c ∈ Hof BstLean.Part268.WorldRow13022.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13022) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13022) (by norm_num) BstLean.Part268.WorldRow13022.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13022} (hw : c ∈ Hof BstLean.Part268.WorldRow13022.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13022) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13022).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13022) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13022_eq : scalarRow13022.targetFrame = BstLean.Part268.agent13022.frame := by
  norm_num [scalarRow13022,BstLean.Part268.agent13022]

noncomputable def frameData13022 : BstLean.Part264b.FrameData 13022 :=
  BstLean.Part269.frameData_from_numerics (n := 13022) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13022.worldPackage rfl BstLean.Part268.WorldRow13022.product_lower (BstLean.Part268.WorldRow13022.producthi.2.trans (by norm_num))
    scalarRow13022 repair13022 covarianceInputs13022 (fun i hi => sourceNumerics13022 hi)
    BstLean.Part268.agent13022.frame targetFrame13022_eq


end BstLean.Part269.N13022

namespace BstLean.Part269.N13023
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13023 : scalarRow13023.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13023, BstLean.Part268.grid13023, BstLean.Part263.worldGrid]

theorem supplies13023 (j : Fin 43) : Supply 13023 (parameters j)
    (cellLower scalarRow13023.grid (sourceIndex j))
    (cellUpper scalarRow13023.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13023.grid grid_top_bounds13023 j

theorem radii13023 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13023.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13023 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13023 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13023.grid grid_top_bounds13023 j hθ

noncomputable def covarianceInputs13023 :
    BstLean.Part263.CovarianceInputs 13023 scalarRow13023.grid parameters (caps repair13023) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13023 grid_top_bounds13023 repair13023

noncomputable def covarianceEvent13023 : Set (AgFam 13023) :=
  BstLean.Part263.covarianceEvent 13023 scalarRow13023.grid parameters

theorem covarianceEvent13023_measurable : MeasurableSet covarianceEvent13023 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13023_payment :
    (retDist (paperDesignP 13023).toCentres).real
      (agentEv (paperDesignP 13023) covarianceEvent13023)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13023

theorem localCov13023 : BstLean.Part259.LocalCovarianceOn covarianceEvent13023
    (BstLean.Part263.cell scalarRow13023.grid) (caps repair13023) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13023

theorem covarianceGood13023_payment :
    (retDist (paperDesignP 13023).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13023)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13023_payment



end BstLean.Part269.N13023

namespace BstLean.Part269.N13023
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13023}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13023.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13023) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13023).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13023 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13023) (by norm_num) BstLean.Part268.WorldRow13023.worldPackage rfl
    BstLean.Part268.WorldRow13023.product_lower (BstLean.Part268.WorldRow13023.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13023} (hw : c ∈ Hof BstLean.Part268.WorldRow13023.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13023) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13023) (by norm_num) BstLean.Part268.WorldRow13023.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13023} (hw : c ∈ Hof BstLean.Part268.WorldRow13023.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13023) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13023).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13023) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13023_eq : scalarRow13023.targetFrame = BstLean.Part268.agent13023.frame := by
  norm_num [scalarRow13023,BstLean.Part268.agent13023]

noncomputable def frameData13023 : BstLean.Part264b.FrameData 13023 :=
  BstLean.Part269.frameData_from_numerics (n := 13023) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13023.worldPackage rfl BstLean.Part268.WorldRow13023.product_lower (BstLean.Part268.WorldRow13023.producthi.2.trans (by norm_num))
    scalarRow13023 repair13023 covarianceInputs13023 (fun i hi => sourceNumerics13023 hi)
    BstLean.Part268.agent13023.frame targetFrame13023_eq


end BstLean.Part269.N13023

namespace BstLean.Part269.N13024
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13024 : scalarRow13024.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13024, BstLean.Part268.grid13024, BstLean.Part263.worldGrid]

theorem supplies13024 (j : Fin 43) : Supply 13024 (parameters j)
    (cellLower scalarRow13024.grid (sourceIndex j))
    (cellUpper scalarRow13024.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13024.grid grid_top_bounds13024 j

theorem radii13024 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13024.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13024 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13024 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13024.grid grid_top_bounds13024 j hθ

noncomputable def covarianceInputs13024 :
    BstLean.Part263.CovarianceInputs 13024 scalarRow13024.grid parameters (caps repair13024) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13024 grid_top_bounds13024 repair13024

noncomputable def covarianceEvent13024 : Set (AgFam 13024) :=
  BstLean.Part263.covarianceEvent 13024 scalarRow13024.grid parameters

theorem covarianceEvent13024_measurable : MeasurableSet covarianceEvent13024 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13024_payment :
    (retDist (paperDesignP 13024).toCentres).real
      (agentEv (paperDesignP 13024) covarianceEvent13024)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13024

theorem localCov13024 : BstLean.Part259.LocalCovarianceOn covarianceEvent13024
    (BstLean.Part263.cell scalarRow13024.grid) (caps repair13024) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13024

theorem covarianceGood13024_payment :
    (retDist (paperDesignP 13024).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13024)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13024_payment



end BstLean.Part269.N13024

namespace BstLean.Part269.N13024
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13024}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13024.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13024) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13024).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13024 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13024) (by norm_num) BstLean.Part268.WorldRow13024.worldPackage rfl
    BstLean.Part268.WorldRow13024.product_lower (BstLean.Part268.WorldRow13024.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13024} (hw : c ∈ Hof BstLean.Part268.WorldRow13024.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13024) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13024) (by norm_num) BstLean.Part268.WorldRow13024.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13024} (hw : c ∈ Hof BstLean.Part268.WorldRow13024.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13024) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13024).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13024) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13024_eq : scalarRow13024.targetFrame = BstLean.Part268.agent13024.frame := by
  norm_num [scalarRow13024,BstLean.Part268.agent13024]

noncomputable def frameData13024 : BstLean.Part264b.FrameData 13024 :=
  BstLean.Part269.frameData_from_numerics (n := 13024) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13024.worldPackage rfl BstLean.Part268.WorldRow13024.product_lower (BstLean.Part268.WorldRow13024.producthi.2.trans (by norm_num))
    scalarRow13024 repair13024 covarianceInputs13024 (fun i hi => sourceNumerics13024 hi)
    BstLean.Part268.agent13024.frame targetFrame13024_eq


end BstLean.Part269.N13024
