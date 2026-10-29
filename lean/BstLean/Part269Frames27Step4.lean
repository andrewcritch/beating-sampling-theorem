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

namespace BstLean.Part269.N13045
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13045 : scalarRow13045.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13045, BstLean.Part268.grid13045, BstLean.Part263.worldGrid]

theorem supplies13045 (j : Fin 43) : Supply 13045 (parameters j)
    (cellLower scalarRow13045.grid (sourceIndex j))
    (cellUpper scalarRow13045.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13045.grid grid_top_bounds13045 j

theorem radii13045 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13045.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13045 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13045 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13045.grid grid_top_bounds13045 j hθ

noncomputable def covarianceInputs13045 :
    BstLean.Part263.CovarianceInputs 13045 scalarRow13045.grid parameters (caps repair13045) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13045 grid_top_bounds13045 repair13045

noncomputable def covarianceEvent13045 : Set (AgFam 13045) :=
  BstLean.Part263.covarianceEvent 13045 scalarRow13045.grid parameters

theorem covarianceEvent13045_measurable : MeasurableSet covarianceEvent13045 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13045_payment :
    (retDist (paperDesignP 13045).toCentres).real
      (agentEv (paperDesignP 13045) covarianceEvent13045)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13045

theorem localCov13045 : BstLean.Part259.LocalCovarianceOn covarianceEvent13045
    (BstLean.Part263.cell scalarRow13045.grid) (caps repair13045) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13045

theorem covarianceGood13045_payment :
    (retDist (paperDesignP 13045).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13045)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13045_payment



end BstLean.Part269.N13045

namespace BstLean.Part269.N13045
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13045}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13045.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13045) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13045).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13045 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13045) (by norm_num) BstLean.Part268.WorldRow13045.worldPackage rfl
    BstLean.Part268.WorldRow13045.product_lower (BstLean.Part268.WorldRow13045.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13045} (hw : c ∈ Hof BstLean.Part268.WorldRow13045.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13045) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13045) (by norm_num) BstLean.Part268.WorldRow13045.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13045} (hw : c ∈ Hof BstLean.Part268.WorldRow13045.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13045) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13045).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13045) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13045_eq : scalarRow13045.targetFrame = BstLean.Part268.agent13045.frame := by
  norm_num [scalarRow13045,BstLean.Part268.agent13045]

noncomputable def frameData13045 : BstLean.Part264b.FrameData 13045 :=
  BstLean.Part269.frameData_from_numerics (n := 13045) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13045.worldPackage rfl BstLean.Part268.WorldRow13045.product_lower (BstLean.Part268.WorldRow13045.producthi.2.trans (by norm_num))
    scalarRow13045 repair13045 covarianceInputs13045 (fun i hi => sourceNumerics13045 hi)
    BstLean.Part268.agent13045.frame targetFrame13045_eq


end BstLean.Part269.N13045

namespace BstLean.Part269.N13046
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13046 : scalarRow13046.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13046, BstLean.Part268.grid13046, BstLean.Part263.worldGrid]

theorem supplies13046 (j : Fin 43) : Supply 13046 (parameters j)
    (cellLower scalarRow13046.grid (sourceIndex j))
    (cellUpper scalarRow13046.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13046.grid grid_top_bounds13046 j

theorem radii13046 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13046.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13046 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13046 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13046.grid grid_top_bounds13046 j hθ

noncomputable def covarianceInputs13046 :
    BstLean.Part263.CovarianceInputs 13046 scalarRow13046.grid parameters (caps repair13046) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13046 grid_top_bounds13046 repair13046

noncomputable def covarianceEvent13046 : Set (AgFam 13046) :=
  BstLean.Part263.covarianceEvent 13046 scalarRow13046.grid parameters

theorem covarianceEvent13046_measurable : MeasurableSet covarianceEvent13046 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13046_payment :
    (retDist (paperDesignP 13046).toCentres).real
      (agentEv (paperDesignP 13046) covarianceEvent13046)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13046

theorem localCov13046 : BstLean.Part259.LocalCovarianceOn covarianceEvent13046
    (BstLean.Part263.cell scalarRow13046.grid) (caps repair13046) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13046

theorem covarianceGood13046_payment :
    (retDist (paperDesignP 13046).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13046)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13046_payment



end BstLean.Part269.N13046

namespace BstLean.Part269.N13046
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13046}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13046.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13046) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13046).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13046 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13046) (by norm_num) BstLean.Part268.WorldRow13046.worldPackage rfl
    BstLean.Part268.WorldRow13046.product_lower (BstLean.Part268.WorldRow13046.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13046} (hw : c ∈ Hof BstLean.Part268.WorldRow13046.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13046) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13046) (by norm_num) BstLean.Part268.WorldRow13046.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13046} (hw : c ∈ Hof BstLean.Part268.WorldRow13046.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13046) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13046).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13046) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13046_eq : scalarRow13046.targetFrame = BstLean.Part268.agent13046.frame := by
  norm_num [scalarRow13046,BstLean.Part268.agent13046]

noncomputable def frameData13046 : BstLean.Part264b.FrameData 13046 :=
  BstLean.Part269.frameData_from_numerics (n := 13046) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13046.worldPackage rfl BstLean.Part268.WorldRow13046.product_lower (BstLean.Part268.WorldRow13046.producthi.2.trans (by norm_num))
    scalarRow13046 repair13046 covarianceInputs13046 (fun i hi => sourceNumerics13046 hi)
    BstLean.Part268.agent13046.frame targetFrame13046_eq


end BstLean.Part269.N13046

namespace BstLean.Part269.N13047
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13047 : scalarRow13047.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13047, BstLean.Part268.grid13047, BstLean.Part263.worldGrid]

theorem supplies13047 (j : Fin 43) : Supply 13047 (parameters j)
    (cellLower scalarRow13047.grid (sourceIndex j))
    (cellUpper scalarRow13047.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13047.grid grid_top_bounds13047 j

theorem radii13047 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13047.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13047 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13047 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13047.grid grid_top_bounds13047 j hθ

noncomputable def covarianceInputs13047 :
    BstLean.Part263.CovarianceInputs 13047 scalarRow13047.grid parameters (caps repair13047) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13047 grid_top_bounds13047 repair13047

noncomputable def covarianceEvent13047 : Set (AgFam 13047) :=
  BstLean.Part263.covarianceEvent 13047 scalarRow13047.grid parameters

theorem covarianceEvent13047_measurable : MeasurableSet covarianceEvent13047 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13047_payment :
    (retDist (paperDesignP 13047).toCentres).real
      (agentEv (paperDesignP 13047) covarianceEvent13047)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13047

theorem localCov13047 : BstLean.Part259.LocalCovarianceOn covarianceEvent13047
    (BstLean.Part263.cell scalarRow13047.grid) (caps repair13047) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13047

theorem covarianceGood13047_payment :
    (retDist (paperDesignP 13047).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13047)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13047_payment



end BstLean.Part269.N13047

namespace BstLean.Part269.N13047
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13047}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13047.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13047) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13047).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13047 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13047) (by norm_num) BstLean.Part268.WorldRow13047.worldPackage rfl
    BstLean.Part268.WorldRow13047.product_lower (BstLean.Part268.WorldRow13047.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13047} (hw : c ∈ Hof BstLean.Part268.WorldRow13047.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13047) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13047) (by norm_num) BstLean.Part268.WorldRow13047.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13047} (hw : c ∈ Hof BstLean.Part268.WorldRow13047.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13047) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13047).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13047) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13047_eq : scalarRow13047.targetFrame = BstLean.Part268.agent13047.frame := by
  norm_num [scalarRow13047,BstLean.Part268.agent13047]

noncomputable def frameData13047 : BstLean.Part264b.FrameData 13047 :=
  BstLean.Part269.frameData_from_numerics (n := 13047) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13047.worldPackage rfl BstLean.Part268.WorldRow13047.product_lower (BstLean.Part268.WorldRow13047.producthi.2.trans (by norm_num))
    scalarRow13047 repair13047 covarianceInputs13047 (fun i hi => sourceNumerics13047 hi)
    BstLean.Part268.agent13047.frame targetFrame13047_eq


end BstLean.Part269.N13047

namespace BstLean.Part269.N13048
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13048 : scalarRow13048.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13048, BstLean.Part268.grid13048, BstLean.Part263.worldGrid]

theorem supplies13048 (j : Fin 43) : Supply 13048 (parameters j)
    (cellLower scalarRow13048.grid (sourceIndex j))
    (cellUpper scalarRow13048.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13048.grid grid_top_bounds13048 j

theorem radii13048 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13048.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13048 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13048 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13048.grid grid_top_bounds13048 j hθ

noncomputable def covarianceInputs13048 :
    BstLean.Part263.CovarianceInputs 13048 scalarRow13048.grid parameters (caps repair13048) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13048 grid_top_bounds13048 repair13048

noncomputable def covarianceEvent13048 : Set (AgFam 13048) :=
  BstLean.Part263.covarianceEvent 13048 scalarRow13048.grid parameters

theorem covarianceEvent13048_measurable : MeasurableSet covarianceEvent13048 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13048_payment :
    (retDist (paperDesignP 13048).toCentres).real
      (agentEv (paperDesignP 13048) covarianceEvent13048)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13048

theorem localCov13048 : BstLean.Part259.LocalCovarianceOn covarianceEvent13048
    (BstLean.Part263.cell scalarRow13048.grid) (caps repair13048) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13048

theorem covarianceGood13048_payment :
    (retDist (paperDesignP 13048).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13048)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13048_payment



end BstLean.Part269.N13048

namespace BstLean.Part269.N13048
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13048}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13048.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13048) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13048).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13048 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13048) (by norm_num) BstLean.Part268.WorldRow13048.worldPackage rfl
    BstLean.Part268.WorldRow13048.product_lower (BstLean.Part268.WorldRow13048.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13048} (hw : c ∈ Hof BstLean.Part268.WorldRow13048.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13048) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13048) (by norm_num) BstLean.Part268.WorldRow13048.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13048} (hw : c ∈ Hof BstLean.Part268.WorldRow13048.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13048) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13048).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13048) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13048_eq : scalarRow13048.targetFrame = BstLean.Part268.agent13048.frame := by
  norm_num [scalarRow13048,BstLean.Part268.agent13048]

noncomputable def frameData13048 : BstLean.Part264b.FrameData 13048 :=
  BstLean.Part269.frameData_from_numerics (n := 13048) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13048.worldPackage rfl BstLean.Part268.WorldRow13048.product_lower (BstLean.Part268.WorldRow13048.producthi.2.trans (by norm_num))
    scalarRow13048 repair13048 covarianceInputs13048 (fun i hi => sourceNumerics13048 hi)
    BstLean.Part268.agent13048.frame targetFrame13048_eq


end BstLean.Part269.N13048

namespace BstLean.Part269.N13049
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13049 : scalarRow13049.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13049, BstLean.Part268.grid13049, BstLean.Part263.worldGrid]

theorem supplies13049 (j : Fin 43) : Supply 13049 (parameters j)
    (cellLower scalarRow13049.grid (sourceIndex j))
    (cellUpper scalarRow13049.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13049.grid grid_top_bounds13049 j

theorem radii13049 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13049.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13049 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13049 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13049.grid grid_top_bounds13049 j hθ

noncomputable def covarianceInputs13049 :
    BstLean.Part263.CovarianceInputs 13049 scalarRow13049.grid parameters (caps repair13049) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13049 grid_top_bounds13049 repair13049

noncomputable def covarianceEvent13049 : Set (AgFam 13049) :=
  BstLean.Part263.covarianceEvent 13049 scalarRow13049.grid parameters

theorem covarianceEvent13049_measurable : MeasurableSet covarianceEvent13049 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13049_payment :
    (retDist (paperDesignP 13049).toCentres).real
      (agentEv (paperDesignP 13049) covarianceEvent13049)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13049

theorem localCov13049 : BstLean.Part259.LocalCovarianceOn covarianceEvent13049
    (BstLean.Part263.cell scalarRow13049.grid) (caps repair13049) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13049

theorem covarianceGood13049_payment :
    (retDist (paperDesignP 13049).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13049)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13049_payment



end BstLean.Part269.N13049

namespace BstLean.Part269.N13049
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13049}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13049.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13049) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13049).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13049 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13049) (by norm_num) BstLean.Part268.WorldRow13049.worldPackage rfl
    BstLean.Part268.WorldRow13049.product_lower (BstLean.Part268.WorldRow13049.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13049} (hw : c ∈ Hof BstLean.Part268.WorldRow13049.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13049) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13049) (by norm_num) BstLean.Part268.WorldRow13049.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13049} (hw : c ∈ Hof BstLean.Part268.WorldRow13049.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13049) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13049).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13049) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13049_eq : scalarRow13049.targetFrame = BstLean.Part268.agent13049.frame := by
  norm_num [scalarRow13049,BstLean.Part268.agent13049]

noncomputable def frameData13049 : BstLean.Part264b.FrameData 13049 :=
  BstLean.Part269.frameData_from_numerics (n := 13049) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13049.worldPackage rfl BstLean.Part268.WorldRow13049.product_lower (BstLean.Part268.WorldRow13049.producthi.2.trans (by norm_num))
    scalarRow13049 repair13049 covarianceInputs13049 (fun i hi => sourceNumerics13049 hi)
    BstLean.Part268.agent13049.frame targetFrame13049_eq


end BstLean.Part269.N13049
