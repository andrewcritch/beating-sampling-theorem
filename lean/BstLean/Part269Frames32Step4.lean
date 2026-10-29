import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World32Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs32
import BstLean.Part269Rows32
import BstLean.Part269Sources32
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13170
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13170 : scalarRow13170.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13170, BstLean.Part268.grid13170, BstLean.Part263.worldGrid]

theorem supplies13170 (j : Fin 43) : Supply 13170 (parameters j)
    (cellLower scalarRow13170.grid (sourceIndex j))
    (cellUpper scalarRow13170.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13170.grid grid_top_bounds13170 j

theorem radii13170 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13170.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13170 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13170 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13170.grid grid_top_bounds13170 j hθ

noncomputable def covarianceInputs13170 :
    BstLean.Part263.CovarianceInputs 13170 scalarRow13170.grid parameters (caps repair13170) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13170 grid_top_bounds13170 repair13170

noncomputable def covarianceEvent13170 : Set (AgFam 13170) :=
  BstLean.Part263.covarianceEvent 13170 scalarRow13170.grid parameters

theorem covarianceEvent13170_measurable : MeasurableSet covarianceEvent13170 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13170_payment :
    (retDist (paperDesignP 13170).toCentres).real
      (agentEv (paperDesignP 13170) covarianceEvent13170)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13170

theorem localCov13170 : BstLean.Part259.LocalCovarianceOn covarianceEvent13170
    (BstLean.Part263.cell scalarRow13170.grid) (caps repair13170) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13170

theorem covarianceGood13170_payment :
    (retDist (paperDesignP 13170).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13170)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13170_payment



end BstLean.Part269.N13170

namespace BstLean.Part269.N13170
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13170}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13170.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13170) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13170).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13170 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13170) (by norm_num) BstLean.Part268.WorldRow13170.worldPackage rfl
    BstLean.Part268.WorldRow13170.product_lower (BstLean.Part268.WorldRow13170.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13170} (hw : c ∈ Hof BstLean.Part268.WorldRow13170.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13170) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13170) (by norm_num) BstLean.Part268.WorldRow13170.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13170} (hw : c ∈ Hof BstLean.Part268.WorldRow13170.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13170) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13170).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13170) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13170_eq : scalarRow13170.targetFrame = BstLean.Part268.agent13170.frame := by
  norm_num [scalarRow13170,BstLean.Part268.agent13170]

noncomputable def frameData13170 : BstLean.Part264b.FrameData 13170 :=
  BstLean.Part269.frameData_from_numerics (n := 13170) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13170.worldPackage rfl BstLean.Part268.WorldRow13170.product_lower (BstLean.Part268.WorldRow13170.producthi.2.trans (by norm_num))
    scalarRow13170 repair13170 covarianceInputs13170 (fun i hi => sourceNumerics13170 hi)
    BstLean.Part268.agent13170.frame targetFrame13170_eq


end BstLean.Part269.N13170

namespace BstLean.Part269.N13171
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13171 : scalarRow13171.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13171, BstLean.Part268.grid13171, BstLean.Part263.worldGrid]

theorem supplies13171 (j : Fin 43) : Supply 13171 (parameters j)
    (cellLower scalarRow13171.grid (sourceIndex j))
    (cellUpper scalarRow13171.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13171.grid grid_top_bounds13171 j

theorem radii13171 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13171.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13171 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13171 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13171.grid grid_top_bounds13171 j hθ

noncomputable def covarianceInputs13171 :
    BstLean.Part263.CovarianceInputs 13171 scalarRow13171.grid parameters (caps repair13171) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13171 grid_top_bounds13171 repair13171

noncomputable def covarianceEvent13171 : Set (AgFam 13171) :=
  BstLean.Part263.covarianceEvent 13171 scalarRow13171.grid parameters

theorem covarianceEvent13171_measurable : MeasurableSet covarianceEvent13171 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13171_payment :
    (retDist (paperDesignP 13171).toCentres).real
      (agentEv (paperDesignP 13171) covarianceEvent13171)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13171

theorem localCov13171 : BstLean.Part259.LocalCovarianceOn covarianceEvent13171
    (BstLean.Part263.cell scalarRow13171.grid) (caps repair13171) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13171

theorem covarianceGood13171_payment :
    (retDist (paperDesignP 13171).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13171)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13171_payment



end BstLean.Part269.N13171

namespace BstLean.Part269.N13171
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13171}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13171.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13171) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13171).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13171 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13171) (by norm_num) BstLean.Part268.WorldRow13171.worldPackage rfl
    BstLean.Part268.WorldRow13171.product_lower (BstLean.Part268.WorldRow13171.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13171} (hw : c ∈ Hof BstLean.Part268.WorldRow13171.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13171) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13171) (by norm_num) BstLean.Part268.WorldRow13171.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13171} (hw : c ∈ Hof BstLean.Part268.WorldRow13171.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13171) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13171).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13171) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13171_eq : scalarRow13171.targetFrame = BstLean.Part268.agent13171.frame := by
  norm_num [scalarRow13171,BstLean.Part268.agent13171]

noncomputable def frameData13171 : BstLean.Part264b.FrameData 13171 :=
  BstLean.Part269.frameData_from_numerics (n := 13171) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13171.worldPackage rfl BstLean.Part268.WorldRow13171.product_lower (BstLean.Part268.WorldRow13171.producthi.2.trans (by norm_num))
    scalarRow13171 repair13171 covarianceInputs13171 (fun i hi => sourceNumerics13171 hi)
    BstLean.Part268.agent13171.frame targetFrame13171_eq


end BstLean.Part269.N13171

namespace BstLean.Part269.N13172
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13172 : scalarRow13172.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13172, BstLean.Part268.grid13172, BstLean.Part263.worldGrid]

theorem supplies13172 (j : Fin 43) : Supply 13172 (parameters j)
    (cellLower scalarRow13172.grid (sourceIndex j))
    (cellUpper scalarRow13172.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13172.grid grid_top_bounds13172 j

theorem radii13172 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13172.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13172 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13172 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13172.grid grid_top_bounds13172 j hθ

noncomputable def covarianceInputs13172 :
    BstLean.Part263.CovarianceInputs 13172 scalarRow13172.grid parameters (caps repair13172) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13172 grid_top_bounds13172 repair13172

noncomputable def covarianceEvent13172 : Set (AgFam 13172) :=
  BstLean.Part263.covarianceEvent 13172 scalarRow13172.grid parameters

theorem covarianceEvent13172_measurable : MeasurableSet covarianceEvent13172 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13172_payment :
    (retDist (paperDesignP 13172).toCentres).real
      (agentEv (paperDesignP 13172) covarianceEvent13172)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13172

theorem localCov13172 : BstLean.Part259.LocalCovarianceOn covarianceEvent13172
    (BstLean.Part263.cell scalarRow13172.grid) (caps repair13172) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13172

theorem covarianceGood13172_payment :
    (retDist (paperDesignP 13172).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13172)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13172_payment



end BstLean.Part269.N13172

namespace BstLean.Part269.N13172
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13172}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13172.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13172) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13172).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13172 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13172) (by norm_num) BstLean.Part268.WorldRow13172.worldPackage rfl
    BstLean.Part268.WorldRow13172.product_lower (BstLean.Part268.WorldRow13172.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13172} (hw : c ∈ Hof BstLean.Part268.WorldRow13172.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13172) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13172) (by norm_num) BstLean.Part268.WorldRow13172.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13172} (hw : c ∈ Hof BstLean.Part268.WorldRow13172.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13172) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13172).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13172) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13172_eq : scalarRow13172.targetFrame = BstLean.Part268.agent13172.frame := by
  norm_num [scalarRow13172,BstLean.Part268.agent13172]

noncomputable def frameData13172 : BstLean.Part264b.FrameData 13172 :=
  BstLean.Part269.frameData_from_numerics (n := 13172) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13172.worldPackage rfl BstLean.Part268.WorldRow13172.product_lower (BstLean.Part268.WorldRow13172.producthi.2.trans (by norm_num))
    scalarRow13172 repair13172 covarianceInputs13172 (fun i hi => sourceNumerics13172 hi)
    BstLean.Part268.agent13172.frame targetFrame13172_eq


end BstLean.Part269.N13172

namespace BstLean.Part269.N13173
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13173 : scalarRow13173.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13173, BstLean.Part268.grid13173, BstLean.Part263.worldGrid]

theorem supplies13173 (j : Fin 43) : Supply 13173 (parameters j)
    (cellLower scalarRow13173.grid (sourceIndex j))
    (cellUpper scalarRow13173.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13173.grid grid_top_bounds13173 j

theorem radii13173 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13173.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13173 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13173 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13173.grid grid_top_bounds13173 j hθ

noncomputable def covarianceInputs13173 :
    BstLean.Part263.CovarianceInputs 13173 scalarRow13173.grid parameters (caps repair13173) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13173 grid_top_bounds13173 repair13173

noncomputable def covarianceEvent13173 : Set (AgFam 13173) :=
  BstLean.Part263.covarianceEvent 13173 scalarRow13173.grid parameters

theorem covarianceEvent13173_measurable : MeasurableSet covarianceEvent13173 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13173_payment :
    (retDist (paperDesignP 13173).toCentres).real
      (agentEv (paperDesignP 13173) covarianceEvent13173)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13173

theorem localCov13173 : BstLean.Part259.LocalCovarianceOn covarianceEvent13173
    (BstLean.Part263.cell scalarRow13173.grid) (caps repair13173) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13173

theorem covarianceGood13173_payment :
    (retDist (paperDesignP 13173).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13173)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13173_payment



end BstLean.Part269.N13173

namespace BstLean.Part269.N13173
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13173}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13173.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13173) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13173).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13173 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13173) (by norm_num) BstLean.Part268.WorldRow13173.worldPackage rfl
    BstLean.Part268.WorldRow13173.product_lower (BstLean.Part268.WorldRow13173.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13173} (hw : c ∈ Hof BstLean.Part268.WorldRow13173.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13173) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13173) (by norm_num) BstLean.Part268.WorldRow13173.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13173} (hw : c ∈ Hof BstLean.Part268.WorldRow13173.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13173) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13173).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13173) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13173_eq : scalarRow13173.targetFrame = BstLean.Part268.agent13173.frame := by
  norm_num [scalarRow13173,BstLean.Part268.agent13173]

noncomputable def frameData13173 : BstLean.Part264b.FrameData 13173 :=
  BstLean.Part269.frameData_from_numerics (n := 13173) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13173.worldPackage rfl BstLean.Part268.WorldRow13173.product_lower (BstLean.Part268.WorldRow13173.producthi.2.trans (by norm_num))
    scalarRow13173 repair13173 covarianceInputs13173 (fun i hi => sourceNumerics13173 hi)
    BstLean.Part268.agent13173.frame targetFrame13173_eq


end BstLean.Part269.N13173

namespace BstLean.Part269.N13174
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13174 : scalarRow13174.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13174, BstLean.Part268.grid13174, BstLean.Part263.worldGrid]

theorem supplies13174 (j : Fin 43) : Supply 13174 (parameters j)
    (cellLower scalarRow13174.grid (sourceIndex j))
    (cellUpper scalarRow13174.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13174.grid grid_top_bounds13174 j

theorem radii13174 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13174.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13174 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13174 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13174.grid grid_top_bounds13174 j hθ

noncomputable def covarianceInputs13174 :
    BstLean.Part263.CovarianceInputs 13174 scalarRow13174.grid parameters (caps repair13174) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13174 grid_top_bounds13174 repair13174

noncomputable def covarianceEvent13174 : Set (AgFam 13174) :=
  BstLean.Part263.covarianceEvent 13174 scalarRow13174.grid parameters

theorem covarianceEvent13174_measurable : MeasurableSet covarianceEvent13174 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13174_payment :
    (retDist (paperDesignP 13174).toCentres).real
      (agentEv (paperDesignP 13174) covarianceEvent13174)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13174

theorem localCov13174 : BstLean.Part259.LocalCovarianceOn covarianceEvent13174
    (BstLean.Part263.cell scalarRow13174.grid) (caps repair13174) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13174

theorem covarianceGood13174_payment :
    (retDist (paperDesignP 13174).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13174)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13174_payment



end BstLean.Part269.N13174

namespace BstLean.Part269.N13174
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13174}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13174.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13174) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13174).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13174 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13174) (by norm_num) BstLean.Part268.WorldRow13174.worldPackage rfl
    BstLean.Part268.WorldRow13174.product_lower (BstLean.Part268.WorldRow13174.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13174} (hw : c ∈ Hof BstLean.Part268.WorldRow13174.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13174) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13174) (by norm_num) BstLean.Part268.WorldRow13174.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13174} (hw : c ∈ Hof BstLean.Part268.WorldRow13174.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13174) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13174).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13174) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13174_eq : scalarRow13174.targetFrame = BstLean.Part268.agent13174.frame := by
  norm_num [scalarRow13174,BstLean.Part268.agent13174]

noncomputable def frameData13174 : BstLean.Part264b.FrameData 13174 :=
  BstLean.Part269.frameData_from_numerics (n := 13174) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13174.worldPackage rfl BstLean.Part268.WorldRow13174.product_lower (BstLean.Part268.WorldRow13174.producthi.2.trans (by norm_num))
    scalarRow13174 repair13174 covarianceInputs13174 (fun i hi => sourceNumerics13174 hi)
    BstLean.Part268.agent13174.frame targetFrame13174_eq


end BstLean.Part269.N13174
