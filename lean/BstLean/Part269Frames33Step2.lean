import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World33Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs33
import BstLean.Part269Rows33
import BstLean.Part269Sources33
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N13185
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13185 : scalarRow13185.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13185, BstLean.Part268.grid13185, BstLean.Part263.worldGrid]

theorem supplies13185 (j : Fin 43) : Supply 13185 (parameters j)
    (cellLower scalarRow13185.grid (sourceIndex j))
    (cellUpper scalarRow13185.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13185.grid grid_top_bounds13185 j

theorem radii13185 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13185.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13185 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13185 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13185.grid grid_top_bounds13185 j hθ

noncomputable def covarianceInputs13185 :
    BstLean.Part263.CovarianceInputs 13185 scalarRow13185.grid parameters (caps repair13185) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13185 grid_top_bounds13185 repair13185

noncomputable def covarianceEvent13185 : Set (AgFam 13185) :=
  BstLean.Part263.covarianceEvent 13185 scalarRow13185.grid parameters

theorem covarianceEvent13185_measurable : MeasurableSet covarianceEvent13185 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13185_payment :
    (retDist (paperDesignP 13185).toCentres).real
      (agentEv (paperDesignP 13185) covarianceEvent13185)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13185

theorem localCov13185 : BstLean.Part259.LocalCovarianceOn covarianceEvent13185
    (BstLean.Part263.cell scalarRow13185.grid) (caps repair13185) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13185

theorem covarianceGood13185_payment :
    (retDist (paperDesignP 13185).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13185)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13185_payment



end BstLean.Part269.N13185

namespace BstLean.Part269.N13185
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13185}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13185.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13185) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13185).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13185 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13185) (by norm_num) BstLean.Part268.WorldRow13185.worldPackage rfl
    BstLean.Part268.WorldRow13185.product_lower (BstLean.Part268.WorldRow13185.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13185} (hw : c ∈ Hof BstLean.Part268.WorldRow13185.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13185) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13185) (by norm_num) BstLean.Part268.WorldRow13185.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13185} (hw : c ∈ Hof BstLean.Part268.WorldRow13185.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13185) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13185).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13185) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13185_eq : scalarRow13185.targetFrame = BstLean.Part268.agent13185.frame := by
  norm_num [scalarRow13185,BstLean.Part268.agent13185]

noncomputable def frameData13185 : BstLean.Part264b.FrameData 13185 :=
  BstLean.Part269.frameData_from_numerics (n := 13185) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13185.worldPackage rfl BstLean.Part268.WorldRow13185.product_lower (BstLean.Part268.WorldRow13185.producthi.2.trans (by norm_num))
    scalarRow13185 repair13185 covarianceInputs13185 (fun i hi => sourceNumerics13185 hi)
    BstLean.Part268.agent13185.frame targetFrame13185_eq


end BstLean.Part269.N13185

namespace BstLean.Part269.N13186
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13186 : scalarRow13186.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13186, BstLean.Part268.grid13186, BstLean.Part263.worldGrid]

theorem supplies13186 (j : Fin 43) : Supply 13186 (parameters j)
    (cellLower scalarRow13186.grid (sourceIndex j))
    (cellUpper scalarRow13186.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13186.grid grid_top_bounds13186 j

theorem radii13186 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13186.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13186 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13186 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13186.grid grid_top_bounds13186 j hθ

noncomputable def covarianceInputs13186 :
    BstLean.Part263.CovarianceInputs 13186 scalarRow13186.grid parameters (caps repair13186) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13186 grid_top_bounds13186 repair13186

noncomputable def covarianceEvent13186 : Set (AgFam 13186) :=
  BstLean.Part263.covarianceEvent 13186 scalarRow13186.grid parameters

theorem covarianceEvent13186_measurable : MeasurableSet covarianceEvent13186 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13186_payment :
    (retDist (paperDesignP 13186).toCentres).real
      (agentEv (paperDesignP 13186) covarianceEvent13186)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13186

theorem localCov13186 : BstLean.Part259.LocalCovarianceOn covarianceEvent13186
    (BstLean.Part263.cell scalarRow13186.grid) (caps repair13186) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13186

theorem covarianceGood13186_payment :
    (retDist (paperDesignP 13186).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13186)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13186_payment



end BstLean.Part269.N13186

namespace BstLean.Part269.N13186
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13186}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13186.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13186) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13186).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13186 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13186) (by norm_num) BstLean.Part268.WorldRow13186.worldPackage rfl
    BstLean.Part268.WorldRow13186.product_lower (BstLean.Part268.WorldRow13186.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13186} (hw : c ∈ Hof BstLean.Part268.WorldRow13186.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13186) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13186) (by norm_num) BstLean.Part268.WorldRow13186.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13186} (hw : c ∈ Hof BstLean.Part268.WorldRow13186.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13186) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13186).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13186) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13186_eq : scalarRow13186.targetFrame = BstLean.Part268.agent13186.frame := by
  norm_num [scalarRow13186,BstLean.Part268.agent13186]

noncomputable def frameData13186 : BstLean.Part264b.FrameData 13186 :=
  BstLean.Part269.frameData_from_numerics (n := 13186) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13186.worldPackage rfl BstLean.Part268.WorldRow13186.product_lower (BstLean.Part268.WorldRow13186.producthi.2.trans (by norm_num))
    scalarRow13186 repair13186 covarianceInputs13186 (fun i hi => sourceNumerics13186 hi)
    BstLean.Part268.agent13186.frame targetFrame13186_eq


end BstLean.Part269.N13186

namespace BstLean.Part269.N13187
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13187 : scalarRow13187.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13187, BstLean.Part268.grid13187, BstLean.Part263.worldGrid]

theorem supplies13187 (j : Fin 43) : Supply 13187 (parameters j)
    (cellLower scalarRow13187.grid (sourceIndex j))
    (cellUpper scalarRow13187.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13187.grid grid_top_bounds13187 j

theorem radii13187 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13187.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13187 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13187 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13187.grid grid_top_bounds13187 j hθ

noncomputable def covarianceInputs13187 :
    BstLean.Part263.CovarianceInputs 13187 scalarRow13187.grid parameters (caps repair13187) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13187 grid_top_bounds13187 repair13187

noncomputable def covarianceEvent13187 : Set (AgFam 13187) :=
  BstLean.Part263.covarianceEvent 13187 scalarRow13187.grid parameters

theorem covarianceEvent13187_measurable : MeasurableSet covarianceEvent13187 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13187_payment :
    (retDist (paperDesignP 13187).toCentres).real
      (agentEv (paperDesignP 13187) covarianceEvent13187)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13187

theorem localCov13187 : BstLean.Part259.LocalCovarianceOn covarianceEvent13187
    (BstLean.Part263.cell scalarRow13187.grid) (caps repair13187) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13187

theorem covarianceGood13187_payment :
    (retDist (paperDesignP 13187).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13187)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13187_payment



end BstLean.Part269.N13187

namespace BstLean.Part269.N13187
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13187}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13187.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13187) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13187).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13187 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13187) (by norm_num) BstLean.Part268.WorldRow13187.worldPackage rfl
    BstLean.Part268.WorldRow13187.product_lower (BstLean.Part268.WorldRow13187.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13187} (hw : c ∈ Hof BstLean.Part268.WorldRow13187.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13187) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13187) (by norm_num) BstLean.Part268.WorldRow13187.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13187} (hw : c ∈ Hof BstLean.Part268.WorldRow13187.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13187) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13187).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13187) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13187_eq : scalarRow13187.targetFrame = BstLean.Part268.agent13187.frame := by
  norm_num [scalarRow13187,BstLean.Part268.agent13187]

noncomputable def frameData13187 : BstLean.Part264b.FrameData 13187 :=
  BstLean.Part269.frameData_from_numerics (n := 13187) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13187.worldPackage rfl BstLean.Part268.WorldRow13187.product_lower (BstLean.Part268.WorldRow13187.producthi.2.trans (by norm_num))
    scalarRow13187 repair13187 covarianceInputs13187 (fun i hi => sourceNumerics13187 hi)
    BstLean.Part268.agent13187.frame targetFrame13187_eq


end BstLean.Part269.N13187

namespace BstLean.Part269.N13188
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13188 : scalarRow13188.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13188, BstLean.Part268.grid13188, BstLean.Part263.worldGrid]

theorem supplies13188 (j : Fin 43) : Supply 13188 (parameters j)
    (cellLower scalarRow13188.grid (sourceIndex j))
    (cellUpper scalarRow13188.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13188.grid grid_top_bounds13188 j

theorem radii13188 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13188.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13188 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13188 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13188.grid grid_top_bounds13188 j hθ

noncomputable def covarianceInputs13188 :
    BstLean.Part263.CovarianceInputs 13188 scalarRow13188.grid parameters (caps repair13188) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13188 grid_top_bounds13188 repair13188

noncomputable def covarianceEvent13188 : Set (AgFam 13188) :=
  BstLean.Part263.covarianceEvent 13188 scalarRow13188.grid parameters

theorem covarianceEvent13188_measurable : MeasurableSet covarianceEvent13188 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13188_payment :
    (retDist (paperDesignP 13188).toCentres).real
      (agentEv (paperDesignP 13188) covarianceEvent13188)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13188

theorem localCov13188 : BstLean.Part259.LocalCovarianceOn covarianceEvent13188
    (BstLean.Part263.cell scalarRow13188.grid) (caps repair13188) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13188

theorem covarianceGood13188_payment :
    (retDist (paperDesignP 13188).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13188)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13188_payment



end BstLean.Part269.N13188

namespace BstLean.Part269.N13188
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13188}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13188.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13188) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13188).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13188 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13188) (by norm_num) BstLean.Part268.WorldRow13188.worldPackage rfl
    BstLean.Part268.WorldRow13188.product_lower (BstLean.Part268.WorldRow13188.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13188} (hw : c ∈ Hof BstLean.Part268.WorldRow13188.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13188) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13188) (by norm_num) BstLean.Part268.WorldRow13188.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13188} (hw : c ∈ Hof BstLean.Part268.WorldRow13188.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13188) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13188).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13188) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13188_eq : scalarRow13188.targetFrame = BstLean.Part268.agent13188.frame := by
  norm_num [scalarRow13188,BstLean.Part268.agent13188]

noncomputable def frameData13188 : BstLean.Part264b.FrameData 13188 :=
  BstLean.Part269.frameData_from_numerics (n := 13188) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13188.worldPackage rfl BstLean.Part268.WorldRow13188.product_lower (BstLean.Part268.WorldRow13188.producthi.2.trans (by norm_num))
    scalarRow13188 repair13188 covarianceInputs13188 (fun i hi => sourceNumerics13188 hi)
    BstLean.Part268.agent13188.frame targetFrame13188_eq


end BstLean.Part269.N13188

namespace BstLean.Part269.N13189
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13189 : scalarRow13189.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13189, BstLean.Part268.grid13189, BstLean.Part263.worldGrid]

theorem supplies13189 (j : Fin 43) : Supply 13189 (parameters j)
    (cellLower scalarRow13189.grid (sourceIndex j))
    (cellUpper scalarRow13189.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13189.grid grid_top_bounds13189 j

theorem radii13189 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13189.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13189 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13189 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13189.grid grid_top_bounds13189 j hθ

noncomputable def covarianceInputs13189 :
    BstLean.Part263.CovarianceInputs 13189 scalarRow13189.grid parameters (caps repair13189) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13189 grid_top_bounds13189 repair13189

noncomputable def covarianceEvent13189 : Set (AgFam 13189) :=
  BstLean.Part263.covarianceEvent 13189 scalarRow13189.grid parameters

theorem covarianceEvent13189_measurable : MeasurableSet covarianceEvent13189 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13189_payment :
    (retDist (paperDesignP 13189).toCentres).real
      (agentEv (paperDesignP 13189) covarianceEvent13189)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13189

theorem localCov13189 : BstLean.Part259.LocalCovarianceOn covarianceEvent13189
    (BstLean.Part263.cell scalarRow13189.grid) (caps repair13189) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13189

theorem covarianceGood13189_payment :
    (retDist (paperDesignP 13189).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13189)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13189_payment



end BstLean.Part269.N13189

namespace BstLean.Part269.N13189
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13189}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13189.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13189) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13189).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13189 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13189) (by norm_num) BstLean.Part268.WorldRow13189.worldPackage rfl
    BstLean.Part268.WorldRow13189.product_lower (BstLean.Part268.WorldRow13189.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13189} (hw : c ∈ Hof BstLean.Part268.WorldRow13189.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13189) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13189) (by norm_num) BstLean.Part268.WorldRow13189.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13189} (hw : c ∈ Hof BstLean.Part268.WorldRow13189.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13189) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13189).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13189) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13189_eq : scalarRow13189.targetFrame = BstLean.Part268.agent13189.frame := by
  norm_num [scalarRow13189,BstLean.Part268.agent13189]

noncomputable def frameData13189 : BstLean.Part264b.FrameData 13189 :=
  BstLean.Part269.frameData_from_numerics (n := 13189) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13189.worldPackage rfl BstLean.Part268.WorldRow13189.product_lower (BstLean.Part268.WorldRow13189.producthi.2.trans (by norm_num))
    scalarRow13189 repair13189 covarianceInputs13189 (fun i hi => sourceNumerics13189 hi)
    BstLean.Part268.agent13189.frame targetFrame13189_eq


end BstLean.Part269.N13189
