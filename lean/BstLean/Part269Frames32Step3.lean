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

namespace BstLean.Part269.N13165
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13165 : scalarRow13165.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13165, BstLean.Part268.grid13165, BstLean.Part263.worldGrid]

theorem supplies13165 (j : Fin 43) : Supply 13165 (parameters j)
    (cellLower scalarRow13165.grid (sourceIndex j))
    (cellUpper scalarRow13165.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13165.grid grid_top_bounds13165 j

theorem radii13165 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13165.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13165 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13165 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13165.grid grid_top_bounds13165 j hθ

noncomputable def covarianceInputs13165 :
    BstLean.Part263.CovarianceInputs 13165 scalarRow13165.grid parameters (caps repair13165) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13165 grid_top_bounds13165 repair13165

noncomputable def covarianceEvent13165 : Set (AgFam 13165) :=
  BstLean.Part263.covarianceEvent 13165 scalarRow13165.grid parameters

theorem covarianceEvent13165_measurable : MeasurableSet covarianceEvent13165 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13165_payment :
    (retDist (paperDesignP 13165).toCentres).real
      (agentEv (paperDesignP 13165) covarianceEvent13165)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13165

theorem localCov13165 : BstLean.Part259.LocalCovarianceOn covarianceEvent13165
    (BstLean.Part263.cell scalarRow13165.grid) (caps repair13165) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13165

theorem covarianceGood13165_payment :
    (retDist (paperDesignP 13165).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13165)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13165_payment



end BstLean.Part269.N13165

namespace BstLean.Part269.N13165
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13165}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13165.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13165) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13165).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13165 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13165) (by norm_num) BstLean.Part268.WorldRow13165.worldPackage rfl
    BstLean.Part268.WorldRow13165.product_lower (BstLean.Part268.WorldRow13165.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13165} (hw : c ∈ Hof BstLean.Part268.WorldRow13165.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13165) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13165) (by norm_num) BstLean.Part268.WorldRow13165.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13165} (hw : c ∈ Hof BstLean.Part268.WorldRow13165.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13165) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13165).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13165) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13165_eq : scalarRow13165.targetFrame = BstLean.Part268.agent13165.frame := by
  norm_num [scalarRow13165,BstLean.Part268.agent13165]

noncomputable def frameData13165 : BstLean.Part264b.FrameData 13165 :=
  BstLean.Part269.frameData_from_numerics (n := 13165) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13165.worldPackage rfl BstLean.Part268.WorldRow13165.product_lower (BstLean.Part268.WorldRow13165.producthi.2.trans (by norm_num))
    scalarRow13165 repair13165 covarianceInputs13165 (fun i hi => sourceNumerics13165 hi)
    BstLean.Part268.agent13165.frame targetFrame13165_eq


end BstLean.Part269.N13165

namespace BstLean.Part269.N13166
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13166 : scalarRow13166.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13166, BstLean.Part268.grid13166, BstLean.Part263.worldGrid]

theorem supplies13166 (j : Fin 43) : Supply 13166 (parameters j)
    (cellLower scalarRow13166.grid (sourceIndex j))
    (cellUpper scalarRow13166.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13166.grid grid_top_bounds13166 j

theorem radii13166 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13166.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13166 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13166 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13166.grid grid_top_bounds13166 j hθ

noncomputable def covarianceInputs13166 :
    BstLean.Part263.CovarianceInputs 13166 scalarRow13166.grid parameters (caps repair13166) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13166 grid_top_bounds13166 repair13166

noncomputable def covarianceEvent13166 : Set (AgFam 13166) :=
  BstLean.Part263.covarianceEvent 13166 scalarRow13166.grid parameters

theorem covarianceEvent13166_measurable : MeasurableSet covarianceEvent13166 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13166_payment :
    (retDist (paperDesignP 13166).toCentres).real
      (agentEv (paperDesignP 13166) covarianceEvent13166)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13166

theorem localCov13166 : BstLean.Part259.LocalCovarianceOn covarianceEvent13166
    (BstLean.Part263.cell scalarRow13166.grid) (caps repair13166) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13166

theorem covarianceGood13166_payment :
    (retDist (paperDesignP 13166).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13166)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13166_payment



end BstLean.Part269.N13166

namespace BstLean.Part269.N13166
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13166}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13166.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13166) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13166).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13166 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13166) (by norm_num) BstLean.Part268.WorldRow13166.worldPackage rfl
    BstLean.Part268.WorldRow13166.product_lower (BstLean.Part268.WorldRow13166.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13166} (hw : c ∈ Hof BstLean.Part268.WorldRow13166.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13166) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13166) (by norm_num) BstLean.Part268.WorldRow13166.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13166} (hw : c ∈ Hof BstLean.Part268.WorldRow13166.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13166) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13166).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13166) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13166_eq : scalarRow13166.targetFrame = BstLean.Part268.agent13166.frame := by
  norm_num [scalarRow13166,BstLean.Part268.agent13166]

noncomputable def frameData13166 : BstLean.Part264b.FrameData 13166 :=
  BstLean.Part269.frameData_from_numerics (n := 13166) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13166.worldPackage rfl BstLean.Part268.WorldRow13166.product_lower (BstLean.Part268.WorldRow13166.producthi.2.trans (by norm_num))
    scalarRow13166 repair13166 covarianceInputs13166 (fun i hi => sourceNumerics13166 hi)
    BstLean.Part268.agent13166.frame targetFrame13166_eq


end BstLean.Part269.N13166

namespace BstLean.Part269.N13167
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13167 : scalarRow13167.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13167, BstLean.Part268.grid13167, BstLean.Part263.worldGrid]

theorem supplies13167 (j : Fin 43) : Supply 13167 (parameters j)
    (cellLower scalarRow13167.grid (sourceIndex j))
    (cellUpper scalarRow13167.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13167.grid grid_top_bounds13167 j

theorem radii13167 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13167.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13167 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13167 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13167.grid grid_top_bounds13167 j hθ

noncomputable def covarianceInputs13167 :
    BstLean.Part263.CovarianceInputs 13167 scalarRow13167.grid parameters (caps repair13167) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13167 grid_top_bounds13167 repair13167

noncomputable def covarianceEvent13167 : Set (AgFam 13167) :=
  BstLean.Part263.covarianceEvent 13167 scalarRow13167.grid parameters

theorem covarianceEvent13167_measurable : MeasurableSet covarianceEvent13167 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13167_payment :
    (retDist (paperDesignP 13167).toCentres).real
      (agentEv (paperDesignP 13167) covarianceEvent13167)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13167

theorem localCov13167 : BstLean.Part259.LocalCovarianceOn covarianceEvent13167
    (BstLean.Part263.cell scalarRow13167.grid) (caps repair13167) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13167

theorem covarianceGood13167_payment :
    (retDist (paperDesignP 13167).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13167)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13167_payment



end BstLean.Part269.N13167

namespace BstLean.Part269.N13167
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13167}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13167.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13167) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13167).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13167 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13167) (by norm_num) BstLean.Part268.WorldRow13167.worldPackage rfl
    BstLean.Part268.WorldRow13167.product_lower (BstLean.Part268.WorldRow13167.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13167} (hw : c ∈ Hof BstLean.Part268.WorldRow13167.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13167) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13167) (by norm_num) BstLean.Part268.WorldRow13167.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13167} (hw : c ∈ Hof BstLean.Part268.WorldRow13167.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13167) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13167).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13167) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13167_eq : scalarRow13167.targetFrame = BstLean.Part268.agent13167.frame := by
  norm_num [scalarRow13167,BstLean.Part268.agent13167]

noncomputable def frameData13167 : BstLean.Part264b.FrameData 13167 :=
  BstLean.Part269.frameData_from_numerics (n := 13167) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13167.worldPackage rfl BstLean.Part268.WorldRow13167.product_lower (BstLean.Part268.WorldRow13167.producthi.2.trans (by norm_num))
    scalarRow13167 repair13167 covarianceInputs13167 (fun i hi => sourceNumerics13167 hi)
    BstLean.Part268.agent13167.frame targetFrame13167_eq


end BstLean.Part269.N13167

namespace BstLean.Part269.N13168
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13168 : scalarRow13168.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13168, BstLean.Part268.grid13168, BstLean.Part263.worldGrid]

theorem supplies13168 (j : Fin 43) : Supply 13168 (parameters j)
    (cellLower scalarRow13168.grid (sourceIndex j))
    (cellUpper scalarRow13168.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13168.grid grid_top_bounds13168 j

theorem radii13168 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13168.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13168 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13168 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13168.grid grid_top_bounds13168 j hθ

noncomputable def covarianceInputs13168 :
    BstLean.Part263.CovarianceInputs 13168 scalarRow13168.grid parameters (caps repair13168) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13168 grid_top_bounds13168 repair13168

noncomputable def covarianceEvent13168 : Set (AgFam 13168) :=
  BstLean.Part263.covarianceEvent 13168 scalarRow13168.grid parameters

theorem covarianceEvent13168_measurable : MeasurableSet covarianceEvent13168 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13168_payment :
    (retDist (paperDesignP 13168).toCentres).real
      (agentEv (paperDesignP 13168) covarianceEvent13168)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13168

theorem localCov13168 : BstLean.Part259.LocalCovarianceOn covarianceEvent13168
    (BstLean.Part263.cell scalarRow13168.grid) (caps repair13168) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13168

theorem covarianceGood13168_payment :
    (retDist (paperDesignP 13168).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13168)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13168_payment



end BstLean.Part269.N13168

namespace BstLean.Part269.N13168
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13168}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13168.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13168) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13168).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13168 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13168) (by norm_num) BstLean.Part268.WorldRow13168.worldPackage rfl
    BstLean.Part268.WorldRow13168.product_lower (BstLean.Part268.WorldRow13168.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13168} (hw : c ∈ Hof BstLean.Part268.WorldRow13168.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13168) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13168) (by norm_num) BstLean.Part268.WorldRow13168.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13168} (hw : c ∈ Hof BstLean.Part268.WorldRow13168.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13168) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13168).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13168) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13168_eq : scalarRow13168.targetFrame = BstLean.Part268.agent13168.frame := by
  norm_num [scalarRow13168,BstLean.Part268.agent13168]

noncomputable def frameData13168 : BstLean.Part264b.FrameData 13168 :=
  BstLean.Part269.frameData_from_numerics (n := 13168) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13168.worldPackage rfl BstLean.Part268.WorldRow13168.product_lower (BstLean.Part268.WorldRow13168.producthi.2.trans (by norm_num))
    scalarRow13168 repair13168 covarianceInputs13168 (fun i hi => sourceNumerics13168 hi)
    BstLean.Part268.agent13168.frame targetFrame13168_eq


end BstLean.Part269.N13168

namespace BstLean.Part269.N13169
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13169 : scalarRow13169.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13169, BstLean.Part268.grid13169, BstLean.Part263.worldGrid]

theorem supplies13169 (j : Fin 43) : Supply 13169 (parameters j)
    (cellLower scalarRow13169.grid (sourceIndex j))
    (cellUpper scalarRow13169.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13169.grid grid_top_bounds13169 j

theorem radii13169 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13169.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13169 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13169 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13169.grid grid_top_bounds13169 j hθ

noncomputable def covarianceInputs13169 :
    BstLean.Part263.CovarianceInputs 13169 scalarRow13169.grid parameters (caps repair13169) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13169 grid_top_bounds13169 repair13169

noncomputable def covarianceEvent13169 : Set (AgFam 13169) :=
  BstLean.Part263.covarianceEvent 13169 scalarRow13169.grid parameters

theorem covarianceEvent13169_measurable : MeasurableSet covarianceEvent13169 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13169_payment :
    (retDist (paperDesignP 13169).toCentres).real
      (agentEv (paperDesignP 13169) covarianceEvent13169)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13169

theorem localCov13169 : BstLean.Part259.LocalCovarianceOn covarianceEvent13169
    (BstLean.Part263.cell scalarRow13169.grid) (caps repair13169) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13169

theorem covarianceGood13169_payment :
    (retDist (paperDesignP 13169).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13169)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13169_payment



end BstLean.Part269.N13169

namespace BstLean.Part269.N13169
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13169}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13169.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13169) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13169).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13169 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13169) (by norm_num) BstLean.Part268.WorldRow13169.worldPackage rfl
    BstLean.Part268.WorldRow13169.product_lower (BstLean.Part268.WorldRow13169.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13169} (hw : c ∈ Hof BstLean.Part268.WorldRow13169.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13169) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13169) (by norm_num) BstLean.Part268.WorldRow13169.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13169} (hw : c ∈ Hof BstLean.Part268.WorldRow13169.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13169) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13169).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13169) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13169_eq : scalarRow13169.targetFrame = BstLean.Part268.agent13169.frame := by
  norm_num [scalarRow13169,BstLean.Part268.agent13169]

noncomputable def frameData13169 : BstLean.Part264b.FrameData 13169 :=
  BstLean.Part269.frameData_from_numerics (n := 13169) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13169.worldPackage rfl BstLean.Part268.WorldRow13169.product_lower (BstLean.Part268.WorldRow13169.producthi.2.trans (by norm_num))
    scalarRow13169 repair13169 covarianceInputs13169 (fun i hi => sourceNumerics13169 hi)
    BstLean.Part268.agent13169.frame targetFrame13169_eq


end BstLean.Part269.N13169
