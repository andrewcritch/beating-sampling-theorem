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

namespace BstLean.Part269.N13180
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13180 : scalarRow13180.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13180, BstLean.Part268.grid13180, BstLean.Part263.worldGrid]

theorem supplies13180 (j : Fin 43) : Supply 13180 (parameters j)
    (cellLower scalarRow13180.grid (sourceIndex j))
    (cellUpper scalarRow13180.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13180.grid grid_top_bounds13180 j

theorem radii13180 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13180.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13180 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13180 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13180.grid grid_top_bounds13180 j hθ

noncomputable def covarianceInputs13180 :
    BstLean.Part263.CovarianceInputs 13180 scalarRow13180.grid parameters (caps repair13180) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13180 grid_top_bounds13180 repair13180

noncomputable def covarianceEvent13180 : Set (AgFam 13180) :=
  BstLean.Part263.covarianceEvent 13180 scalarRow13180.grid parameters

theorem covarianceEvent13180_measurable : MeasurableSet covarianceEvent13180 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13180_payment :
    (retDist (paperDesignP 13180).toCentres).real
      (agentEv (paperDesignP 13180) covarianceEvent13180)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13180

theorem localCov13180 : BstLean.Part259.LocalCovarianceOn covarianceEvent13180
    (BstLean.Part263.cell scalarRow13180.grid) (caps repair13180) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13180

theorem covarianceGood13180_payment :
    (retDist (paperDesignP 13180).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13180)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13180_payment



end BstLean.Part269.N13180

namespace BstLean.Part269.N13180
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13180}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13180.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13180) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13180).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13180 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13180) (by norm_num) BstLean.Part268.WorldRow13180.worldPackage rfl
    BstLean.Part268.WorldRow13180.product_lower (BstLean.Part268.WorldRow13180.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13180} (hw : c ∈ Hof BstLean.Part268.WorldRow13180.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13180) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13180) (by norm_num) BstLean.Part268.WorldRow13180.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13180} (hw : c ∈ Hof BstLean.Part268.WorldRow13180.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13180) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13180).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13180) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13180_eq : scalarRow13180.targetFrame = BstLean.Part268.agent13180.frame := by
  norm_num [scalarRow13180,BstLean.Part268.agent13180]

noncomputable def frameData13180 : BstLean.Part264b.FrameData 13180 :=
  BstLean.Part269.frameData_from_numerics (n := 13180) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13180.worldPackage rfl BstLean.Part268.WorldRow13180.product_lower (BstLean.Part268.WorldRow13180.producthi.2.trans (by norm_num))
    scalarRow13180 repair13180 covarianceInputs13180 (fun i hi => sourceNumerics13180 hi)
    BstLean.Part268.agent13180.frame targetFrame13180_eq


end BstLean.Part269.N13180

namespace BstLean.Part269.N13181
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13181 : scalarRow13181.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13181, BstLean.Part268.grid13181, BstLean.Part263.worldGrid]

theorem supplies13181 (j : Fin 43) : Supply 13181 (parameters j)
    (cellLower scalarRow13181.grid (sourceIndex j))
    (cellUpper scalarRow13181.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13181.grid grid_top_bounds13181 j

theorem radii13181 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13181.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13181 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13181 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13181.grid grid_top_bounds13181 j hθ

noncomputable def covarianceInputs13181 :
    BstLean.Part263.CovarianceInputs 13181 scalarRow13181.grid parameters (caps repair13181) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13181 grid_top_bounds13181 repair13181

noncomputable def covarianceEvent13181 : Set (AgFam 13181) :=
  BstLean.Part263.covarianceEvent 13181 scalarRow13181.grid parameters

theorem covarianceEvent13181_measurable : MeasurableSet covarianceEvent13181 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13181_payment :
    (retDist (paperDesignP 13181).toCentres).real
      (agentEv (paperDesignP 13181) covarianceEvent13181)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13181

theorem localCov13181 : BstLean.Part259.LocalCovarianceOn covarianceEvent13181
    (BstLean.Part263.cell scalarRow13181.grid) (caps repair13181) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13181

theorem covarianceGood13181_payment :
    (retDist (paperDesignP 13181).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13181)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13181_payment



end BstLean.Part269.N13181

namespace BstLean.Part269.N13181
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13181}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13181.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13181) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13181).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13181 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13181) (by norm_num) BstLean.Part268.WorldRow13181.worldPackage rfl
    BstLean.Part268.WorldRow13181.product_lower (BstLean.Part268.WorldRow13181.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13181} (hw : c ∈ Hof BstLean.Part268.WorldRow13181.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13181) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13181) (by norm_num) BstLean.Part268.WorldRow13181.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13181} (hw : c ∈ Hof BstLean.Part268.WorldRow13181.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13181) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13181).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13181) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13181_eq : scalarRow13181.targetFrame = BstLean.Part268.agent13181.frame := by
  norm_num [scalarRow13181,BstLean.Part268.agent13181]

noncomputable def frameData13181 : BstLean.Part264b.FrameData 13181 :=
  BstLean.Part269.frameData_from_numerics (n := 13181) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13181.worldPackage rfl BstLean.Part268.WorldRow13181.product_lower (BstLean.Part268.WorldRow13181.producthi.2.trans (by norm_num))
    scalarRow13181 repair13181 covarianceInputs13181 (fun i hi => sourceNumerics13181 hi)
    BstLean.Part268.agent13181.frame targetFrame13181_eq


end BstLean.Part269.N13181

namespace BstLean.Part269.N13182
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13182 : scalarRow13182.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13182, BstLean.Part268.grid13182, BstLean.Part263.worldGrid]

theorem supplies13182 (j : Fin 43) : Supply 13182 (parameters j)
    (cellLower scalarRow13182.grid (sourceIndex j))
    (cellUpper scalarRow13182.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13182.grid grid_top_bounds13182 j

theorem radii13182 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13182.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13182 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13182 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13182.grid grid_top_bounds13182 j hθ

noncomputable def covarianceInputs13182 :
    BstLean.Part263.CovarianceInputs 13182 scalarRow13182.grid parameters (caps repair13182) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13182 grid_top_bounds13182 repair13182

noncomputable def covarianceEvent13182 : Set (AgFam 13182) :=
  BstLean.Part263.covarianceEvent 13182 scalarRow13182.grid parameters

theorem covarianceEvent13182_measurable : MeasurableSet covarianceEvent13182 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13182_payment :
    (retDist (paperDesignP 13182).toCentres).real
      (agentEv (paperDesignP 13182) covarianceEvent13182)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13182

theorem localCov13182 : BstLean.Part259.LocalCovarianceOn covarianceEvent13182
    (BstLean.Part263.cell scalarRow13182.grid) (caps repair13182) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13182

theorem covarianceGood13182_payment :
    (retDist (paperDesignP 13182).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13182)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13182_payment



end BstLean.Part269.N13182

namespace BstLean.Part269.N13182
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13182}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13182.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13182) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13182).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13182 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13182) (by norm_num) BstLean.Part268.WorldRow13182.worldPackage rfl
    BstLean.Part268.WorldRow13182.product_lower (BstLean.Part268.WorldRow13182.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13182} (hw : c ∈ Hof BstLean.Part268.WorldRow13182.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13182) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13182) (by norm_num) BstLean.Part268.WorldRow13182.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13182} (hw : c ∈ Hof BstLean.Part268.WorldRow13182.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13182) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13182).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13182) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13182_eq : scalarRow13182.targetFrame = BstLean.Part268.agent13182.frame := by
  norm_num [scalarRow13182,BstLean.Part268.agent13182]

noncomputable def frameData13182 : BstLean.Part264b.FrameData 13182 :=
  BstLean.Part269.frameData_from_numerics (n := 13182) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13182.worldPackage rfl BstLean.Part268.WorldRow13182.product_lower (BstLean.Part268.WorldRow13182.producthi.2.trans (by norm_num))
    scalarRow13182 repair13182 covarianceInputs13182 (fun i hi => sourceNumerics13182 hi)
    BstLean.Part268.agent13182.frame targetFrame13182_eq


end BstLean.Part269.N13182

namespace BstLean.Part269.N13183
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13183 : scalarRow13183.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13183, BstLean.Part268.grid13183, BstLean.Part263.worldGrid]

theorem supplies13183 (j : Fin 43) : Supply 13183 (parameters j)
    (cellLower scalarRow13183.grid (sourceIndex j))
    (cellUpper scalarRow13183.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13183.grid grid_top_bounds13183 j

theorem radii13183 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13183.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13183 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13183 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13183.grid grid_top_bounds13183 j hθ

noncomputable def covarianceInputs13183 :
    BstLean.Part263.CovarianceInputs 13183 scalarRow13183.grid parameters (caps repair13183) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13183 grid_top_bounds13183 repair13183

noncomputable def covarianceEvent13183 : Set (AgFam 13183) :=
  BstLean.Part263.covarianceEvent 13183 scalarRow13183.grid parameters

theorem covarianceEvent13183_measurable : MeasurableSet covarianceEvent13183 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13183_payment :
    (retDist (paperDesignP 13183).toCentres).real
      (agentEv (paperDesignP 13183) covarianceEvent13183)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13183

theorem localCov13183 : BstLean.Part259.LocalCovarianceOn covarianceEvent13183
    (BstLean.Part263.cell scalarRow13183.grid) (caps repair13183) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13183

theorem covarianceGood13183_payment :
    (retDist (paperDesignP 13183).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13183)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13183_payment



end BstLean.Part269.N13183

namespace BstLean.Part269.N13183
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13183}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13183.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13183) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13183).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13183 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13183) (by norm_num) BstLean.Part268.WorldRow13183.worldPackage rfl
    BstLean.Part268.WorldRow13183.product_lower (BstLean.Part268.WorldRow13183.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13183} (hw : c ∈ Hof BstLean.Part268.WorldRow13183.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13183) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13183) (by norm_num) BstLean.Part268.WorldRow13183.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13183} (hw : c ∈ Hof BstLean.Part268.WorldRow13183.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13183) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13183).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13183) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13183_eq : scalarRow13183.targetFrame = BstLean.Part268.agent13183.frame := by
  norm_num [scalarRow13183,BstLean.Part268.agent13183]

noncomputable def frameData13183 : BstLean.Part264b.FrameData 13183 :=
  BstLean.Part269.frameData_from_numerics (n := 13183) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13183.worldPackage rfl BstLean.Part268.WorldRow13183.product_lower (BstLean.Part268.WorldRow13183.producthi.2.trans (by norm_num))
    scalarRow13183 repair13183 covarianceInputs13183 (fun i hi => sourceNumerics13183 hi)
    BstLean.Part268.agent13183.frame targetFrame13183_eq


end BstLean.Part269.N13183

namespace BstLean.Part269.N13184
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13184 : scalarRow13184.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13184, BstLean.Part268.grid13184, BstLean.Part263.worldGrid]

theorem supplies13184 (j : Fin 43) : Supply 13184 (parameters j)
    (cellLower scalarRow13184.grid (sourceIndex j))
    (cellUpper scalarRow13184.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13184.grid grid_top_bounds13184 j

theorem radii13184 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13184.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13184 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13184 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13184.grid grid_top_bounds13184 j hθ

noncomputable def covarianceInputs13184 :
    BstLean.Part263.CovarianceInputs 13184 scalarRow13184.grid parameters (caps repair13184) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13184 grid_top_bounds13184 repair13184

noncomputable def covarianceEvent13184 : Set (AgFam 13184) :=
  BstLean.Part263.covarianceEvent 13184 scalarRow13184.grid parameters

theorem covarianceEvent13184_measurable : MeasurableSet covarianceEvent13184 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13184_payment :
    (retDist (paperDesignP 13184).toCentres).real
      (agentEv (paperDesignP 13184) covarianceEvent13184)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13184

theorem localCov13184 : BstLean.Part259.LocalCovarianceOn covarianceEvent13184
    (BstLean.Part263.cell scalarRow13184.grid) (caps repair13184) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13184

theorem covarianceGood13184_payment :
    (retDist (paperDesignP 13184).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13184)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13184_payment



end BstLean.Part269.N13184

namespace BstLean.Part269.N13184
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13184}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13184.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13184) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13184).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13184 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13184) (by norm_num) BstLean.Part268.WorldRow13184.worldPackage rfl
    BstLean.Part268.WorldRow13184.product_lower (BstLean.Part268.WorldRow13184.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13184} (hw : c ∈ Hof BstLean.Part268.WorldRow13184.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13184) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13184) (by norm_num) BstLean.Part268.WorldRow13184.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13184} (hw : c ∈ Hof BstLean.Part268.WorldRow13184.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13184) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13184).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13184) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13184_eq : scalarRow13184.targetFrame = BstLean.Part268.agent13184.frame := by
  norm_num [scalarRow13184,BstLean.Part268.agent13184]

noncomputable def frameData13184 : BstLean.Part264b.FrameData 13184 :=
  BstLean.Part269.frameData_from_numerics (n := 13184) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13184.worldPackage rfl BstLean.Part268.WorldRow13184.product_lower (BstLean.Part268.WorldRow13184.producthi.2.trans (by norm_num))
    scalarRow13184 repair13184 covarianceInputs13184 (fun i hi => sourceNumerics13184 hi)
    BstLean.Part268.agent13184.frame targetFrame13184_eq


end BstLean.Part269.N13184
