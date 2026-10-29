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

namespace BstLean.Part269.N13195
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13195 : scalarRow13195.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13195, BstLean.Part268.grid13195, BstLean.Part263.worldGrid]

theorem supplies13195 (j : Fin 43) : Supply 13195 (parameters j)
    (cellLower scalarRow13195.grid (sourceIndex j))
    (cellUpper scalarRow13195.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13195.grid grid_top_bounds13195 j

theorem radii13195 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13195.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13195 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13195 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13195.grid grid_top_bounds13195 j hθ

noncomputable def covarianceInputs13195 :
    BstLean.Part263.CovarianceInputs 13195 scalarRow13195.grid parameters (caps repair13195) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13195 grid_top_bounds13195 repair13195

noncomputable def covarianceEvent13195 : Set (AgFam 13195) :=
  BstLean.Part263.covarianceEvent 13195 scalarRow13195.grid parameters

theorem covarianceEvent13195_measurable : MeasurableSet covarianceEvent13195 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13195_payment :
    (retDist (paperDesignP 13195).toCentres).real
      (agentEv (paperDesignP 13195) covarianceEvent13195)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13195

theorem localCov13195 : BstLean.Part259.LocalCovarianceOn covarianceEvent13195
    (BstLean.Part263.cell scalarRow13195.grid) (caps repair13195) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13195

theorem covarianceGood13195_payment :
    (retDist (paperDesignP 13195).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13195)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13195_payment



end BstLean.Part269.N13195

namespace BstLean.Part269.N13195
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13195}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13195.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13195) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13195).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13195 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13195) (by norm_num) BstLean.Part268.WorldRow13195.worldPackage rfl
    BstLean.Part268.WorldRow13195.product_lower (BstLean.Part268.WorldRow13195.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13195} (hw : c ∈ Hof BstLean.Part268.WorldRow13195.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13195) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13195) (by norm_num) BstLean.Part268.WorldRow13195.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13195} (hw : c ∈ Hof BstLean.Part268.WorldRow13195.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13195) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13195).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13195) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13195_eq : scalarRow13195.targetFrame = BstLean.Part268.agent13195.frame := by
  norm_num [scalarRow13195,BstLean.Part268.agent13195]

noncomputable def frameData13195 : BstLean.Part264b.FrameData 13195 :=
  BstLean.Part269.frameData_from_numerics (n := 13195) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13195.worldPackage rfl BstLean.Part268.WorldRow13195.product_lower (BstLean.Part268.WorldRow13195.producthi.2.trans (by norm_num))
    scalarRow13195 repair13195 covarianceInputs13195 (fun i hi => sourceNumerics13195 hi)
    BstLean.Part268.agent13195.frame targetFrame13195_eq


end BstLean.Part269.N13195

namespace BstLean.Part269.N13196
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13196 : scalarRow13196.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13196, BstLean.Part268.grid13196, BstLean.Part263.worldGrid]

theorem supplies13196 (j : Fin 43) : Supply 13196 (parameters j)
    (cellLower scalarRow13196.grid (sourceIndex j))
    (cellUpper scalarRow13196.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13196.grid grid_top_bounds13196 j

theorem radii13196 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13196.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13196 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13196 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13196.grid grid_top_bounds13196 j hθ

noncomputable def covarianceInputs13196 :
    BstLean.Part263.CovarianceInputs 13196 scalarRow13196.grid parameters (caps repair13196) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13196 grid_top_bounds13196 repair13196

noncomputable def covarianceEvent13196 : Set (AgFam 13196) :=
  BstLean.Part263.covarianceEvent 13196 scalarRow13196.grid parameters

theorem covarianceEvent13196_measurable : MeasurableSet covarianceEvent13196 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13196_payment :
    (retDist (paperDesignP 13196).toCentres).real
      (agentEv (paperDesignP 13196) covarianceEvent13196)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13196

theorem localCov13196 : BstLean.Part259.LocalCovarianceOn covarianceEvent13196
    (BstLean.Part263.cell scalarRow13196.grid) (caps repair13196) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13196

theorem covarianceGood13196_payment :
    (retDist (paperDesignP 13196).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13196)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13196_payment



end BstLean.Part269.N13196

namespace BstLean.Part269.N13196
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13196}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13196.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13196) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13196).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13196 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13196) (by norm_num) BstLean.Part268.WorldRow13196.worldPackage rfl
    BstLean.Part268.WorldRow13196.product_lower (BstLean.Part268.WorldRow13196.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13196} (hw : c ∈ Hof BstLean.Part268.WorldRow13196.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13196) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13196) (by norm_num) BstLean.Part268.WorldRow13196.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13196} (hw : c ∈ Hof BstLean.Part268.WorldRow13196.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13196) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13196).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13196) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13196_eq : scalarRow13196.targetFrame = BstLean.Part268.agent13196.frame := by
  norm_num [scalarRow13196,BstLean.Part268.agent13196]

noncomputable def frameData13196 : BstLean.Part264b.FrameData 13196 :=
  BstLean.Part269.frameData_from_numerics (n := 13196) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13196.worldPackage rfl BstLean.Part268.WorldRow13196.product_lower (BstLean.Part268.WorldRow13196.producthi.2.trans (by norm_num))
    scalarRow13196 repair13196 covarianceInputs13196 (fun i hi => sourceNumerics13196 hi)
    BstLean.Part268.agent13196.frame targetFrame13196_eq


end BstLean.Part269.N13196

namespace BstLean.Part269.N13197
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13197 : scalarRow13197.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13197, BstLean.Part268.grid13197, BstLean.Part263.worldGrid]

theorem supplies13197 (j : Fin 43) : Supply 13197 (parameters j)
    (cellLower scalarRow13197.grid (sourceIndex j))
    (cellUpper scalarRow13197.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13197.grid grid_top_bounds13197 j

theorem radii13197 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13197.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13197 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13197 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13197.grid grid_top_bounds13197 j hθ

noncomputable def covarianceInputs13197 :
    BstLean.Part263.CovarianceInputs 13197 scalarRow13197.grid parameters (caps repair13197) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13197 grid_top_bounds13197 repair13197

noncomputable def covarianceEvent13197 : Set (AgFam 13197) :=
  BstLean.Part263.covarianceEvent 13197 scalarRow13197.grid parameters

theorem covarianceEvent13197_measurable : MeasurableSet covarianceEvent13197 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13197_payment :
    (retDist (paperDesignP 13197).toCentres).real
      (agentEv (paperDesignP 13197) covarianceEvent13197)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13197

theorem localCov13197 : BstLean.Part259.LocalCovarianceOn covarianceEvent13197
    (BstLean.Part263.cell scalarRow13197.grid) (caps repair13197) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13197

theorem covarianceGood13197_payment :
    (retDist (paperDesignP 13197).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13197)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13197_payment



end BstLean.Part269.N13197

namespace BstLean.Part269.N13197
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13197}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13197.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13197) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13197).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13197 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13197) (by norm_num) BstLean.Part268.WorldRow13197.worldPackage rfl
    BstLean.Part268.WorldRow13197.product_lower (BstLean.Part268.WorldRow13197.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13197} (hw : c ∈ Hof BstLean.Part268.WorldRow13197.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13197) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13197) (by norm_num) BstLean.Part268.WorldRow13197.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13197} (hw : c ∈ Hof BstLean.Part268.WorldRow13197.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13197) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13197).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13197) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13197_eq : scalarRow13197.targetFrame = BstLean.Part268.agent13197.frame := by
  norm_num [scalarRow13197,BstLean.Part268.agent13197]

noncomputable def frameData13197 : BstLean.Part264b.FrameData 13197 :=
  BstLean.Part269.frameData_from_numerics (n := 13197) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13197.worldPackage rfl BstLean.Part268.WorldRow13197.product_lower (BstLean.Part268.WorldRow13197.producthi.2.trans (by norm_num))
    scalarRow13197 repair13197 covarianceInputs13197 (fun i hi => sourceNumerics13197 hi)
    BstLean.Part268.agent13197.frame targetFrame13197_eq


end BstLean.Part269.N13197

namespace BstLean.Part269.N13198
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13198 : scalarRow13198.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13198, BstLean.Part268.grid13198, BstLean.Part263.worldGrid]

theorem supplies13198 (j : Fin 43) : Supply 13198 (parameters j)
    (cellLower scalarRow13198.grid (sourceIndex j))
    (cellUpper scalarRow13198.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13198.grid grid_top_bounds13198 j

theorem radii13198 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13198.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13198 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13198 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13198.grid grid_top_bounds13198 j hθ

noncomputable def covarianceInputs13198 :
    BstLean.Part263.CovarianceInputs 13198 scalarRow13198.grid parameters (caps repair13198) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13198 grid_top_bounds13198 repair13198

noncomputable def covarianceEvent13198 : Set (AgFam 13198) :=
  BstLean.Part263.covarianceEvent 13198 scalarRow13198.grid parameters

theorem covarianceEvent13198_measurable : MeasurableSet covarianceEvent13198 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13198_payment :
    (retDist (paperDesignP 13198).toCentres).real
      (agentEv (paperDesignP 13198) covarianceEvent13198)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13198

theorem localCov13198 : BstLean.Part259.LocalCovarianceOn covarianceEvent13198
    (BstLean.Part263.cell scalarRow13198.grid) (caps repair13198) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13198

theorem covarianceGood13198_payment :
    (retDist (paperDesignP 13198).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13198)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13198_payment



end BstLean.Part269.N13198

namespace BstLean.Part269.N13198
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13198}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13198.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13198) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13198).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13198 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13198) (by norm_num) BstLean.Part268.WorldRow13198.worldPackage rfl
    BstLean.Part268.WorldRow13198.product_lower (BstLean.Part268.WorldRow13198.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13198} (hw : c ∈ Hof BstLean.Part268.WorldRow13198.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13198) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13198) (by norm_num) BstLean.Part268.WorldRow13198.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13198} (hw : c ∈ Hof BstLean.Part268.WorldRow13198.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13198) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13198).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13198) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13198_eq : scalarRow13198.targetFrame = BstLean.Part268.agent13198.frame := by
  norm_num [scalarRow13198,BstLean.Part268.agent13198]

noncomputable def frameData13198 : BstLean.Part264b.FrameData 13198 :=
  BstLean.Part269.frameData_from_numerics (n := 13198) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13198.worldPackage rfl BstLean.Part268.WorldRow13198.product_lower (BstLean.Part268.WorldRow13198.producthi.2.trans (by norm_num))
    scalarRow13198 repair13198 covarianceInputs13198 (fun i hi => sourceNumerics13198 hi)
    BstLean.Part268.agent13198.frame targetFrame13198_eq


end BstLean.Part269.N13198

namespace BstLean.Part269.N13199
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13199 : scalarRow13199.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13199, BstLean.Part268.grid13199, BstLean.Part263.worldGrid]

theorem supplies13199 (j : Fin 43) : Supply 13199 (parameters j)
    (cellLower scalarRow13199.grid (sourceIndex j))
    (cellUpper scalarRow13199.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow13199.grid grid_top_bounds13199 j

theorem radii13199 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow13199.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 13199 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 13199 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow13199.grid grid_top_bounds13199 j hθ

noncomputable def covarianceInputs13199 :
    BstLean.Part263.CovarianceInputs 13199 scalarRow13199.grid parameters (caps repair13199) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow13199 grid_top_bounds13199 repair13199

noncomputable def covarianceEvent13199 : Set (AgFam 13199) :=
  BstLean.Part263.covarianceEvent 13199 scalarRow13199.grid parameters

theorem covarianceEvent13199_measurable : MeasurableSet covarianceEvent13199 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13199_payment :
    (retDist (paperDesignP 13199).toCentres).real
      (agentEv (paperDesignP 13199) covarianceEvent13199)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13199

theorem localCov13199 : BstLean.Part259.LocalCovarianceOn covarianceEvent13199
    (BstLean.Part263.cell scalarRow13199.grid) (caps repair13199) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13199

theorem covarianceGood13199_payment :
    (retDist (paperDesignP 13199).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13199)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13199_payment



end BstLean.Part269.N13199

namespace BstLean.Part269.N13199
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 13199}
    (hw : c ∈ Hof BstLean.Part268.WorldRow13199.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 13199) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13199).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 13199 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 13199) (by norm_num) BstLean.Part268.WorldRow13199.worldPackage rfl
    BstLean.Part268.WorldRow13199.product_lower (BstLean.Part268.WorldRow13199.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 13199} (hw : c ∈ Hof BstLean.Part268.WorldRow13199.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13199) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 13199) (by norm_num) BstLean.Part268.WorldRow13199.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 13199} (hw : c ∈ Hof BstLean.Part268.WorldRow13199.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 13199) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 13199).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 13199) (by norm_num) (actual_world_window hw hc)

theorem targetFrame13199_eq : scalarRow13199.targetFrame = BstLean.Part268.agent13199.frame := by
  norm_num [scalarRow13199,BstLean.Part268.agent13199]

noncomputable def frameData13199 : BstLean.Part264b.FrameData 13199 :=
  BstLean.Part269.frameData_from_numerics (n := 13199) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow13199.worldPackage rfl BstLean.Part268.WorldRow13199.product_lower (BstLean.Part268.WorldRow13199.producthi.2.trans (by norm_num))
    scalarRow13199 repair13199 covarianceInputs13199 (fun i hi => sourceNumerics13199 hi)
    BstLean.Part268.agent13199.frame targetFrame13199_eq


end BstLean.Part269.N13199
