import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World22Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs22
import BstLean.Part269Rows22
import BstLean.Part269Sources22
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12910
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12910 : scalarRow12910.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12910, BstLean.Part268.grid12910, BstLean.Part263.worldGrid]

theorem supplies12910 (j : Fin 43) : Supply 12910 (parameters j)
    (cellLower scalarRow12910.grid (sourceIndex j))
    (cellUpper scalarRow12910.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12910.grid grid_top_bounds12910 j

theorem radii12910 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12910.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12910 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12910 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12910.grid grid_top_bounds12910 j hθ

noncomputable def covarianceInputs12910 :
    BstLean.Part263.CovarianceInputs 12910 scalarRow12910.grid parameters (caps repair12910) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12910 grid_top_bounds12910 repair12910

noncomputable def covarianceEvent12910 : Set (AgFam 12910) :=
  BstLean.Part263.covarianceEvent 12910 scalarRow12910.grid parameters

theorem covarianceEvent12910_measurable : MeasurableSet covarianceEvent12910 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12910_payment :
    (retDist (paperDesignP 12910).toCentres).real
      (agentEv (paperDesignP 12910) covarianceEvent12910)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12910

theorem localCov12910 : BstLean.Part259.LocalCovarianceOn covarianceEvent12910
    (BstLean.Part263.cell scalarRow12910.grid) (caps repair12910) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12910

theorem covarianceGood12910_payment :
    (retDist (paperDesignP 12910).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12910)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12910_payment



end BstLean.Part269.N12910

namespace BstLean.Part269.N12910
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12910}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12910.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12910) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12910).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12910 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12910) (by norm_num) BstLean.Part268.WorldRow12910.worldPackage rfl
    BstLean.Part268.WorldRow12910.product_lower (BstLean.Part268.WorldRow12910.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12910} (hw : c ∈ Hof BstLean.Part268.WorldRow12910.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12910) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12910) (by norm_num) BstLean.Part268.WorldRow12910.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12910} (hw : c ∈ Hof BstLean.Part268.WorldRow12910.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12910) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12910).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12910) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12910_eq : scalarRow12910.targetFrame = BstLean.Part268.agent12910.frame := by
  norm_num [scalarRow12910,BstLean.Part268.agent12910]

noncomputable def frameData12910 : BstLean.Part264b.FrameData 12910 :=
  BstLean.Part269.frameData_from_numerics (n := 12910) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12910.worldPackage rfl BstLean.Part268.WorldRow12910.product_lower (BstLean.Part268.WorldRow12910.producthi.2.trans (by norm_num))
    scalarRow12910 repair12910 covarianceInputs12910 (fun i hi => sourceNumerics12910 hi)
    BstLean.Part268.agent12910.frame targetFrame12910_eq


end BstLean.Part269.N12910

namespace BstLean.Part269.N12911
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12911 : scalarRow12911.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12911, BstLean.Part268.grid12911, BstLean.Part263.worldGrid]

theorem supplies12911 (j : Fin 43) : Supply 12911 (parameters j)
    (cellLower scalarRow12911.grid (sourceIndex j))
    (cellUpper scalarRow12911.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12911.grid grid_top_bounds12911 j

theorem radii12911 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12911.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12911 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12911 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12911.grid grid_top_bounds12911 j hθ

noncomputable def covarianceInputs12911 :
    BstLean.Part263.CovarianceInputs 12911 scalarRow12911.grid parameters (caps repair12911) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12911 grid_top_bounds12911 repair12911

noncomputable def covarianceEvent12911 : Set (AgFam 12911) :=
  BstLean.Part263.covarianceEvent 12911 scalarRow12911.grid parameters

theorem covarianceEvent12911_measurable : MeasurableSet covarianceEvent12911 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12911_payment :
    (retDist (paperDesignP 12911).toCentres).real
      (agentEv (paperDesignP 12911) covarianceEvent12911)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12911

theorem localCov12911 : BstLean.Part259.LocalCovarianceOn covarianceEvent12911
    (BstLean.Part263.cell scalarRow12911.grid) (caps repair12911) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12911

theorem covarianceGood12911_payment :
    (retDist (paperDesignP 12911).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12911)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12911_payment



end BstLean.Part269.N12911

namespace BstLean.Part269.N12911
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12911}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12911.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12911) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12911).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12911 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12911) (by norm_num) BstLean.Part268.WorldRow12911.worldPackage rfl
    BstLean.Part268.WorldRow12911.product_lower (BstLean.Part268.WorldRow12911.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12911} (hw : c ∈ Hof BstLean.Part268.WorldRow12911.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12911) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12911) (by norm_num) BstLean.Part268.WorldRow12911.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12911} (hw : c ∈ Hof BstLean.Part268.WorldRow12911.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12911) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12911).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12911) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12911_eq : scalarRow12911.targetFrame = BstLean.Part268.agent12911.frame := by
  norm_num [scalarRow12911,BstLean.Part268.agent12911]

noncomputable def frameData12911 : BstLean.Part264b.FrameData 12911 :=
  BstLean.Part269.frameData_from_numerics (n := 12911) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12911.worldPackage rfl BstLean.Part268.WorldRow12911.product_lower (BstLean.Part268.WorldRow12911.producthi.2.trans (by norm_num))
    scalarRow12911 repair12911 covarianceInputs12911 (fun i hi => sourceNumerics12911 hi)
    BstLean.Part268.agent12911.frame targetFrame12911_eq


end BstLean.Part269.N12911

namespace BstLean.Part269.N12912
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12912 : scalarRow12912.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12912, BstLean.Part268.grid12912, BstLean.Part263.worldGrid]

theorem supplies12912 (j : Fin 43) : Supply 12912 (parameters j)
    (cellLower scalarRow12912.grid (sourceIndex j))
    (cellUpper scalarRow12912.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12912.grid grid_top_bounds12912 j

theorem radii12912 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12912.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12912 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12912 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12912.grid grid_top_bounds12912 j hθ

noncomputable def covarianceInputs12912 :
    BstLean.Part263.CovarianceInputs 12912 scalarRow12912.grid parameters (caps repair12912) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12912 grid_top_bounds12912 repair12912

noncomputable def covarianceEvent12912 : Set (AgFam 12912) :=
  BstLean.Part263.covarianceEvent 12912 scalarRow12912.grid parameters

theorem covarianceEvent12912_measurable : MeasurableSet covarianceEvent12912 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12912_payment :
    (retDist (paperDesignP 12912).toCentres).real
      (agentEv (paperDesignP 12912) covarianceEvent12912)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12912

theorem localCov12912 : BstLean.Part259.LocalCovarianceOn covarianceEvent12912
    (BstLean.Part263.cell scalarRow12912.grid) (caps repair12912) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12912

theorem covarianceGood12912_payment :
    (retDist (paperDesignP 12912).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12912)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12912_payment



end BstLean.Part269.N12912

namespace BstLean.Part269.N12912
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12912}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12912.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12912) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12912).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12912 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12912) (by norm_num) BstLean.Part268.WorldRow12912.worldPackage rfl
    BstLean.Part268.WorldRow12912.product_lower (BstLean.Part268.WorldRow12912.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12912} (hw : c ∈ Hof BstLean.Part268.WorldRow12912.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12912) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12912) (by norm_num) BstLean.Part268.WorldRow12912.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12912} (hw : c ∈ Hof BstLean.Part268.WorldRow12912.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12912) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12912).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12912) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12912_eq : scalarRow12912.targetFrame = BstLean.Part268.agent12912.frame := by
  norm_num [scalarRow12912,BstLean.Part268.agent12912]

noncomputable def frameData12912 : BstLean.Part264b.FrameData 12912 :=
  BstLean.Part269.frameData_from_numerics (n := 12912) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12912.worldPackage rfl BstLean.Part268.WorldRow12912.product_lower (BstLean.Part268.WorldRow12912.producthi.2.trans (by norm_num))
    scalarRow12912 repair12912 covarianceInputs12912 (fun i hi => sourceNumerics12912 hi)
    BstLean.Part268.agent12912.frame targetFrame12912_eq


end BstLean.Part269.N12912

namespace BstLean.Part269.N12913
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12913 : scalarRow12913.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12913, BstLean.Part268.grid12913, BstLean.Part263.worldGrid]

theorem supplies12913 (j : Fin 43) : Supply 12913 (parameters j)
    (cellLower scalarRow12913.grid (sourceIndex j))
    (cellUpper scalarRow12913.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12913.grid grid_top_bounds12913 j

theorem radii12913 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12913.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12913 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12913 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12913.grid grid_top_bounds12913 j hθ

noncomputable def covarianceInputs12913 :
    BstLean.Part263.CovarianceInputs 12913 scalarRow12913.grid parameters (caps repair12913) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12913 grid_top_bounds12913 repair12913

noncomputable def covarianceEvent12913 : Set (AgFam 12913) :=
  BstLean.Part263.covarianceEvent 12913 scalarRow12913.grid parameters

theorem covarianceEvent12913_measurable : MeasurableSet covarianceEvent12913 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12913_payment :
    (retDist (paperDesignP 12913).toCentres).real
      (agentEv (paperDesignP 12913) covarianceEvent12913)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12913

theorem localCov12913 : BstLean.Part259.LocalCovarianceOn covarianceEvent12913
    (BstLean.Part263.cell scalarRow12913.grid) (caps repair12913) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12913

theorem covarianceGood12913_payment :
    (retDist (paperDesignP 12913).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12913)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12913_payment



end BstLean.Part269.N12913

namespace BstLean.Part269.N12913
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12913}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12913.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12913) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12913).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12913 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12913) (by norm_num) BstLean.Part268.WorldRow12913.worldPackage rfl
    BstLean.Part268.WorldRow12913.product_lower (BstLean.Part268.WorldRow12913.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12913} (hw : c ∈ Hof BstLean.Part268.WorldRow12913.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12913) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12913) (by norm_num) BstLean.Part268.WorldRow12913.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12913} (hw : c ∈ Hof BstLean.Part268.WorldRow12913.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12913) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12913).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12913) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12913_eq : scalarRow12913.targetFrame = BstLean.Part268.agent12913.frame := by
  norm_num [scalarRow12913,BstLean.Part268.agent12913]

noncomputable def frameData12913 : BstLean.Part264b.FrameData 12913 :=
  BstLean.Part269.frameData_from_numerics (n := 12913) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12913.worldPackage rfl BstLean.Part268.WorldRow12913.product_lower (BstLean.Part268.WorldRow12913.producthi.2.trans (by norm_num))
    scalarRow12913 repair12913 covarianceInputs12913 (fun i hi => sourceNumerics12913 hi)
    BstLean.Part268.agent12913.frame targetFrame12913_eq


end BstLean.Part269.N12913

namespace BstLean.Part269.N12914
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12914 : scalarRow12914.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12914, BstLean.Part268.grid12914, BstLean.Part263.worldGrid]

theorem supplies12914 (j : Fin 43) : Supply 12914 (parameters j)
    (cellLower scalarRow12914.grid (sourceIndex j))
    (cellUpper scalarRow12914.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12914.grid grid_top_bounds12914 j

theorem radii12914 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12914.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12914 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12914 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12914.grid grid_top_bounds12914 j hθ

noncomputable def covarianceInputs12914 :
    BstLean.Part263.CovarianceInputs 12914 scalarRow12914.grid parameters (caps repair12914) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12914 grid_top_bounds12914 repair12914

noncomputable def covarianceEvent12914 : Set (AgFam 12914) :=
  BstLean.Part263.covarianceEvent 12914 scalarRow12914.grid parameters

theorem covarianceEvent12914_measurable : MeasurableSet covarianceEvent12914 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12914_payment :
    (retDist (paperDesignP 12914).toCentres).real
      (agentEv (paperDesignP 12914) covarianceEvent12914)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12914

theorem localCov12914 : BstLean.Part259.LocalCovarianceOn covarianceEvent12914
    (BstLean.Part263.cell scalarRow12914.grid) (caps repair12914) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12914

theorem covarianceGood12914_payment :
    (retDist (paperDesignP 12914).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12914)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12914_payment



end BstLean.Part269.N12914

namespace BstLean.Part269.N12914
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12914}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12914.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12914) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12914).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12914 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12914) (by norm_num) BstLean.Part268.WorldRow12914.worldPackage rfl
    BstLean.Part268.WorldRow12914.product_lower (BstLean.Part268.WorldRow12914.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12914} (hw : c ∈ Hof BstLean.Part268.WorldRow12914.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12914) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12914) (by norm_num) BstLean.Part268.WorldRow12914.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12914} (hw : c ∈ Hof BstLean.Part268.WorldRow12914.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12914) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12914).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12914) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12914_eq : scalarRow12914.targetFrame = BstLean.Part268.agent12914.frame := by
  norm_num [scalarRow12914,BstLean.Part268.agent12914]

noncomputable def frameData12914 : BstLean.Part264b.FrameData 12914 :=
  BstLean.Part269.frameData_from_numerics (n := 12914) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12914.worldPackage rfl BstLean.Part268.WorldRow12914.product_lower (BstLean.Part268.WorldRow12914.producthi.2.trans (by norm_num))
    scalarRow12914 repair12914 covarianceInputs12914 (fun i hi => sourceNumerics12914 hi)
    BstLean.Part268.agent12914.frame targetFrame12914_eq


end BstLean.Part269.N12914
