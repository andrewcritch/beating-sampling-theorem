import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World20Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs20
import BstLean.Part269Rows20
import BstLean.Part269Sources20
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12855
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12855 : scalarRow12855.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12855, BstLean.Part268.grid12855, BstLean.Part263.worldGrid]

theorem supplies12855 (j : Fin 43) : Supply 12855 (parameters j)
    (cellLower scalarRow12855.grid (sourceIndex j))
    (cellUpper scalarRow12855.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12855.grid grid_top_bounds12855 j

theorem radii12855 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12855.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12855 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12855 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12855.grid grid_top_bounds12855 j hθ

noncomputable def covarianceInputs12855 :
    BstLean.Part263.CovarianceInputs 12855 scalarRow12855.grid parameters (caps repair12855) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12855 grid_top_bounds12855 repair12855

noncomputable def covarianceEvent12855 : Set (AgFam 12855) :=
  BstLean.Part263.covarianceEvent 12855 scalarRow12855.grid parameters

theorem covarianceEvent12855_measurable : MeasurableSet covarianceEvent12855 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12855_payment :
    (retDist (paperDesignP 12855).toCentres).real
      (agentEv (paperDesignP 12855) covarianceEvent12855)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12855

theorem localCov12855 : BstLean.Part259.LocalCovarianceOn covarianceEvent12855
    (BstLean.Part263.cell scalarRow12855.grid) (caps repair12855) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12855

theorem covarianceGood12855_payment :
    (retDist (paperDesignP 12855).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12855)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12855_payment



end BstLean.Part269.N12855

namespace BstLean.Part269.N12855
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12855}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12855.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12855) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12855).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12855 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12855) (by norm_num) BstLean.Part268.WorldRow12855.worldPackage rfl
    BstLean.Part268.WorldRow12855.product_lower (BstLean.Part268.WorldRow12855.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12855} (hw : c ∈ Hof BstLean.Part268.WorldRow12855.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12855) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12855) (by norm_num) BstLean.Part268.WorldRow12855.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12855} (hw : c ∈ Hof BstLean.Part268.WorldRow12855.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12855) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12855).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12855) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12855_eq : scalarRow12855.targetFrame = BstLean.Part268.agent12855.frame := by
  norm_num [scalarRow12855,BstLean.Part268.agent12855]

noncomputable def frameData12855 : BstLean.Part264b.FrameData 12855 :=
  BstLean.Part269.frameData_from_numerics (n := 12855) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12855.worldPackage rfl BstLean.Part268.WorldRow12855.product_lower (BstLean.Part268.WorldRow12855.producthi.2.trans (by norm_num))
    scalarRow12855 repair12855 covarianceInputs12855 (fun i hi => sourceNumerics12855 hi)
    BstLean.Part268.agent12855.frame targetFrame12855_eq


end BstLean.Part269.N12855

namespace BstLean.Part269.N12856
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12856 : scalarRow12856.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12856, BstLean.Part268.grid12856, BstLean.Part263.worldGrid]

theorem supplies12856 (j : Fin 43) : Supply 12856 (parameters j)
    (cellLower scalarRow12856.grid (sourceIndex j))
    (cellUpper scalarRow12856.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12856.grid grid_top_bounds12856 j

theorem radii12856 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12856.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12856 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12856 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12856.grid grid_top_bounds12856 j hθ

noncomputable def covarianceInputs12856 :
    BstLean.Part263.CovarianceInputs 12856 scalarRow12856.grid parameters (caps repair12856) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12856 grid_top_bounds12856 repair12856

noncomputable def covarianceEvent12856 : Set (AgFam 12856) :=
  BstLean.Part263.covarianceEvent 12856 scalarRow12856.grid parameters

theorem covarianceEvent12856_measurable : MeasurableSet covarianceEvent12856 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12856_payment :
    (retDist (paperDesignP 12856).toCentres).real
      (agentEv (paperDesignP 12856) covarianceEvent12856)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12856

theorem localCov12856 : BstLean.Part259.LocalCovarianceOn covarianceEvent12856
    (BstLean.Part263.cell scalarRow12856.grid) (caps repair12856) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12856

theorem covarianceGood12856_payment :
    (retDist (paperDesignP 12856).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12856)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12856_payment



end BstLean.Part269.N12856

namespace BstLean.Part269.N12856
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12856}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12856.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12856) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12856).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12856 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12856) (by norm_num) BstLean.Part268.WorldRow12856.worldPackage rfl
    BstLean.Part268.WorldRow12856.product_lower (BstLean.Part268.WorldRow12856.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12856} (hw : c ∈ Hof BstLean.Part268.WorldRow12856.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12856) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12856) (by norm_num) BstLean.Part268.WorldRow12856.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12856} (hw : c ∈ Hof BstLean.Part268.WorldRow12856.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12856) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12856).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12856) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12856_eq : scalarRow12856.targetFrame = BstLean.Part268.agent12856.frame := by
  norm_num [scalarRow12856,BstLean.Part268.agent12856]

noncomputable def frameData12856 : BstLean.Part264b.FrameData 12856 :=
  BstLean.Part269.frameData_from_numerics (n := 12856) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12856.worldPackage rfl BstLean.Part268.WorldRow12856.product_lower (BstLean.Part268.WorldRow12856.producthi.2.trans (by norm_num))
    scalarRow12856 repair12856 covarianceInputs12856 (fun i hi => sourceNumerics12856 hi)
    BstLean.Part268.agent12856.frame targetFrame12856_eq


end BstLean.Part269.N12856

namespace BstLean.Part269.N12857
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12857 : scalarRow12857.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12857, BstLean.Part268.grid12857, BstLean.Part263.worldGrid]

theorem supplies12857 (j : Fin 43) : Supply 12857 (parameters j)
    (cellLower scalarRow12857.grid (sourceIndex j))
    (cellUpper scalarRow12857.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12857.grid grid_top_bounds12857 j

theorem radii12857 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12857.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12857 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12857 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12857.grid grid_top_bounds12857 j hθ

noncomputable def covarianceInputs12857 :
    BstLean.Part263.CovarianceInputs 12857 scalarRow12857.grid parameters (caps repair12857) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12857 grid_top_bounds12857 repair12857

noncomputable def covarianceEvent12857 : Set (AgFam 12857) :=
  BstLean.Part263.covarianceEvent 12857 scalarRow12857.grid parameters

theorem covarianceEvent12857_measurable : MeasurableSet covarianceEvent12857 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12857_payment :
    (retDist (paperDesignP 12857).toCentres).real
      (agentEv (paperDesignP 12857) covarianceEvent12857)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12857

theorem localCov12857 : BstLean.Part259.LocalCovarianceOn covarianceEvent12857
    (BstLean.Part263.cell scalarRow12857.grid) (caps repair12857) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12857

theorem covarianceGood12857_payment :
    (retDist (paperDesignP 12857).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12857)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12857_payment



end BstLean.Part269.N12857

namespace BstLean.Part269.N12857
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12857}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12857.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12857) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12857).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12857 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12857) (by norm_num) BstLean.Part268.WorldRow12857.worldPackage rfl
    BstLean.Part268.WorldRow12857.product_lower (BstLean.Part268.WorldRow12857.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12857} (hw : c ∈ Hof BstLean.Part268.WorldRow12857.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12857) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12857) (by norm_num) BstLean.Part268.WorldRow12857.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12857} (hw : c ∈ Hof BstLean.Part268.WorldRow12857.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12857) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12857).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12857) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12857_eq : scalarRow12857.targetFrame = BstLean.Part268.agent12857.frame := by
  norm_num [scalarRow12857,BstLean.Part268.agent12857]

noncomputable def frameData12857 : BstLean.Part264b.FrameData 12857 :=
  BstLean.Part269.frameData_from_numerics (n := 12857) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12857.worldPackage rfl BstLean.Part268.WorldRow12857.product_lower (BstLean.Part268.WorldRow12857.producthi.2.trans (by norm_num))
    scalarRow12857 repair12857 covarianceInputs12857 (fun i hi => sourceNumerics12857 hi)
    BstLean.Part268.agent12857.frame targetFrame12857_eq


end BstLean.Part269.N12857

namespace BstLean.Part269.N12858
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12858 : scalarRow12858.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12858, BstLean.Part268.grid12858, BstLean.Part263.worldGrid]

theorem supplies12858 (j : Fin 43) : Supply 12858 (parameters j)
    (cellLower scalarRow12858.grid (sourceIndex j))
    (cellUpper scalarRow12858.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12858.grid grid_top_bounds12858 j

theorem radii12858 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12858.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12858 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12858 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12858.grid grid_top_bounds12858 j hθ

noncomputable def covarianceInputs12858 :
    BstLean.Part263.CovarianceInputs 12858 scalarRow12858.grid parameters (caps repair12858) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12858 grid_top_bounds12858 repair12858

noncomputable def covarianceEvent12858 : Set (AgFam 12858) :=
  BstLean.Part263.covarianceEvent 12858 scalarRow12858.grid parameters

theorem covarianceEvent12858_measurable : MeasurableSet covarianceEvent12858 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12858_payment :
    (retDist (paperDesignP 12858).toCentres).real
      (agentEv (paperDesignP 12858) covarianceEvent12858)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12858

theorem localCov12858 : BstLean.Part259.LocalCovarianceOn covarianceEvent12858
    (BstLean.Part263.cell scalarRow12858.grid) (caps repair12858) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12858

theorem covarianceGood12858_payment :
    (retDist (paperDesignP 12858).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12858)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12858_payment



end BstLean.Part269.N12858

namespace BstLean.Part269.N12858
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12858}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12858.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12858) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12858).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12858 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12858) (by norm_num) BstLean.Part268.WorldRow12858.worldPackage rfl
    BstLean.Part268.WorldRow12858.product_lower (BstLean.Part268.WorldRow12858.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12858} (hw : c ∈ Hof BstLean.Part268.WorldRow12858.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12858) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12858) (by norm_num) BstLean.Part268.WorldRow12858.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12858} (hw : c ∈ Hof BstLean.Part268.WorldRow12858.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12858) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12858).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12858) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12858_eq : scalarRow12858.targetFrame = BstLean.Part268.agent12858.frame := by
  norm_num [scalarRow12858,BstLean.Part268.agent12858]

noncomputable def frameData12858 : BstLean.Part264b.FrameData 12858 :=
  BstLean.Part269.frameData_from_numerics (n := 12858) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12858.worldPackage rfl BstLean.Part268.WorldRow12858.product_lower (BstLean.Part268.WorldRow12858.producthi.2.trans (by norm_num))
    scalarRow12858 repair12858 covarianceInputs12858 (fun i hi => sourceNumerics12858 hi)
    BstLean.Part268.agent12858.frame targetFrame12858_eq


end BstLean.Part269.N12858

namespace BstLean.Part269.N12859
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12859 : scalarRow12859.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12859, BstLean.Part268.grid12859, BstLean.Part263.worldGrid]

theorem supplies12859 (j : Fin 43) : Supply 12859 (parameters j)
    (cellLower scalarRow12859.grid (sourceIndex j))
    (cellUpper scalarRow12859.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12859.grid grid_top_bounds12859 j

theorem radii12859 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12859.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12859 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12859 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12859.grid grid_top_bounds12859 j hθ

noncomputable def covarianceInputs12859 :
    BstLean.Part263.CovarianceInputs 12859 scalarRow12859.grid parameters (caps repair12859) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12859 grid_top_bounds12859 repair12859

noncomputable def covarianceEvent12859 : Set (AgFam 12859) :=
  BstLean.Part263.covarianceEvent 12859 scalarRow12859.grid parameters

theorem covarianceEvent12859_measurable : MeasurableSet covarianceEvent12859 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12859_payment :
    (retDist (paperDesignP 12859).toCentres).real
      (agentEv (paperDesignP 12859) covarianceEvent12859)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12859

theorem localCov12859 : BstLean.Part259.LocalCovarianceOn covarianceEvent12859
    (BstLean.Part263.cell scalarRow12859.grid) (caps repair12859) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12859

theorem covarianceGood12859_payment :
    (retDist (paperDesignP 12859).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12859)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12859_payment



end BstLean.Part269.N12859

namespace BstLean.Part269.N12859
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12859}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12859.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12859) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12859).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12859 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12859) (by norm_num) BstLean.Part268.WorldRow12859.worldPackage rfl
    BstLean.Part268.WorldRow12859.product_lower (BstLean.Part268.WorldRow12859.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12859} (hw : c ∈ Hof BstLean.Part268.WorldRow12859.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12859) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12859) (by norm_num) BstLean.Part268.WorldRow12859.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12859} (hw : c ∈ Hof BstLean.Part268.WorldRow12859.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12859) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12859).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12859) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12859_eq : scalarRow12859.targetFrame = BstLean.Part268.agent12859.frame := by
  norm_num [scalarRow12859,BstLean.Part268.agent12859]

noncomputable def frameData12859 : BstLean.Part264b.FrameData 12859 :=
  BstLean.Part269.frameData_from_numerics (n := 12859) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12859.worldPackage rfl BstLean.Part268.WorldRow12859.product_lower (BstLean.Part268.WorldRow12859.producthi.2.trans (by norm_num))
    scalarRow12859 repair12859 covarianceInputs12859 (fun i hi => sourceNumerics12859 hi)
    BstLean.Part268.agent12859.frame targetFrame12859_eq


end BstLean.Part269.N12859
