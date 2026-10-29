import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World19Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs19
import BstLean.Part269Rows19
import BstLean.Part269Sources19
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12845
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12845 : scalarRow12845.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12845, BstLean.Part268.grid12845, BstLean.Part263.worldGrid]

theorem supplies12845 (j : Fin 43) : Supply 12845 (parameters j)
    (cellLower scalarRow12845.grid (sourceIndex j))
    (cellUpper scalarRow12845.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12845.grid grid_top_bounds12845 j

theorem radii12845 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12845.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12845 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12845 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12845.grid grid_top_bounds12845 j hθ

noncomputable def covarianceInputs12845 :
    BstLean.Part263.CovarianceInputs 12845 scalarRow12845.grid parameters (caps repair12845) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12845 grid_top_bounds12845 repair12845

noncomputable def covarianceEvent12845 : Set (AgFam 12845) :=
  BstLean.Part263.covarianceEvent 12845 scalarRow12845.grid parameters

theorem covarianceEvent12845_measurable : MeasurableSet covarianceEvent12845 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12845_payment :
    (retDist (paperDesignP 12845).toCentres).real
      (agentEv (paperDesignP 12845) covarianceEvent12845)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12845

theorem localCov12845 : BstLean.Part259.LocalCovarianceOn covarianceEvent12845
    (BstLean.Part263.cell scalarRow12845.grid) (caps repair12845) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12845

theorem covarianceGood12845_payment :
    (retDist (paperDesignP 12845).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12845)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12845_payment



end BstLean.Part269.N12845

namespace BstLean.Part269.N12845
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12845}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12845.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12845) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12845).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12845 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12845) (by norm_num) BstLean.Part268.WorldRow12845.worldPackage rfl
    BstLean.Part268.WorldRow12845.product_lower (BstLean.Part268.WorldRow12845.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12845} (hw : c ∈ Hof BstLean.Part268.WorldRow12845.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12845) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12845) (by norm_num) BstLean.Part268.WorldRow12845.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12845} (hw : c ∈ Hof BstLean.Part268.WorldRow12845.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12845) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12845).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12845) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12845_eq : scalarRow12845.targetFrame = BstLean.Part268.agent12845.frame := by
  norm_num [scalarRow12845,BstLean.Part268.agent12845]

noncomputable def frameData12845 : BstLean.Part264b.FrameData 12845 :=
  BstLean.Part269.frameData_from_numerics (n := 12845) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12845.worldPackage rfl BstLean.Part268.WorldRow12845.product_lower (BstLean.Part268.WorldRow12845.producthi.2.trans (by norm_num))
    scalarRow12845 repair12845 covarianceInputs12845 (fun i hi => sourceNumerics12845 hi)
    BstLean.Part268.agent12845.frame targetFrame12845_eq


end BstLean.Part269.N12845

namespace BstLean.Part269.N12846
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12846 : scalarRow12846.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12846, BstLean.Part268.grid12846, BstLean.Part263.worldGrid]

theorem supplies12846 (j : Fin 43) : Supply 12846 (parameters j)
    (cellLower scalarRow12846.grid (sourceIndex j))
    (cellUpper scalarRow12846.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12846.grid grid_top_bounds12846 j

theorem radii12846 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12846.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12846 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12846 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12846.grid grid_top_bounds12846 j hθ

noncomputable def covarianceInputs12846 :
    BstLean.Part263.CovarianceInputs 12846 scalarRow12846.grid parameters (caps repair12846) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12846 grid_top_bounds12846 repair12846

noncomputable def covarianceEvent12846 : Set (AgFam 12846) :=
  BstLean.Part263.covarianceEvent 12846 scalarRow12846.grid parameters

theorem covarianceEvent12846_measurable : MeasurableSet covarianceEvent12846 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12846_payment :
    (retDist (paperDesignP 12846).toCentres).real
      (agentEv (paperDesignP 12846) covarianceEvent12846)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12846

theorem localCov12846 : BstLean.Part259.LocalCovarianceOn covarianceEvent12846
    (BstLean.Part263.cell scalarRow12846.grid) (caps repair12846) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12846

theorem covarianceGood12846_payment :
    (retDist (paperDesignP 12846).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12846)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12846_payment



end BstLean.Part269.N12846

namespace BstLean.Part269.N12846
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12846}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12846.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12846) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12846).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12846 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12846) (by norm_num) BstLean.Part268.WorldRow12846.worldPackage rfl
    BstLean.Part268.WorldRow12846.product_lower (BstLean.Part268.WorldRow12846.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12846} (hw : c ∈ Hof BstLean.Part268.WorldRow12846.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12846) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12846) (by norm_num) BstLean.Part268.WorldRow12846.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12846} (hw : c ∈ Hof BstLean.Part268.WorldRow12846.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12846) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12846).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12846) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12846_eq : scalarRow12846.targetFrame = BstLean.Part268.agent12846.frame := by
  norm_num [scalarRow12846,BstLean.Part268.agent12846]

noncomputable def frameData12846 : BstLean.Part264b.FrameData 12846 :=
  BstLean.Part269.frameData_from_numerics (n := 12846) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12846.worldPackage rfl BstLean.Part268.WorldRow12846.product_lower (BstLean.Part268.WorldRow12846.producthi.2.trans (by norm_num))
    scalarRow12846 repair12846 covarianceInputs12846 (fun i hi => sourceNumerics12846 hi)
    BstLean.Part268.agent12846.frame targetFrame12846_eq


end BstLean.Part269.N12846

namespace BstLean.Part269.N12847
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12847 : scalarRow12847.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12847, BstLean.Part268.grid12847, BstLean.Part263.worldGrid]

theorem supplies12847 (j : Fin 43) : Supply 12847 (parameters j)
    (cellLower scalarRow12847.grid (sourceIndex j))
    (cellUpper scalarRow12847.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12847.grid grid_top_bounds12847 j

theorem radii12847 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12847.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12847 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12847 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12847.grid grid_top_bounds12847 j hθ

noncomputable def covarianceInputs12847 :
    BstLean.Part263.CovarianceInputs 12847 scalarRow12847.grid parameters (caps repair12847) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12847 grid_top_bounds12847 repair12847

noncomputable def covarianceEvent12847 : Set (AgFam 12847) :=
  BstLean.Part263.covarianceEvent 12847 scalarRow12847.grid parameters

theorem covarianceEvent12847_measurable : MeasurableSet covarianceEvent12847 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12847_payment :
    (retDist (paperDesignP 12847).toCentres).real
      (agentEv (paperDesignP 12847) covarianceEvent12847)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12847

theorem localCov12847 : BstLean.Part259.LocalCovarianceOn covarianceEvent12847
    (BstLean.Part263.cell scalarRow12847.grid) (caps repair12847) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12847

theorem covarianceGood12847_payment :
    (retDist (paperDesignP 12847).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12847)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12847_payment



end BstLean.Part269.N12847

namespace BstLean.Part269.N12847
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12847}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12847.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12847) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12847).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12847 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12847) (by norm_num) BstLean.Part268.WorldRow12847.worldPackage rfl
    BstLean.Part268.WorldRow12847.product_lower (BstLean.Part268.WorldRow12847.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12847} (hw : c ∈ Hof BstLean.Part268.WorldRow12847.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12847) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12847) (by norm_num) BstLean.Part268.WorldRow12847.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12847} (hw : c ∈ Hof BstLean.Part268.WorldRow12847.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12847) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12847).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12847) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12847_eq : scalarRow12847.targetFrame = BstLean.Part268.agent12847.frame := by
  norm_num [scalarRow12847,BstLean.Part268.agent12847]

noncomputable def frameData12847 : BstLean.Part264b.FrameData 12847 :=
  BstLean.Part269.frameData_from_numerics (n := 12847) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12847.worldPackage rfl BstLean.Part268.WorldRow12847.product_lower (BstLean.Part268.WorldRow12847.producthi.2.trans (by norm_num))
    scalarRow12847 repair12847 covarianceInputs12847 (fun i hi => sourceNumerics12847 hi)
    BstLean.Part268.agent12847.frame targetFrame12847_eq


end BstLean.Part269.N12847

namespace BstLean.Part269.N12848
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12848 : scalarRow12848.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12848, BstLean.Part268.grid12848, BstLean.Part263.worldGrid]

theorem supplies12848 (j : Fin 43) : Supply 12848 (parameters j)
    (cellLower scalarRow12848.grid (sourceIndex j))
    (cellUpper scalarRow12848.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12848.grid grid_top_bounds12848 j

theorem radii12848 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12848.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12848 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12848 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12848.grid grid_top_bounds12848 j hθ

noncomputable def covarianceInputs12848 :
    BstLean.Part263.CovarianceInputs 12848 scalarRow12848.grid parameters (caps repair12848) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12848 grid_top_bounds12848 repair12848

noncomputable def covarianceEvent12848 : Set (AgFam 12848) :=
  BstLean.Part263.covarianceEvent 12848 scalarRow12848.grid parameters

theorem covarianceEvent12848_measurable : MeasurableSet covarianceEvent12848 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12848_payment :
    (retDist (paperDesignP 12848).toCentres).real
      (agentEv (paperDesignP 12848) covarianceEvent12848)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12848

theorem localCov12848 : BstLean.Part259.LocalCovarianceOn covarianceEvent12848
    (BstLean.Part263.cell scalarRow12848.grid) (caps repair12848) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12848

theorem covarianceGood12848_payment :
    (retDist (paperDesignP 12848).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12848)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12848_payment



end BstLean.Part269.N12848

namespace BstLean.Part269.N12848
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12848}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12848.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12848) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12848).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12848 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12848) (by norm_num) BstLean.Part268.WorldRow12848.worldPackage rfl
    BstLean.Part268.WorldRow12848.product_lower (BstLean.Part268.WorldRow12848.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12848} (hw : c ∈ Hof BstLean.Part268.WorldRow12848.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12848) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12848) (by norm_num) BstLean.Part268.WorldRow12848.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12848} (hw : c ∈ Hof BstLean.Part268.WorldRow12848.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12848) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12848).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12848) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12848_eq : scalarRow12848.targetFrame = BstLean.Part268.agent12848.frame := by
  norm_num [scalarRow12848,BstLean.Part268.agent12848]

noncomputable def frameData12848 : BstLean.Part264b.FrameData 12848 :=
  BstLean.Part269.frameData_from_numerics (n := 12848) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12848.worldPackage rfl BstLean.Part268.WorldRow12848.product_lower (BstLean.Part268.WorldRow12848.producthi.2.trans (by norm_num))
    scalarRow12848 repair12848 covarianceInputs12848 (fun i hi => sourceNumerics12848 hi)
    BstLean.Part268.agent12848.frame targetFrame12848_eq


end BstLean.Part269.N12848

namespace BstLean.Part269.N12849
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12849 : scalarRow12849.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12849, BstLean.Part268.grid12849, BstLean.Part263.worldGrid]

theorem supplies12849 (j : Fin 43) : Supply 12849 (parameters j)
    (cellLower scalarRow12849.grid (sourceIndex j))
    (cellUpper scalarRow12849.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12849.grid grid_top_bounds12849 j

theorem radii12849 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12849.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12849 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12849 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12849.grid grid_top_bounds12849 j hθ

noncomputable def covarianceInputs12849 :
    BstLean.Part263.CovarianceInputs 12849 scalarRow12849.grid parameters (caps repair12849) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12849 grid_top_bounds12849 repair12849

noncomputable def covarianceEvent12849 : Set (AgFam 12849) :=
  BstLean.Part263.covarianceEvent 12849 scalarRow12849.grid parameters

theorem covarianceEvent12849_measurable : MeasurableSet covarianceEvent12849 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12849_payment :
    (retDist (paperDesignP 12849).toCentres).real
      (agentEv (paperDesignP 12849) covarianceEvent12849)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12849

theorem localCov12849 : BstLean.Part259.LocalCovarianceOn covarianceEvent12849
    (BstLean.Part263.cell scalarRow12849.grid) (caps repair12849) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12849

theorem covarianceGood12849_payment :
    (retDist (paperDesignP 12849).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12849)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12849_payment



end BstLean.Part269.N12849

namespace BstLean.Part269.N12849
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12849}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12849.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12849) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12849).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12849 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12849) (by norm_num) BstLean.Part268.WorldRow12849.worldPackage rfl
    BstLean.Part268.WorldRow12849.product_lower (BstLean.Part268.WorldRow12849.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12849} (hw : c ∈ Hof BstLean.Part268.WorldRow12849.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12849) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12849) (by norm_num) BstLean.Part268.WorldRow12849.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12849} (hw : c ∈ Hof BstLean.Part268.WorldRow12849.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12849) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12849).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12849) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12849_eq : scalarRow12849.targetFrame = BstLean.Part268.agent12849.frame := by
  norm_num [scalarRow12849,BstLean.Part268.agent12849]

noncomputable def frameData12849 : BstLean.Part264b.FrameData 12849 :=
  BstLean.Part269.frameData_from_numerics (n := 12849) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12849.worldPackage rfl BstLean.Part268.WorldRow12849.product_lower (BstLean.Part268.WorldRow12849.producthi.2.trans (by norm_num))
    scalarRow12849 repair12849 covarianceInputs12849 (fun i hi => sourceNumerics12849 hi)
    BstLean.Part268.agent12849.frame targetFrame12849_eq


end BstLean.Part269.N12849
