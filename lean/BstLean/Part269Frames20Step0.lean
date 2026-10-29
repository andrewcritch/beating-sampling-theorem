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

namespace BstLean.Part269.N12850
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12850 : scalarRow12850.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12850, BstLean.Part268.grid12850, BstLean.Part263.worldGrid]

theorem supplies12850 (j : Fin 43) : Supply 12850 (parameters j)
    (cellLower scalarRow12850.grid (sourceIndex j))
    (cellUpper scalarRow12850.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12850.grid grid_top_bounds12850 j

theorem radii12850 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12850.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12850 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12850 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12850.grid grid_top_bounds12850 j hθ

noncomputable def covarianceInputs12850 :
    BstLean.Part263.CovarianceInputs 12850 scalarRow12850.grid parameters (caps repair12850) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12850 grid_top_bounds12850 repair12850

noncomputable def covarianceEvent12850 : Set (AgFam 12850) :=
  BstLean.Part263.covarianceEvent 12850 scalarRow12850.grid parameters

theorem covarianceEvent12850_measurable : MeasurableSet covarianceEvent12850 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12850_payment :
    (retDist (paperDesignP 12850).toCentres).real
      (agentEv (paperDesignP 12850) covarianceEvent12850)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12850

theorem localCov12850 : BstLean.Part259.LocalCovarianceOn covarianceEvent12850
    (BstLean.Part263.cell scalarRow12850.grid) (caps repair12850) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12850

theorem covarianceGood12850_payment :
    (retDist (paperDesignP 12850).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12850)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12850_payment



end BstLean.Part269.N12850

namespace BstLean.Part269.N12850
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12850}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12850.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12850) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12850).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12850 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12850) (by norm_num) BstLean.Part268.WorldRow12850.worldPackage rfl
    BstLean.Part268.WorldRow12850.product_lower (BstLean.Part268.WorldRow12850.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12850} (hw : c ∈ Hof BstLean.Part268.WorldRow12850.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12850) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12850) (by norm_num) BstLean.Part268.WorldRow12850.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12850} (hw : c ∈ Hof BstLean.Part268.WorldRow12850.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12850) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12850).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12850) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12850_eq : scalarRow12850.targetFrame = BstLean.Part268.agent12850.frame := by
  norm_num [scalarRow12850,BstLean.Part268.agent12850]

noncomputable def frameData12850 : BstLean.Part264b.FrameData 12850 :=
  BstLean.Part269.frameData_from_numerics (n := 12850) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12850.worldPackage rfl BstLean.Part268.WorldRow12850.product_lower (BstLean.Part268.WorldRow12850.producthi.2.trans (by norm_num))
    scalarRow12850 repair12850 covarianceInputs12850 (fun i hi => sourceNumerics12850 hi)
    BstLean.Part268.agent12850.frame targetFrame12850_eq


end BstLean.Part269.N12850

namespace BstLean.Part269.N12851
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12851 : scalarRow12851.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12851, BstLean.Part268.grid12851, BstLean.Part263.worldGrid]

theorem supplies12851 (j : Fin 43) : Supply 12851 (parameters j)
    (cellLower scalarRow12851.grid (sourceIndex j))
    (cellUpper scalarRow12851.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12851.grid grid_top_bounds12851 j

theorem radii12851 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12851.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12851 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12851 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12851.grid grid_top_bounds12851 j hθ

noncomputable def covarianceInputs12851 :
    BstLean.Part263.CovarianceInputs 12851 scalarRow12851.grid parameters (caps repair12851) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12851 grid_top_bounds12851 repair12851

noncomputable def covarianceEvent12851 : Set (AgFam 12851) :=
  BstLean.Part263.covarianceEvent 12851 scalarRow12851.grid parameters

theorem covarianceEvent12851_measurable : MeasurableSet covarianceEvent12851 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12851_payment :
    (retDist (paperDesignP 12851).toCentres).real
      (agentEv (paperDesignP 12851) covarianceEvent12851)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12851

theorem localCov12851 : BstLean.Part259.LocalCovarianceOn covarianceEvent12851
    (BstLean.Part263.cell scalarRow12851.grid) (caps repair12851) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12851

theorem covarianceGood12851_payment :
    (retDist (paperDesignP 12851).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12851)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12851_payment



end BstLean.Part269.N12851

namespace BstLean.Part269.N12851
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12851}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12851.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12851) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12851).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12851 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12851) (by norm_num) BstLean.Part268.WorldRow12851.worldPackage rfl
    BstLean.Part268.WorldRow12851.product_lower (BstLean.Part268.WorldRow12851.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12851} (hw : c ∈ Hof BstLean.Part268.WorldRow12851.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12851) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12851) (by norm_num) BstLean.Part268.WorldRow12851.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12851} (hw : c ∈ Hof BstLean.Part268.WorldRow12851.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12851) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12851).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12851) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12851_eq : scalarRow12851.targetFrame = BstLean.Part268.agent12851.frame := by
  norm_num [scalarRow12851,BstLean.Part268.agent12851]

noncomputable def frameData12851 : BstLean.Part264b.FrameData 12851 :=
  BstLean.Part269.frameData_from_numerics (n := 12851) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12851.worldPackage rfl BstLean.Part268.WorldRow12851.product_lower (BstLean.Part268.WorldRow12851.producthi.2.trans (by norm_num))
    scalarRow12851 repair12851 covarianceInputs12851 (fun i hi => sourceNumerics12851 hi)
    BstLean.Part268.agent12851.frame targetFrame12851_eq


end BstLean.Part269.N12851

namespace BstLean.Part269.N12852
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12852 : scalarRow12852.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12852, BstLean.Part268.grid12852, BstLean.Part263.worldGrid]

theorem supplies12852 (j : Fin 43) : Supply 12852 (parameters j)
    (cellLower scalarRow12852.grid (sourceIndex j))
    (cellUpper scalarRow12852.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12852.grid grid_top_bounds12852 j

theorem radii12852 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12852.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12852 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12852 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12852.grid grid_top_bounds12852 j hθ

noncomputable def covarianceInputs12852 :
    BstLean.Part263.CovarianceInputs 12852 scalarRow12852.grid parameters (caps repair12852) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12852 grid_top_bounds12852 repair12852

noncomputable def covarianceEvent12852 : Set (AgFam 12852) :=
  BstLean.Part263.covarianceEvent 12852 scalarRow12852.grid parameters

theorem covarianceEvent12852_measurable : MeasurableSet covarianceEvent12852 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12852_payment :
    (retDist (paperDesignP 12852).toCentres).real
      (agentEv (paperDesignP 12852) covarianceEvent12852)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12852

theorem localCov12852 : BstLean.Part259.LocalCovarianceOn covarianceEvent12852
    (BstLean.Part263.cell scalarRow12852.grid) (caps repair12852) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12852

theorem covarianceGood12852_payment :
    (retDist (paperDesignP 12852).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12852)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12852_payment



end BstLean.Part269.N12852

namespace BstLean.Part269.N12852
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12852}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12852.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12852) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12852).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12852 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12852) (by norm_num) BstLean.Part268.WorldRow12852.worldPackage rfl
    BstLean.Part268.WorldRow12852.product_lower (BstLean.Part268.WorldRow12852.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12852} (hw : c ∈ Hof BstLean.Part268.WorldRow12852.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12852) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12852) (by norm_num) BstLean.Part268.WorldRow12852.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12852} (hw : c ∈ Hof BstLean.Part268.WorldRow12852.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12852) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12852).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12852) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12852_eq : scalarRow12852.targetFrame = BstLean.Part268.agent12852.frame := by
  norm_num [scalarRow12852,BstLean.Part268.agent12852]

noncomputable def frameData12852 : BstLean.Part264b.FrameData 12852 :=
  BstLean.Part269.frameData_from_numerics (n := 12852) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12852.worldPackage rfl BstLean.Part268.WorldRow12852.product_lower (BstLean.Part268.WorldRow12852.producthi.2.trans (by norm_num))
    scalarRow12852 repair12852 covarianceInputs12852 (fun i hi => sourceNumerics12852 hi)
    BstLean.Part268.agent12852.frame targetFrame12852_eq


end BstLean.Part269.N12852

namespace BstLean.Part269.N12853
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12853 : scalarRow12853.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12853, BstLean.Part268.grid12853, BstLean.Part263.worldGrid]

theorem supplies12853 (j : Fin 43) : Supply 12853 (parameters j)
    (cellLower scalarRow12853.grid (sourceIndex j))
    (cellUpper scalarRow12853.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12853.grid grid_top_bounds12853 j

theorem radii12853 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12853.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12853 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12853 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12853.grid grid_top_bounds12853 j hθ

noncomputable def covarianceInputs12853 :
    BstLean.Part263.CovarianceInputs 12853 scalarRow12853.grid parameters (caps repair12853) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12853 grid_top_bounds12853 repair12853

noncomputable def covarianceEvent12853 : Set (AgFam 12853) :=
  BstLean.Part263.covarianceEvent 12853 scalarRow12853.grid parameters

theorem covarianceEvent12853_measurable : MeasurableSet covarianceEvent12853 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12853_payment :
    (retDist (paperDesignP 12853).toCentres).real
      (agentEv (paperDesignP 12853) covarianceEvent12853)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12853

theorem localCov12853 : BstLean.Part259.LocalCovarianceOn covarianceEvent12853
    (BstLean.Part263.cell scalarRow12853.grid) (caps repair12853) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12853

theorem covarianceGood12853_payment :
    (retDist (paperDesignP 12853).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12853)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12853_payment



end BstLean.Part269.N12853

namespace BstLean.Part269.N12853
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12853}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12853.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12853) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12853).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12853 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12853) (by norm_num) BstLean.Part268.WorldRow12853.worldPackage rfl
    BstLean.Part268.WorldRow12853.product_lower (BstLean.Part268.WorldRow12853.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12853} (hw : c ∈ Hof BstLean.Part268.WorldRow12853.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12853) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12853) (by norm_num) BstLean.Part268.WorldRow12853.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12853} (hw : c ∈ Hof BstLean.Part268.WorldRow12853.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12853) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12853).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12853) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12853_eq : scalarRow12853.targetFrame = BstLean.Part268.agent12853.frame := by
  norm_num [scalarRow12853,BstLean.Part268.agent12853]

noncomputable def frameData12853 : BstLean.Part264b.FrameData 12853 :=
  BstLean.Part269.frameData_from_numerics (n := 12853) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12853.worldPackage rfl BstLean.Part268.WorldRow12853.product_lower (BstLean.Part268.WorldRow12853.producthi.2.trans (by norm_num))
    scalarRow12853 repair12853 covarianceInputs12853 (fun i hi => sourceNumerics12853 hi)
    BstLean.Part268.agent12853.frame targetFrame12853_eq


end BstLean.Part269.N12853

namespace BstLean.Part269.N12854
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12854 : scalarRow12854.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12854, BstLean.Part268.grid12854, BstLean.Part263.worldGrid]

theorem supplies12854 (j : Fin 43) : Supply 12854 (parameters j)
    (cellLower scalarRow12854.grid (sourceIndex j))
    (cellUpper scalarRow12854.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12854.grid grid_top_bounds12854 j

theorem radii12854 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12854.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12854 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12854 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12854.grid grid_top_bounds12854 j hθ

noncomputable def covarianceInputs12854 :
    BstLean.Part263.CovarianceInputs 12854 scalarRow12854.grid parameters (caps repair12854) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12854 grid_top_bounds12854 repair12854

noncomputable def covarianceEvent12854 : Set (AgFam 12854) :=
  BstLean.Part263.covarianceEvent 12854 scalarRow12854.grid parameters

theorem covarianceEvent12854_measurable : MeasurableSet covarianceEvent12854 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12854_payment :
    (retDist (paperDesignP 12854).toCentres).real
      (agentEv (paperDesignP 12854) covarianceEvent12854)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12854

theorem localCov12854 : BstLean.Part259.LocalCovarianceOn covarianceEvent12854
    (BstLean.Part263.cell scalarRow12854.grid) (caps repair12854) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12854

theorem covarianceGood12854_payment :
    (retDist (paperDesignP 12854).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12854)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12854_payment



end BstLean.Part269.N12854

namespace BstLean.Part269.N12854
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12854}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12854.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12854) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12854).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12854 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12854) (by norm_num) BstLean.Part268.WorldRow12854.worldPackage rfl
    BstLean.Part268.WorldRow12854.product_lower (BstLean.Part268.WorldRow12854.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12854} (hw : c ∈ Hof BstLean.Part268.WorldRow12854.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12854) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12854) (by norm_num) BstLean.Part268.WorldRow12854.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12854} (hw : c ∈ Hof BstLean.Part268.WorldRow12854.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12854) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12854).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12854) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12854_eq : scalarRow12854.targetFrame = BstLean.Part268.agent12854.frame := by
  norm_num [scalarRow12854,BstLean.Part268.agent12854]

noncomputable def frameData12854 : BstLean.Part264b.FrameData 12854 :=
  BstLean.Part269.frameData_from_numerics (n := 12854) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12854.worldPackage rfl BstLean.Part268.WorldRow12854.product_lower (BstLean.Part268.WorldRow12854.producthi.2.trans (by norm_num))
    scalarRow12854 repair12854 covarianceInputs12854 (fun i hi => sourceNumerics12854 hi)
    BstLean.Part268.agent12854.frame targetFrame12854_eq


end BstLean.Part269.N12854
