import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World23Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs23
import BstLean.Part269Rows23
import BstLean.Part269Sources23
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12935
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12935 : scalarRow12935.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12935, BstLean.Part268.grid12935, BstLean.Part263.worldGrid]

theorem supplies12935 (j : Fin 43) : Supply 12935 (parameters j)
    (cellLower scalarRow12935.grid (sourceIndex j))
    (cellUpper scalarRow12935.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12935.grid grid_top_bounds12935 j

theorem radii12935 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12935.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12935 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12935 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12935.grid grid_top_bounds12935 j hθ

noncomputable def covarianceInputs12935 :
    BstLean.Part263.CovarianceInputs 12935 scalarRow12935.grid parameters (caps repair12935) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12935 grid_top_bounds12935 repair12935

noncomputable def covarianceEvent12935 : Set (AgFam 12935) :=
  BstLean.Part263.covarianceEvent 12935 scalarRow12935.grid parameters

theorem covarianceEvent12935_measurable : MeasurableSet covarianceEvent12935 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12935_payment :
    (retDist (paperDesignP 12935).toCentres).real
      (agentEv (paperDesignP 12935) covarianceEvent12935)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12935

theorem localCov12935 : BstLean.Part259.LocalCovarianceOn covarianceEvent12935
    (BstLean.Part263.cell scalarRow12935.grid) (caps repair12935) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12935

theorem covarianceGood12935_payment :
    (retDist (paperDesignP 12935).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12935)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12935_payment



end BstLean.Part269.N12935

namespace BstLean.Part269.N12935
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12935}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12935.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12935) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12935).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12935 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12935) (by norm_num) BstLean.Part268.WorldRow12935.worldPackage rfl
    BstLean.Part268.WorldRow12935.product_lower (BstLean.Part268.WorldRow12935.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12935} (hw : c ∈ Hof BstLean.Part268.WorldRow12935.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12935) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12935) (by norm_num) BstLean.Part268.WorldRow12935.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12935} (hw : c ∈ Hof BstLean.Part268.WorldRow12935.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12935) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12935).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12935) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12935_eq : scalarRow12935.targetFrame = BstLean.Part268.agent12935.frame := by
  norm_num [scalarRow12935,BstLean.Part268.agent12935]

noncomputable def frameData12935 : BstLean.Part264b.FrameData 12935 :=
  BstLean.Part269.frameData_from_numerics (n := 12935) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12935.worldPackage rfl BstLean.Part268.WorldRow12935.product_lower (BstLean.Part268.WorldRow12935.producthi.2.trans (by norm_num))
    scalarRow12935 repair12935 covarianceInputs12935 (fun i hi => sourceNumerics12935 hi)
    BstLean.Part268.agent12935.frame targetFrame12935_eq


end BstLean.Part269.N12935

namespace BstLean.Part269.N12936
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12936 : scalarRow12936.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12936, BstLean.Part268.grid12936, BstLean.Part263.worldGrid]

theorem supplies12936 (j : Fin 43) : Supply 12936 (parameters j)
    (cellLower scalarRow12936.grid (sourceIndex j))
    (cellUpper scalarRow12936.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12936.grid grid_top_bounds12936 j

theorem radii12936 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12936.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12936 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12936 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12936.grid grid_top_bounds12936 j hθ

noncomputable def covarianceInputs12936 :
    BstLean.Part263.CovarianceInputs 12936 scalarRow12936.grid parameters (caps repair12936) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12936 grid_top_bounds12936 repair12936

noncomputable def covarianceEvent12936 : Set (AgFam 12936) :=
  BstLean.Part263.covarianceEvent 12936 scalarRow12936.grid parameters

theorem covarianceEvent12936_measurable : MeasurableSet covarianceEvent12936 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12936_payment :
    (retDist (paperDesignP 12936).toCentres).real
      (agentEv (paperDesignP 12936) covarianceEvent12936)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12936

theorem localCov12936 : BstLean.Part259.LocalCovarianceOn covarianceEvent12936
    (BstLean.Part263.cell scalarRow12936.grid) (caps repair12936) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12936

theorem covarianceGood12936_payment :
    (retDist (paperDesignP 12936).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12936)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12936_payment



end BstLean.Part269.N12936

namespace BstLean.Part269.N12936
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12936}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12936.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12936) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12936).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12936 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12936) (by norm_num) BstLean.Part268.WorldRow12936.worldPackage rfl
    BstLean.Part268.WorldRow12936.product_lower (BstLean.Part268.WorldRow12936.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12936} (hw : c ∈ Hof BstLean.Part268.WorldRow12936.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12936) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12936) (by norm_num) BstLean.Part268.WorldRow12936.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12936} (hw : c ∈ Hof BstLean.Part268.WorldRow12936.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12936) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12936).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12936) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12936_eq : scalarRow12936.targetFrame = BstLean.Part268.agent12936.frame := by
  norm_num [scalarRow12936,BstLean.Part268.agent12936]

noncomputable def frameData12936 : BstLean.Part264b.FrameData 12936 :=
  BstLean.Part269.frameData_from_numerics (n := 12936) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12936.worldPackage rfl BstLean.Part268.WorldRow12936.product_lower (BstLean.Part268.WorldRow12936.producthi.2.trans (by norm_num))
    scalarRow12936 repair12936 covarianceInputs12936 (fun i hi => sourceNumerics12936 hi)
    BstLean.Part268.agent12936.frame targetFrame12936_eq


end BstLean.Part269.N12936

namespace BstLean.Part269.N12937
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12937 : scalarRow12937.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12937, BstLean.Part268.grid12937, BstLean.Part263.worldGrid]

theorem supplies12937 (j : Fin 43) : Supply 12937 (parameters j)
    (cellLower scalarRow12937.grid (sourceIndex j))
    (cellUpper scalarRow12937.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12937.grid grid_top_bounds12937 j

theorem radii12937 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12937.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12937 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12937 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12937.grid grid_top_bounds12937 j hθ

noncomputable def covarianceInputs12937 :
    BstLean.Part263.CovarianceInputs 12937 scalarRow12937.grid parameters (caps repair12937) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12937 grid_top_bounds12937 repair12937

noncomputable def covarianceEvent12937 : Set (AgFam 12937) :=
  BstLean.Part263.covarianceEvent 12937 scalarRow12937.grid parameters

theorem covarianceEvent12937_measurable : MeasurableSet covarianceEvent12937 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12937_payment :
    (retDist (paperDesignP 12937).toCentres).real
      (agentEv (paperDesignP 12937) covarianceEvent12937)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12937

theorem localCov12937 : BstLean.Part259.LocalCovarianceOn covarianceEvent12937
    (BstLean.Part263.cell scalarRow12937.grid) (caps repair12937) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12937

theorem covarianceGood12937_payment :
    (retDist (paperDesignP 12937).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12937)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12937_payment



end BstLean.Part269.N12937

namespace BstLean.Part269.N12937
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12937}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12937.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12937) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12937).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12937 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12937) (by norm_num) BstLean.Part268.WorldRow12937.worldPackage rfl
    BstLean.Part268.WorldRow12937.product_lower (BstLean.Part268.WorldRow12937.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12937} (hw : c ∈ Hof BstLean.Part268.WorldRow12937.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12937) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12937) (by norm_num) BstLean.Part268.WorldRow12937.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12937} (hw : c ∈ Hof BstLean.Part268.WorldRow12937.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12937) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12937).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12937) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12937_eq : scalarRow12937.targetFrame = BstLean.Part268.agent12937.frame := by
  norm_num [scalarRow12937,BstLean.Part268.agent12937]

noncomputable def frameData12937 : BstLean.Part264b.FrameData 12937 :=
  BstLean.Part269.frameData_from_numerics (n := 12937) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12937.worldPackage rfl BstLean.Part268.WorldRow12937.product_lower (BstLean.Part268.WorldRow12937.producthi.2.trans (by norm_num))
    scalarRow12937 repair12937 covarianceInputs12937 (fun i hi => sourceNumerics12937 hi)
    BstLean.Part268.agent12937.frame targetFrame12937_eq


end BstLean.Part269.N12937

namespace BstLean.Part269.N12938
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12938 : scalarRow12938.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12938, BstLean.Part268.grid12938, BstLean.Part263.worldGrid]

theorem supplies12938 (j : Fin 43) : Supply 12938 (parameters j)
    (cellLower scalarRow12938.grid (sourceIndex j))
    (cellUpper scalarRow12938.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12938.grid grid_top_bounds12938 j

theorem radii12938 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12938.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12938 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12938 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12938.grid grid_top_bounds12938 j hθ

noncomputable def covarianceInputs12938 :
    BstLean.Part263.CovarianceInputs 12938 scalarRow12938.grid parameters (caps repair12938) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12938 grid_top_bounds12938 repair12938

noncomputable def covarianceEvent12938 : Set (AgFam 12938) :=
  BstLean.Part263.covarianceEvent 12938 scalarRow12938.grid parameters

theorem covarianceEvent12938_measurable : MeasurableSet covarianceEvent12938 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12938_payment :
    (retDist (paperDesignP 12938).toCentres).real
      (agentEv (paperDesignP 12938) covarianceEvent12938)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12938

theorem localCov12938 : BstLean.Part259.LocalCovarianceOn covarianceEvent12938
    (BstLean.Part263.cell scalarRow12938.grid) (caps repair12938) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12938

theorem covarianceGood12938_payment :
    (retDist (paperDesignP 12938).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12938)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12938_payment



end BstLean.Part269.N12938

namespace BstLean.Part269.N12938
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12938}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12938.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12938) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12938).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12938 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12938) (by norm_num) BstLean.Part268.WorldRow12938.worldPackage rfl
    BstLean.Part268.WorldRow12938.product_lower (BstLean.Part268.WorldRow12938.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12938} (hw : c ∈ Hof BstLean.Part268.WorldRow12938.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12938) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12938) (by norm_num) BstLean.Part268.WorldRow12938.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12938} (hw : c ∈ Hof BstLean.Part268.WorldRow12938.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12938) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12938).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12938) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12938_eq : scalarRow12938.targetFrame = BstLean.Part268.agent12938.frame := by
  norm_num [scalarRow12938,BstLean.Part268.agent12938]

noncomputable def frameData12938 : BstLean.Part264b.FrameData 12938 :=
  BstLean.Part269.frameData_from_numerics (n := 12938) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12938.worldPackage rfl BstLean.Part268.WorldRow12938.product_lower (BstLean.Part268.WorldRow12938.producthi.2.trans (by norm_num))
    scalarRow12938 repair12938 covarianceInputs12938 (fun i hi => sourceNumerics12938 hi)
    BstLean.Part268.agent12938.frame targetFrame12938_eq


end BstLean.Part269.N12938

namespace BstLean.Part269.N12939
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12939 : scalarRow12939.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12939, BstLean.Part268.grid12939, BstLean.Part263.worldGrid]

theorem supplies12939 (j : Fin 43) : Supply 12939 (parameters j)
    (cellLower scalarRow12939.grid (sourceIndex j))
    (cellUpper scalarRow12939.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12939.grid grid_top_bounds12939 j

theorem radii12939 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12939.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12939 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12939 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12939.grid grid_top_bounds12939 j hθ

noncomputable def covarianceInputs12939 :
    BstLean.Part263.CovarianceInputs 12939 scalarRow12939.grid parameters (caps repair12939) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12939 grid_top_bounds12939 repair12939

noncomputable def covarianceEvent12939 : Set (AgFam 12939) :=
  BstLean.Part263.covarianceEvent 12939 scalarRow12939.grid parameters

theorem covarianceEvent12939_measurable : MeasurableSet covarianceEvent12939 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12939_payment :
    (retDist (paperDesignP 12939).toCentres).real
      (agentEv (paperDesignP 12939) covarianceEvent12939)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12939

theorem localCov12939 : BstLean.Part259.LocalCovarianceOn covarianceEvent12939
    (BstLean.Part263.cell scalarRow12939.grid) (caps repair12939) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12939

theorem covarianceGood12939_payment :
    (retDist (paperDesignP 12939).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12939)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12939_payment



end BstLean.Part269.N12939

namespace BstLean.Part269.N12939
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12939}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12939.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12939) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12939).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12939 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12939) (by norm_num) BstLean.Part268.WorldRow12939.worldPackage rfl
    BstLean.Part268.WorldRow12939.product_lower (BstLean.Part268.WorldRow12939.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12939} (hw : c ∈ Hof BstLean.Part268.WorldRow12939.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12939) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12939) (by norm_num) BstLean.Part268.WorldRow12939.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12939} (hw : c ∈ Hof BstLean.Part268.WorldRow12939.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12939) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12939).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12939) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12939_eq : scalarRow12939.targetFrame = BstLean.Part268.agent12939.frame := by
  norm_num [scalarRow12939,BstLean.Part268.agent12939]

noncomputable def frameData12939 : BstLean.Part264b.FrameData 12939 :=
  BstLean.Part269.frameData_from_numerics (n := 12939) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12939.worldPackage rfl BstLean.Part268.WorldRow12939.product_lower (BstLean.Part268.WorldRow12939.producthi.2.trans (by norm_num))
    scalarRow12939 repair12939 covarianceInputs12939 (fun i hi => sourceNumerics12939 hi)
    BstLean.Part268.agent12939.frame targetFrame12939_eq


end BstLean.Part269.N12939
