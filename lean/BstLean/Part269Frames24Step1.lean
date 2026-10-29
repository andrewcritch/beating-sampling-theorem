import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World24Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs24
import BstLean.Part269Rows24
import BstLean.Part269Sources24
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12955
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12955 : scalarRow12955.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12955, BstLean.Part268.grid12955, BstLean.Part263.worldGrid]

theorem supplies12955 (j : Fin 43) : Supply 12955 (parameters j)
    (cellLower scalarRow12955.grid (sourceIndex j))
    (cellUpper scalarRow12955.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12955.grid grid_top_bounds12955 j

theorem radii12955 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12955.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12955 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12955 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12955.grid grid_top_bounds12955 j hθ

noncomputable def covarianceInputs12955 :
    BstLean.Part263.CovarianceInputs 12955 scalarRow12955.grid parameters (caps repair12955) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12955 grid_top_bounds12955 repair12955

noncomputable def covarianceEvent12955 : Set (AgFam 12955) :=
  BstLean.Part263.covarianceEvent 12955 scalarRow12955.grid parameters

theorem covarianceEvent12955_measurable : MeasurableSet covarianceEvent12955 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12955_payment :
    (retDist (paperDesignP 12955).toCentres).real
      (agentEv (paperDesignP 12955) covarianceEvent12955)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12955

theorem localCov12955 : BstLean.Part259.LocalCovarianceOn covarianceEvent12955
    (BstLean.Part263.cell scalarRow12955.grid) (caps repair12955) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12955

theorem covarianceGood12955_payment :
    (retDist (paperDesignP 12955).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12955)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12955_payment



end BstLean.Part269.N12955

namespace BstLean.Part269.N12955
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12955}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12955.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12955) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12955).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12955 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12955) (by norm_num) BstLean.Part268.WorldRow12955.worldPackage rfl
    BstLean.Part268.WorldRow12955.product_lower (BstLean.Part268.WorldRow12955.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12955} (hw : c ∈ Hof BstLean.Part268.WorldRow12955.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12955) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12955) (by norm_num) BstLean.Part268.WorldRow12955.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12955} (hw : c ∈ Hof BstLean.Part268.WorldRow12955.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12955) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12955).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12955) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12955_eq : scalarRow12955.targetFrame = BstLean.Part268.agent12955.frame := by
  norm_num [scalarRow12955,BstLean.Part268.agent12955]

noncomputable def frameData12955 : BstLean.Part264b.FrameData 12955 :=
  BstLean.Part269.frameData_from_numerics (n := 12955) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12955.worldPackage rfl BstLean.Part268.WorldRow12955.product_lower (BstLean.Part268.WorldRow12955.producthi.2.trans (by norm_num))
    scalarRow12955 repair12955 covarianceInputs12955 (fun i hi => sourceNumerics12955 hi)
    BstLean.Part268.agent12955.frame targetFrame12955_eq


end BstLean.Part269.N12955

namespace BstLean.Part269.N12956
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12956 : scalarRow12956.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12956, BstLean.Part268.grid12956, BstLean.Part263.worldGrid]

theorem supplies12956 (j : Fin 43) : Supply 12956 (parameters j)
    (cellLower scalarRow12956.grid (sourceIndex j))
    (cellUpper scalarRow12956.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12956.grid grid_top_bounds12956 j

theorem radii12956 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12956.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12956 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12956 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12956.grid grid_top_bounds12956 j hθ

noncomputable def covarianceInputs12956 :
    BstLean.Part263.CovarianceInputs 12956 scalarRow12956.grid parameters (caps repair12956) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12956 grid_top_bounds12956 repair12956

noncomputable def covarianceEvent12956 : Set (AgFam 12956) :=
  BstLean.Part263.covarianceEvent 12956 scalarRow12956.grid parameters

theorem covarianceEvent12956_measurable : MeasurableSet covarianceEvent12956 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12956_payment :
    (retDist (paperDesignP 12956).toCentres).real
      (agentEv (paperDesignP 12956) covarianceEvent12956)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12956

theorem localCov12956 : BstLean.Part259.LocalCovarianceOn covarianceEvent12956
    (BstLean.Part263.cell scalarRow12956.grid) (caps repair12956) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12956

theorem covarianceGood12956_payment :
    (retDist (paperDesignP 12956).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12956)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12956_payment



end BstLean.Part269.N12956

namespace BstLean.Part269.N12956
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12956}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12956.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12956) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12956).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12956 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12956) (by norm_num) BstLean.Part268.WorldRow12956.worldPackage rfl
    BstLean.Part268.WorldRow12956.product_lower (BstLean.Part268.WorldRow12956.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12956} (hw : c ∈ Hof BstLean.Part268.WorldRow12956.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12956) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12956) (by norm_num) BstLean.Part268.WorldRow12956.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12956} (hw : c ∈ Hof BstLean.Part268.WorldRow12956.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12956) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12956).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12956) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12956_eq : scalarRow12956.targetFrame = BstLean.Part268.agent12956.frame := by
  norm_num [scalarRow12956,BstLean.Part268.agent12956]

noncomputable def frameData12956 : BstLean.Part264b.FrameData 12956 :=
  BstLean.Part269.frameData_from_numerics (n := 12956) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12956.worldPackage rfl BstLean.Part268.WorldRow12956.product_lower (BstLean.Part268.WorldRow12956.producthi.2.trans (by norm_num))
    scalarRow12956 repair12956 covarianceInputs12956 (fun i hi => sourceNumerics12956 hi)
    BstLean.Part268.agent12956.frame targetFrame12956_eq


end BstLean.Part269.N12956

namespace BstLean.Part269.N12957
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12957 : scalarRow12957.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12957, BstLean.Part268.grid12957, BstLean.Part263.worldGrid]

theorem supplies12957 (j : Fin 43) : Supply 12957 (parameters j)
    (cellLower scalarRow12957.grid (sourceIndex j))
    (cellUpper scalarRow12957.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12957.grid grid_top_bounds12957 j

theorem radii12957 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12957.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12957 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12957 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12957.grid grid_top_bounds12957 j hθ

noncomputable def covarianceInputs12957 :
    BstLean.Part263.CovarianceInputs 12957 scalarRow12957.grid parameters (caps repair12957) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12957 grid_top_bounds12957 repair12957

noncomputable def covarianceEvent12957 : Set (AgFam 12957) :=
  BstLean.Part263.covarianceEvent 12957 scalarRow12957.grid parameters

theorem covarianceEvent12957_measurable : MeasurableSet covarianceEvent12957 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12957_payment :
    (retDist (paperDesignP 12957).toCentres).real
      (agentEv (paperDesignP 12957) covarianceEvent12957)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12957

theorem localCov12957 : BstLean.Part259.LocalCovarianceOn covarianceEvent12957
    (BstLean.Part263.cell scalarRow12957.grid) (caps repair12957) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12957

theorem covarianceGood12957_payment :
    (retDist (paperDesignP 12957).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12957)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12957_payment



end BstLean.Part269.N12957

namespace BstLean.Part269.N12957
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12957}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12957.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12957) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12957).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12957 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12957) (by norm_num) BstLean.Part268.WorldRow12957.worldPackage rfl
    BstLean.Part268.WorldRow12957.product_lower (BstLean.Part268.WorldRow12957.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12957} (hw : c ∈ Hof BstLean.Part268.WorldRow12957.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12957) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12957) (by norm_num) BstLean.Part268.WorldRow12957.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12957} (hw : c ∈ Hof BstLean.Part268.WorldRow12957.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12957) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12957).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12957) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12957_eq : scalarRow12957.targetFrame = BstLean.Part268.agent12957.frame := by
  norm_num [scalarRow12957,BstLean.Part268.agent12957]

noncomputable def frameData12957 : BstLean.Part264b.FrameData 12957 :=
  BstLean.Part269.frameData_from_numerics (n := 12957) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12957.worldPackage rfl BstLean.Part268.WorldRow12957.product_lower (BstLean.Part268.WorldRow12957.producthi.2.trans (by norm_num))
    scalarRow12957 repair12957 covarianceInputs12957 (fun i hi => sourceNumerics12957 hi)
    BstLean.Part268.agent12957.frame targetFrame12957_eq


end BstLean.Part269.N12957

namespace BstLean.Part269.N12958
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12958 : scalarRow12958.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12958, BstLean.Part268.grid12958, BstLean.Part263.worldGrid]

theorem supplies12958 (j : Fin 43) : Supply 12958 (parameters j)
    (cellLower scalarRow12958.grid (sourceIndex j))
    (cellUpper scalarRow12958.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12958.grid grid_top_bounds12958 j

theorem radii12958 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12958.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12958 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12958 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12958.grid grid_top_bounds12958 j hθ

noncomputable def covarianceInputs12958 :
    BstLean.Part263.CovarianceInputs 12958 scalarRow12958.grid parameters (caps repair12958) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12958 grid_top_bounds12958 repair12958

noncomputable def covarianceEvent12958 : Set (AgFam 12958) :=
  BstLean.Part263.covarianceEvent 12958 scalarRow12958.grid parameters

theorem covarianceEvent12958_measurable : MeasurableSet covarianceEvent12958 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12958_payment :
    (retDist (paperDesignP 12958).toCentres).real
      (agentEv (paperDesignP 12958) covarianceEvent12958)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12958

theorem localCov12958 : BstLean.Part259.LocalCovarianceOn covarianceEvent12958
    (BstLean.Part263.cell scalarRow12958.grid) (caps repair12958) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12958

theorem covarianceGood12958_payment :
    (retDist (paperDesignP 12958).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12958)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12958_payment



end BstLean.Part269.N12958

namespace BstLean.Part269.N12958
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12958}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12958.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12958) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12958).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12958 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12958) (by norm_num) BstLean.Part268.WorldRow12958.worldPackage rfl
    BstLean.Part268.WorldRow12958.product_lower (BstLean.Part268.WorldRow12958.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12958} (hw : c ∈ Hof BstLean.Part268.WorldRow12958.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12958) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12958) (by norm_num) BstLean.Part268.WorldRow12958.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12958} (hw : c ∈ Hof BstLean.Part268.WorldRow12958.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12958) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12958).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12958) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12958_eq : scalarRow12958.targetFrame = BstLean.Part268.agent12958.frame := by
  norm_num [scalarRow12958,BstLean.Part268.agent12958]

noncomputable def frameData12958 : BstLean.Part264b.FrameData 12958 :=
  BstLean.Part269.frameData_from_numerics (n := 12958) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12958.worldPackage rfl BstLean.Part268.WorldRow12958.product_lower (BstLean.Part268.WorldRow12958.producthi.2.trans (by norm_num))
    scalarRow12958 repair12958 covarianceInputs12958 (fun i hi => sourceNumerics12958 hi)
    BstLean.Part268.agent12958.frame targetFrame12958_eq


end BstLean.Part269.N12958

namespace BstLean.Part269.N12959
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12959 : scalarRow12959.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12959, BstLean.Part268.grid12959, BstLean.Part263.worldGrid]

theorem supplies12959 (j : Fin 43) : Supply 12959 (parameters j)
    (cellLower scalarRow12959.grid (sourceIndex j))
    (cellUpper scalarRow12959.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12959.grid grid_top_bounds12959 j

theorem radii12959 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12959.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12959 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12959 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12959.grid grid_top_bounds12959 j hθ

noncomputable def covarianceInputs12959 :
    BstLean.Part263.CovarianceInputs 12959 scalarRow12959.grid parameters (caps repair12959) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12959 grid_top_bounds12959 repair12959

noncomputable def covarianceEvent12959 : Set (AgFam 12959) :=
  BstLean.Part263.covarianceEvent 12959 scalarRow12959.grid parameters

theorem covarianceEvent12959_measurable : MeasurableSet covarianceEvent12959 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12959_payment :
    (retDist (paperDesignP 12959).toCentres).real
      (agentEv (paperDesignP 12959) covarianceEvent12959)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12959

theorem localCov12959 : BstLean.Part259.LocalCovarianceOn covarianceEvent12959
    (BstLean.Part263.cell scalarRow12959.grid) (caps repair12959) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12959

theorem covarianceGood12959_payment :
    (retDist (paperDesignP 12959).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12959)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12959_payment



end BstLean.Part269.N12959

namespace BstLean.Part269.N12959
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12959}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12959.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12959) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12959).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12959 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12959) (by norm_num) BstLean.Part268.WorldRow12959.worldPackage rfl
    BstLean.Part268.WorldRow12959.product_lower (BstLean.Part268.WorldRow12959.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12959} (hw : c ∈ Hof BstLean.Part268.WorldRow12959.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12959) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12959) (by norm_num) BstLean.Part268.WorldRow12959.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12959} (hw : c ∈ Hof BstLean.Part268.WorldRow12959.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12959) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12959).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12959) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12959_eq : scalarRow12959.targetFrame = BstLean.Part268.agent12959.frame := by
  norm_num [scalarRow12959,BstLean.Part268.agent12959]

noncomputable def frameData12959 : BstLean.Part264b.FrameData 12959 :=
  BstLean.Part269.frameData_from_numerics (n := 12959) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12959.worldPackage rfl BstLean.Part268.WorldRow12959.product_lower (BstLean.Part268.WorldRow12959.producthi.2.trans (by norm_num))
    scalarRow12959 repair12959 covarianceInputs12959 (fun i hi => sourceNumerics12959 hi)
    BstLean.Part268.agent12959.frame targetFrame12959_eq


end BstLean.Part269.N12959
