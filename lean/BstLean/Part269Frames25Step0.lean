import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World25Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs25
import BstLean.Part269Rows25
import BstLean.Part269Sources25
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12975
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12975 : scalarRow12975.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12975, BstLean.Part268.grid12975, BstLean.Part263.worldGrid]

theorem supplies12975 (j : Fin 43) : Supply 12975 (parameters j)
    (cellLower scalarRow12975.grid (sourceIndex j))
    (cellUpper scalarRow12975.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12975.grid grid_top_bounds12975 j

theorem radii12975 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12975.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12975 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12975 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12975.grid grid_top_bounds12975 j hθ

noncomputable def covarianceInputs12975 :
    BstLean.Part263.CovarianceInputs 12975 scalarRow12975.grid parameters (caps repair12975) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12975 grid_top_bounds12975 repair12975

noncomputable def covarianceEvent12975 : Set (AgFam 12975) :=
  BstLean.Part263.covarianceEvent 12975 scalarRow12975.grid parameters

theorem covarianceEvent12975_measurable : MeasurableSet covarianceEvent12975 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12975_payment :
    (retDist (paperDesignP 12975).toCentres).real
      (agentEv (paperDesignP 12975) covarianceEvent12975)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12975

theorem localCov12975 : BstLean.Part259.LocalCovarianceOn covarianceEvent12975
    (BstLean.Part263.cell scalarRow12975.grid) (caps repair12975) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12975

theorem covarianceGood12975_payment :
    (retDist (paperDesignP 12975).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12975)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12975_payment



end BstLean.Part269.N12975

namespace BstLean.Part269.N12975
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12975}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12975.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12975) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12975).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12975 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12975) (by norm_num) BstLean.Part268.WorldRow12975.worldPackage rfl
    BstLean.Part268.WorldRow12975.product_lower (BstLean.Part268.WorldRow12975.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12975} (hw : c ∈ Hof BstLean.Part268.WorldRow12975.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12975) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12975) (by norm_num) BstLean.Part268.WorldRow12975.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12975} (hw : c ∈ Hof BstLean.Part268.WorldRow12975.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12975) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12975).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12975) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12975_eq : scalarRow12975.targetFrame = BstLean.Part268.agent12975.frame := by
  norm_num [scalarRow12975,BstLean.Part268.agent12975]

noncomputable def frameData12975 : BstLean.Part264b.FrameData 12975 :=
  BstLean.Part269.frameData_from_numerics (n := 12975) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12975.worldPackage rfl BstLean.Part268.WorldRow12975.product_lower (BstLean.Part268.WorldRow12975.producthi.2.trans (by norm_num))
    scalarRow12975 repair12975 covarianceInputs12975 (fun i hi => sourceNumerics12975 hi)
    BstLean.Part268.agent12975.frame targetFrame12975_eq


end BstLean.Part269.N12975

namespace BstLean.Part269.N12976
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12976 : scalarRow12976.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12976, BstLean.Part268.grid12976, BstLean.Part263.worldGrid]

theorem supplies12976 (j : Fin 43) : Supply 12976 (parameters j)
    (cellLower scalarRow12976.grid (sourceIndex j))
    (cellUpper scalarRow12976.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12976.grid grid_top_bounds12976 j

theorem radii12976 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12976.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12976 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12976 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12976.grid grid_top_bounds12976 j hθ

noncomputable def covarianceInputs12976 :
    BstLean.Part263.CovarianceInputs 12976 scalarRow12976.grid parameters (caps repair12976) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12976 grid_top_bounds12976 repair12976

noncomputable def covarianceEvent12976 : Set (AgFam 12976) :=
  BstLean.Part263.covarianceEvent 12976 scalarRow12976.grid parameters

theorem covarianceEvent12976_measurable : MeasurableSet covarianceEvent12976 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12976_payment :
    (retDist (paperDesignP 12976).toCentres).real
      (agentEv (paperDesignP 12976) covarianceEvent12976)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12976

theorem localCov12976 : BstLean.Part259.LocalCovarianceOn covarianceEvent12976
    (BstLean.Part263.cell scalarRow12976.grid) (caps repair12976) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12976

theorem covarianceGood12976_payment :
    (retDist (paperDesignP 12976).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12976)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12976_payment



end BstLean.Part269.N12976

namespace BstLean.Part269.N12976
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12976}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12976.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12976) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12976).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12976 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12976) (by norm_num) BstLean.Part268.WorldRow12976.worldPackage rfl
    BstLean.Part268.WorldRow12976.product_lower (BstLean.Part268.WorldRow12976.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12976} (hw : c ∈ Hof BstLean.Part268.WorldRow12976.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12976) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12976) (by norm_num) BstLean.Part268.WorldRow12976.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12976} (hw : c ∈ Hof BstLean.Part268.WorldRow12976.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12976) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12976).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12976) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12976_eq : scalarRow12976.targetFrame = BstLean.Part268.agent12976.frame := by
  norm_num [scalarRow12976,BstLean.Part268.agent12976]

noncomputable def frameData12976 : BstLean.Part264b.FrameData 12976 :=
  BstLean.Part269.frameData_from_numerics (n := 12976) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12976.worldPackage rfl BstLean.Part268.WorldRow12976.product_lower (BstLean.Part268.WorldRow12976.producthi.2.trans (by norm_num))
    scalarRow12976 repair12976 covarianceInputs12976 (fun i hi => sourceNumerics12976 hi)
    BstLean.Part268.agent12976.frame targetFrame12976_eq


end BstLean.Part269.N12976

namespace BstLean.Part269.N12977
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12977 : scalarRow12977.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12977, BstLean.Part268.grid12977, BstLean.Part263.worldGrid]

theorem supplies12977 (j : Fin 43) : Supply 12977 (parameters j)
    (cellLower scalarRow12977.grid (sourceIndex j))
    (cellUpper scalarRow12977.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12977.grid grid_top_bounds12977 j

theorem radii12977 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12977.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12977 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12977 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12977.grid grid_top_bounds12977 j hθ

noncomputable def covarianceInputs12977 :
    BstLean.Part263.CovarianceInputs 12977 scalarRow12977.grid parameters (caps repair12977) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12977 grid_top_bounds12977 repair12977

noncomputable def covarianceEvent12977 : Set (AgFam 12977) :=
  BstLean.Part263.covarianceEvent 12977 scalarRow12977.grid parameters

theorem covarianceEvent12977_measurable : MeasurableSet covarianceEvent12977 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12977_payment :
    (retDist (paperDesignP 12977).toCentres).real
      (agentEv (paperDesignP 12977) covarianceEvent12977)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12977

theorem localCov12977 : BstLean.Part259.LocalCovarianceOn covarianceEvent12977
    (BstLean.Part263.cell scalarRow12977.grid) (caps repair12977) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12977

theorem covarianceGood12977_payment :
    (retDist (paperDesignP 12977).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12977)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12977_payment



end BstLean.Part269.N12977

namespace BstLean.Part269.N12977
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12977}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12977.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12977) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12977).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12977 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12977) (by norm_num) BstLean.Part268.WorldRow12977.worldPackage rfl
    BstLean.Part268.WorldRow12977.product_lower (BstLean.Part268.WorldRow12977.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12977} (hw : c ∈ Hof BstLean.Part268.WorldRow12977.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12977) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12977) (by norm_num) BstLean.Part268.WorldRow12977.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12977} (hw : c ∈ Hof BstLean.Part268.WorldRow12977.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12977) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12977).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12977) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12977_eq : scalarRow12977.targetFrame = BstLean.Part268.agent12977.frame := by
  norm_num [scalarRow12977,BstLean.Part268.agent12977]

noncomputable def frameData12977 : BstLean.Part264b.FrameData 12977 :=
  BstLean.Part269.frameData_from_numerics (n := 12977) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12977.worldPackage rfl BstLean.Part268.WorldRow12977.product_lower (BstLean.Part268.WorldRow12977.producthi.2.trans (by norm_num))
    scalarRow12977 repair12977 covarianceInputs12977 (fun i hi => sourceNumerics12977 hi)
    BstLean.Part268.agent12977.frame targetFrame12977_eq


end BstLean.Part269.N12977

namespace BstLean.Part269.N12978
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12978 : scalarRow12978.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12978, BstLean.Part268.grid12978, BstLean.Part263.worldGrid]

theorem supplies12978 (j : Fin 43) : Supply 12978 (parameters j)
    (cellLower scalarRow12978.grid (sourceIndex j))
    (cellUpper scalarRow12978.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12978.grid grid_top_bounds12978 j

theorem radii12978 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12978.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12978 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12978 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12978.grid grid_top_bounds12978 j hθ

noncomputable def covarianceInputs12978 :
    BstLean.Part263.CovarianceInputs 12978 scalarRow12978.grid parameters (caps repair12978) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12978 grid_top_bounds12978 repair12978

noncomputable def covarianceEvent12978 : Set (AgFam 12978) :=
  BstLean.Part263.covarianceEvent 12978 scalarRow12978.grid parameters

theorem covarianceEvent12978_measurable : MeasurableSet covarianceEvent12978 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12978_payment :
    (retDist (paperDesignP 12978).toCentres).real
      (agentEv (paperDesignP 12978) covarianceEvent12978)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12978

theorem localCov12978 : BstLean.Part259.LocalCovarianceOn covarianceEvent12978
    (BstLean.Part263.cell scalarRow12978.grid) (caps repair12978) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12978

theorem covarianceGood12978_payment :
    (retDist (paperDesignP 12978).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12978)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12978_payment



end BstLean.Part269.N12978

namespace BstLean.Part269.N12978
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12978}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12978.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12978) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12978).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12978 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12978) (by norm_num) BstLean.Part268.WorldRow12978.worldPackage rfl
    BstLean.Part268.WorldRow12978.product_lower (BstLean.Part268.WorldRow12978.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12978} (hw : c ∈ Hof BstLean.Part268.WorldRow12978.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12978) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12978) (by norm_num) BstLean.Part268.WorldRow12978.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12978} (hw : c ∈ Hof BstLean.Part268.WorldRow12978.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12978) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12978).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12978) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12978_eq : scalarRow12978.targetFrame = BstLean.Part268.agent12978.frame := by
  norm_num [scalarRow12978,BstLean.Part268.agent12978]

noncomputable def frameData12978 : BstLean.Part264b.FrameData 12978 :=
  BstLean.Part269.frameData_from_numerics (n := 12978) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12978.worldPackage rfl BstLean.Part268.WorldRow12978.product_lower (BstLean.Part268.WorldRow12978.producthi.2.trans (by norm_num))
    scalarRow12978 repair12978 covarianceInputs12978 (fun i hi => sourceNumerics12978 hi)
    BstLean.Part268.agent12978.frame targetFrame12978_eq


end BstLean.Part269.N12978

namespace BstLean.Part269.N12979
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12979 : scalarRow12979.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12979, BstLean.Part268.grid12979, BstLean.Part263.worldGrid]

theorem supplies12979 (j : Fin 43) : Supply 12979 (parameters j)
    (cellLower scalarRow12979.grid (sourceIndex j))
    (cellUpper scalarRow12979.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12979.grid grid_top_bounds12979 j

theorem radii12979 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12979.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12979 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12979 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12979.grid grid_top_bounds12979 j hθ

noncomputable def covarianceInputs12979 :
    BstLean.Part263.CovarianceInputs 12979 scalarRow12979.grid parameters (caps repair12979) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12979 grid_top_bounds12979 repair12979

noncomputable def covarianceEvent12979 : Set (AgFam 12979) :=
  BstLean.Part263.covarianceEvent 12979 scalarRow12979.grid parameters

theorem covarianceEvent12979_measurable : MeasurableSet covarianceEvent12979 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12979_payment :
    (retDist (paperDesignP 12979).toCentres).real
      (agentEv (paperDesignP 12979) covarianceEvent12979)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12979

theorem localCov12979 : BstLean.Part259.LocalCovarianceOn covarianceEvent12979
    (BstLean.Part263.cell scalarRow12979.grid) (caps repair12979) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12979

theorem covarianceGood12979_payment :
    (retDist (paperDesignP 12979).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12979)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12979_payment



end BstLean.Part269.N12979

namespace BstLean.Part269.N12979
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12979}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12979.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12979) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12979).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12979 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12979) (by norm_num) BstLean.Part268.WorldRow12979.worldPackage rfl
    BstLean.Part268.WorldRow12979.product_lower (BstLean.Part268.WorldRow12979.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12979} (hw : c ∈ Hof BstLean.Part268.WorldRow12979.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12979) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12979) (by norm_num) BstLean.Part268.WorldRow12979.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12979} (hw : c ∈ Hof BstLean.Part268.WorldRow12979.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12979) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12979).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12979) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12979_eq : scalarRow12979.targetFrame = BstLean.Part268.agent12979.frame := by
  norm_num [scalarRow12979,BstLean.Part268.agent12979]

noncomputable def frameData12979 : BstLean.Part264b.FrameData 12979 :=
  BstLean.Part269.frameData_from_numerics (n := 12979) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12979.worldPackage rfl BstLean.Part268.WorldRow12979.product_lower (BstLean.Part268.WorldRow12979.producthi.2.trans (by norm_num))
    scalarRow12979 repair12979 covarianceInputs12979 (fun i hi => sourceNumerics12979 hi)
    BstLean.Part268.agent12979.frame targetFrame12979_eq


end BstLean.Part269.N12979
