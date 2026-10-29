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

namespace BstLean.Part269.N12950
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12950 : scalarRow12950.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12950, BstLean.Part268.grid12950, BstLean.Part263.worldGrid]

theorem supplies12950 (j : Fin 43) : Supply 12950 (parameters j)
    (cellLower scalarRow12950.grid (sourceIndex j))
    (cellUpper scalarRow12950.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12950.grid grid_top_bounds12950 j

theorem radii12950 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12950.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12950 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12950 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12950.grid grid_top_bounds12950 j hθ

noncomputable def covarianceInputs12950 :
    BstLean.Part263.CovarianceInputs 12950 scalarRow12950.grid parameters (caps repair12950) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12950 grid_top_bounds12950 repair12950

noncomputable def covarianceEvent12950 : Set (AgFam 12950) :=
  BstLean.Part263.covarianceEvent 12950 scalarRow12950.grid parameters

theorem covarianceEvent12950_measurable : MeasurableSet covarianceEvent12950 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12950_payment :
    (retDist (paperDesignP 12950).toCentres).real
      (agentEv (paperDesignP 12950) covarianceEvent12950)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12950

theorem localCov12950 : BstLean.Part259.LocalCovarianceOn covarianceEvent12950
    (BstLean.Part263.cell scalarRow12950.grid) (caps repair12950) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12950

theorem covarianceGood12950_payment :
    (retDist (paperDesignP 12950).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12950)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12950_payment



end BstLean.Part269.N12950

namespace BstLean.Part269.N12950
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12950}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12950.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12950) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12950).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12950 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12950) (by norm_num) BstLean.Part268.WorldRow12950.worldPackage rfl
    BstLean.Part268.WorldRow12950.product_lower (BstLean.Part268.WorldRow12950.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12950} (hw : c ∈ Hof BstLean.Part268.WorldRow12950.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12950) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12950) (by norm_num) BstLean.Part268.WorldRow12950.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12950} (hw : c ∈ Hof BstLean.Part268.WorldRow12950.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12950) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12950).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12950) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12950_eq : scalarRow12950.targetFrame = BstLean.Part268.agent12950.frame := by
  norm_num [scalarRow12950,BstLean.Part268.agent12950]

noncomputable def frameData12950 : BstLean.Part264b.FrameData 12950 :=
  BstLean.Part269.frameData_from_numerics (n := 12950) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12950.worldPackage rfl BstLean.Part268.WorldRow12950.product_lower (BstLean.Part268.WorldRow12950.producthi.2.trans (by norm_num))
    scalarRow12950 repair12950 covarianceInputs12950 (fun i hi => sourceNumerics12950 hi)
    BstLean.Part268.agent12950.frame targetFrame12950_eq


end BstLean.Part269.N12950

namespace BstLean.Part269.N12951
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12951 : scalarRow12951.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12951, BstLean.Part268.grid12951, BstLean.Part263.worldGrid]

theorem supplies12951 (j : Fin 43) : Supply 12951 (parameters j)
    (cellLower scalarRow12951.grid (sourceIndex j))
    (cellUpper scalarRow12951.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12951.grid grid_top_bounds12951 j

theorem radii12951 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12951.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12951 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12951 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12951.grid grid_top_bounds12951 j hθ

noncomputable def covarianceInputs12951 :
    BstLean.Part263.CovarianceInputs 12951 scalarRow12951.grid parameters (caps repair12951) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12951 grid_top_bounds12951 repair12951

noncomputable def covarianceEvent12951 : Set (AgFam 12951) :=
  BstLean.Part263.covarianceEvent 12951 scalarRow12951.grid parameters

theorem covarianceEvent12951_measurable : MeasurableSet covarianceEvent12951 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12951_payment :
    (retDist (paperDesignP 12951).toCentres).real
      (agentEv (paperDesignP 12951) covarianceEvent12951)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12951

theorem localCov12951 : BstLean.Part259.LocalCovarianceOn covarianceEvent12951
    (BstLean.Part263.cell scalarRow12951.grid) (caps repair12951) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12951

theorem covarianceGood12951_payment :
    (retDist (paperDesignP 12951).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12951)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12951_payment



end BstLean.Part269.N12951

namespace BstLean.Part269.N12951
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12951}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12951.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12951) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12951).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12951 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12951) (by norm_num) BstLean.Part268.WorldRow12951.worldPackage rfl
    BstLean.Part268.WorldRow12951.product_lower (BstLean.Part268.WorldRow12951.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12951} (hw : c ∈ Hof BstLean.Part268.WorldRow12951.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12951) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12951) (by norm_num) BstLean.Part268.WorldRow12951.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12951} (hw : c ∈ Hof BstLean.Part268.WorldRow12951.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12951) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12951).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12951) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12951_eq : scalarRow12951.targetFrame = BstLean.Part268.agent12951.frame := by
  norm_num [scalarRow12951,BstLean.Part268.agent12951]

noncomputable def frameData12951 : BstLean.Part264b.FrameData 12951 :=
  BstLean.Part269.frameData_from_numerics (n := 12951) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12951.worldPackage rfl BstLean.Part268.WorldRow12951.product_lower (BstLean.Part268.WorldRow12951.producthi.2.trans (by norm_num))
    scalarRow12951 repair12951 covarianceInputs12951 (fun i hi => sourceNumerics12951 hi)
    BstLean.Part268.agent12951.frame targetFrame12951_eq


end BstLean.Part269.N12951

namespace BstLean.Part269.N12952
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12952 : scalarRow12952.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12952, BstLean.Part268.grid12952, BstLean.Part263.worldGrid]

theorem supplies12952 (j : Fin 43) : Supply 12952 (parameters j)
    (cellLower scalarRow12952.grid (sourceIndex j))
    (cellUpper scalarRow12952.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12952.grid grid_top_bounds12952 j

theorem radii12952 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12952.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12952 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12952 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12952.grid grid_top_bounds12952 j hθ

noncomputable def covarianceInputs12952 :
    BstLean.Part263.CovarianceInputs 12952 scalarRow12952.grid parameters (caps repair12952) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12952 grid_top_bounds12952 repair12952

noncomputable def covarianceEvent12952 : Set (AgFam 12952) :=
  BstLean.Part263.covarianceEvent 12952 scalarRow12952.grid parameters

theorem covarianceEvent12952_measurable : MeasurableSet covarianceEvent12952 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12952_payment :
    (retDist (paperDesignP 12952).toCentres).real
      (agentEv (paperDesignP 12952) covarianceEvent12952)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12952

theorem localCov12952 : BstLean.Part259.LocalCovarianceOn covarianceEvent12952
    (BstLean.Part263.cell scalarRow12952.grid) (caps repair12952) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12952

theorem covarianceGood12952_payment :
    (retDist (paperDesignP 12952).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12952)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12952_payment



end BstLean.Part269.N12952

namespace BstLean.Part269.N12952
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12952}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12952.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12952) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12952).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12952 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12952) (by norm_num) BstLean.Part268.WorldRow12952.worldPackage rfl
    BstLean.Part268.WorldRow12952.product_lower (BstLean.Part268.WorldRow12952.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12952} (hw : c ∈ Hof BstLean.Part268.WorldRow12952.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12952) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12952) (by norm_num) BstLean.Part268.WorldRow12952.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12952} (hw : c ∈ Hof BstLean.Part268.WorldRow12952.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12952) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12952).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12952) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12952_eq : scalarRow12952.targetFrame = BstLean.Part268.agent12952.frame := by
  norm_num [scalarRow12952,BstLean.Part268.agent12952]

noncomputable def frameData12952 : BstLean.Part264b.FrameData 12952 :=
  BstLean.Part269.frameData_from_numerics (n := 12952) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12952.worldPackage rfl BstLean.Part268.WorldRow12952.product_lower (BstLean.Part268.WorldRow12952.producthi.2.trans (by norm_num))
    scalarRow12952 repair12952 covarianceInputs12952 (fun i hi => sourceNumerics12952 hi)
    BstLean.Part268.agent12952.frame targetFrame12952_eq


end BstLean.Part269.N12952

namespace BstLean.Part269.N12953
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12953 : scalarRow12953.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12953, BstLean.Part268.grid12953, BstLean.Part263.worldGrid]

theorem supplies12953 (j : Fin 43) : Supply 12953 (parameters j)
    (cellLower scalarRow12953.grid (sourceIndex j))
    (cellUpper scalarRow12953.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12953.grid grid_top_bounds12953 j

theorem radii12953 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12953.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12953 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12953 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12953.grid grid_top_bounds12953 j hθ

noncomputable def covarianceInputs12953 :
    BstLean.Part263.CovarianceInputs 12953 scalarRow12953.grid parameters (caps repair12953) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12953 grid_top_bounds12953 repair12953

noncomputable def covarianceEvent12953 : Set (AgFam 12953) :=
  BstLean.Part263.covarianceEvent 12953 scalarRow12953.grid parameters

theorem covarianceEvent12953_measurable : MeasurableSet covarianceEvent12953 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12953_payment :
    (retDist (paperDesignP 12953).toCentres).real
      (agentEv (paperDesignP 12953) covarianceEvent12953)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12953

theorem localCov12953 : BstLean.Part259.LocalCovarianceOn covarianceEvent12953
    (BstLean.Part263.cell scalarRow12953.grid) (caps repair12953) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12953

theorem covarianceGood12953_payment :
    (retDist (paperDesignP 12953).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12953)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12953_payment



end BstLean.Part269.N12953

namespace BstLean.Part269.N12953
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12953}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12953.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12953) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12953).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12953 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12953) (by norm_num) BstLean.Part268.WorldRow12953.worldPackage rfl
    BstLean.Part268.WorldRow12953.product_lower (BstLean.Part268.WorldRow12953.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12953} (hw : c ∈ Hof BstLean.Part268.WorldRow12953.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12953) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12953) (by norm_num) BstLean.Part268.WorldRow12953.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12953} (hw : c ∈ Hof BstLean.Part268.WorldRow12953.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12953) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12953).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12953) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12953_eq : scalarRow12953.targetFrame = BstLean.Part268.agent12953.frame := by
  norm_num [scalarRow12953,BstLean.Part268.agent12953]

noncomputable def frameData12953 : BstLean.Part264b.FrameData 12953 :=
  BstLean.Part269.frameData_from_numerics (n := 12953) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12953.worldPackage rfl BstLean.Part268.WorldRow12953.product_lower (BstLean.Part268.WorldRow12953.producthi.2.trans (by norm_num))
    scalarRow12953 repair12953 covarianceInputs12953 (fun i hi => sourceNumerics12953 hi)
    BstLean.Part268.agent12953.frame targetFrame12953_eq


end BstLean.Part269.N12953

namespace BstLean.Part269.N12954
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12954 : scalarRow12954.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12954, BstLean.Part268.grid12954, BstLean.Part263.worldGrid]

theorem supplies12954 (j : Fin 43) : Supply 12954 (parameters j)
    (cellLower scalarRow12954.grid (sourceIndex j))
    (cellUpper scalarRow12954.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12954.grid grid_top_bounds12954 j

theorem radii12954 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12954.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12954 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12954 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12954.grid grid_top_bounds12954 j hθ

noncomputable def covarianceInputs12954 :
    BstLean.Part263.CovarianceInputs 12954 scalarRow12954.grid parameters (caps repair12954) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12954 grid_top_bounds12954 repair12954

noncomputable def covarianceEvent12954 : Set (AgFam 12954) :=
  BstLean.Part263.covarianceEvent 12954 scalarRow12954.grid parameters

theorem covarianceEvent12954_measurable : MeasurableSet covarianceEvent12954 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12954_payment :
    (retDist (paperDesignP 12954).toCentres).real
      (agentEv (paperDesignP 12954) covarianceEvent12954)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12954

theorem localCov12954 : BstLean.Part259.LocalCovarianceOn covarianceEvent12954
    (BstLean.Part263.cell scalarRow12954.grid) (caps repair12954) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12954

theorem covarianceGood12954_payment :
    (retDist (paperDesignP 12954).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12954)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12954_payment



end BstLean.Part269.N12954

namespace BstLean.Part269.N12954
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12954}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12954.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12954) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12954).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12954 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12954) (by norm_num) BstLean.Part268.WorldRow12954.worldPackage rfl
    BstLean.Part268.WorldRow12954.product_lower (BstLean.Part268.WorldRow12954.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12954} (hw : c ∈ Hof BstLean.Part268.WorldRow12954.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12954) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12954) (by norm_num) BstLean.Part268.WorldRow12954.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12954} (hw : c ∈ Hof BstLean.Part268.WorldRow12954.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12954) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12954).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12954) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12954_eq : scalarRow12954.targetFrame = BstLean.Part268.agent12954.frame := by
  norm_num [scalarRow12954,BstLean.Part268.agent12954]

noncomputable def frameData12954 : BstLean.Part264b.FrameData 12954 :=
  BstLean.Part269.frameData_from_numerics (n := 12954) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12954.worldPackage rfl BstLean.Part268.WorldRow12954.product_lower (BstLean.Part268.WorldRow12954.producthi.2.trans (by norm_num))
    scalarRow12954 repair12954 covarianceInputs12954 (fun i hi => sourceNumerics12954 hi)
    BstLean.Part268.agent12954.frame targetFrame12954_eq


end BstLean.Part269.N12954
