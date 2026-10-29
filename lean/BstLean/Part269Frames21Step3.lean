import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World21Step6
import BstLean.Part269BlockSupplies2
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs21
import BstLean.Part269Rows21
import BstLean.Part269Sources21
import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1

namespace BstLean.Part269.N12890
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12890 : scalarRow12890.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12890, BstLean.Part268.grid12890, BstLean.Part263.worldGrid]

theorem supplies12890 (j : Fin 43) : Supply 12890 (parameters j)
    (cellLower scalarRow12890.grid (sourceIndex j))
    (cellUpper scalarRow12890.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12890.grid grid_top_bounds12890 j

theorem radii12890 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12890.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12890 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12890 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12890.grid grid_top_bounds12890 j hθ

noncomputable def covarianceInputs12890 :
    BstLean.Part263.CovarianceInputs 12890 scalarRow12890.grid parameters (caps repair12890) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12890 grid_top_bounds12890 repair12890

noncomputable def covarianceEvent12890 : Set (AgFam 12890) :=
  BstLean.Part263.covarianceEvent 12890 scalarRow12890.grid parameters

theorem covarianceEvent12890_measurable : MeasurableSet covarianceEvent12890 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12890_payment :
    (retDist (paperDesignP 12890).toCentres).real
      (agentEv (paperDesignP 12890) covarianceEvent12890)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12890

theorem localCov12890 : BstLean.Part259.LocalCovarianceOn covarianceEvent12890
    (BstLean.Part263.cell scalarRow12890.grid) (caps repair12890) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12890

theorem covarianceGood12890_payment :
    (retDist (paperDesignP 12890).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12890)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12890_payment



end BstLean.Part269.N12890

namespace BstLean.Part269.N12890
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12890}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12890.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12890) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12890).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12890 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12890) (by norm_num) BstLean.Part268.WorldRow12890.worldPackage rfl
    BstLean.Part268.WorldRow12890.product_lower (BstLean.Part268.WorldRow12890.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12890} (hw : c ∈ Hof BstLean.Part268.WorldRow12890.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12890) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12890) (by norm_num) BstLean.Part268.WorldRow12890.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12890} (hw : c ∈ Hof BstLean.Part268.WorldRow12890.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12890) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12890).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12890) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12890_eq : scalarRow12890.targetFrame = BstLean.Part268.agent12890.frame := by
  norm_num [scalarRow12890,BstLean.Part268.agent12890]

noncomputable def frameData12890 : BstLean.Part264b.FrameData 12890 :=
  BstLean.Part269.frameData_from_numerics (n := 12890) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12890.worldPackage rfl BstLean.Part268.WorldRow12890.product_lower (BstLean.Part268.WorldRow12890.producthi.2.trans (by norm_num))
    scalarRow12890 repair12890 covarianceInputs12890 (fun i hi => sourceNumerics12890 hi)
    BstLean.Part268.agent12890.frame targetFrame12890_eq


end BstLean.Part269.N12890

namespace BstLean.Part269.N12891
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12891 : scalarRow12891.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12891, BstLean.Part268.grid12891, BstLean.Part263.worldGrid]

theorem supplies12891 (j : Fin 43) : Supply 12891 (parameters j)
    (cellLower scalarRow12891.grid (sourceIndex j))
    (cellUpper scalarRow12891.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12891.grid grid_top_bounds12891 j

theorem radii12891 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12891.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12891 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12891 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12891.grid grid_top_bounds12891 j hθ

noncomputable def covarianceInputs12891 :
    BstLean.Part263.CovarianceInputs 12891 scalarRow12891.grid parameters (caps repair12891) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12891 grid_top_bounds12891 repair12891

noncomputable def covarianceEvent12891 : Set (AgFam 12891) :=
  BstLean.Part263.covarianceEvent 12891 scalarRow12891.grid parameters

theorem covarianceEvent12891_measurable : MeasurableSet covarianceEvent12891 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12891_payment :
    (retDist (paperDesignP 12891).toCentres).real
      (agentEv (paperDesignP 12891) covarianceEvent12891)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12891

theorem localCov12891 : BstLean.Part259.LocalCovarianceOn covarianceEvent12891
    (BstLean.Part263.cell scalarRow12891.grid) (caps repair12891) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12891

theorem covarianceGood12891_payment :
    (retDist (paperDesignP 12891).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12891)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12891_payment



end BstLean.Part269.N12891

namespace BstLean.Part269.N12891
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12891}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12891.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12891) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12891).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12891 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12891) (by norm_num) BstLean.Part268.WorldRow12891.worldPackage rfl
    BstLean.Part268.WorldRow12891.product_lower (BstLean.Part268.WorldRow12891.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12891} (hw : c ∈ Hof BstLean.Part268.WorldRow12891.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12891) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12891) (by norm_num) BstLean.Part268.WorldRow12891.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12891} (hw : c ∈ Hof BstLean.Part268.WorldRow12891.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12891) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12891).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12891) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12891_eq : scalarRow12891.targetFrame = BstLean.Part268.agent12891.frame := by
  norm_num [scalarRow12891,BstLean.Part268.agent12891]

noncomputable def frameData12891 : BstLean.Part264b.FrameData 12891 :=
  BstLean.Part269.frameData_from_numerics (n := 12891) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12891.worldPackage rfl BstLean.Part268.WorldRow12891.product_lower (BstLean.Part268.WorldRow12891.producthi.2.trans (by norm_num))
    scalarRow12891 repair12891 covarianceInputs12891 (fun i hi => sourceNumerics12891 hi)
    BstLean.Part268.agent12891.frame targetFrame12891_eq


end BstLean.Part269.N12891

namespace BstLean.Part269.N12892
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12892 : scalarRow12892.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12892, BstLean.Part268.grid12892, BstLean.Part263.worldGrid]

theorem supplies12892 (j : Fin 43) : Supply 12892 (parameters j)
    (cellLower scalarRow12892.grid (sourceIndex j))
    (cellUpper scalarRow12892.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12892.grid grid_top_bounds12892 j

theorem radii12892 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12892.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12892 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12892 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12892.grid grid_top_bounds12892 j hθ

noncomputable def covarianceInputs12892 :
    BstLean.Part263.CovarianceInputs 12892 scalarRow12892.grid parameters (caps repair12892) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12892 grid_top_bounds12892 repair12892

noncomputable def covarianceEvent12892 : Set (AgFam 12892) :=
  BstLean.Part263.covarianceEvent 12892 scalarRow12892.grid parameters

theorem covarianceEvent12892_measurable : MeasurableSet covarianceEvent12892 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12892_payment :
    (retDist (paperDesignP 12892).toCentres).real
      (agentEv (paperDesignP 12892) covarianceEvent12892)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12892

theorem localCov12892 : BstLean.Part259.LocalCovarianceOn covarianceEvent12892
    (BstLean.Part263.cell scalarRow12892.grid) (caps repair12892) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12892

theorem covarianceGood12892_payment :
    (retDist (paperDesignP 12892).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12892)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12892_payment



end BstLean.Part269.N12892

namespace BstLean.Part269.N12892
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12892}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12892.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12892) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12892).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12892 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12892) (by norm_num) BstLean.Part268.WorldRow12892.worldPackage rfl
    BstLean.Part268.WorldRow12892.product_lower (BstLean.Part268.WorldRow12892.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12892} (hw : c ∈ Hof BstLean.Part268.WorldRow12892.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12892) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12892) (by norm_num) BstLean.Part268.WorldRow12892.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12892} (hw : c ∈ Hof BstLean.Part268.WorldRow12892.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12892) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12892).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12892) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12892_eq : scalarRow12892.targetFrame = BstLean.Part268.agent12892.frame := by
  norm_num [scalarRow12892,BstLean.Part268.agent12892]

noncomputable def frameData12892 : BstLean.Part264b.FrameData 12892 :=
  BstLean.Part269.frameData_from_numerics (n := 12892) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12892.worldPackage rfl BstLean.Part268.WorldRow12892.product_lower (BstLean.Part268.WorldRow12892.producthi.2.trans (by norm_num))
    scalarRow12892 repair12892 covarianceInputs12892 (fun i hi => sourceNumerics12892 hi)
    BstLean.Part268.agent12892.frame targetFrame12892_eq


end BstLean.Part269.N12892

namespace BstLean.Part269.N12893
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12893 : scalarRow12893.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12893, BstLean.Part268.grid12893, BstLean.Part263.worldGrid]

theorem supplies12893 (j : Fin 43) : Supply 12893 (parameters j)
    (cellLower scalarRow12893.grid (sourceIndex j))
    (cellUpper scalarRow12893.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12893.grid grid_top_bounds12893 j

theorem radii12893 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12893.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12893 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12893 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12893.grid grid_top_bounds12893 j hθ

noncomputable def covarianceInputs12893 :
    BstLean.Part263.CovarianceInputs 12893 scalarRow12893.grid parameters (caps repair12893) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12893 grid_top_bounds12893 repair12893

noncomputable def covarianceEvent12893 : Set (AgFam 12893) :=
  BstLean.Part263.covarianceEvent 12893 scalarRow12893.grid parameters

theorem covarianceEvent12893_measurable : MeasurableSet covarianceEvent12893 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12893_payment :
    (retDist (paperDesignP 12893).toCentres).real
      (agentEv (paperDesignP 12893) covarianceEvent12893)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12893

theorem localCov12893 : BstLean.Part259.LocalCovarianceOn covarianceEvent12893
    (BstLean.Part263.cell scalarRow12893.grid) (caps repair12893) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12893

theorem covarianceGood12893_payment :
    (retDist (paperDesignP 12893).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12893)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12893_payment



end BstLean.Part269.N12893

namespace BstLean.Part269.N12893
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12893}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12893.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12893) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12893).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12893 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12893) (by norm_num) BstLean.Part268.WorldRow12893.worldPackage rfl
    BstLean.Part268.WorldRow12893.product_lower (BstLean.Part268.WorldRow12893.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12893} (hw : c ∈ Hof BstLean.Part268.WorldRow12893.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12893) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12893) (by norm_num) BstLean.Part268.WorldRow12893.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12893} (hw : c ∈ Hof BstLean.Part268.WorldRow12893.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12893) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12893).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12893) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12893_eq : scalarRow12893.targetFrame = BstLean.Part268.agent12893.frame := by
  norm_num [scalarRow12893,BstLean.Part268.agent12893]

noncomputable def frameData12893 : BstLean.Part264b.FrameData 12893 :=
  BstLean.Part269.frameData_from_numerics (n := 12893) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12893.worldPackage rfl BstLean.Part268.WorldRow12893.product_lower (BstLean.Part268.WorldRow12893.producthi.2.trans (by norm_num))
    scalarRow12893 repair12893 covarianceInputs12893 (fun i hi => sourceNumerics12893 hi)
    BstLean.Part268.agent12893.frame targetFrame12893_eq


end BstLean.Part269.N12893

namespace BstLean.Part269.N12894
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12894 : scalarRow12894.grid.top ∈
    Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow12894, BstLean.Part268.grid12894, BstLean.Part263.worldGrid]

theorem supplies12894 (j : Fin 43) : Supply 12894 (parameters j)
    (cellLower scalarRow12894.grid (sourceIndex j))
    (cellUpper scalarRow12894.grid (sourceIndex j)) :=
  BstLean.Part269.BG2.supplies (by constructor <;> norm_num)
    scalarRow12894.grid grid_top_bounds12894 j

theorem radii12894 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12894.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12894 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12894 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG2.radii (by constructor <;> norm_num)
    scalarRow12894.grid grid_top_bounds12894 j hθ

noncomputable def covarianceInputs12894 :
    BstLean.Part263.CovarianceInputs 12894 scalarRow12894.grid parameters (caps repair12894) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num)
    scalarRow12894 grid_top_bounds12894 repair12894

noncomputable def covarianceEvent12894 : Set (AgFam 12894) :=
  BstLean.Part263.covarianceEvent 12894 scalarRow12894.grid parameters

theorem covarianceEvent12894_measurable : MeasurableSet covarianceEvent12894 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12894_payment :
    (retDist (paperDesignP 12894).toCentres).real
      (agentEv (paperDesignP 12894) covarianceEvent12894)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12894

theorem localCov12894 : BstLean.Part259.LocalCovarianceOn covarianceEvent12894
    (BstLean.Part263.cell scalarRow12894.grid) (caps repair12894) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12894

theorem covarianceGood12894_payment :
    (retDist (paperDesignP 12894).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12894)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12894_payment



end BstLean.Part269.N12894

namespace BstLean.Part269.N12894
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12894}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12894.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12894) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12894).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12894 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12894) (by norm_num) BstLean.Part268.WorldRow12894.worldPackage rfl
    BstLean.Part268.WorldRow12894.product_lower (BstLean.Part268.WorldRow12894.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12894} (hw : c ∈ Hof BstLean.Part268.WorldRow12894.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12894) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12894) (by norm_num) BstLean.Part268.WorldRow12894.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12894} (hw : c ∈ Hof BstLean.Part268.WorldRow12894.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12894) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12894).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12894) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12894_eq : scalarRow12894.targetFrame = BstLean.Part268.agent12894.frame := by
  norm_num [scalarRow12894,BstLean.Part268.agent12894]

noncomputable def frameData12894 : BstLean.Part264b.FrameData 12894 :=
  BstLean.Part269.frameData_from_numerics (n := 12894) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12894.worldPackage rfl BstLean.Part268.WorldRow12894.product_lower (BstLean.Part268.WorldRow12894.producthi.2.trans (by norm_num))
    scalarRow12894 repair12894 covarianceInputs12894 (fun i hi => sourceNumerics12894 hi)
    BstLean.Part268.agent12894.frame targetFrame12894_eq


end BstLean.Part269.N12894
