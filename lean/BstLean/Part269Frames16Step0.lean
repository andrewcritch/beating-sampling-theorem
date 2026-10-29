import BstLean.Part264Covariance
import BstLean.Part264bUniformTI
import BstLean.Part268World16Step6
import BstLean.Part269BlockSupplies1
import BstLean.Part269FrameAdapter
import BstLean.Part269Repairs16
import BstLean.Part269Rows16
import BstLean.Part269Sources16
import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1

namespace BstLean.Part269.N12750
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12750 : scalarRow12750.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12750, BstLean.Part268.grid12750, BstLean.Part263.worldGrid]

theorem supplies12750 (j : Fin 43) : Supply 12750 (parameters j)
    (cellLower scalarRow12750.grid (sourceIndex j))
    (cellUpper scalarRow12750.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12750.grid grid_top_bounds12750 j

theorem radii12750 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12750.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12750 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12750 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12750.grid grid_top_bounds12750 j hθ

noncomputable def covarianceInputs12750 :
    BstLean.Part263.CovarianceInputs 12750 scalarRow12750.grid parameters (caps repair12750) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12750 grid_top_bounds12750 repair12750

noncomputable def covarianceEvent12750 : Set (AgFam 12750) :=
  BstLean.Part263.covarianceEvent 12750 scalarRow12750.grid parameters

theorem covarianceEvent12750_measurable : MeasurableSet covarianceEvent12750 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12750_payment :
    (retDist (paperDesignP 12750).toCentres).real
      (agentEv (paperDesignP 12750) covarianceEvent12750)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12750

theorem localCov12750 : BstLean.Part259.LocalCovarianceOn covarianceEvent12750
    (BstLean.Part263.cell scalarRow12750.grid) (caps repair12750) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12750

theorem covarianceGood12750_payment :
    (retDist (paperDesignP 12750).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12750)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12750_payment



end BstLean.Part269.N12750

namespace BstLean.Part269.N12750
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12750}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12750.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12750) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12750).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12750 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12750) (by norm_num) BstLean.Part268.WorldRow12750.worldPackage rfl
    BstLean.Part268.WorldRow12750.product_lower (BstLean.Part268.WorldRow12750.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12750} (hw : c ∈ Hof BstLean.Part268.WorldRow12750.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12750) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12750) (by norm_num) BstLean.Part268.WorldRow12750.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12750} (hw : c ∈ Hof BstLean.Part268.WorldRow12750.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12750) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12750).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12750) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12750_eq : scalarRow12750.targetFrame = BstLean.Part268.agent12750.frame := by
  norm_num [scalarRow12750,BstLean.Part268.agent12750]

noncomputable def frameData12750 : BstLean.Part264b.FrameData 12750 :=
  BstLean.Part269.frameData_from_numerics (n := 12750) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12750.worldPackage rfl BstLean.Part268.WorldRow12750.product_lower (BstLean.Part268.WorldRow12750.producthi.2.trans (by norm_num))
    scalarRow12750 repair12750 covarianceInputs12750 (fun i hi => sourceNumerics12750 hi)
    BstLean.Part268.agent12750.frame targetFrame12750_eq


end BstLean.Part269.N12750

namespace BstLean.Part269.N12751
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12751 : scalarRow12751.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12751, BstLean.Part268.grid12751, BstLean.Part263.worldGrid]

theorem supplies12751 (j : Fin 43) : Supply 12751 (parameters j)
    (cellLower scalarRow12751.grid (sourceIndex j))
    (cellUpper scalarRow12751.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12751.grid grid_top_bounds12751 j

theorem radii12751 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12751.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12751 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12751 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12751.grid grid_top_bounds12751 j hθ

noncomputable def covarianceInputs12751 :
    BstLean.Part263.CovarianceInputs 12751 scalarRow12751.grid parameters (caps repair12751) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12751 grid_top_bounds12751 repair12751

noncomputable def covarianceEvent12751 : Set (AgFam 12751) :=
  BstLean.Part263.covarianceEvent 12751 scalarRow12751.grid parameters

theorem covarianceEvent12751_measurable : MeasurableSet covarianceEvent12751 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12751_payment :
    (retDist (paperDesignP 12751).toCentres).real
      (agentEv (paperDesignP 12751) covarianceEvent12751)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12751

theorem localCov12751 : BstLean.Part259.LocalCovarianceOn covarianceEvent12751
    (BstLean.Part263.cell scalarRow12751.grid) (caps repair12751) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12751

theorem covarianceGood12751_payment :
    (retDist (paperDesignP 12751).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12751)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12751_payment



end BstLean.Part269.N12751

namespace BstLean.Part269.N12751
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12751}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12751.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12751) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12751).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12751 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12751) (by norm_num) BstLean.Part268.WorldRow12751.worldPackage rfl
    BstLean.Part268.WorldRow12751.product_lower (BstLean.Part268.WorldRow12751.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12751} (hw : c ∈ Hof BstLean.Part268.WorldRow12751.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12751) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12751) (by norm_num) BstLean.Part268.WorldRow12751.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12751} (hw : c ∈ Hof BstLean.Part268.WorldRow12751.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12751) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12751).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12751) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12751_eq : scalarRow12751.targetFrame = BstLean.Part268.agent12751.frame := by
  norm_num [scalarRow12751,BstLean.Part268.agent12751]

noncomputable def frameData12751 : BstLean.Part264b.FrameData 12751 :=
  BstLean.Part269.frameData_from_numerics (n := 12751) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12751.worldPackage rfl BstLean.Part268.WorldRow12751.product_lower (BstLean.Part268.WorldRow12751.producthi.2.trans (by norm_num))
    scalarRow12751 repair12751 covarianceInputs12751 (fun i hi => sourceNumerics12751 hi)
    BstLean.Part268.agent12751.frame targetFrame12751_eq


end BstLean.Part269.N12751

namespace BstLean.Part269.N12752
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12752 : scalarRow12752.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12752, BstLean.Part268.grid12752, BstLean.Part263.worldGrid]

theorem supplies12752 (j : Fin 43) : Supply 12752 (parameters j)
    (cellLower scalarRow12752.grid (sourceIndex j))
    (cellUpper scalarRow12752.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12752.grid grid_top_bounds12752 j

theorem radii12752 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12752.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12752 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12752 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12752.grid grid_top_bounds12752 j hθ

noncomputable def covarianceInputs12752 :
    BstLean.Part263.CovarianceInputs 12752 scalarRow12752.grid parameters (caps repair12752) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12752 grid_top_bounds12752 repair12752

noncomputable def covarianceEvent12752 : Set (AgFam 12752) :=
  BstLean.Part263.covarianceEvent 12752 scalarRow12752.grid parameters

theorem covarianceEvent12752_measurable : MeasurableSet covarianceEvent12752 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12752_payment :
    (retDist (paperDesignP 12752).toCentres).real
      (agentEv (paperDesignP 12752) covarianceEvent12752)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12752

theorem localCov12752 : BstLean.Part259.LocalCovarianceOn covarianceEvent12752
    (BstLean.Part263.cell scalarRow12752.grid) (caps repair12752) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12752

theorem covarianceGood12752_payment :
    (retDist (paperDesignP 12752).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12752)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12752_payment



end BstLean.Part269.N12752

namespace BstLean.Part269.N12752
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12752}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12752.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12752) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12752).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12752 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12752) (by norm_num) BstLean.Part268.WorldRow12752.worldPackage rfl
    BstLean.Part268.WorldRow12752.product_lower (BstLean.Part268.WorldRow12752.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12752} (hw : c ∈ Hof BstLean.Part268.WorldRow12752.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12752) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12752) (by norm_num) BstLean.Part268.WorldRow12752.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12752} (hw : c ∈ Hof BstLean.Part268.WorldRow12752.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12752) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12752).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12752) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12752_eq : scalarRow12752.targetFrame = BstLean.Part268.agent12752.frame := by
  norm_num [scalarRow12752,BstLean.Part268.agent12752]

noncomputable def frameData12752 : BstLean.Part264b.FrameData 12752 :=
  BstLean.Part269.frameData_from_numerics (n := 12752) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12752.worldPackage rfl BstLean.Part268.WorldRow12752.product_lower (BstLean.Part268.WorldRow12752.producthi.2.trans (by norm_num))
    scalarRow12752 repair12752 covarianceInputs12752 (fun i hi => sourceNumerics12752 hi)
    BstLean.Part268.agent12752.frame targetFrame12752_eq


end BstLean.Part269.N12752

namespace BstLean.Part269.N12753
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12753 : scalarRow12753.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12753, BstLean.Part268.grid12753, BstLean.Part263.worldGrid]

theorem supplies12753 (j : Fin 43) : Supply 12753 (parameters j)
    (cellLower scalarRow12753.grid (sourceIndex j))
    (cellUpper scalarRow12753.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12753.grid grid_top_bounds12753 j

theorem radii12753 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12753.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12753 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12753 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12753.grid grid_top_bounds12753 j hθ

noncomputable def covarianceInputs12753 :
    BstLean.Part263.CovarianceInputs 12753 scalarRow12753.grid parameters (caps repair12753) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12753 grid_top_bounds12753 repair12753

noncomputable def covarianceEvent12753 : Set (AgFam 12753) :=
  BstLean.Part263.covarianceEvent 12753 scalarRow12753.grid parameters

theorem covarianceEvent12753_measurable : MeasurableSet covarianceEvent12753 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12753_payment :
    (retDist (paperDesignP 12753).toCentres).real
      (agentEv (paperDesignP 12753) covarianceEvent12753)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12753

theorem localCov12753 : BstLean.Part259.LocalCovarianceOn covarianceEvent12753
    (BstLean.Part263.cell scalarRow12753.grid) (caps repair12753) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12753

theorem covarianceGood12753_payment :
    (retDist (paperDesignP 12753).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12753)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12753_payment



end BstLean.Part269.N12753

namespace BstLean.Part269.N12753
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12753}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12753.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12753) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12753).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12753 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12753) (by norm_num) BstLean.Part268.WorldRow12753.worldPackage rfl
    BstLean.Part268.WorldRow12753.product_lower (BstLean.Part268.WorldRow12753.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12753} (hw : c ∈ Hof BstLean.Part268.WorldRow12753.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12753) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12753) (by norm_num) BstLean.Part268.WorldRow12753.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12753} (hw : c ∈ Hof BstLean.Part268.WorldRow12753.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12753) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12753).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12753) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12753_eq : scalarRow12753.targetFrame = BstLean.Part268.agent12753.frame := by
  norm_num [scalarRow12753,BstLean.Part268.agent12753]

noncomputable def frameData12753 : BstLean.Part264b.FrameData 12753 :=
  BstLean.Part269.frameData_from_numerics (n := 12753) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12753.worldPackage rfl BstLean.Part268.WorldRow12753.product_lower (BstLean.Part268.WorldRow12753.producthi.2.trans (by norm_num))
    scalarRow12753 repair12753 covarianceInputs12753 (fun i hi => sourceNumerics12753 hi)
    BstLean.Part268.agent12753.frame targetFrame12753_eq


end BstLean.Part269.N12753

namespace BstLean.Part269.N12754
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds12754 : scalarRow12754.grid.top ∈
    Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000) := by
  constructor <;> norm_num [scalarRow12754, BstLean.Part268.grid12754, BstLean.Part263.worldGrid]

theorem supplies12754 (j : Fin 43) : Supply 12754 (parameters j)
    (cellLower scalarRow12754.grid (sourceIndex j))
    (cellUpper scalarRow12754.grid (sourceIndex j)) :=
  BstLean.Part269.BG1.supplies (by constructor <;> norm_num)
    scalarRow12754.grid grid_top_bounds12754 j

theorem radii12754 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12754.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12754 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12754 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius :=
  BstLean.Part269.BG1.radii (by constructor <;> norm_num)
    scalarRow12754.grid grid_top_bounds12754 j hθ

noncomputable def covarianceInputs12754 :
    BstLean.Part263.CovarianceInputs 12754 scalarRow12754.grid parameters (caps repair12754) :=
  BstLean.Part269.BG1.covarianceInputs (by constructor <;> norm_num)
    scalarRow12754 grid_top_bounds12754 repair12754

noncomputable def covarianceEvent12754 : Set (AgFam 12754) :=
  BstLean.Part263.covarianceEvent 12754 scalarRow12754.grid parameters

theorem covarianceEvent12754_measurable : MeasurableSet covarianceEvent12754 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12754_payment :
    (retDist (paperDesignP 12754).toCentres).real
      (agentEv (paperDesignP 12754) covarianceEvent12754)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12754

theorem localCov12754 : BstLean.Part259.LocalCovarianceOn covarianceEvent12754
    (BstLean.Part263.cell scalarRow12754.grid) (caps repair12754) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12754

theorem covarianceGood12754_payment :
    (retDist (paperDesignP 12754).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12754)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12754_payment



end BstLean.Part269.N12754

namespace BstLean.Part269.N12754
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem actual_world_window {c : Ret 12754}
    (hw : c ∈ Hof BstLean.Part268.WorldRow12754.worldPackage.hidden) (hc : c ∈ BstLean.Part262.sourceBase 12754) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12754).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper 12754 (202831/100000)) :=
  BstLean.Part269.exact_world_window (n := 12754) (by norm_num) BstLean.Part268.WorldRow12754.worldPackage rfl
    BstLean.Part268.WorldRow12754.product_lower (BstLean.Part268.WorldRow12754.producthi.2.trans (by norm_num)) hw hc

theorem source_events {c : Ret 12754} (hw : c ∈ Hof BstLean.Part268.WorldRow12754.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12754) : BstLean.Part262.SourceEvents c :=
  BstLean.Part269.events_from_exact_window (n := 12754) (by norm_num) BstLean.Part268.WorldRow12754.worldPackage
    hw hc (actual_world_window hw hc)

theorem direction_window {c : Ret 12754} (hw : c ∈ Hof BstLean.Part268.WorldRow12754.worldPackage.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12754) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12754).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 :=
  BstLean.Part269.direction_from_exact_window (n := 12754) (by norm_num) (actual_world_window hw hc)

theorem targetFrame12754_eq : scalarRow12754.targetFrame = BstLean.Part268.agent12754.frame := by
  norm_num [scalarRow12754,BstLean.Part268.agent12754]

noncomputable def frameData12754 : BstLean.Part264b.FrameData 12754 :=
  BstLean.Part269.frameData_from_numerics (n := 12754) (by norm_num) (by norm_num)
    BstLean.Part268.WorldRow12754.worldPackage rfl BstLean.Part268.WorldRow12754.product_lower (BstLean.Part268.WorldRow12754.producthi.2.trans (by norm_num))
    scalarRow12754 repair12754 covarianceInputs12754 (fun i hi => sourceNumerics12754 hi)
    BstLean.Part268.agent12754.frame targetFrame12754_eq


end BstLean.Part269.N12754
