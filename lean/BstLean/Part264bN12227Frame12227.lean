import BstLean.Part264bN12227PilotSourceSupply
import BstLean.Part264bN12227Actual12227
import BstLean.Part264Frame
import BstLean.Part259Data0

/-! Actual 12227 LocalFrameInputs on the original hidden and paid source events. -/
namespace BstLean.Part264b.N12227
open BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169
open BstLean.Part263 (scalarRow12227)

theorem targetFrame12227_eq : scalarRow12227.targetFrame = BstLean.Part259.agent12227.frame := by
  norm_num [scalarRow12227,BstLean.Part259.agent12227]

noncomputable def frameInputs12227 {c : Ret 12227} {i : Fin 60}
    (hi : 10 ≤ i.val ∧ i.val ≤ 52)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12227).tau0 c) ∈
      BstLean.Part263.cell scalarRow12227.grid i)
    (hw : c ∈ Hof (BstLean.Part260.worldPackage 12227 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12227) :
    BstLean.Part259.LocalFrameInputs 12227 covarianceEvent12227
      (BstLean.Part263.cell scalarRow12227.grid) (caps repair12227) c
        BstLean.Part259.agent12227.frame := by
  have F := frameInputs_from_numeric_sources (by constructor <;> norm_num) repair12227
    covarianceInputs12227 hi hm (sourceNumerics12227 hi) hw hc
  rw [targetFrame12227_eq] at F
  exact F

noncomputable def frame12227 {hW : ℝ} (c : Ret 12227)
    (hc : c ∈ goodSet
      (Hof (BstLean.Part260.worldPackage 12227 (by constructor <;> norm_num)).hidden)
      (BstLean.Part262.sourceBase 12227 ∩ BstLean.Part259.covarianceGood covarianceEvent12227)
      (HbarW (paperDesignP 12227)) hW) :
    Nonempty (BstLean.Part259.LocalFrameInputs 12227 covarianceEvent12227
      (BstLean.Part263.cell scalarRow12227.grid) (caps repair12227) c
        BstLean.Part259.agent12227.frame) := by
  obtain ⟨i,hi,hm⟩ := local_cell (by constructor <;> norm_num) scalarRow12227 hc.1.1 hc.2.1
  exact ⟨frameInputs12227 hi hm hc.1.1 hc.2.1⟩

end BstLean.Part264b.N12227
