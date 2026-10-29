import BstLean.Part264PilotSourceSupply
import BstLean.Part264Actual12226
import BstLean.Part264Frame
import BstLean.Part259Data0

/-! Actual 12226 LocalFrameInputs on the original hidden and paid source events. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169
open BstLean.Part263 (scalarRow12226)

theorem targetFrame12226_eq : scalarRow12226.targetFrame = BstLean.Part259.agent12226.frame := by
  norm_num [scalarRow12226,BstLean.Part259.agent12226]

noncomputable def frameInputs12226 {c : Ret 12226} {i : Fin 60}
    (hi : 10 ≤ i.val ∧ i.val ≤ 52)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12226).tau0 c) ∈
      BstLean.Part263.cell scalarRow12226.grid i)
    (hw : c ∈ Hof (BstLean.Part260.worldPackage 12226 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12226) :
    BstLean.Part259.LocalFrameInputs 12226 covarianceEvent12226
      (BstLean.Part263.cell scalarRow12226.grid) (caps repair12226) c
        BstLean.Part259.agent12226.frame := by
  have F := frameInputs_from_numeric_sources (by constructor <;> norm_num) repair12226
    covarianceInputs12226 hi hm (sourceNumerics12226 hi) hw hc
  rw [targetFrame12226_eq] at F
  exact F

noncomputable def frame12226 {hW : ℝ} (c : Ret 12226)
    (hc : c ∈ goodSet
      (Hof (BstLean.Part260.worldPackage 12226 (by constructor <;> norm_num)).hidden)
      (BstLean.Part262.sourceBase 12226 ∩ BstLean.Part259.covarianceGood covarianceEvent12226)
      (HbarW (paperDesignP 12226)) hW) :
    Nonempty (BstLean.Part259.LocalFrameInputs 12226 covarianceEvent12226
      (BstLean.Part263.cell scalarRow12226.grid) (caps repair12226) c
        BstLean.Part259.agent12226.frame) := by
  obtain ⟨i,hi,hm⟩ := local_cell (by constructor <;> norm_num) scalarRow12226 hc.1.1 hc.2.1
  exact ⟨frameInputs12226 hi hm hc.1.1 hc.2.1⟩

end BstLean.Part264
