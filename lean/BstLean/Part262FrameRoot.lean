import BstLean.Part262ActualInterface

/-! The local frame supply gives the remaining local interfaces of the root.
Only scalar cap comparisons and the cell window remain explicit. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def rootInputs_from_frame {n : ℕ} {root t cf : ℝ}
    {event : Set (BstLean.Part160.AgFam n)} {cell : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ}
    {c : Ret n} (C : ActualRootCertificate n root)
    (F : BstLean.Part259.LocalFrameInputs n event cell caps c cf)
    (hc : c ∈ sourceBase n)
    (hcell : cell F.index ⊆ Icc (46 / 100 : ℝ) (54 / 100))
    (hM : F.M ≤ 91 / 1000) (hH : F.H ≤ (2101 / 100) / n)
    (hxi : F.xiP ≤ 4 / 100) (hE : F.E ≤ 702 / 1000) :
    BstLean.Part243.RootInputs n t c root := by
  have hn : 1 ≤ n := by have := C.dimension; omega
  have hw := BstLean.Part252.window_of_theta hn (paperDesignP n) c
    F.scale_pos (hcell F.member)
  have I : WFInterfaces (paperDesignP n) c
      (91 / 1000) ((2101 / 100) / n) (4 / 100) := by
    refine ⟨BstLean.Part219.directionMoment_mono F.interfaces.direction hM, ?_, ?_⟩
    · exact ⟨by positivity, F.interfaces.energy.2.1,
        F.interfaces.energy.2.2.trans (pow_le_pow_left₀ F.interfaces.energy.1 hH 32)⟩
    · refine ⟨by norm_num, F.interfaces.parallel.2.trans ?_⟩
      apply sqrt_le_sqrt
      exact div_le_div_of_nonneg_right hxi (Nat.cast_nonneg n)
  exact C.inputs t c hw hc I (F.centre_energy.trans hE)

end BstLean.Part262
