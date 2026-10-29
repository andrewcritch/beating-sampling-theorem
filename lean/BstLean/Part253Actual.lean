import BstLean.Part253ActualScalar
import BstLean.Part253RetunedSupply

/-! The actual supplied covariance contract gives the weaker frame 1.505. -/
namespace BstLean.Part253
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157
open BstLean.Part169 (paperDesignP)

theorem source_noise_node_eq (j : ℕ) : BstLean.Part251.noiseNode j = noiseNode j := by
  unfold BstLean.Part251.noiseNode BstLean.Part251.proposedThetaUpper noiseNode
  norm_num

theorem supplied_cell_subset (i : Fin 60) : BstLean.Part254.cell i ⊆ cell i := by
  intro θ hθ
  have hlo : BstLean.Part251.noiseNode i.val ≤ θ := (le_max_left _ _).trans hθ.1
  have hhi : θ ≤ BstLean.Part251.noiseNode (i.val + 1) := hθ.2.trans (min_le_left _ _)
  rw [source_noise_node_eq] at hlo hhi
  exact ⟨hlo, hhi⟩

noncomputable def frameInputs_from_supplied_events {c : Ret 12225} {i : Fin 60}
    (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ BstLean.Part254.cell i)
    (F : SourceEvents c) :
    LocalFrameInputs BstLean.Part254.cell BstLean.Part254.capTable c 1.505 :=
  frameInputs_from_retuned_network_general BstLean.Part254.localCov_part253 hi hm
    (retuned_network_from_events hi (supplied_cell_subset i hm) F)
    (supplied_frame_on_needed hi).cap_nonneg (supplied_frame_on_needed hi).frame_upper

theorem frame_from_supplied_events {c : Ret 12225}
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      Icc BstLean.Part254.worldLower BstLean.Part254.worldUpper)
    (F : SourceEvents c) (hc : c ∈ BstLean.Part249.optionBGood (paperDesignP 12225)) :
    ∀ v : Fin (mA 12225) → ℝ,
      ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP 12225).bA c.1 c.2.1.1)
        (hStand (paperDesignP 12225) c ξ) j * v j) ^ 2 ∂BstLean.Part29.stdGauss (Fin 12225) ≤
        1.505 / 12225 * ∑ j, v j ^ 2 := by
  obtain ⟨i, hi, hm⟩ := BstLean.Part254.cells_cover hw
  exact frame_from_inputs (frameInputs_from_supplied_events hi hm F) hc

end BstLean.Part253
