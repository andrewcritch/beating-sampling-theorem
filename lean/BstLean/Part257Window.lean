import BstLean.Part257Events

/-! The supplied World interval is not contained in the selected-cell interval. -/
namespace BstLean.Part257
open Real Set

noncomputable def actualNoiseInterval : Set ℝ :=
  Icc (BstLean.Part227.noiseLower (202225 / 100000))
    (BstLean.Part227.noiseUpper 12225 (202831 / 100000))

theorem lower_endpoint_gap :
    BstLean.Part227.noiseLower (202225 / 100000) < BstLean.Part254.worldLower :=
  BstLean.Part250.noiselo.2.trans_lt (by norm_num [BstLean.Part254.worldLower])

theorem upper_endpoint_gap :
    BstLean.Part254.worldUpper < BstLean.Part227.noiseUpper 12225 (202831 / 100000) :=
  lt_of_lt_of_le (by norm_num [BstLean.Part254.worldUpper]) BstLean.Part250.noisehi.1

theorem actualNoiseInterval_not_subset :
    ¬ actualNoiseInterval ⊆ Icc BstLean.Part254.worldLower BstLean.Part254.worldUpper := by
  intro hs
  have hlo := BstLean.Part250.noiselo.2
  have hhi := BstLean.Part250.noisehi.1
  have horder : BstLean.Part227.noiseLower (202225 / 100000) ≤
      BstLean.Part227.noiseUpper 12225 (202831 / 100000) := by
    linarith
  have h := hs (show BstLean.Part227.noiseLower (202225 / 100000) ∈
    actualNoiseInterval from ⟨le_rfl, horder⟩)
  exact (not_le_of_gt lower_endpoint_gap) h.1

theorem actual_endpoint_outside_every_selected_cell (i : Fin 60) :
    BstLean.Part227.noiseLower (202225 / 100000) ∉ BstLean.Part255.cell i := by
  intro h
  have hl : BstLean.Part254.worldLower ≤
      BstLean.Part227.noiseLower (202225 / 100000) :=
    (le_max_right _ _).trans h.1
  exact (not_le_of_gt lower_endpoint_gap) hl

end BstLean.Part257
