import BstLean.Part257Window
import BstLean.Part251Data

/-! The 43 selected cells are clipped to the exact certified World interval. -/
namespace BstLean.Part258
open Real Set BstLean.Part251

noncomputable def worldLower : ℝ := BstLean.Part227.noiseLower (202225 / 100000)
noncomputable def worldUpper : ℝ := BstLean.Part227.noiseUpper 12225 (202831 / 100000)

def Needed (i : Fin 60) : Prop := 10 ≤ i.val ∧ i.val ≤ 52

noncomputable def cellLower (i : Fin 60) : ℝ := max (noiseNode i.val) worldLower
noncomputable def cellUpper (i : Fin 60) : ℝ := min (noiseNode (i.val + 1)) worldUpper
noncomputable def cell (i : Fin 60) : Set ℝ := Icc (cellLower i) (cellUpper i)

theorem lower_bound : (472080/10^6 : ℝ) ≤ worldLower :=
  le_trans (by norm_num) BstLean.Part250.noiselo.1

theorem lower_upper : worldLower ≤ (472081/10^6 : ℝ) :=
  BstLean.Part250.noiselo.2.trans (by norm_num)

theorem upper_bound : worldUpper ≤ (523141/10^6 : ℝ) :=
  BstLean.Part250.noisehi.2.trans (by norm_num)

theorem upper_lower : (523140/10^6 : ℝ) ≤ worldUpper :=
  le_trans (by norm_num) BstLean.Part250.noisehi.1

theorem lower_node : noiseNode 10 < worldLower :=
  lt_of_lt_of_le (by norm_num [noiseNode, proposedThetaUpper]) lower_bound

theorem upper_node : worldUpper < noiseNode 53 :=
  upper_bound.trans_lt (by norm_num [noiseNode, proposedThetaUpper])

theorem world_window : Icc worldLower worldUpper ⊆ Icc (46 / 100 : ℝ) (528 / 1000) := by
  intro θ hθ
  exact ⟨le_trans (by norm_num) (lower_bound.trans hθ.1),
    (hθ.2.trans upper_bound).trans (by norm_num)⟩

theorem cell_world {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    θ ∈ Icc worldLower worldUpper :=
  ⟨(le_max_right _ _).trans hθ.1, hθ.2.trans (min_le_right _ _)⟩

theorem cell_window {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    θ ∈ Icc (46 / 100) (528 / 1000) := world_window (cell_world hθ)

theorem cell_needed {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) : Needed i := by
  have hnlo : noiseNode i.val ≤ θ := (le_max_left _ _).trans hθ.1
  have hnhi : θ ≤ noiseNode (i.val + 1) := hθ.2.trans (min_le_left _ _)
  have hw := cell_world hθ
  have h10 : noiseNode 10 < worldLower := lower_node
  have h53 : worldUpper < noiseNode 53 := upper_node
  constructor
  · by_contra h
    have hm := noiseNode_mono (show i.val + 1 ≤ 10 by omega)
    linarith [hw.1]
  · by_contra h
    have hm := noiseNode_mono (show 53 ≤ i.val by omega)
    linarith [hw.2]

theorem cells_cover {θ : ℝ} (hθ : θ ∈ Icc worldLower worldUpper) :
    ∃ i : Fin 60, Needed i ∧ θ ∈ cell i := by
  have hw := world_window hθ
  have hh : θ ≤ proposedThetaUpper :=
    (hθ.2.trans upper_bound).trans (by norm_num [proposedThetaUpper])
  obtain ⟨i, hi⟩ := noise_cells_cover ⟨hw.1, hh⟩
  have hc : θ ∈ cell i := ⟨max_le hi.1 hθ.1, le_min hi.2 hθ.2⟩
  exact ⟨i, cell_needed hc, hc⟩

theorem cell_nonempty (i : Fin 60) (hi : Needed i) : cellLower i ≤ cellUpper i := by
  unfold Needed at hi
  have hu := noiseNode_mono (show i.val ≤ 52 from hi.2)
  have hl := noiseNode_mono (show 11 ≤ i.val + 1 by omega)
  have h52 : noiseNode 52 ≤ worldUpper := le_trans (by norm_num [noiseNode, proposedThetaUpper]) upper_lower
  have h11 : worldLower ≤ noiseNode 11 := lower_upper.trans (by norm_num [noiseNode, proposedThetaUpper])
  unfold cellLower cellUpper
  apply max_le
  · exact le_min (noiseNode_mono (Nat.le_succ _)) (hu.trans h52)
  · exact le_min (h11.trans hl) (lower_upper.trans (le_trans (by norm_num) upper_lower))


noncomputable def sourceLower (i : Fin 60) : ℝ := noiseNode i.val
noncomputable def sourceUpper (i : Fin 60) : ℝ := noiseNode (i.val + 1)
noncomputable def sourceCell (i : Fin 60) : Set ℝ := Icc (sourceLower i) (sourceUpper i)

theorem cell_source {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) : θ ∈ sourceCell i :=
  ⟨(le_max_left _ _).trans hθ.1, hθ.2.trans (min_le_left _ _)⟩

theorem domain_eq : Icc worldLower worldUpper = BstLean.Part257.actualNoiseInterval := rfl

end BstLean.Part258
