import BstLean.Part254Scalar
import BstLean.Part251Data

/-! The 43 cells that meet an outward rational enclosure of the source World
noise interval. The enclosure is a conditional domain, not a World theorem. -/
namespace BstLean.Part254
open Real Set BstLean.Part251

noncomputable def worldLower : ℝ := 472081996077768900335414 / 10 ^ 24
noncomputable def worldUpper : ℝ := 523138096855696257379105 / 10 ^ 24

def Needed (i : Fin 60) : Prop := 10 ≤ i.val ∧ i.val ≤ 52

noncomputable def cellLower (i : Fin 60) : ℝ := max (noiseNode i.val) worldLower
noncomputable def cellUpper (i : Fin 60) : ℝ := min (noiseNode (i.val + 1)) worldUpper
noncomputable def cell (i : Fin 60) : Set ℝ := Icc (cellLower i) (cellUpper i)

theorem world_window : Icc worldLower worldUpper ⊆ Icc (46 / 100 : ℝ) (528 / 1000) := by
  intro θ hθ
  constructor <;> norm_num [worldLower, worldUpper] at hθ ⊢ <;> linarith [hθ.1, hθ.2]

theorem cell_world {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    θ ∈ Icc worldLower worldUpper :=
  ⟨(le_max_right _ _).trans hθ.1, hθ.2.trans (min_le_right _ _)⟩

theorem cell_window {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    θ ∈ Icc (46 / 100) (528 / 1000) := world_window (cell_world hθ)

theorem cell_needed {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) : Needed i := by
  have hnlo : noiseNode i.val ≤ θ := (le_max_left _ _).trans hθ.1
  have hnhi : θ ≤ noiseNode (i.val + 1) := hθ.2.trans (min_le_left _ _)
  have hw := cell_world hθ
  have h10 : noiseNode 10 < worldLower := by norm_num [noiseNode, proposedThetaUpper, worldLower]
  have h53 : worldUpper < noiseNode 53 := by norm_num [noiseNode, proposedThetaUpper, worldUpper]
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
    hθ.2.trans (by norm_num [worldUpper, proposedThetaUpper])
  obtain ⟨i, hi⟩ := noise_cells_cover ⟨hw.1, hh⟩
  have hc : θ ∈ cell i := ⟨max_le hi.1 hθ.1, le_min hi.2 hθ.2⟩
  exact ⟨i, cell_needed hc, hc⟩

theorem cell_nonempty (i : Fin 60) (hi : Needed i) : cellLower i ≤ cellUpper i := by
  unfold Needed at hi
  have hu := noiseNode_mono (show i.val ≤ 52 from hi.2)
  have hl := noiseNode_mono (show 11 ≤ i.val + 1 by omega)
  have h52 : noiseNode 52 ≤ worldUpper := by norm_num [noiseNode, proposedThetaUpper, worldUpper]
  have h11 : worldLower ≤ noiseNode 11 := by norm_num [noiseNode, proposedThetaUpper, worldLower]
  unfold cellLower cellUpper
  apply max_le
  · exact le_min (noiseNode_mono (Nat.le_succ _)) (hu.trans h52)
  · exact le_min (h11.trans hl) (by norm_num [worldLower, worldUpper])

theorem proposal_rejected {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    (rowCellAudit i).covarianceCap < fixedCovariance 12225 θ :=
  cell_covariance_rejected (rowCellAudit i) (cell_window hθ)
    ((le_max_left _ _).trans hθ.1)

/-- Minimality below refers only to a billionth grid and this explicit envelope. -/
structure GridCertificate (i : Fin 60) (cap : ℝ) : Prop where
  upper : scalarEnvelope (cellUpper i) ≤ cap
  previous : cap - 1 / 10 ^ 9 < scalarEnvelope (cellUpper i)
  nonneg : 0 ≤ cap

end BstLean.Part254
