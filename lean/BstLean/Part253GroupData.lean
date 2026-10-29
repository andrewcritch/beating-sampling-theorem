import BstLean.Part253FullGroups
import BstLean.Part253Retune
import BstLean.Part253HSGroup1
import BstLean.Part253HSGroup2
import BstLean.Part253HSGroup3
import BstLean.Part253HSGroup4
import BstLean.Part253HSGroup5
import BstLean.Part253HSGroup6
import BstLean.Part253HSGroup7
import BstLean.Part253HSGroup8

/-! The eight groups that contain needed cells have explicit scalar certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

def NeededGroup (g : Fin 10) : Prop := 1 ≤ g.val ∧ g.val ≤ 8

noncomputable def groupTheta (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.474393260
  | 2 => 0.481589889
  | 3 => 0.488786519
  | 4 => 0.495983148
  | 5 => 0.503179778
  | 6 => 0.510376407
  | 7 => 0.517573037
  | 8 => 0.524769666
  | _ => 0.5

noncomputable def groupProfile (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.161707182529
  | 2 => 0.164220346040
  | 3 => 0.166717763490
  | 4 => 0.169199068410
  | 5 => 0.171663904382
  | 6 => 0.174111921985
  | 7 => 0.176542781247
  | 8 => 0.178956148662
  | _ => 0.17

structure GroupScalarCertificate (g : Fin 10) : Prop where
  window : groupTheta g ∈ Icc (0.46 : ℝ) 0.525
  profile_nonneg : 0 ≤ groupProfile g
  profile_le : groupProfile g ≤ 0.17895615
  node_upper : noiseNode (6 * g.val + 6) ≤ groupTheta g
  centre_nonneg : 0 ≤ retunedCentre g
  centre_le : retunedCentre g ≤ 0.1
  full_scalar : fullFormula 12225 12225 0.011 1.22 1.12 0.46
    (groupTheta g) (groupProfile g) 1.22 ≤ retunedCentre g

theorem groupScalar1 : GroupScalarCertificate 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup1⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar2 : GroupScalarCertificate 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup2⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar3 : GroupScalarCertificate 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup3⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar4 : GroupScalarCertificate 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup4⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar5 : GroupScalarCertificate 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup5⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar6 : GroupScalarCertificate 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup6⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar7 : GroupScalarCertificate 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup7⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalar8 : GroupScalarCertificate 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fullCentreGroup8⟩
    <;> norm_num [groupTheta, groupProfile, noiseNode, retunedCentre, centreTable]

theorem groupScalarNeeded (j : Fin 8) : GroupScalarCertificate ⟨j.val + 1, by omega⟩ := by
  match j with
  | ⟨0, _⟩ => exact groupScalar1
  | ⟨1, _⟩ => exact groupScalar2
  | ⟨2, _⟩ => exact groupScalar3
  | ⟨3, _⟩ => exact groupScalar4
  | ⟨4, _⟩ => exact groupScalar5
  | ⟨5, _⟩ => exact groupScalar6
  | ⟨6, _⟩ => exact groupScalar7
  | ⟨7, _⟩ => exact groupScalar8
  | ⟨k + 8, h⟩ => omega

theorem group_scalar {g : Fin 10} (hg : NeededGroup g) : GroupScalarCertificate g := by
  let j : Fin 8 := ⟨g.val - 1, by have := hg.2; omega⟩
  have he : (⟨j.val + 1, by omega⟩ : Fin 10) = g := by
    apply Fin.ext
    dsimp [j]
    have := hg.1
    omega
  rw [← he]
  exact groupScalarNeeded j

theorem groupProfileNeeded (j : Fin 8) {θ : ℝ}
    (hw : θ ∈ Icc (0.46 : ℝ) (groupTheta ⟨j.val + 1, by omega⟩)) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ groupProfile ⟨j.val + 1, by omega⟩ := by
  match j with
  | ⟨0, _⟩ => exact hsGroup1 hw
  | ⟨1, _⟩ => exact hsGroup2 hw
  | ⟨2, _⟩ => exact hsGroup3 hw
  | ⟨3, _⟩ => exact hsGroup4 hw
  | ⟨4, _⟩ => exact hsGroup5 hw
  | ⟨5, _⟩ => exact hsGroup6 hw
  | ⟨6, _⟩ => exact hsGroup7 hw
  | ⟨7, _⟩ => exact hsGroup8 hw
  | ⟨k + 8, h⟩ => omega

theorem profile_on_group {g : Fin 10} (hg : NeededGroup g) {θ : ℝ}
    (hw : θ ∈ Icc (0.46 : ℝ) (groupTheta g)) :
    hsProfile 12225 θ 0.006 * (θ * √θ) ≤ groupProfile g := by
  let j : Fin 8 := ⟨g.val - 1, by have := hg.2; omega⟩
  have he : (⟨j.val + 1, by omega⟩ : Fin 10) = g := by
    apply Fin.ext
    dsimp [j]
    have := hg.1
    omega
  have h := groupProfileNeeded j (by simpa only [he] using hw)
  simpa only [he] using h

theorem needed_group {i : Fin 60} (hi : needed i) : NeededGroup (centreGroup i) := by
  change 1 ≤ i.val / 6 ∧ i.val / 6 ≤ 8
  rcases hi with ⟨hlo, hhi⟩
  constructor <;> omega

theorem cell_inside_group {i : Fin 60} (hi : needed i) {θ : ℝ} (hm : θ ∈ cell i) :
    θ ∈ Icc (0.46 : ℝ) (groupTheta (centreGroup i)) := by
  have G := group_scalar (needed_group hi)
  have hidx : i.val + 1 ≤ 6 * (centreGroup i).val + 6 := by
    dsimp [centreGroup]
    omega
  have hlo := noiseNode_mono (Nat.zero_le i.val)
  have hhi := noiseNode_mono hidx
  have he : noiseNode 0 = (0.46 : ℝ) := by norm_num [noiseNode]
  exact ⟨by rw [he] at hlo; exact hlo.trans hm.1, hm.2.trans (hhi.trans G.node_upper)⟩

end BstLean.Part253
