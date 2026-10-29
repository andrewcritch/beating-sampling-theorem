import BstLean.Part253Local
import BstLean.Part193Cover

/-! Closed deterministic cells and the World interval used at dimension 12225. -/
namespace BstLean.Part253
open Real Set

noncomputable def noiseNode (j : ℕ) : ℝ :=
  46 / 100 + (531966295480402052191389 / 10 ^ 24 - 46 / 100) * j / 60

noncomputable def cell (i : Fin 60) : Set ℝ := Icc (noiseNode i.val) (noiseNode (i.val + 1))

/-- These rational endpoints enclose the displayed World interval. -/
noncomputable def worldInterval : Set ℝ := Icc 0.4720819960777689 0.523138096855696258

def needed (i : Fin 60) : Prop := 10 ≤ i.val ∧ i.val ≤ 52

theorem noiseNode_mono : Monotone noiseNode := by
  intro i j hij
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  dsimp [noiseNode]
  gcongr

theorem needed_of_intersection {i : Fin 60} {θ : ℝ}
    (hw : θ ∈ worldInterval) (hi : θ ∈ cell i) : needed i := by
  constructor
  · by_contra h
    have hn := noiseNode_mono (show i.val + 1 ≤ 10 by omega)
    have he : noiseNode 10 < 0.4720819960777689 := by norm_num [noiseNode]
    exact (not_lt_of_ge hw.1) (hi.2.trans_lt (hn.trans_lt he))
  · by_contra h
    have hn := noiseNode_mono (show 53 ≤ i.val by omega)
    have he : 0.523138096855696258 < noiseNode 53 := by norm_num [noiseNode]
    exact (not_lt_of_ge hw.2) (he.trans_le (hn.trans hi.1))

theorem needed_cells_cover {θ : ℝ} (hw : θ ∈ worldInterval) :
    ∃ i : Fin 60, needed i ∧ θ ∈ cell i := by
  have h0 : noiseNode 0 ≤ θ := by
    have := hw.1
    norm_num [noiseNode]
    linarith
  have h60 : θ ≤ noiseNode 60 := by
    have := hw.2
    norm_num [noiseNode]
    linarith
  obtain ⟨j, hj, hc⟩ := BstLean.Part193.chain_coverage noiseNode
    (by norm_num : 0 < 60) (fun j _ => noiseNode_mono (Nat.le_succ j)) ⟨h0, h60⟩
  let i : Fin 60 := ⟨j, Finset.mem_range.mp hj⟩
  exact ⟨i, needed_of_intersection hw hc, hc⟩

theorem needed_inside_optionB {i : Fin 60} (hi : needed i) {θ : ℝ} (hθ : θ ∈ cell i) :
    θ ∈ Icc (46 / 100) (528 / 1000) := by
  have hlo := noiseNode_mono (Nat.zero_le i.val)
  have hhi := noiseNode_mono (show i.val + 1 ≤ 53 by have := hi.2; omega)
  have h53 : noiseNode 53 ≤ (528 / 1000 : ℝ) := by norm_num [noiseNode]
  exact ⟨(by simpa only [noiseNode, Nat.cast_zero, mul_zero, zero_div, add_zero] using
    hlo.trans hθ.1), hθ.2.trans (hhi.trans h53)⟩

end BstLean.Part253
