import BstLean.Part254Selection
import BstLean.Part258Cells
import Mathlib.MeasureTheory.Function.Floor

/-! A measurable choice of one of the 43 retained-noise cells. -/
namespace BstLean.Part258
open MeasureTheory Real Set
open BstLean.Part251 (noiseNode proposedThetaUpper)
open BstLean.Part255 (sourceIndex noiseStep bin select noiseStep_pos noiseNode_add select_measurable)


theorem select_member {θ : ℝ} (hθ : θ ∈ Icc worldLower worldUpper) :
    θ ∈ cell (sourceIndex (select θ)) := by
  have hstart : noiseNode 10 < θ :=
    lower_node.trans_le hθ.1
  have hend : θ < noiseNode 53 := hθ.2.trans_lt
    upper_node
  have hz : 0 < (θ - noiseNode 10) / noiseStep :=
    div_pos (sub_pos.mpr hstart) noiseStep_pos
  have hz43 : (θ - noiseNode 10) / noiseStep < (43 : ℝ) := by
    rw [div_lt_iff₀ noiseStep_pos]
    have hn := noiseNode_add 43
    norm_num only at hn
    linarith
  have hceil : Nat.ceil ((θ-noiseNode 10)/noiseStep) ≤ 43 := Nat.ceil_le.mpr hz43.le
  have hone : 1 ≤ Nat.ceil ((θ-noiseNode 10)/noiseStep) := Nat.one_le_ceil_iff.mpr hz
  have hb : bin θ ≤ 42 := by unfold bin; omega
  have hs : (select θ).val = bin θ := min_eq_right hb
  have he : (bin θ : ℝ) = (Nat.ceil ((θ-noiseNode 10)/noiseStep) : ℝ)-1 := by
    unfold bin
    rw [Nat.cast_sub hone]
    norm_num
  have hl := Nat.ceil_lt_add_one hz.le
  have hh := Nat.le_ceil ((θ-noiseNode 10)/noiseStep)
  have hlo : (bin θ : ℝ) ≤ (θ-noiseNode 10)/noiseStep := by linarith only [he,hl]
  have hhi : (θ-noiseNode 10)/noiseStep ≤ (bin θ : ℝ)+1 := by linarith only [he,hh]
  rw [le_div_iff₀ noiseStep_pos] at hlo
  rw [div_le_iff₀ noiseStep_pos] at hhi
  have hnlo : noiseNode (sourceIndex (select θ)).val ≤ θ := by
    change noiseNode ((select θ).val + 10) ≤ θ
    rw [noiseNode_add, hs]
    nlinarith
  have hnhi : θ ≤ noiseNode ((sourceIndex (select θ)).val + 1) := by
    change θ ≤ noiseNode ((select θ).val + 10 + 1)
    rw [show (select θ).val + 10 + 1 = ((select θ).val + 1) + 10 by omega,
      noiseNode_add, hs]
    push_cast
    nlinarith
  exact ⟨max_le hnlo hθ.1, le_min hnhi hθ.2⟩

theorem select_le_of_mem {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    (select θ).val ≤ i.val-10 := by
  have hn := cell_needed hθ
  have hn10 : 10 ≤ i.val := hn.1
  have hu : θ ≤ noiseNode (i.val+1) := hθ.2.trans (min_le_left _ _)
  have he : noiseNode (i.val+1) = noiseNode 10 + noiseStep * ((i.val-10+1 : ℕ) : ℝ) := by
    have h := noiseNode_add (i.val-10+1)
    rw [show i.val-10+1+10 = i.val+1 by omega] at h
    exact h
  have hr : (θ-noiseNode 10)/noiseStep ≤ ((i.val-10+1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ noiseStep_pos]
    rw [he] at hu
    linarith
  have hceil : Nat.ceil ((θ-noiseNode 10)/noiseStep) ≤ i.val-10+1 := Nat.ceil_le.mpr hr
  change min 42 (Nat.ceil ((θ-noiseNode 10)/noiseStep)-1) ≤ i.val-10
  exact (min_le_right _ _).trans (by omega)

theorem select_needed (θ : ℝ) : Needed (sourceIndex (select θ)) := by
  have h := (select θ).isLt
  constructor <;> dsimp [sourceIndex] <;> omega

end BstLean.Part258
