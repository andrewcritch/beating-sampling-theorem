import BstLean.Part255Selection

/-! Exact interval clipping and one measurable cell selector. -/
namespace BstLean.Part263
open MeasureTheory Real Set
open BstLean.Part255 (sourceIndex)

noncomputable def noiseNode (top : ℝ) (j : ℕ) : ℝ :=
  46 / 100 + (top - 46 / 100) * j / 60

noncomputable def noiseStep (top : ℝ) : ℝ := (top - 46 / 100) / 60
noncomputable def bin (top θ : ℝ) : ℕ := Nat.ceil ((θ - noiseNode top 10) / noiseStep top) - 1
noncomputable def select (top θ : ℝ) : Fin 43 := ⟨min 42 (bin top θ), by omega⟩

structure Grid where
  top : ℝ
  worldLower : ℝ
  worldUpper : ℝ
  top_pos : 46 / 100 < top
  lower_node : noiseNode top 10 < worldLower
  upper_node : worldUpper < noiseNode top 53

noncomputable def cellLower (G : Grid) (i : Fin 60) : ℝ :=
  max (noiseNode G.top i.val) G.worldLower
noncomputable def cellUpper (G : Grid) (i : Fin 60) : ℝ :=
  min (noiseNode G.top (i.val + 1)) G.worldUpper
noncomputable def cell (G : Grid) (i : Fin 60) : Set ℝ :=
  Icc (cellLower G i) (cellUpper G i)

theorem noiseStep_pos (G : Grid) : 0 < noiseStep G.top := by
  unfold noiseStep
  exact div_pos (sub_pos.mpr G.top_pos) (by norm_num)

theorem noiseNode_add (top : ℝ) (j : ℕ) :
    noiseNode top (j + 10) = noiseNode top 10 + noiseStep top * j := by
  unfold noiseNode noiseStep
  push_cast
  ring

theorem noiseNode_mono (G : Grid) : Monotone (noiseNode G.top) := by
  intro i j hij
  unfold noiseNode
  gcongr
  exact sub_nonneg.mpr G.top_pos.le

theorem select_measurable (top : ℝ) (i : Fin 43) :
    MeasurableSet {θ | select top θ = i} := by
  have hm : Measurable (fun θ : ℝ => min 42 (bin top θ)) := by
    exact measurable_const.min
      ((Nat.measurable_ceil.comp ((measurable_id.sub_const _).div_const _)).sub_const 1)
  have he : {θ | select top θ = i} = {θ : ℝ | min 42 (bin top θ) = i.val} := by
    ext θ
    simp only [mem_setOf_eq]
    exact Fin.ext_iff
  rw [he]
  exact hm (measurableSet_singleton i.val)

theorem cell_world {G : Grid} {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell G i) :
    θ ∈ Icc G.worldLower G.worldUpper :=
  ⟨(le_max_right _ _).trans hθ.1, hθ.2.trans (min_le_right _ _)⟩

theorem cell_needed {G : Grid} {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell G i) :
    10 ≤ i.val ∧ i.val ≤ 52 := by
  have hnlo : noiseNode G.top i.val ≤ θ := (le_max_left _ _).trans hθ.1
  have hnhi : θ ≤ noiseNode G.top (i.val+1) := hθ.2.trans (min_le_left _ _)
  have hw := cell_world hθ
  constructor
  · by_contra h
    have hm := noiseNode_mono G (show i.val+1 ≤ 10 by omega)
    linarith [hw.1, G.lower_node]
  · by_contra h
    have hm := noiseNode_mono G (show 53 ≤ i.val by omega)
    linarith [hw.2, G.upper_node]

theorem select_member (G : Grid) {θ : ℝ} (hθ : θ ∈ Icc G.worldLower G.worldUpper) :
    θ ∈ cell G (sourceIndex (select G.top θ)) := by
  have hstart : noiseNode G.top 10 < θ := G.lower_node.trans_le hθ.1
  have hend : θ < noiseNode G.top 53 := hθ.2.trans_lt G.upper_node
  have hz : 0 < (θ - noiseNode G.top 10) / noiseStep G.top :=
    div_pos (sub_pos.mpr hstart) (noiseStep_pos G)
  have hz43 : (θ - noiseNode G.top 10) / noiseStep G.top < (43 : ℝ) := by
    rw [div_lt_iff₀ (noiseStep_pos G)]
    have hn := noiseNode_add G.top 43
    norm_num only at hn
    linarith
  have hceil : Nat.ceil ((θ-noiseNode G.top 10)/noiseStep G.top) ≤ 43 := Nat.ceil_le.mpr hz43.le
  have hone : 1 ≤ Nat.ceil ((θ-noiseNode G.top 10)/noiseStep G.top) := Nat.one_le_ceil_iff.mpr hz
  have hb : bin G.top θ ≤ 42 := by unfold bin; omega
  have hs : (select G.top θ).val = bin G.top θ := min_eq_right hb
  have he : (bin G.top θ : ℝ) = (Nat.ceil ((θ-noiseNode G.top 10)/noiseStep G.top) : ℝ)-1 := by
    unfold bin
    rw [Nat.cast_sub hone]
    norm_num
  have hl := Nat.ceil_lt_add_one hz.le
  have hh := Nat.le_ceil ((θ-noiseNode G.top 10)/noiseStep G.top)
  have hlo : (bin G.top θ : ℝ) ≤ (θ-noiseNode G.top 10)/noiseStep G.top := by linarith only [he,hl]
  have hhi : (θ-noiseNode G.top 10)/noiseStep G.top ≤ (bin G.top θ : ℝ)+1 := by linarith only [he,hh]
  rw [le_div_iff₀ (noiseStep_pos G)] at hlo
  rw [div_le_iff₀ (noiseStep_pos G)] at hhi
  have hnlo : noiseNode G.top (sourceIndex (select G.top θ)).val ≤ θ := by
    change noiseNode G.top ((select G.top θ).val+10) ≤ θ
    rw [noiseNode_add, hs]
    nlinarith
  have hnhi : θ ≤ noiseNode G.top ((sourceIndex (select G.top θ)).val+1) := by
    change θ ≤ noiseNode G.top ((select G.top θ).val+10+1)
    rw [show (select G.top θ).val+10+1 = ((select G.top θ).val+1)+10 by omega,
      noiseNode_add, hs]
    push_cast
    nlinarith
  exact ⟨max_le hnlo hθ.1, le_min hnhi hθ.2⟩

theorem cells_cover (G : Grid) : Icc G.worldLower G.worldUpper ⊆
    ⋃ i : Fin 60, cell G i := by
  intro θ hθ
  exact mem_iUnion.mpr ⟨_, select_member G hθ⟩

theorem cell_source {G : Grid} {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell G i) :
    θ ∈ Icc (noiseNode G.top i.val) (noiseNode G.top (i.val+1)) :=
  ⟨(le_max_left _ _).trans hθ.1, hθ.2.trans (min_le_left _ _)⟩

end BstLean.Part263
