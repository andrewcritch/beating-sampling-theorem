import BstLean.Part228Cells00
import BstLean.Part228Cells01
import BstLean.Part228Cells02
import BstLean.Part228Cells03
import BstLean.Part228Cells04
import BstLean.Part228Cells05
import BstLean.Part228Cells06
import BstLean.Part228Cells07
import BstLean.Part228Cells08
import BstLean.Part228Cells09
import BstLean.Part228Cells10
import BstLean.Part228Cells11
import BstLean.Part228Cells12
import BstLean.Part228Cells13
import BstLean.Part228Cells14
import BstLean.Part228Cells15
import BstLean.Part228Cells16
import BstLean.Part228Cells17
import BstLean.Part228Cells18
import BstLean.Part228Cells19

/-! A deterministic closed cover. No union probability is paid. -/
namespace BstLean.Part228

private theorem cover_0 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (47/100))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_0_lower hθ hx, cell_0_upper hθ hx⟩

private theorem cover_1 {θ x : ℝ}
    (hθ : Bounds θ (47/100) (12/25))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_1_lower hθ hx, cell_1_upper hθ hx⟩

private theorem cover_2 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (12/25))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (47/100) with h | h
  · exact cover_0 ⟨hθ.1, h⟩ hx
  · exact cover_1 ⟨h, hθ.2⟩ hx

private theorem cover_3 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (47/100))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_2_lower hθ hx, cell_2_upper hθ hx⟩

private theorem cover_4 {θ x : ℝ}
    (hθ : Bounds θ (47/100) (12/25))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_3_lower hθ hx, cell_3_upper hθ hx⟩

private theorem cover_5 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (12/25))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (47/100) with h | h
  · exact cover_3 ⟨hθ.1, h⟩ hx
  · exact cover_4 ⟨h, hθ.2⟩ hx

private theorem cover_6 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (12/25))
    (hx : Bounds x 0 (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/2500) with h | h
  · exact cover_2 hθ ⟨hx.1, h⟩
  · exact cover_5 hθ ⟨h, hx.2⟩

private theorem cover_7 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (49/100))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_4_lower hθ hx, cell_4_upper hθ hx⟩

private theorem cover_8 {θ x : ℝ}
    (hθ : Bounds θ (49/100) (1/2))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_5_lower hθ hx, cell_5_upper hθ hx⟩

private theorem cover_9 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (1/2))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (49/100) with h | h
  · exact cover_7 ⟨hθ.1, h⟩ hx
  · exact cover_8 ⟨h, hθ.2⟩ hx

private theorem cover_10 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (49/100))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_6_lower hθ hx, cell_6_upper hθ hx⟩

private theorem cover_11 {θ x : ℝ}
    (hθ : Bounds θ (49/100) (1/2))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_7_lower hθ hx, cell_7_upper hθ hx⟩

private theorem cover_12 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (1/2))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (49/100) with h | h
  · exact cover_10 ⟨hθ.1, h⟩ hx
  · exact cover_11 ⟨h, hθ.2⟩ hx

private theorem cover_13 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (1/2))
    (hx : Bounds x 0 (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/2500) with h | h
  · exact cover_9 hθ ⟨hx.1, h⟩
  · exact cover_12 hθ ⟨h, hx.2⟩

private theorem cover_14 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (1/2))
    (hx : Bounds x 0 (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (12/25) with h | h
  · exact cover_6 ⟨hθ.1, h⟩ hx
  · exact cover_13 ⟨h, hθ.2⟩ hx

private theorem cover_15 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (47/100))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_8_lower hθ hx, cell_8_upper hθ hx⟩

private theorem cover_16 {θ x : ℝ}
    (hθ : Bounds θ (47/100) (12/25))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_9_lower hθ hx, cell_9_upper hθ hx⟩

private theorem cover_17 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (12/25))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (47/100) with h | h
  · exact cover_15 ⟨hθ.1, h⟩ hx
  · exact cover_16 ⟨h, hθ.2⟩ hx

private theorem cover_18 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (47/100))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_10_lower hθ hx, cell_10_upper hθ hx⟩

private theorem cover_19 {θ x : ℝ}
    (hθ : Bounds θ (47/100) (12/25))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_11_lower hθ hx, cell_11_upper hθ hx⟩

private theorem cover_20 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (12/25))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (47/100) with h | h
  · exact cover_18 ⟨hθ.1, h⟩ hx
  · exact cover_19 ⟨h, hθ.2⟩ hx

private theorem cover_21 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (12/25))
    (hx : Bounds x (7/1250) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2500) with h | h
  · exact cover_17 hθ ⟨hx.1, h⟩
  · exact cover_20 hθ ⟨h, hx.2⟩

private theorem cover_22 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (49/100))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_12_lower hθ hx, cell_12_upper hθ hx⟩

private theorem cover_23 {θ x : ℝ}
    (hθ : Bounds θ (49/100) (1/2))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_13_lower hθ hx, cell_13_upper hθ hx⟩

private theorem cover_24 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (1/2))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (49/100) with h | h
  · exact cover_22 ⟨hθ.1, h⟩ hx
  · exact cover_23 ⟨h, hθ.2⟩ hx

private theorem cover_25 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (49/100))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_14_lower hθ hx, cell_14_upper hθ hx⟩

private theorem cover_26 {θ x : ℝ}
    (hθ : Bounds θ (49/100) (1/2))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_15_lower hθ hx, cell_15_upper hθ hx⟩

private theorem cover_27 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (1/2))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (49/100) with h | h
  · exact cover_25 ⟨hθ.1, h⟩ hx
  · exact cover_26 ⟨h, hθ.2⟩ hx

private theorem cover_28 {θ x : ℝ}
    (hθ : Bounds θ (12/25) (1/2))
    (hx : Bounds x (7/1250) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2500) with h | h
  · exact cover_24 hθ ⟨hx.1, h⟩
  · exact cover_27 hθ ⟨h, hx.2⟩

private theorem cover_29 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (1/2))
    (hx : Bounds x (7/1250) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (12/25) with h | h
  · exact cover_21 ⟨hθ.1, h⟩ hx
  · exact cover_28 ⟨h, hθ.2⟩ hx

private theorem cover_30 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (1/2))
    (hx : Bounds x 0 (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/1250) with h | h
  · exact cover_14 hθ ⟨hx.1, h⟩
  · exact cover_29 hθ ⟨h, hx.2⟩

private theorem cover_31 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_16_lower hθ hx, cell_16_upper hθ hx⟩

private theorem cover_32 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_17_lower hθ hx, cell_17_upper hθ hx⟩

private theorem cover_33 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/5000) with h | h
  · exact cover_31 hθ ⟨hx.1, h⟩
  · exact cover_32 hθ ⟨h, hx.2⟩

private theorem cover_34 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (103/200))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_18_lower hθ hx, cell_18_upper hθ hx⟩

private theorem cover_35 {θ x : ℝ}
    (hθ : Bounds θ (103/200) (13/25))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_19_lower hθ hx, cell_19_upper hθ hx⟩

private theorem cover_36 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (103/200) with h | h
  · exact cover_34 ⟨hθ.1, h⟩ hx
  · exact cover_35 ⟨h, hθ.2⟩ hx

private theorem cover_37 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_20_lower hθ hx, cell_20_upper hθ hx⟩

private theorem cover_38 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/5000) with h | h
  · exact cover_36 hθ ⟨hx.1, h⟩
  · exact cover_37 hθ ⟨h, hx.2⟩

private theorem cover_39 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (13/25))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (51/100) with h | h
  · exact cover_33 ⟨hθ.1, h⟩ hx
  · exact cover_38 ⟨h, hθ.2⟩ hx

private theorem cover_40 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_21_lower hθ hx, cell_21_upper hθ hx⟩

private theorem cover_41 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (21/5000) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_22_lower hθ hx, cell_22_upper hθ hx⟩

private theorem cover_42 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/5000) with h | h
  · exact cover_40 hθ ⟨hx.1, h⟩
  · exact cover_41 hθ ⟨h, hx.2⟩

private theorem cover_43 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_23_lower hθ hx, cell_23_upper hθ hx⟩

private theorem cover_44 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (21/5000) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_24_lower hθ hx, cell_24_upper hθ hx⟩

private theorem cover_45 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/5000) with h | h
  · exact cover_43 hθ ⟨hx.1, h⟩
  · exact cover_44 hθ ⟨h, hx.2⟩

private theorem cover_46 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (13/25))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (51/100) with h | h
  · exact cover_42 ⟨hθ.1, h⟩ hx
  · exact cover_45 ⟨h, hθ.2⟩ hx

private theorem cover_47 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (13/25))
    (hx : Bounds x 0 (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/2500) with h | h
  · exact cover_39 hθ ⟨hx.1, h⟩
  · exact cover_46 hθ ⟨h, hx.2⟩

private theorem cover_48 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_25_lower hθ hx, cell_25_upper hθ hx⟩

private theorem cover_49 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_26_lower hθ hx, cell_26_upper hθ hx⟩

private theorem cover_50 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_48 ⟨hθ.1, h⟩ hx
  · exact cover_49 ⟨h, hθ.2⟩ hx

private theorem cover_51 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_27_lower hθ hx, cell_27_upper hθ hx⟩

private theorem cover_52 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_28_lower hθ hx, cell_28_upper hθ hx⟩

private theorem cover_53 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_51 ⟨hθ.1, h⟩ hx
  · exact cover_52 ⟨h, hθ.2⟩ hx

private theorem cover_54 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/5000) with h | h
  · exact cover_50 hθ ⟨hx.1, h⟩
  · exact cover_53 hθ ⟨h, hx.2⟩

private theorem cover_55 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_29_lower hθ hx, cell_29_upper hθ hx⟩

private theorem cover_56 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x 0 (7/10000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_30_lower hθ hx, cell_30_upper hθ hx⟩

private theorem cover_57 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (7/10000) (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_31_lower hθ hx, cell_31_upper hθ hx⟩

private theorem cover_58 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/10000) with h | h
  · exact cover_56 hθ ⟨hx.1, h⟩
  · exact cover_57 hθ ⟨h, hx.2⟩

private theorem cover_59 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x 0 (7/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_55 ⟨hθ.1, h⟩ hx
  · exact cover_58 ⟨h, hθ.2⟩ hx

private theorem cover_60 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_32_lower hθ hx, cell_32_upper hθ hx⟩

private theorem cover_61 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_33_lower hθ hx, cell_33_upper hθ hx⟩

private theorem cover_62 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (7/5000) (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_60 ⟨hθ.1, h⟩ hx
  · exact cover_61 ⟨h, hθ.2⟩ hx

private theorem cover_63 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/5000) with h | h
  · exact cover_59 hθ ⟨hx.1, h⟩
  · exact cover_62 hθ ⟨h, hx.2⟩

private theorem cover_64 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (27/50))
    (hx : Bounds x 0 (7/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (53/100) with h | h
  · exact cover_54 ⟨hθ.1, h⟩ hx
  · exact cover_63 ⟨h, hθ.2⟩ hx

private theorem cover_65 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_34_lower hθ hx, cell_34_upper hθ hx⟩

private theorem cover_66 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_35_lower hθ hx, cell_35_upper hθ hx⟩

private theorem cover_67 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_65 ⟨hθ.1, h⟩ hx
  · exact cover_66 ⟨h, hθ.2⟩ hx

private theorem cover_68 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (21/5000) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_36_lower hθ hx, cell_36_upper hθ hx⟩

private theorem cover_69 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/5000) with h | h
  · exact cover_67 hθ ⟨hx.1, h⟩
  · exact cover_68 hθ ⟨h, hx.2⟩

private theorem cover_70 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_37_lower hθ hx, cell_37_upper hθ hx⟩

private theorem cover_71 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_38_lower hθ hx, cell_38_upper hθ hx⟩

private theorem cover_72 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (7/2500) (21/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_70 ⟨hθ.1, h⟩ hx
  · exact cover_71 ⟨h, hθ.2⟩ hx

private theorem cover_73 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (21/5000) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_39_lower hθ hx, cell_39_upper hθ hx⟩

private theorem cover_74 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (21/5000) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_40_lower hθ hx, cell_40_upper hθ hx⟩

private theorem cover_75 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (21/5000) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_73 ⟨hθ.1, h⟩ hx
  · exact cover_74 ⟨h, hθ.2⟩ hx

private theorem cover_76 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/5000) with h | h
  · exact cover_72 hθ ⟨hx.1, h⟩
  · exact cover_75 hθ ⟨h, hx.2⟩

private theorem cover_77 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (27/50))
    (hx : Bounds x (7/2500) (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (53/100) with h | h
  · exact cover_69 ⟨hθ.1, h⟩ hx
  · exact cover_76 ⟨h, hθ.2⟩ hx

private theorem cover_78 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (27/50))
    (hx : Bounds x 0 (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/2500) with h | h
  · exact cover_64 hθ ⟨hx.1, h⟩
  · exact cover_77 hθ ⟨h, hx.2⟩

private theorem cover_79 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (27/50))
    (hx : Bounds x 0 (7/1250)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (13/25) with h | h
  · exact cover_47 ⟨hθ.1, h⟩ hx
  · exact cover_78 ⟨h, hθ.2⟩ hx

private theorem cover_80 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_41_lower hθ hx, cell_41_upper hθ hx⟩

private theorem cover_81 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_42_lower hθ hx, cell_42_upper hθ hx⟩

private theorem cover_82 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_43_lower hθ hx, cell_43_upper hθ hx⟩

private theorem cover_83 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/1000) with h | h
  · exact cover_81 hθ ⟨hx.1, h⟩
  · exact cover_82 hθ ⟨h, hx.2⟩

private theorem cover_84 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (13/25))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (51/100) with h | h
  · exact cover_80 ⟨hθ.1, h⟩ hx
  · exact cover_83 ⟨h, hθ.2⟩ hx

private theorem cover_85 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_44_lower hθ hx, cell_44_upper hθ hx⟩

private theorem cover_86 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_45_lower hθ hx, cell_45_upper hθ hx⟩

private theorem cover_87 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (51/100))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (49/5000) with h | h
  · exact cover_85 hθ ⟨hx.1, h⟩
  · exact cover_86 hθ ⟨h, hx.2⟩

private theorem cover_88 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (103/200))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_46_lower hθ hx, cell_46_upper hθ hx⟩

private theorem cover_89 {θ x : ℝ}
    (hθ : Bounds θ (103/200) (13/25))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_47_lower hθ hx, cell_47_upper hθ hx⟩

private theorem cover_90 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (103/200) with h | h
  · exact cover_88 ⟨hθ.1, h⟩ hx
  · exact cover_89 ⟨h, hθ.2⟩ hx

private theorem cover_91 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (103/200))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_48_lower hθ hx, cell_48_upper hθ hx⟩

private theorem cover_92 {θ x : ℝ}
    (hθ : Bounds θ (103/200) (13/25))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_49_lower hθ hx, cell_49_upper hθ hx⟩

private theorem cover_93 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (103/200) with h | h
  · exact cover_91 ⟨hθ.1, h⟩ hx
  · exact cover_92 ⟨h, hθ.2⟩ hx

private theorem cover_94 {θ x : ℝ}
    (hθ : Bounds θ (51/100) (13/25))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (49/5000) with h | h
  · exact cover_90 hθ ⟨hx.1, h⟩
  · exact cover_93 hθ ⟨h, hx.2⟩

private theorem cover_95 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (13/25))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (51/100) with h | h
  · exact cover_87 ⟨hθ.1, h⟩ hx
  · exact cover_94 ⟨h, hθ.2⟩ hx

private theorem cover_96 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (13/25))
    (hx : Bounds x (7/1250) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2500) with h | h
  · exact cover_84 hθ ⟨hx.1, h⟩
  · exact cover_95 hθ ⟨h, hx.2⟩

private theorem cover_97 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_50_lower hθ hx, cell_50_upper hθ hx⟩

private theorem cover_98 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_51_lower hθ hx, cell_51_upper hθ hx⟩

private theorem cover_99 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_97 ⟨hθ.1, h⟩ hx
  · exact cover_98 ⟨h, hθ.2⟩ hx

private theorem cover_100 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_52_lower hθ hx, cell_52_upper hθ hx⟩

private theorem cover_101 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_53_lower hθ hx, cell_53_upper hθ hx⟩

private theorem cover_102 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_100 ⟨hθ.1, h⟩ hx
  · exact cover_101 ⟨h, hθ.2⟩ hx

private theorem cover_103 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/1000) with h | h
  · exact cover_99 hθ ⟨hx.1, h⟩
  · exact cover_102 hθ ⟨h, hx.2⟩

private theorem cover_104 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_54_lower hθ hx, cell_54_upper hθ hx⟩

private theorem cover_105 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_55_lower hθ hx, cell_55_upper hθ hx⟩

private theorem cover_106 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (7/1250) (7/1000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_104 ⟨hθ.1, h⟩ hx
  · exact cover_105 ⟨h, hθ.2⟩ hx

private theorem cover_107 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_56_lower hθ hx, cell_56_upper hθ hx⟩

private theorem cover_108 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (7/1000) (77/10000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_57_lower hθ hx, cell_57_upper hθ hx⟩

private theorem cover_109 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (77/10000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_58_lower hθ hx, cell_58_upper hθ hx⟩

private theorem cover_110 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (77/10000) with h | h
  · exact cover_108 hθ ⟨hx.1, h⟩
  · exact cover_109 hθ ⟨h, hx.2⟩

private theorem cover_111 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (7/1000) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_107 ⟨hθ.1, h⟩ hx
  · exact cover_110 ⟨h, hθ.2⟩ hx

private theorem cover_112 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/1000) with h | h
  · exact cover_106 hθ ⟨hx.1, h⟩
  · exact cover_111 hθ ⟨h, hx.2⟩

private theorem cover_113 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (27/50))
    (hx : Bounds x (7/1250) (21/2500)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (53/100) with h | h
  · exact cover_103 ⟨hθ.1, h⟩ hx
  · exact cover_112 ⟨h, hθ.2⟩ hx

private theorem cover_114 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_59_lower hθ hx, cell_59_upper hθ hx⟩

private theorem cover_115 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_60_lower hθ hx, cell_60_upper hθ hx⟩

private theorem cover_116 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_114 ⟨hθ.1, h⟩ hx
  · exact cover_115 ⟨h, hθ.2⟩ hx

private theorem cover_117 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (21/40))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_61_lower hθ hx, cell_61_upper hθ hx⟩

private theorem cover_118 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (49/5000) (21/2000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_62_lower hθ hx, cell_62_upper hθ hx⟩

private theorem cover_119 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_63_lower hθ hx, cell_63_upper hθ hx⟩

private theorem cover_120 {θ x : ℝ}
    (hθ : Bounds θ (21/40) (53/100))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2000) with h | h
  · exact cover_118 hθ ⟨hx.1, h⟩
  · exact cover_119 hθ ⟨h, hx.2⟩

private theorem cover_121 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (21/40) with h | h
  · exact cover_117 ⟨hθ.1, h⟩ hx
  · exact cover_120 ⟨h, hθ.2⟩ hx

private theorem cover_122 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (53/100))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (49/5000) with h | h
  · exact cover_116 hθ ⟨hx.1, h⟩
  · exact cover_121 hθ ⟨h, hx.2⟩

private theorem cover_123 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (21/2500) (91/10000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_64_lower hθ hx, cell_64_upper hθ hx⟩

private theorem cover_124 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (91/10000) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_65_lower hθ hx, cell_65_upper hθ hx⟩

private theorem cover_125 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (91/10000) with h | h
  · exact cover_123 hθ ⟨hx.1, h⟩
  · exact cover_124 hθ ⟨h, hx.2⟩

private theorem cover_126 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (21/2500) (91/10000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_66_lower hθ hx, cell_66_upper hθ hx⟩

private theorem cover_127 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (43/80))
    (hx : Bounds x (91/10000) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_67_lower hθ hx, cell_67_upper hθ hx⟩

private theorem cover_128 {θ x : ℝ}
    (hθ : Bounds θ (43/80) (27/50))
    (hx : Bounds x (91/10000) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_68_lower hθ hx, cell_68_upper hθ hx⟩

private theorem cover_129 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (91/10000) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (43/80) with h | h
  · exact cover_127 ⟨hθ.1, h⟩ hx
  · exact cover_128 ⟨h, hθ.2⟩ hx

private theorem cover_130 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (91/10000) with h | h
  · exact cover_126 hθ ⟨hx.1, h⟩
  · exact cover_129 hθ ⟨h, hx.2⟩

private theorem cover_131 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (21/2500) (49/5000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_125 ⟨hθ.1, h⟩ hx
  · exact cover_130 ⟨h, hθ.2⟩ hx

private theorem cover_132 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (49/5000) (21/2000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_69_lower hθ hx, cell_69_upper hθ hx⟩

private theorem cover_133 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (213/400))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_70_lower hθ hx, cell_70_upper hθ hx⟩

private theorem cover_134 {θ x : ℝ}
    (hθ : Bounds θ (213/400) (107/200))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_71_lower hθ hx, cell_71_upper hθ hx⟩

private theorem cover_135 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (213/400) with h | h
  · exact cover_133 ⟨hθ.1, h⟩ hx
  · exact cover_134 ⟨h, hθ.2⟩ hx

private theorem cover_136 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (107/200))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2000) with h | h
  · exact cover_132 hθ ⟨hx.1, h⟩
  · exact cover_135 hθ ⟨h, hx.2⟩

private theorem cover_137 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (43/80))
    (hx : Bounds x (49/5000) (21/2000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_72_lower hθ hx, cell_72_upper hθ hx⟩

private theorem cover_138 {θ x : ℝ}
    (hθ : Bounds θ (43/80) (27/50))
    (hx : Bounds x (49/5000) (21/2000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_73_lower hθ hx, cell_73_upper hθ hx⟩

private theorem cover_139 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (49/5000) (21/2000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (43/80) with h | h
  · exact cover_137 ⟨hθ.1, h⟩ hx
  · exact cover_138 ⟨h, hθ.2⟩ hx

private theorem cover_140 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (43/80))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_74_lower hθ hx, cell_74_upper hθ hx⟩

private theorem cover_141 {θ x : ℝ}
    (hθ : Bounds θ (43/80) (27/50))
    (hx : Bounds x (21/2000) (217/20000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_75_lower hθ hx, cell_75_upper hθ hx⟩

private theorem cover_142 {θ x : ℝ}
    (hθ : Bounds θ (43/80) (27/50))
    (hx : Bounds x (217/20000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  exact ⟨cell_76_lower hθ hx, cell_76_upper hθ hx⟩

private theorem cover_143 {θ x : ℝ}
    (hθ : Bounds θ (43/80) (27/50))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (217/20000) with h | h
  · exact cover_141 hθ ⟨hx.1, h⟩
  · exact cover_142 hθ ⟨h, hx.2⟩

private theorem cover_144 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (21/2000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (43/80) with h | h
  · exact cover_140 ⟨hθ.1, h⟩ hx
  · exact cover_143 ⟨h, hθ.2⟩ hx

private theorem cover_145 {θ x : ℝ}
    (hθ : Bounds θ (107/200) (27/50))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2000) with h | h
  · exact cover_139 hθ ⟨hx.1, h⟩
  · exact cover_144 hθ ⟨h, hx.2⟩

private theorem cover_146 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (49/5000) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (107/200) with h | h
  · exact cover_136 ⟨hθ.1, h⟩ hx
  · exact cover_145 ⟨h, hθ.2⟩ hx

private theorem cover_147 {θ x : ℝ}
    (hθ : Bounds θ (53/100) (27/50))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (49/5000) with h | h
  · exact cover_131 hθ ⟨hx.1, h⟩
  · exact cover_146 hθ ⟨h, hx.2⟩

private theorem cover_148 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (27/50))
    (hx : Bounds x (21/2500) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (53/100) with h | h
  · exact cover_122 ⟨hθ.1, h⟩ hx
  · exact cover_147 ⟨h, hθ.2⟩ hx

private theorem cover_149 {θ x : ℝ}
    (hθ : Bounds θ (13/25) (27/50))
    (hx : Bounds x (7/1250) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (21/2500) with h | h
  · exact cover_113 hθ ⟨hx.1, h⟩
  · exact cover_148 hθ ⟨h, hx.2⟩

private theorem cover_150 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (27/50))
    (hx : Bounds x (7/1250) (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (13/25) with h | h
  · exact cover_96 ⟨hθ.1, h⟩ hx
  · exact cover_149 ⟨h, hθ.2⟩ hx

private theorem cover_151 {θ x : ℝ}
    (hθ : Bounds θ (1/2) (27/50))
    (hx : Bounds x 0 (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total x (7/1250) with h | h
  · exact cover_79 hθ ⟨hx.1, h⟩
  · exact cover_150 hθ ⟨h, hx.2⟩

private theorem cover_152 {θ x : ℝ}
    (hθ : Bounds θ (23/50) (27/50))
    (hx : Bounds x 0 (7/625)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  rcases le_total θ (1/2) with h | h
  · exact cover_30 ⟨hθ.1, h⟩ hx
  · exact cover_151 ⟨h, hθ.2⟩ hx

 theorem scaled_cells_cover {θ x : ℝ}
    (hθ : Bounds θ (46/100) (54/100)) (hx : Bounds x 0 (112/10000)) :
    ScaledCell θ x (-1) (-377/10) ∧ ScaledCell θ x 1 (-41) := by
  apply cover_152
  · constructor <;> linarith [hθ.1, hθ.2]
  · constructor <;> linarith [hx.1, hx.2]

end BstLean.Part228
