import BstLean.Part203Fibre

/-! Part 232: a finite radius cover starts at zero and retains its terminal cell. -/
namespace BstLean.Part232
open Real

/-- The first cell includes zero. Each later cell excludes its lower boundary. -/
def radiusCell (h : ℕ → ℝ) (i : ℕ) (r : ℝ) : Prop :=
  (if i = 0 then 0 ≤ r else h i < r) ∧ r ≤ h (i + 1)

/-- Strictly increasing radius endpoints, with an explicit zero endpoint. -/
structure RadiusCover where
  K : ℕ
  positive : 0 < K
  h : ℕ → ℝ
  zero : h 0 = 0
  increasing : ∀ i < K, h i < h (i + 1)

lemma RadiusCover.nonneg (C : RadiusCover) {i : ℕ} (hi : i ≤ C.K) : 0 ≤ C.h i := by
  induction i with
  | zero => rw [C.zero]
  | succ i ih => exact (ih (by omega)).trans (C.increasing i (by omega)).le

/-- A nonnegative radius belongs to a finite cell or to the terminal cell. -/
theorem radius_cover {h : ℕ → ℝ} {K : ℕ} (hK : 0 < K) {r : ℝ} (hr : 0 ≤ r) :
    (∃ i < K, radiusCell h i r) ∨ h K < r := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases hlast : h (K + 1) < r
    · exact Or.inr hlast
    · left
      by_cases hK0 : K = 0
      · subst K
        exact ⟨0, by omega, by simp [radiusCell, hr, not_lt.mp hlast]⟩
      · rcases ih (by omega) with ⟨i, hi, hcell⟩ | hprev
        · exact ⟨i, by omega, hcell⟩
        · exact ⟨K, by omega, by simp [radiusCell, hK0, hprev, not_lt.mp hlast]⟩

/-- The lower endpoint of every finite cell gives a squared-radius lower bound. -/
lemma RadiusCover.lower_square (C : RadiusCover) {i : ℕ} {r : ℝ}
    (hi : i < C.K) (hr : 0 ≤ r) (hc : radiusCell C.h i r) : C.h i ^ 2 ≤ r ^ 2 := by
  have hl : C.h i ≤ r := by
    by_cases hz : i = 0
    · subst i; rw [C.zero]; exact hr
    · exact (by simpa [radiusCell, hz] using hc.1 : C.h i < r).le
  exact pow_le_pow_left₀ (C.nonneg (by omega)) hl 2

/-- A single affine majorant covers all cells; the terminal failure bound is one. -/
theorem radius_majorant (C : RadiusCover) {g : ℕ → ℝ} {F : ℝ → ℝ} {c₀ c₁ : ℝ}
    (hc₁ : 0 ≤ c₁)
    (hline : ∀ i < C.K, g i ≤ c₀ + c₁ * C.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * C.h C.K ^ 2)
    (hfinite : ∀ i < C.K, ∀ r, 0 ≤ r → radiusCell C.h i r → F r ≤ g i)
    (hlast : ∀ r, C.h C.K < r → F r ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    F r ≤ c₀ + c₁ * r ^ 2 := by
  rcases radius_cover C.positive hr with ⟨i, hi, hcell⟩ | htail
  · exact (hfinite i hi r hr hcell).trans ((hline i hi).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (C.lower_square hi hr hcell) hc₁)))
  · exact (hlast r htail).trans (hterminal.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (C.nonneg le_rfl) htail.le 2) hc₁)))

/-- The zero endpoint enforces the complete first-cell payment. -/
lemma first_cell_payment (C : RadiusCover) {g : ℕ → ℝ} {c₀ c₁ : ℝ}
    (hline : ∀ i < C.K, g i ≤ c₀ + c₁ * C.h i ^ 2) : g 0 ≤ c₀ := by
  simpa [C.zero] using hline 0 C.positive

end BstLean.Part232
