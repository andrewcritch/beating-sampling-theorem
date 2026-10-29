import BstLean.Part167Lam

/-!
# Part 167 (file `PB`): the plane part `p` of `A₂ᵀD₂y` through `Λ`

No proof is left open; no `native_decide` or `axiom` is used.

* **`plane_norm`**: in the representation of file `Split` (with the gate `D_j = 1{(A₂h₁)_j > 0}`),
  the plane part `p = α₁h + α₂r` satisfies `|p|² ≤ v·|y|²·λ⁺(ξ₁, ξ₂)` (paper:
  `|p|²/|y|² ≤ t_A λ_max(Λ)`), for `h ≠ 0`, `v > 0`.
-/

namespace BstLean.Part167

open MeasureTheory Real
open BstLean.Part130 BstLean.Part134
open BstLean.Part157 (cOf)
open BstLean.Part151 (mask)

variable {m : ℕ}

lemma normSq_two (a b : ℝ) (h r : Fin m → ℝ) :
    normSq (a • h + b • r) =
      a ^ 2 * normSq h + b ^ 2 * normSq r + 2 * a * b * ∑ j, h j * r j := by
  unfold normSq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The plane part through `Λ`.** -/
theorem plane_norm {v : ℝ} (hv : 0 < v) {h : Fin m → ℝ} (hh : h ≠ 0) (g y ξ₁ ξ₂ : Fin m → ℝ) :
    normSq (((normSq h)⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v h ξ₁ i) • h +
      ((normSq (res h g))⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v (res h g) ξ₂ i) •
        res h g) ≤ v * normSq y * lamP ξ₁ ξ₂ := by
  set r := res h g
  have hH : 0 < normSq h := lt_of_le_of_ne (normSq_nonneg h) (Ne.symm (normSq_ne_zero hh))
  set κ := √v * √(normSq h) with hκ
  have hκ0 : 0 < κ := by positivity
  have hmask : ∀ i, mask (cOf v h ξ₁ i) = mask (ξ₁ i) := by
    intro i
    simp only [cOf, Pi.smul_apply, smul_eq_mul]
    exact BstLean.Part153.mask_mul_pos hκ0 _
  set P1 := ∑ j, mask (ξ₁ j) * y j * ξ₁ j
  set P2 := ∑ j, mask (ξ₁ j) * y j * ξ₂ j
  have e1 : ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v h ξ₁ i = κ * P1 := by
    simp only [hmask]; simp only [cOf, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  set κ₂ := √v * √(normSq r)
  have e2 : ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v r ξ₂ i = κ₂ * P2 := by
    simp only [hmask]; simp only [cOf, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, normSq_two]
  have horth : ∑ j, h j * r j = 0 := by
    have := res_orth hh g
    rw [← this]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [horth]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  have t1 : ((normSq h)⁻¹ * (κ * P1)) ^ 2 * normSq h = v * P1 ^ 2 := by
    rw [hκ, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hv.le, Real.sq_sqrt hH.le]
    field_simp
  have t2 : ((normSq r)⁻¹ * (κ₂ * P2)) ^ 2 * normSq r ≤ v * P2 ^ 2 := by
    rcases (normSq_nonneg r).eq_or_lt with h0 | h0
    · rw [← h0]; simp; positivity
    · simp only [κ₂]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hv.le, Real.sq_sqrt h0.le]
      apply le_of_eq; field_simp
  have hl := lam_det y ξ₁ ξ₂
  nlinarith [hl, t1, t2]

end BstLean.Part167
