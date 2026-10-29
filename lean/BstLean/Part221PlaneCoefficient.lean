import BstLean.Part221PlaneEigen
import BstLean.Part168XK

/-! The exact gated-plane bound for the actual Agent coefficient fields. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part151 (mask)
open BstLean.Part167 BstLean.Part168

variable {m n : ℕ}
theorem plane_norm_eigen {v : ℝ} (hv : 0 < v) {h : Fin m → ℝ} (hh : h ≠ 0) (g y ξ₁ ξ₂ : Fin m → ℝ) :
    normSq (((normSq h)⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v h ξ₁ i) • h +
      ((normSq (res h g))⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v (res h g) ξ₂ i) •
        res h g) ≤ v * normSq y * planeEigen ξ₁ ξ₂ := by
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
  have hl := planeEigen_det y ξ₁ ξ₂
  nlinarith [hl, t1, t2]

lemma normSq_planeP_eigen {M : ℕ} {v : ℝ} (hv : 0 < v) (h g : Fin M → ℝ)
    (Y : (Fin M → ℝ) × (Fin M → ℝ) → Fin M → ℝ) (hY : ∀ p, normSq (Y p) ≤ 1)
    (ξ₁ ξ₂ : Fin M → ℝ) : normSq (planeP v h g (gate Y) ξ₁ ξ₂) ≤ v * planeEigen ξ₁ ξ₂ := by
  by_cases hh : h = 0
  · subst hh
    rw [planeP_zero]
    have : normSq (0 : Fin M → ℝ) = 0 := by simp [normSq]
    rw [this]
    exact mul_nonneg hv.le (planeEigen_nonneg _ _)
  · set y := Y (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)
    have e : planeP v h g (gate Y) ξ₁ ξ₂ =
        ((normSq h)⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v h ξ₁ i) • h +
        ((normSq (res h g))⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v (res h g) ξ₂ i) •
          res h g := rfl
    rw [e]
    refine (plane_norm_eigen hv hh g y ξ₁ ξ₂).trans ?_
    have := hY (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)
    have hl := planeEigen_nonneg ξ₁ ξ₂
    have : v * normSq y * planeEigen ξ₁ ξ₂ ≤ v * 1 * planeEigen ξ₁ ξ₂ := by gcongr
    linarith


variable {u w : Fin n → ℝ} {s cs : ℝ}
theorem kap_eigen (hn2 : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (W : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) :
    normSq (kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W) ≤
      2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ)) * planeEigen ξ₁ ξ₂ := by
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have htA : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; have : 0 < n := by omega
                          positivity
    have : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast this
    positivity
  refine (normSq_coef_le hγ _ _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (normSq_planeP_eigen htA _ _ _ (hY1 _) ξ₁ ξ₂) hγ


end BstLean.Part221
