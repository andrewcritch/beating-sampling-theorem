import BstLean.Part153Lp

/-!
# Part 153: the concentration inequality of Part 152 in the form of an event at level `L_c`

For a function `g` of a Gaussian matrix with entry variance `v > 0`, Lipschitz with constant `L`
for the Frobenius norm, and a level `L_c ≥ 0`: the deviation `√(2·L_c·v)·L` has charge
`exp(−L_c)`. The events have STRICT inequalities (as in the paper), so that the statements are
true also for `L = 0` (a constant function).

* `conc_upper_strict`: `Pr(g > E g + √(2L_c v)·L) ≤ exp(−L_c)`.
* `conc_lower_strict`: `Pr(g < E g − √(2L_c v)·L) ≤ exp(−L_c)`.
* `conc_abs_strict`: `Pr(|g − E g| > √(2L_c v)·L) ≤ 2·exp(−L_c)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part152

variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

lemma const_of_lip_zero
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ, |g M - g M'| ≤ 0 * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    (v : ℝ) (M : Matrix (Fin m) (Fin k) ℝ) : ∫ M, g M ∂gaussMat m k v = g M := by
  have h : ∀ M', g M' = g M := fun M' => by
    have := hL M' M
    rw [zero_mul] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  simp_rw [h]
  simp

lemma conc_exponent {v : ℝ} (hv : 0 < v) {Lc : ℝ} (hLc : 0 ≤ Lc) (hL : 0 < L) :
    -(√(2 * Lc * v) * L) ^ 2 / (2 * (v * L ^ 2)) = -Lc := by
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- `Pr(g > E g + √(2L_c v)·L) ≤ exp(−L_c)`. -/
theorem conc_upper_strict (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ, |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 < v) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat m k v).real {M | ∫ M, g M ∂gaussMat m k v + √(2 * Lc * v) * L < g M} ≤
      Real.exp (-Lc) := by
  rcases hL0.eq_or_lt with h0 | hpos
  · subst h0
    have he : {M : Matrix (Fin m) (Fin k) ℝ |
        ∫ M, g M ∂gaussMat m k v + √(2 * Lc * v) * 0 < g M} = ∅ := by
      ext M
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, mul_zero, add_zero]
      exact (const_of_lip_zero hL v M).ge
    rw [he]
    simp [Real.exp_nonneg]
  · have h := gaussConc_mat_upper_sharp hL0 hL hv.le (t := √(2 * Lc * v) * L)
      (mul_nonneg (Real.sqrt_nonneg _) hL0)
    rw [conc_exponent hv hLc hpos] at h
    refine le_trans (measureReal_mono (fun M hM => ?_)) h
    simp only [mem_ofPred_eq] at hM ⊢
    exact le_of_lt hM

/-- `Pr(g < E g − √(2L_c v)·L) ≤ exp(−L_c)`. -/
theorem conc_lower_strict (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ, |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 < v) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat m k v).real {M | g M < ∫ M, g M ∂gaussMat m k v - √(2 * Lc * v) * L} ≤
      Real.exp (-Lc) := by
  rcases hL0.eq_or_lt with h0 | hpos
  · subst h0
    have he : {M : Matrix (Fin m) (Fin k) ℝ |
        g M < ∫ M, g M ∂gaussMat m k v - √(2 * Lc * v) * 0} = ∅ := by
      ext M
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, mul_zero, sub_zero]
      exact (const_of_lip_zero hL v M).le
    rw [he]
    simp [Real.exp_nonneg]
  · have h := gaussConc_mat_lower_sharp hL0 hL hv.le (t := √(2 * Lc * v) * L)
      (mul_nonneg (Real.sqrt_nonneg _) hL0)
    rw [conc_exponent hv hLc hpos] at h
    refine le_trans (measureReal_mono (fun M hM => ?_)) h
    simp only [mem_ofPred_eq] at hM ⊢
    exact le_of_lt hM

/-- `Pr(|g − E g| > √(2L_c v)·L) ≤ 2·exp(−L_c)`. -/
theorem conc_abs_strict (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ, |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 < v) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat m k v).real {M | √(2 * Lc * v) * L < |g M - ∫ M, g M ∂gaussMat m k v|} ≤
      2 * Real.exp (-Lc) := by
  have h1 := conc_upper_strict hL0 hL hv hLc
  have h2 := conc_lower_strict hL0 hL hv hLc
  have hsub : {M : Matrix (Fin m) (Fin k) ℝ | √(2 * Lc * v) * L < |g M - ∫ M, g M ∂gaussMat m k v|} ⊆
      {M | ∫ M, g M ∂gaussMat m k v + √(2 * Lc * v) * L < g M} ∪
        {M | g M < ∫ M, g M ∂gaussMat m k v - √(2 * Lc * v) * L} := by
    intro M hM
    simp only [mem_ofPred_eq, mem_union] at hM ⊢
    rcases lt_abs.mp hM with h | h
    · left; linarith
    · right; linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  linarith

end BstLean.Part153
