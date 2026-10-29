import BstLean.Part211Junction

/-! The directional transfer uses the earlier full-centre error. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part211

/-- The Part211 full error equals the unscaled hidden-vector squared error. -/
theorem fullError_eq_normSq {n J : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    fullError (J := J) A M c τ =
      normSq (hid2Mean_cr A M c τ - hiddenCentre (J := J) A M c τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold fullError mA
  push_cast
  field_simp
  <;> ring

/-- A lower centre energy and a full error give the relative directional transfer error. -/
theorem relative_centre_error {m : ℕ} (μ b : Fin m → ℝ) {N e ξ : ℝ}
    (hN : 0 < N) (he : 0 < e) (hξ : 0 ≤ ξ)
    (hb : N * e ≤ normSq b) (hfull : normSq (μ - b) ≤ ξ) :
    nrm (μ - b) / nrm b ≤ √(ξ / (N * e)) := by
  have hb0 : 0 < normSq b := lt_of_lt_of_le (mul_pos hN he) hb
  have hbN : 0 < nrm b := sqrt_pos.mpr hb0
  apply (div_le_iff₀ hbN).mpr
  have hSq : (√(ξ / (N * e)) * nrm b) ^ 2 = ξ / (N * e) * normSq b := by
    rw [mul_pow, sq_sqrt (by positivity), nrm_sq]
  have hmul := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ ξ / (N * e))
  have hc : ξ / (N * e) * (N * e) = ξ := div_mul_cancel₀ ξ (mul_pos hN he).ne'
  rw [hc] at hmul
  have hlow : nrm (μ - b) ^ 2 ≤ (√(ξ / (N * e)) * nrm b) ^ 2 := by
    rw [nrm_sq, hSq]
    exact hfull.trans hmul
  exact (sq_le_sq₀ (nrm_nonneg _) (by positivity)).mp hlow

/-- The earlier scalar full-error formula supplies the computed-centre transfer ratio. -/
theorem computed_relative_error {n J : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {e ξ : ℝ} (he : 0 < e) (hξ : 0 ≤ ξ)
    (hb : (n : ℝ) * e ≤ normSq (hiddenCentre (J := J) A M c τ))
    (hfull : fullError (J := J) A M c τ ≤ ξ) :
    nrm (hid2Mean_cr A M c τ - hiddenCentre (J := J) A M c τ) /
      nrm (hiddenCentre (J := J) A M c τ) ≤ √(ξ / ((n : ℝ) * e)) := by
  rw [fullError_eq_normSq hn] at hfull
  exact relative_centre_error _ _
    (by exact_mod_cast (show 0 < n by omega)) he hξ hb hfull

/-- This is the final squared allowance in the paper directional formula. -/
noncomputable def directionFormula (n : ℕ) (D err MP ξ e : ℝ) : ℝ :=
  (D + err / √e + √(MP * ξ / ((n : ℝ) * e))) ^ 2

#print axioms fullError_eq_normSq
#print axioms relative_centre_error
#print axioms computed_relative_error
end BstLean.Part215
