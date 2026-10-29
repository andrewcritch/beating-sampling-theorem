import BstLean.Part184DS

/-! Part 208: the deterministic centred Gram reduction in the sharp TI proof.
The probabilistic lower singular-value estimate is a separate obligation. -/
namespace BstLean.Part208
open Real Matrix
open BstLean.Part130 (normSq normSq_nonneg)

/-- Clipping a negative lower singular threshold at zero preserves the paper error. -/
theorem clipped_lower_sq {r h : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) :
    r ^ 2 - (2 * r * h + h ^ 2) ≤ (max (r - h) 0) ^ 2 := by
  rcases le_total h r with hl | hl
  · rw [max_eq_left (sub_nonneg.mpr hl)]
    nlinarith [sq_nonneg h]
  · rw [max_eq_right (sub_nonpos.mpr hl)]
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hl), sq_nonneg h]

/-- Two singular bounds give the centred Gram error `v*(2*sqrt(K)*h+h^2)`.
No dimension floor or positive lower singular threshold is used. -/
theorem gram_from_singular_bounds {N d : ℕ} (G : Matrix (Fin N) (Fin d) ℝ)
    {v K h : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hlo : ∀ z, √v * max (√K - h) 0 * √(normSq z) ≤ √(normSq (G *ᵥ z)))
    (hhi : ∀ z, √(normSq (G *ᵥ z)) ≤ √v * (√K + h) * √(normSq z))
    (p q : Fin d → ℝ) :
    |(G *ᵥ p) ⬝ᵥ (G *ᵥ q) - v * K * (p ⬝ᵥ q)| ≤
      v * (2 * √K * h + h ^ 2) * √(normSq p) * √(normSq q) := by
  have hL : ∀ z, (v * K - v * (2 * √K * h + h ^ 2)) * normSq z ≤
      normSq (G *ᵥ z) := by
    intro z
    have h1 := pow_le_pow_left₀ (by positivity) (hlo z) 2
    rw [mul_pow, mul_pow, sq_sqrt hv, sq_sqrt (normSq_nonneg _),
      sq_sqrt (normSq_nonneg _)] at h1
    have h2 := clipped_lower_sq (sqrt_nonneg K) hh
    rw [sq_sqrt hK] at h2
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hv) (normSq_nonneg z)
    nlinarith only [h1, h3]
  have hU : ∀ z, normSq (G *ᵥ z) ≤
      (v * K + v * (2 * √K * h + h ^ 2)) * normSq z := by
    intro z
    have h1 := pow_le_pow_left₀ (sqrt_nonneg _) (hhi z) 2
    rw [mul_pow, mul_pow, sq_sqrt hv, sq_sqrt (normSq_nonneg _),
      sq_sqrt (normSq_nonneg _)] at h1
    have he : (√K + h) ^ 2 = K + 2 * √K * h + h ^ 2 := by
      nlinarith [sq_sqrt hK]
    rw [he] at h1
    nlinarith only [h1]
  have hres := BstLean.Part184.gram_two_sided G hL hU p q
  have hmid : (v * K + v * (2 * √K * h + h ^ 2) +
      (v * K - v * (2 * √K * h + h ^ 2))) / 2 = v * K := by ring
  have hrad : (v * K + v * (2 * √K * h + h ^ 2) -
      (v * K - v * (2 * √K * h + h ^ 2))) / 2 = v * (2 * √K * h + h ^ 2) := by ring
  rw [hmid, hrad] at hres
  exact hres

/-- The four bilinear terms of the sharp E block combine with the projected cross bound. -/
theorem Eblock_four_terms {main cross₁ cross₂ plane v K L P r ell T zeta : ℝ}
    (hm : |main| ≤ v * K * (L + P ^ 2) + v * r * ell ^ 2)
    (hc₁ : |cross₁| ≤ T * zeta * ell) (hc₂ : |cross₂| ≤ T * zeta * ell)
    (hp : |plane| ≤ T ^ 2) :
    |main + cross₁ + cross₂ + plane| ≤
      v * K * (L + P ^ 2) + v * r * ell ^ 2 + 2 * T * zeta * ell + T ^ 2 := by
  have h := (abs_add_le (main + cross₁ + cross₂) plane).trans
    (add_le_add ((abs_add_le (main + cross₁) cross₂).trans
      (add_le_add (abs_add_le main cross₁) le_rfl)) le_rfl)
  linarith

end BstLean.Part208
