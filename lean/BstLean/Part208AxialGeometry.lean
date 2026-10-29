import BstLean.Part208RadialWeight

/-! Part 208: explicit latitude coordinates for a shifted Gaussian vector. -/
namespace BstLean.Part208
open Real Matrix
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53)

lemma normSq_cons {d : ℕ} (a : ℝ) (v : Fin d → ℝ) :
    normSq (Fin.cons a v) = a ^ 2 + normSq v := by
  simp [normSq, Fin.sum_univ_succ]

lemma dot_cons {d : ℕ} (a b : ℝ) (v w : Fin d → ℝ) :
    Fin.cons a v ⬝ᵥ Fin.cons b w = a * b + v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ]

noncomputable def axialDen (a τ r : ℝ) : ℝ := √(a ^ 2 + τ ^ 2 * r ^ 2)
noncomputable def axialLong (a τ r : ℝ) : ℝ := a / axialDen a τ r
noncomputable def axialTrans (a τ r : ℝ) : ℝ := τ * r / axialDen a τ r

lemma axialLong_abs_le (a τ r : ℝ) : |axialLong a τ r| ≤ 1 := by
  unfold axialLong axialDen
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  by_cases h : a ^ 2 + τ ^ 2 * r ^ 2 = 0
  · simp [h]
  have hp : 0 < a ^ 2 + τ ^ 2 * r ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm h)
  apply (div_le_iff₀ (sqrt_pos.mpr hp)).mpr
  simp only [one_mul]
  apply (le_sqrt (abs_nonneg _) hp.le).mpr
  simp only [sq_abs]
  nlinarith [mul_nonneg (sq_nonneg τ) (sq_nonneg r)]

lemma axialTrans_abs_le (a τ r : ℝ) : |axialTrans a τ r| ≤ 1 := by
  unfold axialTrans axialDen
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  by_cases h : a ^ 2 + τ ^ 2 * r ^ 2 = 0
  · simp [h]
  have hp : 0 < a ^ 2 + τ ^ 2 * r ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm h)
  apply (div_le_iff₀ (sqrt_pos.mpr hp)).mpr
  simp only [one_mul]
  apply (le_sqrt (abs_nonneg _) hp.le).mpr
  simp only [sq_abs, mul_pow]
  linarith [sq_nonneg a]

/-- The identity holds also at the zero vector, with zero normalization. -/
theorem unit_cons_dot {d : ℕ} (a τ p : ℝ) (G v : Fin d → ℝ) :
    unitF53 (Fin.cons a (τ • G)) ⬝ᵥ Fin.cons p v =
      axialLong a τ (radF53 G) * p +
        axialTrans a τ (radF53 G) * (v ⬝ᵥ unitF53 G) := by
  have hN : normSq (Fin.cons a (τ • G)) = a ^ 2 + τ ^ 2 * (radF53 G) ^ 2 := by
    rw [normSq_cons, BstLean.Part130.normSq_smul, BstLean.Part162.radF_sq]
    rfl
  have hD : unitF53 (Fin.cons a (τ • G)) =
      (axialDen a τ (radF53 G))⁻¹ • Fin.cons a (τ • G) := by
    change (1 / √(normSq (Fin.cons a (τ • G)))) • _ = _
    rw [hN, one_div]
    rfl
  have hG : G ⬝ᵥ v = radF53 G * (v ⬝ᵥ unitF53 G) := by
    conv_lhs => rw [← BstLean.Part162.unitF_smul G]
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm]
  rw [hD, smul_dotProduct, smul_eq_mul, dot_cons, smul_dotProduct, smul_eq_mul, hG]
  unfold axialLong axialTrans
  ring

end BstLean.Part208
