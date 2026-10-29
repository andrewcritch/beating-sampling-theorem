import BstLean.Part293Quadrature

/-! Fixed table prices from normalized operator and grid-width bounds. -/
namespace BstLean.Part293
open Real BstLean.Part169

noncomputable def tableSigma (n : ℕ) : ℝ := √(2.48 / ((n : ℝ) - 1))

theorem tableSigma_bounds {n : ℕ} (hn : 8000 ≤ n) :
    0 < tableSigma n ∧ tableSigma n ≤ 0.017608 ∧
      √(n : ℝ) * tableSigma n ^ 2 ≤ 0.02774 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hs : (89.44 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hs0 := sqrt_pos.mpr hn0
  have hratio : (n : ℝ) / ((n : ℝ) - 1) ≤ 8000 / 7999 := by
    rw [div_le_iff₀ hd]
    linarith
  refine ⟨sqrt_pos.mpr (div_pos (by norm_num) hd), ?_, ?_⟩
  · apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hd]
    nlinarith
  · rw [tableSigma, sq_sqrt (div_nonneg (by norm_num) hd.le)]
    have he : √(n : ℝ) * (2.48 / ((n : ℝ) - 1)) =
        2.48 * ((n : ℝ) / ((n : ℝ) - 1)) / √(n : ℝ) := by
      field_simp
      nlinarith [sq_sqrt hn0.le]
    rw [he]
    calc
      _ ≤ (2.48 : ℝ) * (8000 / 7999) / 89.44 := by gcongr
      _ ≤ (0.02774 : ℝ) := by norm_num

theorem finite_rule_ratio_coarse {n : ℕ} (hn : 8000 ≤ n) :
    ((n : ℝ) * √(n : ℝ)) / Jz n ≤ 1.000002 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hs : √(1 / (n : ℝ)) ≤ 0.011181 :=
    sqrt_le_iff.mpr ⟨by norm_num, hx.trans (by norm_num)⟩
  have hp : (1 / (n : ℝ)) * √(1 / (n : ℝ)) ≤ (1 / 8000 : ℝ) * 0.011181 :=
    mul_le_mul hx hs (sqrt_nonneg _) (by norm_num)
  apply (finite_rule_ratio hn).trans
  rw [div_le_iff₀ (show 0 < 1 - (1 / (n : ℝ)) * √(1 / (n : ℝ)) by linarith)]
  linarith

theorem table_rule_prices {n : ℕ} (hn : 8000 ≤ n) :
    (n : ℝ) * (√(n : ℝ) * ((19 / 100) * tableSigma n / Jz n)) ≤ 0.003346 ∧
      (n : ℝ) * (n * ((9 / 100) * tableSigma n ^ 2 / Jz n)) ≤ 0.002497 := by
  have hr := finite_rule_ratio_coarse hn
  obtain ⟨hsp, hs, hs2⟩ := tableSigma_bounds hn
  have hr0 : 0 ≤ ((n : ℝ) * √(n : ℝ)) / Jz n := by positivity
  constructor
  · calc
      _ = (((n : ℝ) * √(n : ℝ)) / Jz n) * ((19 / 100) * tableSigma n) := by ring
      _ ≤ (1.000002 : ℝ) * ((19 / 100) * 0.017608) := by gcongr
      _ ≤ (0.003346 : ℝ) := by norm_num
  · calc
      _ = (((n : ℝ) * √(n : ℝ)) / Jz n) * ((9 / 100) * (√(n : ℝ) * tableSigma n ^ 2)) := by
        symm
        calc
          _ = (n : ℝ) * (√(n : ℝ)) ^ 2 * (9 / 100) * tableSigma n ^ 2 / Jz n := by ring
          _ = _ := by rw [sq_sqrt (Nat.cast_nonneg n)]; ring
      _ ≤ (1.000002 : ℝ) * ((9 / 100) * 0.02774) := by gcongr
      _ ≤ (0.002497 : ℝ) := by norm_num

theorem table_grid_prices {n : ℕ} (hn : 8000 ≤ n) {P delta : ℝ}
    (hP0 : 0 ≤ P) (hd0 : 0 ≤ delta)
    (hP : P ^ 2 ≤ 16.411 * (n : ℝ))
    (hd : (n : ℝ) * √(n : ℝ) * delta ≤ 0.008612) :
    (n : ℝ) * (P * delta / (√(n : ℝ) * √(391 / 1000 : ℝ))) ≤ 0.000625 ∧
      (n : ℝ) * (2 * P ^ 2 * delta / (n * √(391 / 1000 : ℝ))) ≤ 0.00507 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 := sqrt_pos.mpr hn0
  have hs : (89.44 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hq : (0.6252 : ℝ) ≤ √(391 / 1000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hq0 : (0 : ℝ) < √(391 / 1000 : ℝ) := by positivity
  have hden : (89.44 : ℝ) * 0.6252 ≤ √(n : ℝ) * √(391 / 1000 : ℝ) :=
    mul_le_mul hs hq (by norm_num) (sqrt_nonneg _)
  have hP' : P ≤ 4.052 * √(n : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
    rw [mul_pow, sq_sqrt hn0.le]
    nlinarith
  constructor
  · rw [← mul_div_assoc, div_le_iff₀ (mul_pos hs0 hq0)]
    have hm := mul_le_mul_of_nonneg_right hP' (show 0 ≤ (n : ℝ) * delta by positivity)
    have hb := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4.052)
    nlinarith only [hm, hb, hden]
  · have he : (n : ℝ) * (2 * P ^ 2 * delta / (n * √(391 / 1000 : ℝ))) =
        2 * P ^ 2 * delta / √(391 / 1000 : ℝ) := by field_simp
    rw [he, div_le_iff₀ hq0]
    apply (mul_le_mul_iff_right₀ hs0).mp
    have hm := mul_le_mul_of_nonneg_right hP (show 0 ≤ delta * √(n : ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2 * 16.411)
    nlinarith only [hm, hb, hden]

end BstLean.Part293
