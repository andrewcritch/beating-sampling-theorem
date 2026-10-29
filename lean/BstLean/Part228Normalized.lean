import BstLean.Part228Blocks

/-! The normalized latitude transform has the formula used by the paper evaluator. -/
namespace BstLean.Part228
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part161 (muI)
open BstLean.Part157 (latitude)

noncomputable def normalizedExponent (n : ℕ) (θ b u : ℝ) : ℝ :=
  -log (1 - u) / 2 + n * (1 - θ) * u / (2 * θ * (1 - u)) -
    ((n - 1 : ℕ) : ℝ) * log (1 + endpointRatio b * u) / 2

noncomputable def normalizedTailMass (n : ℕ) (θ lo hi ul uu : ℝ) : ℝ :=
  exp (-(n * (1 - θ) / (2 * θ))) + exp (normalizedExponent n θ lo ul) +
    exp (normalizedExponent n θ hi uu)

theorem normalized_transform_identity {n : ℕ} (hn : 1 ≤ n) {θ b u : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    chernoffExponent n (√(1 - θ)) (√(θ / n)) b (n * u / (2 * θ)) =
      normalizedExponent n θ b u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hτ : √(θ / n) ^ 2 = θ / n := sq_sqrt (div_nonneg hθ.le hn0.le)
  have ha : √(1 - θ) ^ 2 = 1 - θ := sq_sqrt (by linarith)
  have hu : 2 * (n * u / (2 * θ)) * (θ / n) = u := by field_simp
  have hb : 2 * (n * u / (2 * θ)) * endpointRatio b * (θ / n) =
      endpointRatio b * u := by field_simp
  unfold chernoffExponent normalizedExponent
  rw [hτ, ha, hu, hb]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem normalized_interval_tail {n : ℕ} (hn : 1 ≤ n) {θ lo hi ul uu : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hlo : 0 < lo) (hlo1 : lo < 1) (hhi : 0 < hi) (hhi1 : hi < 1)
    (hul : ul ≤ 0) (huu : 0 ≤ uu)
    (hlax : 0 < 1 - ul) (hltr : 0 < 1 + endpointRatio lo * ul)
    (huax : 0 < 1 - uu) (hutr : 0 < 1 + endpointRatio hi * uu) :
    (muI n).real {p | latitude (√(1 - θ)) (√(θ / n)) p ∉ Icc lo hi} ≤
      normalizedTailMass n θ lo hi ul uu := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hτ : √(θ / n) ^ 2 = θ / n := sq_sqrt (div_nonneg hθ.le hn0.le)
  have ha : √(1 - θ) ^ 2 = 1 - θ := sq_sqrt (by linarith)
  have hu (u : ℝ) : 2 * (n * u / (2 * θ)) * (√(θ / n)) ^ 2 = u := by
    rw [hτ]; field_simp
  have hb (b u : ℝ) : 2 * (n * u / (2 * θ)) * endpointRatio b * (√(θ / n)) ^ 2 =
      endpointRatio b * u := by rw [hτ]; field_simp
  have hlax' : 0 < 1 - 2 * (n * ul / (2 * θ)) * (√(θ / n)) ^ 2 := by
    rw [hu]; exact hlax
  have hltr' : 0 < 1 + 2 * (n * ul / (2 * θ)) * endpointRatio lo * (√(θ / n)) ^ 2 := by
    rw [hb]; exact hltr
  have huax' : 0 < 1 - 2 * (n * uu / (2 * θ)) * (√(θ / n)) ^ 2 := by
    rw [hu]; exact huax
  have hutr' : 0 < 1 + 2 * (n * uu / (2 * θ)) * endpointRatio hi * (√(θ / n)) ^ 2 := by
    rw [hb]; exact hutr
  have h := latitude_interval_tail n (sqrt_nonneg (1 - θ)) (sqrt_pos.mpr (div_pos hθ hn0))
    hlo hlo1 hhi hhi1
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hn0.le hul) (by positivity))
    (div_nonneg (mul_nonneg hn0.le huu) (by positivity)) hlax' hltr' huax' hutr'
  refine h.trans (le_of_eq ?_)
  unfold latitudeTailMass normalizedTailMass
  rw [chernoffMajorant_eq_exp n hlax' hltr', chernoffMajorant_eq_exp n huax' hutr',
    normalized_transform_identity hn hθ hθ1, normalized_transform_identity hn hθ hθ1,
    ha, hτ]
  congr 3
  field_simp

theorem normalized_bulk_tail {n : ℕ} (hn : 4096 ≤ n) {θ ul uu : ℝ}
    (hθl : 46 / 100 ≤ θ) (hθu : θ ≤ 54 / 100)
    (hul : ul ≤ 0) (huu : 0 ≤ uu) (hlax : 0 < 1 - ul)
    (hltr : 0 < 1 + endpointRatio (√(1 - θ) - 6 * √(θ / n)) * ul)
    (huax : 0 < 1 - uu)
    (hutr : 0 < 1 + endpointRatio (√(1 - θ) + 6 * √(θ / n)) * uu) :
    √(2 * (muI n).real {p | latitude (√(1 - θ)) (√(θ / n)) p ∉
      Icc (√(1 - θ) - 6 * √(θ / n)) (√(1 - θ) + 6 * √(θ / n))}) ≤
      √(2 * normalizedTailMass n θ (√(1 - θ) - 6 * √(θ / n))
        (√(1 - θ) + 6 * √(θ / n)) ul uu) := by
  obtain ⟨hlo, hord, hhi1⟩ := normalized_bulk_frontier hn hθl hθu
  exact sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (normalized_interval_tail (by omega) (by linarith) (by linarith)
      hlo (lt_trans hord hhi1) (lt_trans hlo hord) hhi1 hul huu hlax hltr huax hutr)
    (by norm_num))

theorem endpointRatio_le_four {b : ℝ} (hb : 0 ≤ b) (hbU : b ≤ 7 / 8) :
    0 ≤ endpointRatio b ∧ endpointRatio b ≤ 4 := by
  have hsq : b ^ 2 ≤ (7 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hb hbU 2
  have hd : 0 < 1 - b ^ 2 := by nlinarith
  constructor
  · exact div_nonneg (sq_nonneg _) hd.le
  · unfold endpointRatio
    rw [div_le_iff₀ hd]
    nlinarith

/-- The explicit pair of tilts is admissible throughout the frontier interval.
The resulting root remains the actual analytic value. -/
theorem normalized_bulk_tail_explicit {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ}
    (hθl : 46 / 100 ≤ θ) (hθu : θ ≤ 54 / 100) :
    √(2 * (muI n).real {p | latitude (√(1 - θ)) (√(θ / n)) p ∉
      Icc (√(1 - θ) - 6 * √(θ / n)) (√(1 - θ) + 6 * √(θ / n))}) ≤
      √(2 * normalizedTailMass n θ (√(1 - θ) - 6 * √(θ / n))
        (√(1 - θ) + 6 * √(θ / n)) (-(8 / √(n : ℝ))) (8 / √(n : ℝ))) := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsN : (64 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by nlinarith)
  have hr0 : 0 ≤ (8 : ℝ) / √(n : ℝ) := by positivity
  have hrU : (8 : ℝ) / √(n : ℝ) ≤ 1 / 8 := by
    rw [div_le_iff₀ (sqrt_pos.mpr hn0)]
    linarith
  have haU : √(1 - θ) ≤ (4 / 5 : ℝ) := sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have htU : √(θ / n) ≤ (1 / 80 : ℝ) := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · rw [div_le_iff₀ hn0]
      nlinarith
  have hhiU : √(1 - θ) + 6 * √(θ / n) ≤ 7 / 8 := by linarith
  obtain ⟨hlo, hord, _⟩ := normalized_bulk_frontier hn hθl hθu
  obtain ⟨hAl0, hAlU⟩ := endpointRatio_le_four hlo.le (hord.le.trans hhiU)
  obtain ⟨hAu0, _⟩ := endpointRatio_le_four (lt_trans hlo hord).le hhiU
  have hprod : endpointRatio (√(1 - θ) - 6 * √(θ / n)) * (8 / √(n : ℝ)) ≤ 1 / 2 := by
    calc _ ≤ 4 * (8 / √(n : ℝ)) := mul_le_mul_of_nonneg_right hAlU hr0
      _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hrU (by norm_num)
      _ = _ := by norm_num
  exact normalized_bulk_tail hn hθl hθu (neg_nonpos.mpr hr0) hr0
    (by linarith) (by rw [mul_neg]; linarith) (by linarith)
    (by positivity)

end BstLean.Part228
