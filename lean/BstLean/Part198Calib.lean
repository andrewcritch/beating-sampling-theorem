import BstLean.Part198Pair
import BstLean.Part194HS

/-! Comparison of the integrated radial estimate with the paper HS coefficient. -/
namespace BstLean.Part198
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part194

theorem cutoff_half {n : ℕ} (hn : 4096 ≤ n) : (n : ℝ) / 2 ≤ S0 n := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 * ((n : ℝ) - 1)) ^ 2 = 12 * ((n : ℝ) - 1) := sq_sqrt (by linarith)
  have hp : 0 ≤ ((n : ℝ) / 4 - 1 / 2) ^ 2 - 12 * ((n : ℝ) - 1) := by
    nlinarith [sq_nonneg ((n : ℝ) - 4096)]
  unfold S0
  nlinarith [sqrt_nonneg (12 * ((n : ℝ) - 1))]

theorem cutoff_full {n : ℕ} (hn : 4096 ≤ n) :
    S0 n ≤ (n : ℝ) - 2 * √((n : ℝ) * 12) := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := sq_sqrt (show 0 ≤ (n : ℝ) * 12 by positivity)
  have h2 := sq_sqrt (show 0 ≤ 12 * ((n : ℝ) - 1) by linarith)
  have hlow : 24 ≤ √(12 * ((n : ℝ) - 1)) := by
    apply (le_sqrt' (by norm_num)).mpr
    linarith
  have hmono : √(12 * ((n : ℝ) - 1)) ≤ √((n : ℝ) * 12) := sqrt_le_sqrt (by linarith)
  have hprod : (√((n : ℝ) * 12) - √(12 * ((n : ℝ) - 1))) *
      (√((n : ℝ) * 12) + √(12 * ((n : ℝ) - 1))) = 12 := by nlinarith
  unfold S0
  nlinarith

theorem rowEps_small : rowEps ≤ (1 : ℝ) / 65536 := by
  have he : exp (-12 : ℝ) = exp (-1) ^ 12 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h := pow_le_pow_left₀ (exp_pos (-1)).le BstLean.Part160.exp_neg_one_le 12
  unfold rowEps
  rw [he]
  exact h.trans (by norm_num)

theorem rowJ_lower {n : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hθ : 1 / 4 ≤ thetaC c τ) : 1 / 4 ≤ rowJ c τ (S0 n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS := cutoff_half hn
  have hS0 : 0 < S0 n := by linarith
  have hd : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := normSq_nonneg c
    positivity
  have hθ' : (1 / 4 : ℝ) ≤ n * τ ^ 2 / (normSq c + n * τ ^ 2) := by
    simpa only [thetaC, rhoC_sqP] using hθ
  have hcn : normSq c ≤ 3 * n * τ ^ 2 := by
    have := (le_div_iff₀ hd).mp hθ'
    linarith
  have hp : 2 / π ≤ (2 / 3 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_gt_three.le
  have hb : (2 / π) * normSq c / (τ ^ 2 * S0 n) ≤ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < τ ^ 2 * S0 n)).mpr
    have h1 := mul_le_mul_of_nonneg_right hp (normSq_nonneg c)
    have h2 := mul_le_mul_of_nonneg_left hS (sq_nonneg τ)
    nlinarith
  have hr : √(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0 n))) ≤ 4 := by
    apply (sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith
  have hr0 : 0 < √(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0 n))) := by
    have := normSq_nonneg c
    positivity
  unfold rowJ
  simpa only [one_div] using one_div_le_one_div_of_le hr0 hr

theorem rowJ_paper_identity {n : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) :
    J0 n (thetaC c τ) = (1 - rowEps) * (1 - 1 / S0 n) * rowJ c τ (S0 n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS0 : 0 < S0 n := lt_trans zero_lt_one (S0_gt_one (by omega))
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hd : normSq c + (n : ℝ) * τ ^ 2 ≠ 0 := by
    have := normSq_nonneg c
    positivity
  have he : 2 * axialC (thetaC c τ) * n / S0 n =
      2 * ((2 / π) * normSq c / (τ ^ 2 * S0 n)) := by
    unfold axialC thetaC
    rw [rhoC_sqP]
    field_simp
    <;> ring
  unfold J0 rowEps rowJ
  rw [he]
  rfl

theorem rowJ_gap {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (hθ : 1 / 4 ≤ thetaC c τ) :
    J0 n (thetaC c τ) ≤ rowJ c τ (S0 n) - rowEps := by
  have hS : 1 < S0 n := S0_gt_one (by omega)
  have hSn : S0 n ≤ 16384 := by
    have hnR : (n : ℝ) ≤ 16384 := by exact_mod_cast hn1
    unfold S0
    linarith [sqrt_nonneg (12 * ((n : ℝ) - 1))]
  have hJ := rowJ_lower hn c hτ hθ
  have hJ0 := (rowJ_bounds c hτ (by linarith : 0 < S0 n)).1
  have hinv : (1 : ℝ) / 16384 ≤ 1 / S0 n :=
    one_div_le_one_div_of_le (by linarith) hSn
  have hreserve : rowEps ≤ rowJ c τ (S0 n) * (1 / S0 n) := by
    have h := mul_le_mul hJ hinv (by norm_num : (0 : ℝ) ≤ 1 / 16384)
      hJ0.le
    exact rowEps_small.trans (by nlinarith only [h])
  have he := rowEps_pos.le
  have hgap : 0 ≤ rowEps * (1 - 1 / S0 n) * rowJ c τ (S0 n) := by
    have hinv1 : 1 / S0 n ≤ 1 := (div_le_one (by linarith)).mpr hS.le
    exact mul_nonneg (mul_nonneg he (by linarith)) hJ0.le
  rw [rowJ_paper_identity hn c hτ]
  nlinarith only [hreserve, hgap]

theorem rowPair_le_paper {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (hθ : 1 / 4 ≤ thetaC c τ) :
    rowPair n c τ (S0 n) ≤ qHS n (thetaC c τ) ^ 2 + 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < S0 n := by linarith [cutoff_half hn]
  obtain ⟨hj0, hj1⟩ := rowJ_bounds c hτ hS
  have he := rowEps_pos.le
  have hje : rowEps ≤ rowJ c τ (S0 n) := rowEps_small.trans
    ((by norm_num : (1 : ℝ) / 65536 ≤ 1 / 4).trans (rowJ_lower hn c hτ hθ))
  let q := 1 - rowJ c τ (S0 n) / 2 + rowEps / 2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hqp : q ≤ qHS n (thetaC c τ) := by
    have := rowJ_gap hn hn1 c hτ hθ
    unfold qHS
    dsimp [q]
    linarith
  have hlast : rowJ c τ (S0 n) * (q + 1) / (2 * n) ≤ 1 / n := by
    have h := mul_le_mul hj1 (show q + 1 ≤ 2 by linarith)
      (show 0 ≤ q + 1 by linarith) (by norm_num : (0 : ℝ) ≤ 1)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have hid : (1 / (n : ℝ)) * (2 * n) = 2 := by field_simp
    rw [hid]
    simpa using h
  calc rowPair n c τ (S0 n) = q ^ 2 + rowJ c τ (S0 n) * (q + 1) / (2 * n) := by
        unfold rowPair q
        field_simp
        <;> ring
    _ ≤ _ := add_le_add (pow_le_pow_left₀ hq0 hqp 2) hlast

#print axioms rowPair_le_paper
#print axioms rowJ_gap
end BstLean.Part198
