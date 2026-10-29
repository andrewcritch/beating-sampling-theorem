import BstLean.Part253DirectionError

/-! The actual pair error allowance decreases with dimension from 12225. -/
namespace BstLean.Part264
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part209

theorem sqrt_div_self {x : ℝ} (hx : 0 < x) : √x / x = 1 / √x := by
  calc
    _ = √x / (√x)^2 := by rw [sq_sqrt hx.le]
    _ = _ := by field_simp

theorem pairQ_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    pairQ n P = 2 * (1 / √(n : ℝ) + gaussMomConst P / n) *
      (1 / √(2 : ℝ) + gaussMomConst P / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pairQ
  calc
    _ = 2 * (√(n : ℝ) / n + gaussMomConst P / n) *
        (1 / √(2 : ℝ) + gaussMomConst P / n) := by field_simp
    _ = _ := by rw [sqrt_div_self hnR]

theorem tangentU_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    tangentU n P = 2 * (√((1 / 2 : ℝ) + twoGaussConst P / (2 * n)) +
      1 / √(n : ℝ) + gaussMomConst (2 * P) / n)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrad : √((n : ℝ)^2 / 2 + (n : ℝ) / 2 * twoGaussConst P) =
      (n : ℝ) * √((1 / 2 : ℝ) + twoGaussConst P / (2 * n)) := by
    calc
      _ = √((n : ℝ)^2 * ((1 / 2 : ℝ) + twoGaussConst P / (2 * n))) := by
        congr 1
        field_simp
        <;> ring
      _ = _ := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hnR.le]
  unfold tangentU activeB
  rw [hrad]
  calc
    _ = 2 * (√((1 / 2 : ℝ) + twoGaussConst P / (2 * n)) +
        √(n : ℝ) / n + gaussMomConst (2 * P) / n)^2 := by field_simp
    _ = _ := by rw [sqrt_div_self hnR]

theorem lengthAlpha_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) :
    lengthAlpha n P ≤ lengthAlpha 12225 P := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := twoGaussConst_nonneg P
  unfold lengthAlpha
  gcongr

theorem pairQ_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) : pairQ n P ≤ pairQ 12225 P := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12225 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hg := gaussMomConst_nonneg P
  rw [pairQ_normalized (n := n) (by omega) P, pairQ_normalized (n := 12225) (by norm_num) P]
  gcongr

theorem tangentU_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) :
    tangentU n P ≤ tangentU 12225 P := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12225 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hg := gaussMomConst_nonneg (2 * P)
  have ht := twoGaussConst_nonneg P
  rw [tangentU_normalized (n := n) (by omega) P, tangentU_normalized (n := 12225) (by norm_num) P]
  gcongr

theorem overlapC_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    overlapC n P = 2 * √32 * (2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) / n +
      8 * (2 * ((2 * P).factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) / (n : ℝ)^2 := by
  unfold overlapC
  field_simp
  <;> ring

theorem overlapC_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) : overlapC n P ≤ overlapC 12225 P := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  rw [overlapC_normalized (n := n) (by omega) P, overlapC_normalized (n := 12225) (by norm_num) P]
  gcongr

theorem pairV_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    pairV n P = pairQ n P + 4 * √32 * √(log 162 + factorialRoot P) / n +
      16 * (log 162 + factorialRoot (2 * P)) / (n : ℝ)^2 := by
  unfold pairV pairPlane
  field_simp
  <;> ring

theorem pairV_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) : pairV n P ≤ pairV 12225 P := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hq := pairQ_le hn P
  have hlog : 0 ≤ log (162 : ℝ) := log_nonneg (by norm_num)
  have hf : 0 ≤ factorialRoot (2 * P) := by unfold factorialRoot; positivity
  rw [pairV_normalized (n := n) (by omega) P, pairV_normalized (n := 12225) (by norm_num) P]
  gcongr

theorem pairDelta_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) (η : ℝ) :
    pairDelta n P η ≤ pairDelta 12225 P η := by
  have ho := overlapC_le hn P
  have hl := lengthAlpha_le hn P
  have hl2 := lengthAlpha_le hn (2 * P)
  have hl0 := lengthAlpha_nonneg n (2 * P)
  unfold pairDelta
  gcongr

theorem lowLengthProb_normalized {n : ℕ} (hn : 0 < n) (η : ℝ) :
    lowLengthProb n η = 4 * exp (-((n : ℝ) * η - 2 / n)^2 / 4) := by
  unfold lowLengthProb
  congr 2
  field_simp
  <;> ring

theorem lowLengthProb_le {n : ℕ} (hn : 12225 ≤ n) :
    lowLengthProb n (1 / 100) ≤ lowLengthProb 12225 (1 / 100) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiv : 2 / (n : ℝ) ≤ 2 / (12225 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have harg : (12225 : ℝ) * (1 / 100) - 2 / 12225 ≤ (n : ℝ) * (1 / 100) - 2 / n := by
    linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 12225 * (1 / 100) - 2 / 12225)
    harg 2
  rw [lowLengthProb_normalized (n := n) (by omega), lowLengthProb_normalized (n := 12225) (by norm_num)]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)

theorem complementRoot_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) :
    complementRoot n P ≤ complementRoot 12225 P := by
  have ht := tangentU_le hn (4 * P)
  have hl := lengthAlpha_le hn (8 * P)
  have hl0 := lengthAlpha_nonneg n (8 * P)
  unfold complementRoot
  gcongr

theorem complementB_le {n : ℕ} (hn : 12225 ≤ n) (P : ℕ) :
    complementB n P (1 / 100) ≤ complementB 12225 P (1 / 100) := by
  have hc := complementRoot_le hn P
  have hl := lowLengthProb_le hn
  have hc0 := complementRoot_nonneg n P
  have hlow0 : 0 ≤ lowLengthProb n (1 / 100) := by unfold lowLengthProb; positivity
  unfold complementB
  exact mul_le_mul hc (Real.rpow_le_rpow hlow0 hl (by positivity))
    (rpow_nonneg hlow0 _) (complementRoot_nonneg 12225 P)

theorem pairEpsilon_le {n : ℕ} (hn : 12225 ≤ n) :
    pairEpsilon n 16 (1 / 100) ≤ pairEpsilon 12225 16 (1 / 100) := by
  have hV := pairV_le hn 32
  have hQ := pairQ_le hn 32
  have hd := pairDelta_le hn 16 (1 / 100)
  have ht := tangentU_le hn 32
  have hl := lengthAlpha_le hn 64
  have hc := complementB_le hn 16
  have hV0 := pairV_nonneg n 32
  have hVOld0 := pairV_nonneg 12225 32
  have hQ0 := pairQ_nonneg n 32
  have hl0 := lengthAlpha_nonneg n 64
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  unfold pairEpsilon meanEpsilon fluctuationRoot
  norm_num only [Nat.reduceMul] at *
  gcongr <;> positivity

theorem error_epsilon_upper {n : ℕ} (hn : 12225 ≤ n) :
    pairEpsilon n 16 (1 / 100) ≤ (0.0647 : ℝ) :=
  (pairEpsilon_le hn).trans BstLean.Part253.error_epsilon_upper

end BstLean.Part264
