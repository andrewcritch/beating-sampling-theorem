import BstLean.Part223Event

/-! A symbolic comparison with the paper's order256 coefficient on the frontier range. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA mkR)
open BstLean.Part212 (exactRadius)
open BstLean.Part152 (gaussMomConst gaussMomConst_nonneg)
open BstLean.Part220

noncomputable def paperT0 (n : ℕ) : ℝ := sqrt (2 * log (mA n : ℝ))

noncomputable def paperTail256 (n : ℕ) : ℝ :=
  min (gaussMomConst 128) (((256 : ℕ).factorial : ℝ) ^ (1 / (256 : ℝ)) / paperT0 n)

noncomputable def paperLJ256 (n : ℕ) : ℝ :=
  exactRadius (n - 1 - 1) 128 * sqrt (2 / (n : ℝ)) *
    (sqrt (n : ℝ) + paperT0 n + paperTail256 n)

noncomputable def paperActivationFactor (n : ℕ) : ℝ :=
  1 + sqrt 2 * gaussMomConst 128 / (n : ℝ)

noncomputable def paperBound256 (n : ℕ) : ℝ :=
  paperLJ256 n ^ 2 * paperActivationFactor n ^ 2

lemma paperT0_bounds {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 16384) :
    5 ≤ paperT0 n ∧ paperT0 n ≤ 8 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≤ 16384 := by exact_mod_cast hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by simp [mA]
  have hl2 : (1 / 2 : ℝ) ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hu2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hl : log ((2 : ℝ) ^ 25) ≤ log (mA n : ℝ) :=
    log_le_log (by positivity) (by rw [hm]; norm_num; nlinarith)
  have hu : log (mA n : ℝ) ≤ log ((2 : ℝ) ^ 28) :=
    log_le_log (by rw [hm]; positivity) (by rw [hm]; norm_num; nlinarith)
  rw [log_pow] at hl hu
  norm_num at hl hu
  constructor
  · apply le_sqrt_of_sq_le
    nlinarith
  · apply sqrt_le_iff.mpr
    constructor <;> nlinarith

#print axioms paperT0_bounds
end BstLean.Part223
