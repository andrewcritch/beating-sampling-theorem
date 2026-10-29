import BstLean.Part204All

/-! S07: the sharp calibration bound on the hidden scalar window. -/
namespace BstLean.Part210
open Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part159
open BstLean.Part140 (kap1)

/-- A reciprocal square root has the required local calibration bound. -/
lemma inv_sqrt_error {a : ℝ} (ha : 999 / 1000 ≤ a) :
    |1 / √a - 1| ≤ 501 / 1000 * |a - 1| := by
  have ha0 : 0 ≤ a := by linarith
  have hs0 := Real.sqrt_nonneg a
  have hs2 := Real.sq_sqrt ha0
  have hs : 999 / 1000 ≤ √a := by nlinarith
  have hspos : 0 < √a := by linarith
  have hd : 1 ≤ 501 / 1000 * (√a * (√a + 1)) := by nlinarith
  have he : 1 / √a - 1 = -(a - 1) / (√a * (√a + 1)) := by
    field_simp
    nlinarith
  have hdpos : 0 < √a * (√a + 1) := mul_pos hspos (by linarith)
  rw [he, abs_div, abs_neg, abs_of_pos hdpos, div_le_iff₀ hdpos]
  nlinarith [mul_le_mul_of_nonneg_right hd (abs_nonneg (a - 1))]

/-- The ratio splits into the reciprocal square root and the kernel error. -/
lemma ratio_error {a k K : ℝ} (ha : 999 / 1000 ≤ a)
    (hK : 493719 / 1000000 ≤ K) :
    |k / (√a * K) - 1| ≤ 501 / 1000 * |a - 1| + 203 / 100 * |K - k| := by
  have hs : 999 / 1000 ≤ √a := by
    have := Real.sq_sqrt (show 0 ≤ a by linarith)
    have := Real.sqrt_nonneg a
    nlinarith
  have hspos : 0 < √a := by linarith
  have hKpos : 0 < K := by linarith
  have hd : 1 ≤ 203 / 100 * (√a * K) := by
    have := mul_le_mul hs hK (by norm_num) (by positivity : 0 ≤ √a)
    nlinarith
  have he : k / (√a * K) - 1 = (1 / √a - 1) + (k - K) / (√a * K) := by
    field_simp <;> ring
  rw [he]
  refine (abs_add_le _ _).trans (add_le_add (inv_sqrt_error ha) ?_)
  have hdpos : 0 < √a * K := mul_pos hspos hKpos
  rw [abs_div, abs_sub_comm k K, abs_of_pos hdpos, div_le_iff₀ hdpos]
  nlinarith [mul_le_mul_of_nonneg_right hd (abs_nonneg (K - k))]

/-- The existing network calibration ratio has the sharp pointwise bound. -/
theorem pap_q_error {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n} (hS : θ ∈ goodS n) :
    |qOf n (ccP n) θ - 1| ≤
      501 / 1000 * |SWp θ / 2 - 1| + 203 / 100 * |kapT n - kap1 (2 * n)| := by
  have hwin := abs_le.mp (show |SWp θ / 2 - 1| ≤ 1 / 1000 from hS)
  have ha : 999 / 1000 ≤ SWp θ / 2 := by linarith [hwin.1]
  have hSWpos : 0 < SWp θ := by linarith
  have hK := (BstLean.Part204.kapT_window hn (BstLean.Part201.constK hn)).2.1
  have hk := (BstLean.Part201.kap1_window hn).1
  have hspos : 0 < √(SWp θ / 2) := Real.sqrt_pos.mpr (by linarith)
  have hKpos : 0 < kapT n := by linarith
  have hkpos : 0 < kap1 (2 * n) := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq2 : qOf n (ccP n) θ ^ 2 =
      2 * kap1 (2 * n) ^ 2 / (SWp θ * kapT n ^ 2) := by
    unfold qOf
    rw [Real.sq_sqrt (by unfold ccP; positivity), hNcast]
    unfold ccP
    field_simp
  have hr2 : (kap1 (2 * n) / (√(SWp θ / 2) * kapT n)) ^ 2 =
      2 * kap1 (2 * n) ^ 2 / (SWp θ * kapT n ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
  have hq0 : 0 ≤ qOf n (ccP n) θ := Real.sqrt_nonneg _
  have hr0 : 0 ≤ kap1 (2 * n) / (√(SWp θ / 2) * kapT n) := by positivity
  have he : qOf n (ccP n) θ = kap1 (2 * n) / (√(SWp θ / 2) * kapT n) := by
    nlinarith [hq2, hr2]
  rw [he]
  exact ratio_error ha hK

end BstLean.Part210
#print axioms BstLean.Part210.inv_sqrt_error
#print axioms BstLean.Part210.ratio_error
#print axioms BstLean.Part210.pap_q_error
