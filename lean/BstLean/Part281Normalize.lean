import BstLean.Part264bNormalize

namespace BstLean.Part281.TI
open BstLean.Part264b
open Real BstLean.Part130 BstLean.Part182 BstLean.Part246 BstLean.Part255

theorem invN_bounds {n : ℕ} (hn : 11883 ≤ n) : B 0 (1 / 11883) (invN n) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · unfold invN; positivity
  · unfold invN; gcongr

theorem s_from_normalized {n : ℕ} (hn : 11883 ≤ n) {c cap : ℝ}
    (H : 0 < nam (invN n) ∧ 0 ≤ ndm (invN n) c ∧
      ndm (invN n) c ^ 2 ≤ 2 * nap (invN n) ^ 2 ∧ nc1 (invN n) c < 1 ∧
      0 ≤ npa c - nr1 (invN n) ∧
      ne0 (invN n) ≤ (npa c - nr1 (invN n)) / nap (invN n) ∧
      ns (invN n) c ≤ cap) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
    s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n 46 ∧
    s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
    s3nks n 46 (√23 / n) c ≤ n * cap := by
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have htr : (0 : ℝ) < √(n : ℝ) := by positivity
  have ht : √(n : ℝ)^2 = n := sq_sqrt hnr.le
  have ht0 : √(n : ℝ) ≠ 0 := ne_of_gt htr
  have hnap : 0 < nap (invN n) := by
    unfold nap invN; positivity
  rw [norm_am hn0, norm_dm hn0, norm_ap hn0, norm_c1 hn0,
    norm_pa hn0, norm_r1 hn0, norm_e0 hn0, norm_s hn0]
  refine ⟨mul_pos htr H.1, mul_nonneg htr.le H.2.1, ?_, H.2.2.2.1, ?_, ?_,
    mul_le_mul_of_nonneg_left H.2.2.2.2.2.2 hnr.le⟩
  · simp only [mul_pow, ht]
    nlinarith [mul_le_mul_of_nonneg_left H.2.2.1 hnr.le]
  · rw [← mul_sub]
    exact mul_nonneg hnr.le H.2.2.2.2.1
  · calc
      _ ≤ √(n : ℝ) * ((npa c - nr1 (invN n)) / nap (invN n)) :=
        mul_le_mul_of_nonneg_left H.2.2.2.2.2.1 htr.le
      _ = _ := by
        field_simp
        generalize √(n : ℝ) = a at ht ⊢
        rw [← ht]
        ring

end BstLean.Part281.TI
