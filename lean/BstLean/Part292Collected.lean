import BstLean.Part239WeightedRA
import BstLean.Part213Latitude

/-! The six row coefficients retain their common latitude powers before
endpoint bounds. No independence across nodes is used. -/
namespace BstLean.Part292
open Real
open BstLean.Part171
open BstLean.Part153 (phiG)

noncomputable def lowF0 (lo hi σ Γ D V P : ℝ) : ℝ :=
  sqrt hi * phiG 0 / (2 * σ) * D +
    phiG 0 / (2 * sqrt 2 * σ ^ 3) * (V / sqrt lo + sqrt hi * D ^ 2) +
    (3 / 2) * phiG 0 * Γ / (σ * sqrt lo * lo ^ 4) * P

noncomputable def lowF1 (lo hi σ C D V P : ℝ) : ℝ :=
  phiG 1 / σ ^ 2 * (sqrt D * sqrt V + sqrt hi * sqrt D * D) +
    4 * sqrt 2 * C / lo ^ 4 * P

noncomputable def lowF2 (hi σ D : ℝ) : ℝ := sqrt hi * phiG 0 / (sqrt 2 * σ) * D

noncomputable def lowW0 (lo hi σ Γ D V P : ℝ) : ℝ :=
  hi * D + phiG 1 / (2 * σ ^ 2) * (V + hi * D ^ 2) + 4 * Γ / lo ^ 4 * P

noncomputable def lowW1 (lo hi σ C sp D V P : ℝ) : ℝ :=
  sqrt 2 * phiG 0 / σ * (sqrt hi * sqrt D * sqrt V + hi * sqrt D * D) +
    4 * sqrt 2 * C * sp / lo ^ 4 * P

noncomputable def lowW2 (lo hi C D P : ℝ) : ℝ := hi * D + 28 * C ^ 2 / lo ^ 4 * P

theorem sqrt_variance_split {q D V : ℝ} (hq : 0 ≤ q) (hD : 0 ≤ D) (hV : 0 ≤ V) :
    sqrt (V + q * D ^ 2) ≤ sqrt V + sqrt q * D := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsV := sq_sqrt hV
  have hsq := sq_sqrt hq
  nlinarith [mul_nonneg (sqrt_nonneg V) (mul_nonneg (sqrt_nonneg q) hD)]

theorem AF0_collect {q σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) (Γ D V P : ℝ) :
    AF0 (sqrt q * σ) Γ (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) =
      sqrt q * phiG 0 / (2 * σ) * D +
      phiG 0 / (2 * sqrt 2 * σ ^ 3) * (V / sqrt q + sqrt q * D ^ 2) +
      (3 / 2) * phiG 0 * Γ / (σ * sqrt q * q ^ 4) * P := by
  have hs : sqrt q ^ 2 = q := sq_sqrt hq.le
  have hs0 : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  unfold AF0
  generalize hr : sqrt q = r at *
  field_simp <;> simp only [← hs, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> ring

theorem AF1_collect {q σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) (C D V P : ℝ) :
    AF1 (sqrt q * σ) (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) C =
      phiG 1 / σ ^ 2 * (sqrt D * sqrt (V + q * D ^ 2)) +
      4 * sqrt 2 * C / q ^ 4 * P := by
  unfold AF1
  rw [BstLean.Part213.collected_variance, sqrt_mul hq.le, sqrt_mul hq.le]
  have hs : sqrt q ^ 2 = q := sq_sqrt hq.le
  have hs0 : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  generalize hr : sqrt q = r at *
  simp only [← hs]
  field_simp <;> ring

theorem AF2_collect {q σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) (D : ℝ) :
    AF2 (sqrt q * σ) (q * D) = sqrt q * phiG 0 / (sqrt 2 * σ) * D := by
  have hs : sqrt q ^ 2 = q := sq_sqrt hq.le
  have hs0 : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  unfold AF2
  generalize hr : sqrt q = r at *
  field_simp <;> simp only [← hs, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> ring

theorem AW0_collect {q σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) (Γ D V P : ℝ) :
    AW0 (sqrt q * σ) Γ (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) =
      q * D + phiG 1 / (2 * σ ^ 2) * (V + q * D ^ 2) + 4 * Γ / q ^ 4 * P := by
  have hs : sqrt q ^ 2 = q := sq_sqrt hq.le
  unfold AW0
  rw [mul_pow, hs]
  field_simp <;> ring

theorem AW1_collect {q σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) (C sp D V P : ℝ) :
    AW1 (sqrt q * σ) sp (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) C =
      sqrt 2 * phiG 0 / σ * (sqrt q * sqrt D * sqrt (V + q * D ^ 2)) +
      4 * sqrt 2 * C * sp / q ^ 4 * P := by
  unfold AW1
  rw [BstLean.Part213.collected_variance, sqrt_mul hq.le, sqrt_mul hq.le]
  have hs0 : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  field_simp <;> ring

theorem collected_coefficients_bound {q lo hi σ Γ C sp D V P : ℝ}
    (hlo : 0 < lo) (hql : lo ≤ q) (hqh : q ≤ hi) (hσ : 0 < σ)
    (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hsp : 0 ≤ sp)
    (hD : 0 ≤ D) (hV : 0 ≤ V) (hP : 0 ≤ P) :
    AF0 (sqrt q * σ) Γ (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) ≤ lowF0 lo hi σ Γ D V P ∧
    AF1 (sqrt q * σ) (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) C ≤ lowF1 lo hi σ C D V P ∧
    AF2 (sqrt q * σ) (q * D) ≤ lowF2 hi σ D ∧
    AW0 (sqrt q * σ) Γ (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) ≤ lowW0 lo hi σ Γ D V P ∧
    AW1 (sqrt q * σ) sp (q * D) (q * V + (q * D) ^ 2) (P / q ^ 4) C ≤ lowW1 lo hi σ C sp D V P ∧
    AW2 (q * D) (P / q ^ 4) C ≤ lowW2 lo hi C D P := by
  have hq : 0 < q := hlo.trans_le hql
  have hhi : 0 < hi := hq.trans_le hqh
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  have hsplit := sqrt_variance_split hq.le hD hV
  rw [AF0_collect hq hσ, AF1_collect hq hσ, AF2_collect hq hσ,
    AW0_collect hq hσ, AW1_collect hq hσ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lowF0
    gcongr
  · unfold lowF1
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        sqrt D * sqrt (V + q * D ^ 2) ≤ sqrt D * (sqrt V + sqrt q * D) :=
          mul_le_mul_of_nonneg_left hsplit (sqrt_nonneg _)
        _ ≤ sqrt D * sqrt V + sqrt hi * sqrt D * D := by
          have he : sqrt D * (sqrt V + sqrt q * D) =
              sqrt D * sqrt V + sqrt q * sqrt D * D := by ring
          rw [he]
          gcongr
    · gcongr
  · unfold lowF2
    gcongr
  · unfold lowW0
    gcongr
  · unfold lowW1
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        sqrt q * sqrt D * sqrt (V + q * D ^ 2) ≤
            sqrt q * sqrt D * (sqrt V + sqrt q * D) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ = sqrt q * sqrt D * sqrt V + q * sqrt D * D := by
          have he : sqrt q * sqrt D * (sqrt V + sqrt q * D) =
              sqrt q * sqrt D * sqrt V + (sqrt q)^2 * sqrt D * D := by ring
          rw [he, sq_sqrt hq.le]
        _ ≤ _ := by gcongr
    · gcongr
  · unfold AW2 lowW2
    have hp : P / q ^ 4 * (28 * C ^ 2) = 28 * C ^ 2 / q ^ 4 * P := by ring
    rw [hp]
    gcongr

end BstLean.Part292
