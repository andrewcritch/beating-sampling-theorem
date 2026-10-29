import BstLean.Part291LatitudePlane
import BstLean.Part291Band
import BstLean.Part252LatitudeCap

namespace BstLean.BlueprintLow
open Real MeasureTheory BstLean.Part130 BstLean.Part212
open BstLean.Part29 (stdGauss)
open BstLean.Part167 (Mx)

noncomputable def latitudeMaxMoment (n : ℕ) : ℝ :=
  (mA n : ℝ) ^ (1 / 4 : ℝ) * (((n - 1 - 1 : ℕ) : ℝ) + 319) ^ 80

theorem latitudeMaxMoment_bound {n : ℕ} (hn : 8000 ≤ n) (hm : 0 < mA n) :
    (∫⁻ G, ENNReal.ofReal (Mx hm G ^ 160)
      ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 1 - 1)))) ≤
      ENNReal.ofReal (latitudeMaxMoment n) := maximum160_sharp hm (by omega)

theorem latitude_plane_envelope {n : ℕ} (hn : 8000 ≤ n) :
    planeEnvelope80 (mA n) ≤ 0.5053 * (mA n : ℝ) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have h2 : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 1.009 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1.009)
    have he := rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 80) (by norm_num) (by norm_num)
    norm_num only [Nat.cast_ofNat] at he
    rw [he]
    norm_num
  have hs : √(80 : ℝ) ≤ 8.945 := sqrt_le_iff.mpr (by norm_num)
  have hsn : √((mA n : ℝ) / 2 + 160) ≤ 0.708 * n := by
    apply sqrt_le_iff.mpr
    rw [hm]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((n : ℝ) - 8000)]
  unfold planeEnvelope80
  calc
    _ ≤ 1.009 * ((mA n : ℝ) / 2 + 320) + 8.945 * (0.708 * n) := by gcongr
    _ ≤ 0.5053 * (mA n : ℝ) := by
      rw [hm]
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 8000 by linarith) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem latitude_radial_ratio {n : ℕ} (hn : 8000 ≤ n) :
    radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 ≤ (1.011 : ℝ) ^ 80 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hden : 0 < ((n - 1 - 1 : ℕ) : ℝ) - 1 := by rw [hd]; linarith
  calc
    _ ≤ ((((n - 1 - 1 : ℕ) : ℝ) + 80 - 1) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) ^ 80 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (radialProduct_arithmetic _ _ (by norm_num)) (by positivity)
    _ ≤ (1.011 : ℝ) ^ 80 := by
      apply pow_le_pow_left₀ (div_nonneg
        (by linarith [(Nat.cast_nonneg (n - 1 - 1) : (0 : ℝ) ≤ (n - 1 - 1 : ℕ))]) hden.le)
      apply (div_le_iff₀ hden).mpr
      rw [hd]
      linarith

theorem latitude_row_count {n : ℕ} (hn : LowBand n) :
    (mA n : ℝ) ^ (1 / 4 : ℝ) ≤ (1.061 : ℝ) ^ 80 := by
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hu : (n : ℝ) ≤ 11882 := by exact_mod_cast hn.2
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity : (0 : ℝ) ≤ (1.061 : ℝ) ^ 80)
  have he := rpow_inv_natCast_pow (x := (mA n : ℝ)) (n := 4) (Nat.cast_nonneg _) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he
  rw [he, hm]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hu 2).trans (by norm_num)

theorem latitude_plane_scalar {n : ℕ} (hn : LowBand n) :
    radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
      latitudeMaxMoment n * (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 *
        planeEnvelope80 (mA n) ^ 80 ≤ (2.254 : ℝ) ^ 80 := by
  have hnlo := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < mA n := by unfold mA; positivity
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by have := hn.1; omega)]
    push_cast
    ring
  have hP := latitude_plane_envelope hn.1
  have hP0 : 0 ≤ planeEnvelope80 (mA n) := by unfold planeEnvelope80; positivity
  have hf : (2 / (n : ℝ) * (2 / (mA n : ℝ))) * planeEnvelope80 (mA n) ≤
      (4 * 0.5053 : ℝ) / n := by
    calc
      _ ≤ (2 / (n : ℝ) * (2 / (mA n : ℝ))) * (0.5053 * (mA n : ℝ)) := by gcongr
      _ = _ := by field_simp <;> norm_num
  have hR0 : 0 ≤ radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 := by
    unfold radialProduct
    positivity
  have hR := latitude_radial_ratio hn.1
  have hM : latitudeMaxMoment n ≤ (1.061 : ℝ) ^ 80 * ((n : ℝ) + 317) ^ 80 := by
    unfold latitudeMaxMoment
    rw [hd]
    have he : (n : ℝ) - 2 + 319 = (n : ℝ) + 317 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (latitude_row_count hn) (by positivity)
  have hM0 : 0 ≤ latitudeMaxMoment n := by unfold latitudeMaxMoment; positivity
  calc
    _ = (radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80) *
        latitudeMaxMoment n * ((2 / (n : ℝ) * (2 / (mA n : ℝ))) * planeEnvelope80 (mA n)) ^ 80 := by
      rw [mul_pow (2 / (n : ℝ) * (2 / (mA n : ℝ))) (planeEnvelope80 (mA n)) 80]
      exact mul_assoc _ _ _
    _ ≤ (1.011 : ℝ) ^ 80 * (1.061 ^ 80 * ((n : ℝ) + 317) ^ 80) *
        ((4 * 0.5053 : ℝ) / n) ^ 80 :=
      mul_le_mul (mul_le_mul hR hM hM0 (by positivity))
        (pow_le_pow_left₀ (mul_nonneg (by positivity) hP0) hf 80)
        (pow_nonneg (mul_nonneg (by positivity) hP0) _) (by positivity)
    _ = (1.011 * 1.061 * ((n : ℝ) + 317) * ((4 * 0.5053 : ℝ) / n)) ^ 80 := by
      simp only [mul_pow]
      simp only [mul_assoc]
    _ ≤ (2.254 : ℝ) ^ 80 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [show 1.011 * 1.061 * ((n : ℝ) + 317) * ((4 * 0.5053 : ℝ) / n) =
        (1.011 * 1.061 * 4 * 0.5053 * ((n : ℝ) + 317)) / n by ring]
      apply (div_le_iff₀ hn0).mpr
      nlinarith

end BstLean.BlueprintLow
