import BstLean.Part253DirectionError
import BstLean.Part182SNum

/-! Rational bounds for the deterministic Part219 ideal term. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part219 BstLean.Part215

theorem rotation24_upper : BstLean.Part195.rotationConstant 24 ≤ 6.7 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (48 : ℕ) ≠ 0) (by norm_num)
  have he := BstLean.Part195.rotationConstant_pow (by norm_num : 1 ≤ 24) (by norm_num)
  rw [he, BstLean.Part162.gmom_even]
  have hp := pi_lt_d20.le
  calc
    _ ≤ (3.14159265358979323847 / 2 : ℝ) ^ 48 *
        ∏ j ∈ Finset.range 24, (2 * j + 1 : ℝ) := by gcongr
    _ ≤ (6.7 : ℝ) ^ 48 := by norm_num [Finset.prod_range_succ]

theorem slope_upper {q Q K s B : ℝ} (hq : 0 ≤ q) (hQ : q ≤ Q) (hQ1 : Q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : 1 - Q ^ 2 ≤ s ^ 2)
    (hK : (s + Q * (3141593 / 2000000 +
      (Q + Q ^ 3 / 6 + 3 * Q ^ 5 / 40 + Q ^ 7 / 10))) / (3141592 / 1000000) ≤ K)
    (hK0 : 0 ≤ K) (hK1 : K ≤ 3 / 4)
    (hB : (1 / 2 + (K + K ^ 3 / 6 + 3 * K ^ 5 / 40 + K ^ 7 / 10) /
        (3141592 / 1000000)) *
      (1 / 2 + (Q + Q ^ 3 / 6 + 3 * Q ^ 5 / 40 + Q ^ 7 / 10) /
        (3141592 / 1000000)) ≤ B) : kernelSlope q ≤ B := by
  have hq1 : q ≤ 1 := hQ.trans (hQ1.trans (by norm_num))
  have hQ0 : 0 ≤ Q := hq.trans hQ
  have hkap : kappa q ≤ K :=
    ((kappa_monotoneOn ⟨by linarith, hq1⟩ ⟨by linarith, by linarith⟩ hQ).trans
      (sn_kappa_le hQ0 hQ1 (sqrt_le_iff.mpr ⟨hs, hsq⟩))).trans hK
  have hk0 := (kappa_mem (by linarith : -1 ≤ q) hq1).1
  have hk1 := (kappa_mem (by linarith : -1 ≤ q) hq1).2
  have h1 := (kdot_monotoneOn ⟨by linarith, hk1⟩ ⟨by linarith, by linarith⟩ hkap).trans
    (sn_kdot_le hK0 hK1)
  have h2 := (kdot_monotoneOn ⟨by linarith, hq1⟩ ⟨by linarith, by linarith⟩ hQ).trans
    (sn_kdot_le hQ0 hQ1)
  have he : kernelSlope q = kdot (kappa q) * kdot q := by
    unfold kernelSlope BstLean.Part145.kg kdot
    field_simp
    <;> ring
  rw [he]
  exact (mul_le_mul h1 h2 (kdot_nonneg _) ((kdot_nonneg _).trans h1)).trans hB

theorem radius_upper {θ b R : ℝ} (j : ℕ) (hθ : 0 ≤ θ) (hb : θ ≤ b)
    (hd : 0 < 1 - (2 * j + 2 : ℝ) * b / 12225)
    (hR : b / (1 - (2 * j + 2 : ℝ) * b / 12225) ≤ R) :
    radiusCoefficient 12225 j θ ≤ R := by
  unfold radiusCoefficient
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  apply div_le_div₀ (hθ.trans hb) hb hd
  have hj : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  nlinarith

theorem amplitude_upper {θ a b A : ℝ} (ha : a ≤ θ) (hb : θ ≤ b) (hb1 : b ≤ 1)
    (hd : 0 < 1 - 4 * b / 12225) (hA0 : 0 ≤ A)
    (hA : (1 - a) / (1 - 4 * b / 12225) ≤ A ^ 2) :
    paperAmplitude 12225 θ ≤ A := by
  unfold paperAmplitude
  apply sqrt_le_iff.mpr
  refine ⟨hA0, ?_⟩
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hA
  apply div_le_div₀ (by linarith : 0 ≤ 1 - a) (by linarith) hd
  linarith

/-- The remaining premises are rational bounds on the radius and slope terms. -/
theorem ideal_from_bounds {θ e A K R1 R4 R24 R48 R96 T : ℝ}
    (hθ : 0 ≤ θ) (he : 0.665 ≤ e) (hT : θ ≤ T) (hT0 : 0 ≤ T) (hT1 : T ≤ 0.54)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hA : paperAmplitude 12225 θ ≤ A) (hK : kernelSlope (1 - θ) ≤ K)
    (h1 : radiusCoefficient 12225 1 θ ≤ R1)
    (h4 : radiusCoefficient 12225 4 θ ≤ R4)
    (h24 : radiusCoefficient 12225 24 θ ≤ R24)
    (h48 : radiusCoefficient 12225 48 θ ≤ R48)
    (h96 : radiusCoefficient 12225 96 θ ≤ R96)
    (hR1 : 0 ≤ R1) (hR4 : 0 ≤ R4) (hR24 : 0 ≤ R24)
    (hR48 : 0 ≤ R48) (hR96 : 0 ≤ R96)
    (hscalar : K * A * R48 * 1.001921 / 0.815475 +
      (77 / 100 : ℝ) * √R24 / 0.815475 *
        (√(R1 / 12225) + A * 6.7 * R96 * 1.003879 / 110.566721 +
          2 * ((T + √T * R4 * 1.000123) / 12225)) ≤ 0.230) :
    paperIdeal 12225 θ e ≤ 0.230 := by
  have hsE : (0.815475 : ℝ) ≤ √e := le_sqrt_of_sq_le (by linarith)
  have hsN : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have h47 : √(1 + 47 / (12225 : ℝ)) ≤ 1.001921 := sqrt_le_iff.mpr (by norm_num)
  have h95 : √(1 + 95 / (12225 : ℝ)) ≤ 1.003879 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √(1 + 3 / (12225 : ℝ)) ≤ 1.000123 := sqrt_le_iff.mpr (by norm_num)
  have hr := rotation24_upper
  have hrad (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 12225 j θ := by
    unfold radiusCoefficient
    have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
    have hjc : (2 * j + 2 : ℝ) ≤ 194 := by linarith
    have hp := mul_le_mul hjc (hT.trans hT1) hθ (by norm_num : (0 : ℝ) ≤ 194)
    apply div_nonneg hθ
    simp only [Nat.cast_ofNat]
    nlinarith
  have hr1 := hrad 1 (by norm_num)
  have hr4 := hrad 4 (by norm_num)
  have hr24 := hrad 24 (by norm_num)
  have hr48 := hrad 48 (by norm_num)
  have hr96 := hrad 96 (by norm_num)
  have hslope := kernelSlope_nonneg (1 - θ)
  have hAmp : 0 ≤ paperAmplitude 12225 θ := by unfold paperAmplitude; positivity
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperIdeal paperBias
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hscalar
  gcongr

end BstLean.Part253
