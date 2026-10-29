import BstLean.Part253HS

/-! The actual HS profile decreases with dimension from 12225. -/
namespace BstLean.Part264
open Real Set
open BstLean.Part194 BstLean.Part211

theorem S0_comparisons {n : ℕ} (hn : 12225 ≤ n) :
    S0 12225 ≤ S0 n ∧ (n : ℝ) / S0 n ≤ 12225 / S0 12225 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfrac : 12 * ((n : ℝ) - 1) / (n : ℝ)^2 ≤ 12 * ((12225 : ℝ) - 1) / 12225^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hnpos) (by norm_num)).mpr
    have hprod : 0 ≤ ((n : ℝ) - 12225) * (12224 * (n : ℝ) - 12225) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [hprod]
  have hnorm : √(12 * ((n : ℝ) - 1) / (n : ℝ)^2) = √(12 * ((n : ℝ) - 1)) / n := by
    rw [sqrt_div (by nlinarith), sqrt_sq hnpos.le]
  have hnorm0 : √(12 * ((12225 : ℝ) - 1) / 12225^2) =
      √(12 * ((12225 : ℝ) - 1)) / 12225 := by
    rw [sqrt_div (by norm_num), sqrt_sq (by norm_num : (0 : ℝ) ≤ 12225)]
  have hs := sqrt_le_sqrt hfrac
  rw [hnorm,hnorm0] at hs
  have hi : 1 / (n : ℝ) ≤ 1 / (12225 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hscaled : S0 12225 / 12225 ≤ S0 n / n := by
    unfold S0
    have he : ((n : ℝ) - 1 - 2 * √(12 * ((n : ℝ) - 1))) / n =
        1 - 1 / (n : ℝ) - 2 * (√(12 * ((n : ℝ) - 1)) / n) := by
      field_simp
      <;> ring
    rw [he]
    linarith
  have hS0 : 0 < S0 12225 := lt_of_lt_of_le (by norm_num) BstLean.Part253.S0_lower
  have hnScaled := (le_div_iff₀ hnpos).mp hscaled
  have hSn : S0 12225 ≤ S0 n := by
    calc
      _ = S0 12225 / 12225 * 12225 := by ring
      _ ≤ S0 12225 / 12225 * n := mul_le_mul_of_nonneg_left hnR (by positivity)
      _ ≤ _ := hnScaled
  refine ⟨hSn, ?_⟩
  apply (div_le_div_iff₀ (hS0.trans_le hSn) hS0).mpr
  have hcross := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 12225) hnpos).mp hscaled
  nlinarith only [hcross]

theorem J0_le {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    J0 12225 θ ≤ J0 n θ := by
  obtain ⟨hS,hRatio⟩ := S0_comparisons hn
  have hS0 : 0 < S0 12225 := lt_of_lt_of_le (by norm_num) BstLean.Part253.S0_lower
  have hSn := hS0.trans_le hS
  have hAx : 0 ≤ axialC θ := by
    unfold axialC
    exact div_nonneg (by linarith) (by positivity)
  have hInner : 2 * axialC θ * n / S0 n ≤ 2 * axialC θ * 12225 / S0 12225 := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hRatio (by positivity : 0 ≤ 2 * axialC θ)
  have hDen : √(1 + 2 * axialC θ * n / S0 n) ≤
      √(1 + 2 * axialC θ * 12225 / S0 12225) := sqrt_le_sqrt (by linarith)
  have hDen0 : 0 < √(1 + 2 * axialC θ * n / S0 n) := by positivity
  have he : 0 ≤ 1 - exp (-12 : ℝ) := by
    have h := exp_le_one_iff.mpr (by norm_num : (-12 : ℝ) ≤ 0)
    linarith
  have hInv : 1 / S0 n ≤ 1 / S0 12225 := div_le_div_of_nonneg_left (by norm_num) hS0 hS
  have hNum : (1 - exp (-12)) * (1 - 1 / S0 12225) ≤
      (1 - exp (-12)) * (1 - 1 / S0 n) := mul_le_mul_of_nonneg_left (by linarith) he
  have hInv1 : 1 / S0 n ≤ 1 := by
    apply (div_le_one hSn).mpr
    have := BstLean.Part253.S0_lower
    linarith
  unfold J0
  exact div_le_div₀ (mul_nonneg he (by linarith)) hNum hDen0 hDen

theorem hsProfile_le {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    hsProfile n θ 0.006 ≤ hsProfile 12225 θ 0.006 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hj := J0_le hn hθ hθ1
  have hq : qHS n θ ≤ qHS 12225 θ := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS n θ := by
    have h := J0_bounds (by omega : 64 ≤ n) hθ hθ1
    unfold qHS
    linarith [h.2.2.1]
  have hch : CH n θ 0.006 ≤ CH 12225 θ 0.006 := by
    unfold CH
    gcongr
  have hroot : √(12225 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hroot2 : √(√(12225 : ℝ)) ≤ √(√(n : ℝ)) := sqrt_le_sqrt hroot
  have ha : a0 n ≤ a0 12225 := by unfold a0; gcongr
  have ha0 : 0 ≤ a0 n := by unfold a0; positivity
  rw [hsProfile_eq_paper (n := n) (by omega) hθ,
    hsProfile_eq_paper (n := 12225) (by norm_num) hθ]
  gcongr

end BstLean.Part264
