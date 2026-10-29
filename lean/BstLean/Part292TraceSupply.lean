import BstLean.Part292TracePaid

/-! A single pair of trace events supplies the scale at every nonnegative latitude. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part171 BstLean.Part172

theorem variance_lower_low {n : ℕ} (hn : 8000 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hA : A1 c ∈ traceLow (uHat c)) {s : ℝ} (hs0 : 0 ≤ s) (hs : s^2 ≤ 1) :
    (1-s^2)*lowSigma n^2 ≤ vsig2 c s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hq : 0 ≤ 1-s^2 := sub_nonneg.mpr hs
  have h := sg_vsig2_lower (by omega) c hc hs0 hs
  change (2/(mA n : ℝ))*((1-s^2)/(4*(n-1 : ℕ)))*
    (∑ i, sg_phi1 (uHat c) (A1 c i)) ≤ _ at h
  apply le_trans ?_ h
  calc
    _ = (2/(mA n : ℝ))*((1-s^2)/(4*(n-1 : ℕ)))*
        ((2/(n : ℝ))*(999/2000)*(mA n : ℝ)*(n-1 : ℕ)) := by
      rw [(low_scales_square (by omega)).1]
      simp only [mA, Nat.cast_pow]
      field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

theorem variance_upper_low {n : ℕ} (hn : 8000 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hA : A1 c ∈ traceHigh (uHat c)) {s : ℝ} (hs : s^2 ≤ 1) :
    vsig2 c s ≤ lowUpperSigma n^2*(1-s^2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hq : 0 ≤ 1-s^2 := by linarith
  have h := sg_vsig2_upper (by omega) c hc hs
  change _ ≤ (2/(mA n : ℝ))*((1-s^2)/(n-1 : ℕ))*
    (∑ i, sg_phi2 (uHat c) (A1 c i)) at h
  apply h.trans
  calc
    _ ≤ (2/(mA n : ℝ))*((1-s^2)/(n-1 : ℕ))*
        ((2/(n : ℝ))*(1001/1000)*(mA n : ℝ)*(n-1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    _ = (4004/1000 : ℝ)/(n : ℝ)*(1-s^2) := by
      simp only [mA, Nat.cast_pow]
      field_simp <;> ring
    _ ≤ _ := by
      unfold lowUpperSigma
      rw [div_pow, sq_sqrt hn0.le]
      gcongr
      norm_num

theorem variance_bias_upper_low {n : ℕ} (hn : 8000 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hA : A1 c ∈ traceHigh (uHat c)) {s : ℝ} (hs : s^2 ≤ 1)
    (hq : 1-s^2 ≤ 605/1000) : vsig2 c s ≤ lowBiasUpper n^2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (variance_upper_low hn c hc hA hs).trans
  calc
    _ ≤ lowUpperSigma n^2*(605/1000) := mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    _ ≤ _ := by
      rw [(low_scales_square (by omega)).2]
      unfold lowUpperSigma
      rw [div_pow, sq_sqrt hn0.le, div_mul_eq_mul_div]
      gcongr
      norm_num

end BstLean.Part292
