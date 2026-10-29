import BstLean.Part250Kernel

/-! Outward dimension and width bounds on a closed integer band. -/
namespace BstLean.Part271.R3
open Real BstLean.Part130 BstLean.Part228

theorem width_mono {a b : ℕ} (hab : a ≤ b) : mW a ≤ mW b := by
  apply (mW_le_iff _ _).mpr
  exact (Nat.pow_le_pow_left hab 7).trans ((mW_le_iff _ _).mp le_rfl)

theorem dimension_bounds {a b n : ℕ} (ha : a ≤ n) (hb : n ≤ b) :
    Bounds (n : ℝ) a b := by
  constructor
  · exact_mod_cast ha
  · exact_mod_cast hb

theorem width_bounds {a b n lo hi : ℕ} (ha : a ≤ n) (hb : n ≤ b)
    (hlo : lo ≤ mW a) (hhi : mW b ≤ hi) : Bounds (mW n : ℝ) lo hi := by
  constructor
  · exact_mod_cast hlo.trans (width_mono ha)
  · exact_mod_cast (width_mono hb).trans hhi

theorem inverse_bounds {a b n : ℕ} (ha0 : 0 < a) (ha : a ≤ n) (hb : n ≤ b) :
    Bounds (1 / (n : ℝ)) (1 / (b : ℝ)) (1 / (a : ℝ)) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha0
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hnb : (n : ℝ) ≤ b := by exact_mod_cast hb
  exact ⟨one_div_le_one_div_of_le (hap.trans_le han) hnb,
    one_div_le_one_div_of_le hap han⟩

theorem sqrt_bounds {a b n : ℕ} {lo hi : ℝ} (ha : a ≤ n) (hb : n ≤ b)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hlo2 : lo ^ 2 ≤ a) (hhi2 : (b : ℝ) ≤ hi ^ 2) :
    Bounds (√(n : ℝ)) lo hi :=
  Bounds.sqrt (dimension_bounds ha hb) ⟨hlo, hhi, hlo2, hhi2⟩

/-- Keep the cancellation in the angular offset before bounding its denominator. -/
theorem angular_offset_bounds {N A : ℕ} (hA : 2 ≤ A) (hAN : A ≤ N) :
    Bounds (BstLean.Part218.angularOffset N)
      (-1 / (2 * π * (A : ℝ) * ((A : ℝ) - 1))) 0 := by
  have hN : 2 ≤ N := hA.trans hAN
  have ha : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have han : (A : ℝ) ≤ N := by exact_mod_cast hAN
  have hn : (0 : ℝ) < N := by linarith
  have ha1 : 0 < (A : ℝ) - 1 := by linarith
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window hN
  have hid : 1 / (2 * π * (N : ℝ)) - 1 / (2 * π * ((N : ℝ) - 1)) =
      -1 / (2 * π * (N : ℝ) * ((N : ℝ) - 1)) := by
    field_simp [ne_of_gt hn, ne_of_gt hn1, Real.pi_ne_zero]
    <;> ring
  have hm : (A : ℝ) * ((A : ℝ) - 1) ≤ (N : ℝ) * ((N : ℝ) - 1) :=
    mul_le_mul han (by linarith) ha1.le (by positivity)
  have hd : 2 * π * (A : ℝ) * ((A : ℝ) - 1) ≤
      2 * π * (N : ℝ) * ((N : ℝ) - 1) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 2 * π by positivity)
  have hi := one_div_le_one_div_of_le
    (by positivity : 0 < 2 * π * (A : ℝ) * ((A : ℝ) - 1)) hd
  constructor
  · unfold BstLean.Part218.angularOffset
    have hsub := sub_le_sub_left hu (1 / (2 * π * (N : ℝ)))
    rw [hid] at hsub
    have hneg : -1 / (2 * π * (A : ℝ) * ((A : ℝ) - 1)) ≤
        -1 / (2 * π * (N : ℝ) * ((N : ℝ) - 1)) := by
      simpa only [neg_div] using neg_le_neg hi
    exact hneg.trans hsub
  · unfold BstLean.Part218.angularOffset
    linarith

theorem first_ratio_bounds {N A : ℕ} (hA : 2 ≤ A) (hAN : A ≤ N) :
    Bounds (BstLean.Part218.firstRatio N) (1 / π)
      ((A : ℝ) / (π * ((A : ℝ) - 1))) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.rN_window (hA.trans hAN)
  have ha : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have han : (A : ℝ) ≤ N := by exact_mod_cast hAN
  have ha1 : 0 < (A : ℝ) - 1 := by linarith
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  refine ⟨hl, hu.trans ?_⟩
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr han)]

end BstLean.Part271.R3
