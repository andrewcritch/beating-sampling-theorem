import BstLean.Part271AngularScale

/-! Outward inputs for the dimension-scaled formulas on 13225–16199. -/
namespace BstLean.Part271.R3.Band
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part228
open BstLean.Part250 (pi_bounds)

theorem width_cube {n : ℕ} (ha : 13225 ≤ n) : 115*n^3 ≤ mW n := by
  have hs : (115*n^3)^2 ≤ (mW n)^2 := calc
    _ = 13225*n^6 := by ring
    _ ≤ n*n^6 := Nat.mul_le_mul_right _ ha
    _ = n^7 := by ring
    _ ≤ _ := (mW_le_iff _ _).mp le_rfl
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (Nat.zero_le _) hs

theorem n_positive {n : ℕ} (ha : 13225 ≤ n) : 0 < (n : ℝ) := by
  exact_mod_cast (show 0 < n by omega)

theorem width_positive {n : ℕ} (ha : 13225 ≤ n) : 1 < (mW n : ℝ) := by
  have h := BstLean.Part137.mW_ge_pow42 (show 4096 ≤ n by omega)
  have h' : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast h
  linarith

theorem inverse_dimension {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (1/((2*n : ℕ) : ℝ)) (1/32398) (1/26450) := by
  exact inverse_bounds (a := 26450) (b := 32398) (n := 2*n)
    (by norm_num) (by omega) (by omega)

theorem inverse_width {n : ℕ} (ha : 13225 ≤ n) :
    Bounds (1/(mW n : ℝ)) 0 (1/266001988046875) := by
  have hw : 266001988046875 ≤ mW n := by
    have hw0 : 266001988046875 ≤ mW 13225 := by
      have h : ¬mW 13225 ≤ 266001988046874 := by rw [mW_le_iff]; norm_num
      omega
    exact hw0.trans (width_mono ha)
  have hw' : (266001988046875 : ℝ) ≤ mW n := by exact_mod_cast hw
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hw'⟩

theorem dimension_width {n : ℕ} (ha : 13225 ≤ n) :
    Bounds (((2*n : ℕ) : ℝ)/(mW n : ℝ)) 0 (2/(115*13225^2)) := by
  have hn := n_positive ha
  have hm : 0 < (mW n : ℝ) := by have := width_positive ha; linarith
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast ha
  have hw : 115*(n : ℝ)^3 ≤ mW n := by exact_mod_cast width_cube ha
  constructor
  · positivity
  · push_cast
    calc
      (2*(n : ℝ))/(mW n : ℝ) ≤ 2/(115*(n : ℝ)^2) := by
        apply (div_le_div_iff₀ hm (by positivity)).mpr
        nlinarith only [hw]
      _ ≤ 2/(115*13225^2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13225) hn' 2]

theorem ratio_window {n : ℕ} (ha : 13225 ≤ n) :
    Bounds (firstRatio (2*n))
      (100000000000000000000/314159265358979323847)
      (2645000000000000000000000/(314159265358979323846*26449)) := by
  obtain ⟨hl, hu⟩ := first_ratio_bounds (N := 2*n) (A := 26450) (by norm_num) (by omega)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    apply (div_le_iff₀ (by positivity : 0 < π*((26450 : ℝ)-1))).mpr
    nlinarith only [pi_bounds.1]

theorem offset_window {n : ℕ} (ha : 13225 ≤ n) :
    Bounds (offsetCore (2*n))
      (-(2645000000000000000000000/(2*314159265358979323846*26449))) 0 := by
  obtain ⟨hl, hu⟩ := offsetCore_bounds (N := 2*n) (A := 26450) (by norm_num) (by omega)
  refine ⟨le_trans ?_ hl, hu⟩
  apply (le_div_iff₀ (by positivity : 0 < 2*π*((26450 : ℝ)-1))).mpr
  nlinarith only [pi_bounds.1]

theorem offset_window_reduced {n : ℕ} (ha : 13225 ≤ n) :
    Bounds (offsetCore (2*n))
      (-661250000000000000000000/4154599204739822068201427) 0 := by
  convert offset_window ha using 1 <;> norm_num

theorem ratio_window_reduced {n : ℕ} (ha : 13225 ≤ n) :
    Bounds (firstRatio (2*n))
      (100000000000000000000/314159265358979323847)
      (1322500000000000000000000/4154599204739822068201427) := by
  convert ratio_window ha using 1 <;> norm_num

end BstLean.Part271.R3.Band
