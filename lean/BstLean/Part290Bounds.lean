import BstLean.Part290Ratio

/-! Uniform analytic inputs for the low World band. -/
namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part228
open BstLean.Part271.R3
open BstLean.Part250 (pi_bounds)

theorem n_positive {n : ℕ} (ha : 8000 ≤ n) : 0 < (n : ℝ) := by
  exact_mod_cast (show 0 < n by omega)

theorem width_positive {n : ℕ} (ha : 8000 ≤ n) : 1 < (mW n : ℝ) := by
  have h := BstLean.Part137.mW_ge_pow42 (show 4096 ≤ n by omega)
  have h' : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast h
  linarith

theorem width_cube {n : ℕ} (ha : 8000 ≤ n) :
    (2236/25 : ℝ)*(n : ℝ)^3 ≤ mW n := by
  have hn : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hw : (n : ℝ)^7 ≤ (mW n : ℝ)^2 := by
    exact_mod_cast (mW_le_iff n (mW n)).mp le_rfl
  have hs : ((2236/25 : ℝ)*(n : ℝ)^3)^2 ≤ (mW n : ℝ)^2 := calc
    _ = (2236/25 : ℝ)^2*(n : ℝ)^6 := by ring
    _ ≤ (n : ℝ)*(n : ℝ)^6 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (n : ℝ)^7 := by ring
    _ ≤ _ := hw
  nlinarith [sq_nonneg ((2236/25 : ℝ)*(n : ℝ)^3-(mW n : ℝ))]

theorem inverse_dimension {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (1/((2*n : ℕ) : ℝ)) 0 (1/16000) := by
  have hn : (16000 : ℝ) ≤ ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 16000 ≤ 2*n by omega)
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hn⟩

theorem inverse_width {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (1/(mW n : ℝ)) 0 (1/45793280000000) := by
  have hn : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hn 3
  have hw := width_cube ha
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (by nlinarith)⟩

theorem dimension_width {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (((2*n : ℕ) : ℝ)/(mW n : ℝ)) 0 (1/2862080000) := by
  have hn := n_positive ha
  have hm : 0 < (mW n : ℝ) := by have := width_positive ha; linarith
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hw := width_cube ha
  constructor
  · positivity
  · push_cast
    calc
      (2*(n : ℝ))/(mW n : ℝ) ≤ 2/((2236/25)*(n : ℝ)^2) := by
        apply (div_le_div_iff₀ hm (by positivity)).mpr
        nlinarith only [hw]
      _ ≤ 1/2862080000 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hn' 2]

theorem ratio_sharp {n : ℕ} (hn : 1 ≤ n) :
    1 + 1/(4*(n : ℝ)) ≤ π * firstRatio (2*n) ∧
    π * firstRatio (2*n) ≤ 1/(1-1/(4*(n : ℝ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  convert radiusRatio_sharp k using 1 <;>
    simp only [radiusRatio, firstRatio, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Nat.succ_eq_add_one] <;> ring

noncomputable def radiusOffset (n : ℕ) : ℝ :=
  (2*(n : ℝ))*(π*firstRatio (2*n)-1)

theorem radiusOffset_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (radiusOffset n) (1/2) (25001/50000) := by
  have hn := n_positive ha
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  obtain ⟨hl, hu⟩ := ratio_sharp (show 1 ≤ n by omega)
  have hl' := (div_le_iff₀ (by positivity : 0 < 4*(n : ℝ))).mp
    (show 1/(4*(n : ℝ)) ≤ π*firstRatio (2*n)-1 by linarith)
  have hp : 0 < 1-1/(4*(n : ℝ)) := by
    have hh : 1/(4*(n : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hu' := (le_div_iff₀ hp).mp hu
  have he : (1-1/(4*(n : ℝ)))*(4*(n : ℝ)) = 4*(n : ℝ)-1 := by
    field_simp
  have hh := mul_le_mul_of_nonneg_right hu' (show 0 ≤ 4*(n : ℝ) by positivity)
  rw [mul_assoc, he] at hh
  have hfinal : 2*(n : ℝ)*(π*firstRatio (2*n)-1) ≤ 2*(n : ℝ)/(4*(n : ℝ)-1) := by
    apply (le_div_iff₀ (by linarith : 0 < 4*(n : ℝ)-1)).mpr
    nlinarith only [hh]
  refine ⟨by unfold radiusOffset; linarith only [hl'], hfinal.trans ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 4*(n : ℝ)-1)).mpr
  linarith

theorem offset_identity {n : ℕ} (ha : 8000 ≤ n) :
    offsetCore (2*n) = -radiusOffset n/(2*π) := by
  have hn := n_positive ha
  unfold offsetCore angularOffset radiusOffset firstRatio
  push_cast
  field_simp [ne_of_gt hn, Real.pi_ne_zero]
  <;> ring

theorem offset_window {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (offsetCore (2*n))
      (-(25001/50000)/(2*(314159265358979323846/10^20)))
      (-(1/2)/(2*(314159265358979323847/10^20))) := by
  rw [offset_identity ha]
  obtain ⟨hl, hu⟩ := radiusOffset_bounds ha
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*π)).mpr
    have hp := pi_bounds.1
    norm_num at hp ⊢
    nlinarith only [hp, hu]
  · apply (div_le_iff₀ (by positivity : 0 < 2*π)).mpr
    have hp := pi_bounds.2
    norm_num at hp ⊢
    nlinarith only [hp, hl]

theorem offset_window_reduced {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (offsetCore (2*n))
      (-12500500000000000000/157079632679489661923)
      (-25000000000000000000/314159265358979323847) := by
  convert offset_window ha using 1 <;> norm_num

theorem ratio_window {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (firstRatio (2*n)) (31830988618379067153/10^20) (318319834/10^9) := by
  obtain ⟨hl, hu⟩ := radiusOffset_bounds ha
  have hn := n_positive ha
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hl' : 1 ≤ π*firstRatio (2*n) := by
    have := (ratio_sharp (show 1 ≤ n by omega)).1
    have hp : 0 ≤ 1/(4*(n : ℝ)) := by positivity
    linarith
  have hu' : π*firstRatio (2*n) ≤ 1+(25001/50000)/16000 := by
    have he : π*firstRatio (2*n)-1 = radiusOffset n/(2*(n : ℝ)) := by
      unfold radiusOffset
      field_simp
    have hh : radiusOffset n/(2*(n : ℝ)) ≤ (25001/50000)/16000 := by
      apply div_le_div₀ (by norm_num) hu (by norm_num) (by linarith)
    linarith
  constructor
  · have hh : (31830988618379067153/10^20 : ℝ)*π ≤ firstRatio (2*n)*π := by
      nlinarith only [pi_bounds.2, hl']
    exact le_of_mul_le_mul_right hh Real.pi_pos
  · have hh : firstRatio (2*n)*π ≤ (318319834/10^9 : ℝ)*π := by
      nlinarith only [pi_bounds.1, hu']
    exact le_of_mul_le_mul_right hh Real.pi_pos

theorem ratio_window_reduced {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (firstRatio (2*n)) (31830988618379067153/100000000000000000000)
      (159159917/500000000) := by
  convert ratio_window ha using 1 <;> norm_num

end BstLean.Part290
