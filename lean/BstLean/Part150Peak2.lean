import BstLean.Part150Peak

/-!
# Part 150, item 2: the two peak integrals

See `Part150Peak` for the statements `peak2` and `peak3`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology

/-! ## The third power: a direct bound -/

lemma period3 (J k : ℕ) :
    ∫ u in ((k : ℝ) + 1 / 2) * π..(((k + 1 : ℕ) : ℝ) + 1 / 2) * π, pk J 3 u ≤
      ((((k : ℝ) + 1 / 2) * π) ^ 3)⁻¹ * cJ J := by
  have hpi := Real.pi_pos
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlow : 0 < ((k : ℝ) + 1 / 2) * π := by positivity
  rw [period_shift]
  unfold cJ
  rw [← intervalIntegral.integral_const_mul]
  have hpos : ∀ v ∈ Icc (-(π / 2)) (π / 2), ((k : ℝ) + 1 / 2) * π ≤ v + ((k : ℝ) + 1) * π := by
    intro v hv; nlinarith [hv.1]
  refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun v hv => ?_
  · refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => ?_
    exact (pow_pos (lt_of_lt_of_le hlow (hpos v hv)) 3).ne'
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · rw [div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_right ?_ (cos_pow_bounds J hv.1 hv.2).1
    exact inv_anti₀ (pow_pos hlow 3) (pow_le_pow_left₀ hlow.le (hpos v hv) 3)

lemma inv_cube_le {n : ℝ} (hn : 0 < n) :
    ((n + 1 / 2) ^ 3)⁻¹ ≤ 1 / (2 * n ^ 2) - 1 / (2 * (n + 1) ^ 2) := by
  have e1 : 1 / (2 * n ^ 2) - 1 / (2 * (n + 1) ^ 2) = (n + 1 / 2) / (n * (n + 1)) ^ 2 := by
    field_simp; ring
  have e2 : ((n + 1 / 2) ^ 3)⁻¹ = (n + 1 / 2) / ((n + 1 / 2) ^ 2) ^ 2 := by
    field_simp
  rw [e1, e2]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2

lemma sum_half_cube_succ (N : ℕ) :
    ∑ k ∈ Finset.range (N + 3), (((k : ℝ) + 1 / 2) ^ 3)⁻¹ ≤
      56807 / 6750 - 1 / (2 * ((N : ℝ) + 3) ^ 2) := by
  induction N with
  | zero => norm_num [Finset.sum_range_succ]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := inv_cube_le (n := (N : ℝ) + 3) (by positivity)
    push_cast at h ⊢
    have e : (N : ℝ) + 1 + 3 = N + 3 + 1 := by ring
    rw [e]
    linarith

lemma sum_half_cube (N : ℕ) :
    ∑ k ∈ Finset.range N, (((k : ℝ) + 1 / 2) ^ 3)⁻¹ ≤ 56807 / 6750 := by
  rcases N with _ | _ | _ | N
  · norm_num
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]
  · have h := sum_half_cube_succ N
    have : (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 3) ^ 2) := by positivity
    linarith

/-- **The peaks for the third power.** -/
theorem peak3 {J : ℕ} (hJ : 1 ≤ J) :
    ∫ u in Ioi (π / 2), pk J 3 u ≤ 56807 / (6750 * π ^ 3) * √(2 * π / J) := by
  have hpi := Real.pi_pos
  refine tail_le_of_periods (pk_integrableOn J (by norm_num))
    (a := fun k => ((((k : ℝ) + 1 / 2) * π) ^ 3)⁻¹ * cJ J) (period3 J) fun N => ?_
  rw [← Finset.sum_mul]
  have e : ∑ k ∈ Finset.range N, ((((k : ℝ) + 1 / 2) * π) ^ 3)⁻¹ =
      (π ^ 3)⁻¹ * ∑ k ∈ Finset.range N, (((k : ℝ) + 1 / 2) ^ 3)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, mul_inv]; ring
  rw [e]
  have h1 : (π ^ 3)⁻¹ * ∑ k ∈ Finset.range N, (((k : ℝ) + 1 / 2) ^ 3)⁻¹ ≤ 56807 / (6750 * π ^ 3) := by
    calc (π ^ 3)⁻¹ * ∑ k ∈ Finset.range N, (((k : ℝ) + 1 / 2) ^ 3)⁻¹
        ≤ (π ^ 3)⁻¹ * (56807 / 6750) := mul_le_mul_of_nonneg_left (sum_half_cube N) (by positivity)
      _ = 56807 / (6750 * π ^ 3) := by field_simp
  exact mul_le_mul h1 (cJ_le hJ) (cJ_nonneg J) (by positivity)

/-! ## The second power: the pairing `v ↔ −v` -/

lemma pair_ineq {c v : ℝ} (hc : 0 < c) (hv0 : 0 ≤ v) (hv : 2 * v ≤ c) :
    1 / (v + c) ^ 2 + 1 / (-v + c) ^ 2 ≤ 2 / c ^ 2 + 88 / 9 * v ^ 2 / c ^ 4 := by
  have h1 : 0 < v + c := by linarith
  have h2 : 0 < -v + c := by linarith
  have hcv : 0 < c ^ 2 - v ^ 2 := by nlinarith
  have e1 : 1 / (v + c) ^ 2 + 1 / (-v + c) ^ 2 = 2 * (c ^ 2 + v ^ 2) / (c ^ 2 - v ^ 2) ^ 2 := by
    have : c ^ 2 - v ^ 2 = (v + c) * (-v + c) := by ring
    rw [this]
    field_simp
    ring
  have e2 : 2 / c ^ 2 + 88 / 9 * v ^ 2 / c ^ 4 = 2 * (9 * c ^ 2 + 44 * v ^ 2) / (9 * c ^ 4) := by
    field_simp; ring
  rw [e1, e2, div_le_div_iff₀ (pow_pos hcv 2) (by positivity)]
  have key : 2 * (9 * c ^ 2 + 44 * v ^ 2) * (c ^ 2 - v ^ 2) ^ 2 - 2 * (c ^ 2 + v ^ 2) * (9 * c ^ 4) =
      2 * (v ^ 2 * (c ^ 2 - 4 * v ^ 2) * (17 * c ^ 2 - 11 * v ^ 2)) := by ring
  have hA : 0 ≤ c ^ 2 - 4 * v ^ 2 := by nlinarith
  have hB : 0 ≤ 17 * c ^ 2 - 11 * v ^ 2 := by nlinarith
  have := mul_nonneg (mul_nonneg (sq_nonneg v) hA) hB
  linarith

lemma period2 (J k : ℕ) :
    ∫ u in ((k : ℝ) + 1 / 2) * π..(((k + 1 : ℕ) : ℝ) + 1 / 2) * π, pk J 2 u ≤
      2 / (((k : ℝ) + 1) * π) ^ 2 * hJ0 J + 88 / 9 / (((k : ℝ) + 1) * π) ^ 4 * hJ2 J := by
  have hpi := Real.pi_pos
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set c : ℝ := ((k : ℝ) + 1) * π with hc
  have hcpi : π ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := lt_of_lt_of_le hpi hcpi
  rw [period_shift]
  set g : ℝ → ℝ := fun v => Real.cos v ^ J / (v + c) ^ 2 with hg
  have hcont : ContinuousOn g (Icc (-(π / 2)) (π / 2)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => ?_
    exact (pow_pos (by linarith [hv.1] : 0 < v + c) 2).ne'
  have hi1 : IntervalIntegrable g volume (-(π / 2)) 0 :=
    (hcont.mono (Icc_subset_Icc_right (by positivity))).intervalIntegrable_of_Icc (by linarith)
  have hi2 : IntervalIntegrable g volume 0 (π / 2) :=
    (hcont.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by positivity)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hneg : ∫ x in (0 : ℝ)..(π / 2), g (-x) = ∫ x in (-(π / 2))..0, g x := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π / 2) g
    rwa [neg_zero] at this
  have hi3 : IntervalIntegrable (fun x => g (-x)) volume 0 (π / 2) := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by positivity) ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => ?_
    exact (pow_pos (by linarith [hv.2] : 0 < -v + c) 2).ne'
  rw [← hsplit, ← hneg, ← intervalIntegral.integral_add hi3 hi2]
  have hrhs : 2 / c ^ 2 * hJ0 J + 88 / 9 / c ^ 4 * hJ2 J =
      ∫ x in (0 : ℝ)..(π / 2), (2 / c ^ 2 * Real.cos x ^ J + 88 / 9 / c ^ 4 * (x ^ 2 * Real.cos x ^ J)) := by
    rw [intervalIntegral.integral_add
      ((Continuous.intervalIntegrable (by fun_prop) _ _))
      ((Continuous.intervalIntegrable (by fun_prop) _ _)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  rw [hrhs]
  refine intervalIntegral.integral_mono_on (by positivity) (hi3.add hi2)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun v hv => ?_
  have hcos := (cos_pow_bounds J (by linarith [hv.1]) hv.2).1
  have hp := pair_ineq hc0 hv.1 (by linarith [hv.2])
  simp only [hg, Real.cos_neg]
  calc Real.cos v ^ J / (-v + c) ^ 2 + Real.cos v ^ J / (v + c) ^ 2
      = Real.cos v ^ J * (1 / (v + c) ^ 2 + 1 / (-v + c) ^ 2) := by ring
    _ ≤ Real.cos v ^ J * (2 / c ^ 2 + 88 / 9 * v ^ 2 / c ^ 4) := mul_le_mul_of_nonneg_left hp hcos
    _ = _ := by ring

lemma sum_inv_sq (N : ℕ) : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2 ≤ π ^ 2 / 6 := by
  have h := sum_le_hasSum (Finset.range (N + 1)) (fun i _ => by positivity) hasSum_zeta_two
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    add_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

lemma sum_inv_pow4 (N : ℕ) : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 4 ≤ π ^ 4 / 90 := by
  have h := sum_le_hasSum (Finset.range (N + 1)) (fun i _ => by positivity) hasSum_zeta_four
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    add_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

/-- **The peaks for the second power.** -/
theorem peak2 {J : ℕ} (hJ : 1 ≤ J) :
    ∫ u in Ioi (π / 2), pk J 2 u ≤ √(2 * π / J) * (1 / 6 + 22 / (405 * J)) := by
  have hpi := Real.pi_pos
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hmain : ∫ u in Ioi (π / 2), pk J 2 u ≤ hJ0 J / 3 + 44 / 405 * hJ2 J := by
    refine tail_le_of_periods (pk_integrableOn J le_rfl)
      (a := fun k => 2 / (((k : ℝ) + 1) * π) ^ 2 * hJ0 J + 88 / 9 / (((k : ℝ) + 1) * π) ^ 4 * hJ2 J)
      (period2 J) fun N => ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    have e1 : ∑ k ∈ Finset.range N, 2 / (((k : ℝ) + 1) * π) ^ 2 =
        2 / π ^ 2 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    have e2 : ∑ k ∈ Finset.range N, 88 / 9 / (((k : ℝ) + 1) * π) ^ 4 =
        88 / 9 / π ^ 4 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 4 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [e1, e2]
    have h1 : 2 / π ^ 2 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / 3 := by
      calc 2 / π ^ 2 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2
          ≤ 2 / π ^ 2 * (π ^ 2 / 6) := mul_le_mul_of_nonneg_left (sum_inv_sq N) (by positivity)
        _ = 1 / 3 := by field_simp; norm_num
    have h2 : 88 / 9 / π ^ 4 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 4 ≤ 44 / 405 := by
      calc 88 / 9 / π ^ 4 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 4
          ≤ 88 / 9 / π ^ 4 * (π ^ 4 / 90) :=
            mul_le_mul_of_nonneg_left (sum_inv_pow4 N) (by positivity)
        _ = 44 / 405 := by field_simp; norm_num
    have := mul_le_mul_of_nonneg_right h1 (hJ0_nonneg J)
    have := mul_le_mul_of_nonneg_right h2 (hJ2_nonneg J)
    linarith
  have h0 := hJ0_le hJ
  have h2 := hJ2_le hJ
  have e : √(2 * π / J) * (1 / 6 + 22 / (405 * J)) =
      √(2 * π / J) / 2 / 3 + 44 / 405 * (√(2 * π / J) / (2 * J)) := by
    field_simp; ring
  rw [e]
  linarith

end BstLean.Part150
