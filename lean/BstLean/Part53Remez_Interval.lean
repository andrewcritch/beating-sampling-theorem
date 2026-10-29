import Mathlib

namespace BstLean.Part53.RemezAux

open MeasureTheory Polynomial Polynomial.Chebyshev
open scoped ENNReal

theorem cheb_expansion (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m) :
    ∃ c : ℕ → ℝ, p = ∑ i ∈ Finset.range (m + 1), c i • T ℝ (i : ℤ) := by
  have hmem : p ∈ Polynomial.degreeLT ℝ (m + 1) := by
    rw [Polynomial.mem_degreeLT]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hm)
  rw [← Polynomial.Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (m + 1) = Finset.range (m + 1) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  symm
  simpa only [chebyshevTsequence] using hc

theorem cheb_sq_integral (m : ℕ) (c : ℕ → ℝ) :
    ∫ x, (∑ i ∈ Finset.range (m + 1), c i * (T ℝ (i : ℤ)).eval x) ^ 2 ∂measureT =
      ∑ i ∈ Finset.range (m + 1), c i ^ 2 * (if i = 0 then Real.pi else Real.pi / 2) := by
  have hi (i j : ℕ) : Integrable
      (fun x => (c i * (T ℝ (i : ℤ)).eval x) * (c j * (T ℝ (j : ℤ)).eval x)) measureT :=
    integrable_measureT (by fun_prop)
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  have he (j : ℕ) :
      ∫ x, (c i * (T ℝ (i : ℤ)).eval x) * (c j * (T ℝ (j : ℤ)).eval x) ∂measureT =
        if j = i then c i * c i * (if i = 0 then Real.pi else Real.pi / 2) else 0 := by
    rw [show (fun x => (c i * (T ℝ (i : ℤ)).eval x) * (c j * (T ℝ (j : ℤ)).eval x)) =
        (fun x => (c i * c j) * ((T ℝ (i : ℤ)).eval x * (T ℝ (j : ℤ)).eval x)) by
          funext x; ring,
      integral_const_mul]
    by_cases hij : j = i
    · subst j
      simp only [ite_true]
      by_cases hi0 : i = 0
      · subst i
        simp only [Nat.cast_zero, ite_true, integral_eval_T_real_mul_self_measureT_zero]
      · rw [integral_T_real_mul_self_measureT_of_ne_zero hi0, if_neg hi0]
    · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne (Ne.symm hij), mul_zero,
        if_neg hij]
  simp_rw [he]
  simp [hi']

theorem cheb_sq_integral_lower (m : ℕ) (c : ℕ → ℝ) :
    Real.pi / 2 * (∑ i ∈ Finset.range (m + 1), c i ^ 2) ≤
      ∫ x, (∑ i ∈ Finset.range (m + 1), c i * (T ℝ (i : ℤ)).eval x) ^ 2 ∂measureT := by
  rw [cheb_sq_integral, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · nlinarith [sq_nonneg (c i), Real.pi_pos]
  · exact le_of_eq (mul_comm _ _)

theorem cheb_eval_bound_kernel (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m)
    (C : ℝ) (hC : 0 ≤ C)
    (ht : ∑ i ∈ Finset.range (m + 1), (T ℝ (i : ℤ)).eval 0 ^ 2 ≤ C) :
    p.eval 0 ^ 2 ≤ (2 * C / Real.pi) * ∫ x, p.eval x ^ 2 ∂measureT := by
  obtain ⟨c, hc⟩ := cheb_expansion p m hm
  have he (x : ℝ) : p.eval x =
      ∑ i ∈ Finset.range (m + 1), c i * (T ℝ (i : ℤ)).eval x := by
    rw [hc]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m + 1)) c
    (fun i => (T ℝ (i : ℤ)).eval 0)
  have hc0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), c i ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl := cheb_sq_integral_lower m c
  simp_rw [← he] at hl hcs
  have h0 := hcs.trans (mul_le_mul_of_nonneg_left ht hc0)
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  have h1 := mul_le_mul_of_nonneg_right h0 Real.pi_pos.le
  have h2 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * C by positivity)
  nlinarith

theorem cheb_eval_bound (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m) :
    p.eval 0 ^ 2 ≤ (2 * ((m : ℝ) + 1) / Real.pi) * ∫ x, p.eval x ^ 2 ∂measureT := by
  apply cheb_eval_bound_kernel p m hm ((m : ℝ) + 1) (by positivity)
  calc
    _ ≤ ∑ _i ∈ Finset.range (m + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_eval_T_real_le_one (i : ℤ) (x := 0) (by norm_num)
      rw [abs_le] at h
      nlinarith
    _ = _ := by simp

theorem cheb_eval_bound_four (p : Polynomial ℝ) (hm : p.natDegree ≤ 4) :
    p.eval 0 ^ 2 ≤ (6 / Real.pi) * ∫ x, p.eval x ^ 2 ∂measureT := by
  have ht : ∑ i ∈ Finset.range (4 + 1), (T ℝ (i : ℤ)).eval 0 ^ 2 ≤ (3 : ℝ) := by
    norm_num [Finset.sum_range_succ, T_eval_zero, Int.negOnePow_def]
  simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
    cheb_eval_bound_kernel p 4 hm 3 (by norm_num) ht

theorem taper_factor_le {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) ^ 2 * (Real.sqrt (1 - x ^ 2))⁻¹ ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  let s := Real.sqrt (1 - x ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg x]
  by_cases hs : s = 0
  · change (1 - x ^ 2) ^ 2 * s⁻¹ ≤ 1
    simp [hs]
  · change (1 - x ^ 2) ^ 2 * s⁻¹ ≤ 1
    rw [← hs2]
    have he : (s ^ 2) ^ 2 * s⁻¹ = s ^ 3 := by field_simp
    rw [he]
    exact pow_le_one₀ hs0 hs1

theorem taper_integral_le (p : Polynomial ℝ) :
    ∫ x, (((1 - X ^ 2) * p).eval x) ^ 2 ∂measureT ≤
      ∫ x in (-1 : ℝ)..1, p.eval x ^ 2 := by
  rw [integral_measureT]
  simp only [Real.sqrt_inv]
  have hi : IntervalIntegrable
      (fun x => (((1 - X ^ 2) * p).eval x) ^ 2 * (Real.sqrt (1 - x ^ 2))⁻¹)
      volume (-1) 1 := by
    simpa only [Real.sqrt_inv] using intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul
      (show ContinuousOn (fun x => (((1 - X ^ 2) * p).eval x) ^ 2)
        (Set.uIcc (-1 : ℝ) 1) from (by fun_prop))
  have hp : IntervalIntegrable (fun x => p.eval x ^ 2) volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  apply intervalIntegral.integral_mono_on (by norm_num) hi hp
  intro x hx
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, mul_pow]
  have h := mul_le_mul_of_nonneg_right (taper_factor_le hx) (sq_nonneg (p.eval x))
  nlinarith

theorem midpoint_sq_bound (p : Polynomial ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hp : p.natDegree ≤ k) :
    p.eval 0 ^ 2 ≤ (((k : ℝ) + 1) ^ 2 / 4) * ∫ x in (-1 : ℝ)..1, p.eval x ^ 2 := by
  let q : Polynomial ℝ := (1 - X ^ 2) * p
  have hq : q.natDegree ≤ k + 2 := by
    have ht : ((1 - X ^ 2 : Polynomial ℝ)).natDegree ≤ 2 := by
      have hx : ((X : Polynomial ℝ) ^ 2).natDegree = 2 := Polynomial.natDegree_X_pow 2
      have h := natDegree_sub_le (1 : Polynomial ℝ) ((X : Polynomial ℝ) ^ 2)
      rw [natDegree_one, hx] at h
      exact h
    have hm : ((1 - X ^ 2) * p).natDegree ≤ (1 - X ^ 2 : Polynomial ℝ).natDegree + p.natDegree :=
      natDegree_mul_le
    exact hm.trans (by omega)
  have he : q.eval 0 = p.eval 0 := by simp [q]
  have hi := taper_integral_le p
  change ∫ x, q.eval x ^ 2 ∂measureT ≤ _ at hi
  have hn : 0 ≤ ∫ x in (-1 : ℝ)..1, p.eval x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  by_cases hk2 : k = 2
  · subst k
    have h := cheb_eval_bound_four q (by simpa using hq)
    rw [he] at h
    have hc : (6 : ℝ) / Real.pi ≤ (2 + 1) ^ 2 / 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    exact h.trans ((mul_le_mul_of_nonneg_left hi (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by simpa using hc) hn))
  · have hk3 : 3 ≤ k := by omega
    have h := cheb_eval_bound q (k + 2) hq
    rw [he] at h
    have hc : 2 * (((k + 2 : ℕ) : ℝ) + 1) / Real.pi ≤ ((k : ℝ) + 1) ^ 2 / 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have ha := mul_nonneg (sub_nonneg.mpr hkR) (show 0 ≤ 3 * (k : ℝ) + 7 by positivity)
      have hb := mul_nonneg (sq_nonneg ((k : ℝ) + 1)) (sub_nonneg.mpr Real.pi_gt_three.le)
      push_cast
      nlinarith
    exact h.trans ((mul_le_mul_of_nonneg_left hi (by positivity)).trans
      (mul_le_mul_of_nonneg_right hc hn))

theorem affine_midpoint_sq_bound (p : Polynomial ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hp : p.natDegree ≤ k) (a w : ℝ) (hw : 0 < w) :
    p.eval a ^ 2 ≤ (((k : ℝ) + 1) ^ 2 / (4 * w)) *
      ∫ x in (a - w)..(a + w), p.eval x ^ 2 := by
  let q := p.comp (C a + C w * X)
  have hq : q.natDegree ≤ k := by
    have hd : (C a + C w * X : Polynomial ℝ).natDegree = 1 := by
      rw [natDegree_C_add, natDegree_C_mul_X w hw.ne']
    have h : q.natDegree ≤ p.natDegree * (C a + C w * X).natDegree := natDegree_comp_le
    simpa only [hd, mul_one] using h.trans (by simpa only [hd, mul_one] using hp)
  have he (x : ℝ) : q.eval x = p.eval (a + w * x) := by simp [q]
  have hint : (∫ x in (-1 : ℝ)..1, p.eval (a + w * x) ^ 2) =
      (∫ x in (a - w)..(a + w), p.eval x ^ 2) / w := by
    have h := intervalIntegral.smul_integral_comp_add_mul
      (f := fun x => p.eval x ^ 2) (a := (-1 : ℝ)) (b := 1) w a
    simp only [smul_eq_mul, mul_neg_one, mul_one, ← sub_eq_add_neg] at h
    apply (eq_div_iff hw.ne').2
    linarith
  have h := midpoint_sq_bound q k hk hq
  simp_rw [he] at h
  simp only [mul_zero, add_zero] at h
  rw [hint] at h
  convert h using 1 <;> ring

end BstLean.Part53.RemezAux
