import BstLean.Part53Remez_Interval

/-!
The nonnegative polynomial bound follows from the Chebyshev reproducing kernel.
The taper `1 - X²` converts its weighted integral to an upper bound by the
Lebesgue integral. Explicit kernel bounds cover degrees two through five;
the general kernel bound covers larger degrees.
-/

namespace BstLean.Part59.RPlusAux
open MeasureTheory Polynomial Polynomial.Chebyshev

private lemma cheb_coeff_integral (m : ℕ) (c : ℕ → ℝ) (i : ℕ)
    (hi : i ∈ Finset.range (m + 1)) :
    (∫ x, (∑ j ∈ Finset.range (m + 1), c j * (T ℝ (j : ℤ)).eval x) *
      (T ℝ (i : ℤ)).eval x ∂measureT) =
      c i * (if i = 0 then Real.pi else Real.pi / 2) := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => integrable_measureT (by fun_prop))]
  have he (j : ℕ) : (∫ x, (c j * (T ℝ (j : ℤ)).eval x) *
      (T ℝ (i : ℤ)).eval x ∂measureT) =
      if j = i then c i * (if i = 0 then Real.pi else Real.pi / 2) else 0 := by
    rw [show (fun x => (c j * (T ℝ (j : ℤ)).eval x) * (T ℝ (i : ℤ)).eval x) =
      (fun x => c j * ((T ℝ (j : ℤ)).eval x * (T ℝ (i : ℤ)).eval x)) by funext x; ring,
      integral_const_mul]
    by_cases hj : j = i
    · subst j
      simp only [ite_true]
      by_cases h0 : i = 0
      · subst i; simp only [Nat.cast_zero, ite_true]
        rw [integral_eval_T_real_mul_self_measureT_zero]
      · rw [integral_T_real_mul_self_measureT_of_ne_zero h0, ite_eq_right h0]
    · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hj, mul_zero, ite_eq_right hj]
  simp_rw [he]
  simp [hi]

private lemma cheb_l1 (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m)
    (hn : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x) (B : ℝ)
    (hB : ∑ i ∈ Finset.range (m + 1),
      |(T ℝ (i : ℤ)).eval 0| / (if i = 0 then Real.pi else Real.pi / 2) ≤ B) :
    p.eval 0 ≤ B * ∫ x, p.eval x ∂measureT := by
  classical
  obtain ⟨c, hc⟩ := BstLean.Part53.RemezAux.cheb_expansion p m hm
  have he (x : ℝ) : p.eval x =
      ∑ i ∈ Finset.range (m + 1), c i * (T ℝ (i : ℤ)).eval x := by
    rw [hc]; simp only [eval_finsetSum, eval_smul, smul_eq_mul]
  let K : ℝ → ℝ := fun x => ∑ i ∈ Finset.range (m + 1),
    ((T ℝ (i : ℤ)).eval 0 / (if i = 0 then Real.pi else Real.pi / 2)) *
      (T ℝ (i : ℤ)).eval x
  have hK (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : K x ≤ B := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hB
    have ht := abs_eval_T_real_le_one (i : ℤ) (abs_le.mpr hx)
    have hN : 0 < (if i = 0 then Real.pi else Real.pi / 2) := by split_ifs <;> positivity
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN]
    calc
      _ ≤ |(T ℝ (i : ℤ)).eval 0 * (T ℝ (i : ℤ)).eval x| := le_abs_self _
      _ = |(T ℝ (i : ℤ)).eval 0| * |(T ℝ (i : ℤ)).eval x| := abs_mul _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hrep : ∫ x, p.eval x * K x ∂measureT = p.eval 0 := by
    simp only [K, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_measureT (by fun_prop))]
    apply Eq.trans _ (he 0).symm
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun x => p.eval x *
      ((T ℝ (i : ℤ)).eval 0 / (if i = 0 then Real.pi else Real.pi / 2) *
      (T ℝ (i : ℤ)).eval x)) = (fun x =>
      ((T ℝ (i : ℤ)).eval 0 / (if i = 0 then Real.pi else Real.pi / 2)) *
      (p.eval x * (T ℝ (i : ℤ)).eval x)) by funext x; ring,
      integral_const_mul]
    simp_rw [he]
    rw [cheb_coeff_integral m c i hi]
    have hN : (if i = 0 then Real.pi else Real.pi / 2) ≠ 0 := by split_ifs <;> positivity
    field_simp
  rw [← hrep, ← integral_const_mul]
  apply integral_mono_ae (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))
  have hae : ∀ᵐ x ∂measureT, x ∈ Set.Icc (-1 : ℝ) 1 := by
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun x hx => ⟨hx.1.le, hx.2⟩)
  filter_upwards [hae] with x hx
  exact (mul_le_mul_of_nonneg_left (hK x hx) (hn x hx)).trans_eq (mul_comm _ _)

private lemma taper_l1 (p : Polynomial ℝ)
    (hn : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x) :
    ∫ x, ((1 - X ^ 2) * p).eval x ∂measureT ≤
      ∫ x in (-1 : ℝ)..1, p.eval x := by
  rw [integral_measureT]
  simp only [Real.sqrt_inv]
  have hi : IntervalIntegrable (fun x => ((1 - X ^ 2) * p).eval x *
      (Real.sqrt (1 - x ^ 2))⁻¹) volume (-1) 1 :=
    by
      simpa only [Real.sqrt_inv] using
        (intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul
          (show ContinuousOn (fun x => ((1 - X ^ 2) * p).eval x)
            (Set.uIcc (-1 : ℝ) 1) from (by fun_prop)))
  apply intervalIntegral.integral_mono_on (by norm_num) hi
    (p.continuous.intervalIntegrable _ _)
  intro x hx
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hs : Real.sqrt (1 - x ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg x]
  have he : (1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹ = Real.sqrt (1 - x ^ 2) := by
    calc
      _ = Real.sqrt (1 - x ^ 2) ^ 2 * (Real.sqrt (1 - x ^ 2))⁻¹ := by
        congr 1
        exact (Real.sq_sqrt (show 0 ≤ 1 - x ^ 2 by linarith)).symm
      _ = _ := ?_
    by_cases h : Real.sqrt (1 - x ^ 2) = 0
    · simp [h]
    · field_simp
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X]
  calc
    _ = ((1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹) * p.eval x := by ring
    _ = Real.sqrt (1 - x ^ 2) * p.eval x := by rw [he]
    _ ≤ p.eval x := by simpa using mul_le_mul_of_nonneg_right hs (hn x hx)

private lemma kernel_bound (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (2 * k + 2 + 1),
      |(T ℝ (i : ℤ)).eval 0| / (if i = 0 then Real.pi else Real.pi / 2)) ≤
      ((k : ℝ) + 1) ^ 2 / 4 := by
  classical
  by_cases hsmall : k ≤ 5
  · interval_cases k <;>
      norm_num [Finset.sum_range_succ, T_eval_zero, Int.negOnePow_def] <;>
      (field_simp; nlinarith [Real.pi_gt_d2])
  · have hk6 : 6 ≤ k := by omega
    have hb : (∑ i ∈ Finset.range (2 * k + 2 + 1),
        |(T ℝ (i : ℤ)).eval 0| / (if i = 0 then Real.pi else Real.pi / 2)) ≤
        (2 * ((2 * k + 3 : ℕ) : ℝ)) / Real.pi := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (2 * k + 2 + 1), 2 / Real.pi := by
          apply Finset.sum_le_sum
          intro i _
          have ht := abs_eval_T_real_le_one (i : ℤ) (x := 0) (by norm_num)
          split_ifs
          · exact (div_le_div_of_nonneg_right ht Real.pi_pos.le).trans
              (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)
          · calc
              _ ≤ 1 / (Real.pi / 2) := div_le_div_of_nonneg_right ht (by positivity)
              _ = _ := by ring
        _ = _ := by simp; ring
    apply hb.trans
    rw [div_le_iff₀ Real.pi_pos]
    have hkR : (6 : ℝ) ≤ k := by exact_mod_cast hk6
    have ha := mul_nonneg (sub_nonneg.mpr hkR) (show 0 ≤ 3 * (k : ℝ) + 8 by positivity)
    have hb := mul_nonneg (sq_nonneg ((k : ℝ) + 1)) (sub_nonneg.mpr Real.pi_gt_three.le)
    push_cast
    nlinarith

theorem midpoint_nonneg_bound59x (p : Polynomial ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hp : p.natDegree ≤ 2 * k) (hn : ∀ x : ℝ, 0 ≤ p.eval x) :
    p.eval 0 ≤ (((k : ℝ) + 1) ^ 2 / 4) *
      ∫ x in (-1 : ℝ)..1, p.eval x := by
  let q : Polynomial ℝ := (1 - X ^ 2) * p
  have hq : q.natDegree ≤ 2 * k + 2 := by
    have ht : (1 - X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
      have hx : ((X : Polynomial ℝ) ^ 2).natDegree = 2 := natDegree_X_pow 2
      have h := natDegree_sub_le (1 : Polynomial ℝ) ((X : Polynomial ℝ) ^ 2)
      rwa [natDegree_one, hx, max_eq_right (Nat.zero_le 2)] at h
    exact natDegree_mul_le.trans (by omega)
  have hqn (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ q.eval x := by
    simp only [q, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
    apply mul_nonneg _ (hn x)
    nlinarith [hx.1, hx.2]
  have h := cheb_l1 q (2 * k + 2) hq hqn (((k : ℝ) + 1) ^ 2 / 4) (kernel_bound k hk)
  have hi := taper_l1 p (fun x _ => hn x)
  simpa [q] using h.trans (mul_le_mul_of_nonneg_left hi (by positivity))

theorem affine_nonneg_bound59x (p : Polynomial ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hp : p.natDegree ≤ 2 * k) (hn : ∀ x : ℝ, 0 ≤ p.eval x)
    (a w : ℝ) (hw : 0 < w) :
    p.eval a ≤ (((k : ℝ) + 1) ^ 2 / (4 * w)) *
      ∫ x in (a - w)..(a + w), p.eval x := by
  let q := p.comp (C a + C w * X)
  have hq : q.natDegree ≤ 2 * k := by
    have hd : (C a + C w * X : Polynomial ℝ).natDegree = 1 := by
      rw [Polynomial.natDegree_C_add, Polynomial.natDegree_C_mul_X w hw.ne']
    have h : q.natDegree ≤ p.natDegree * (C a + C w * X).natDegree := natDegree_comp_le
    simpa only [hd, mul_one] using h.trans (by simpa only [hd, mul_one] using hp)
  have he (x : ℝ) : q.eval x = p.eval (a + w * x) := by simp [q]
  have hint : (∫ x in (-1 : ℝ)..1, p.eval (a + w * x)) =
      (∫ x in (a - w)..(a + w), p.eval x) / w := by
    have h := intervalIntegral.smul_integral_comp_add_mul
      (f := fun x => p.eval x) (a := (-1 : ℝ)) (b := 1) w a
    simp only [smul_eq_mul, mul_neg_one, mul_one, ← sub_eq_add_neg] at h
    apply (eq_div_iff hw.ne').2
    linarith
  have h := midpoint_nonneg_bound59x q k hk hq (fun x => by rw [he]; exact hn _)
  simp_rw [he] at h
  simp only [mul_zero, add_zero] at h
  rw [hint] at h
  convert h using 1; ring

end BstLean.Part59.RPlusAux
