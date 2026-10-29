import BstLean.Part88Defs

/-!
# Part 88: the Christoffel bound for the Chebyshev polynomials of the second kind

Proves `ChrisIface D` for every `D` (trigonometric form: sine expansion, Parseval, Cauchy–Schwarz),
and the elementary facts on `Sodd` and `SS`.
-/

namespace BstLean.Part88

open Finset Real Polynomial

/-! ## `Sodd` and `SS` -/

theorem Sodd_nonneg (D : ℕ) : 0 ≤ Sodd D := by
  unfold Sodd
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem Sodd_mono {D D' : ℕ} (h : D ≤ D') : Sodd D ≤ Sodd D' := by
  unfold Sodd
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro j _ _
    split_ifs <;> positivity

theorem Sodd_two_mul (k : ℕ) :
    Sodd (2 * k) = 2 / 3 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) := by
  induction k with
  | zero => simp [Sodd]
  | succ k ih =>
    have e : Sodd (2 * (k + 1)) = Sodd (2 * k) + (2 * (k : ℝ) + 2) ^ 2 := by
      unfold Sodd
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : ¬ ((2 * k + 1 + 1) % 2 = 1) := by omega
      rw [if_pos h1, if_neg h2]
      push_cast
      ring
    rw [e, ih]
    push_cast
    ring

theorem SS_mono_xi (D : ℕ) {ξ ξ' : ℝ} (h : |ξ| ≤ |ξ'|) : SS D ξ ≤ SS D ξ' := by
  unfold SS
  have h2 : ξ ^ 2 ≤ ξ' ^ 2 := sq_le_sq.mpr h
  nlinarith [Sodd_nonneg D, mul_le_mul_of_nonneg_right h2 (Sodd_nonneg D)]

/-! ## Orthogonality and Parseval -/

lemma int_cos_mul (m : ℝ) (hm : m ≠ 0) (hs : Real.sin (m * π) = 0) :
    ∫ θ in (0:ℝ)..π, Real.cos (m * θ) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm]
  simp [integral_cos, hs]

lemma int_sin_sin (i j : ℕ) :
    ∫ θ in (0:ℝ)..π, Real.sin (((i:ℝ) + 1) * θ) * Real.sin (((j:ℝ) + 1) * θ) =
      if i = j then π / 2 else 0 := by
  have h : ∀ θ : ℝ, Real.sin (((i:ℝ) + 1) * θ) * Real.sin (((j:ℝ) + 1) * θ) =
      (1 / 2) * Real.cos (((i:ℝ) - j) * θ) - (1 / 2) * Real.cos (((i:ℝ) + j + 2) * θ) := by
    intro θ
    rw [show ((i:ℝ) - j) * θ = ((i:ℝ) + 1) * θ - ((j:ℝ) + 1) * θ by ring,
      show ((i:ℝ) + j + 2) * θ = ((i:ℝ) + 1) * θ + ((j:ℝ) + 1) * θ by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [h]
  have c1 : Continuous fun θ : ℝ => Real.cos (((i:ℝ) - j) * θ) := by fun_prop
  have c2 : Continuous fun θ : ℝ => Real.cos (((i:ℝ) + j + 2) * θ) := by fun_prop
  rw [intervalIntegral.integral_sub ((c1.const_mul _).intervalIntegrable _ _)
    ((c2.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have z2 : ∫ θ in (0:ℝ)..π, Real.cos (((i:ℝ) + j + 2) * θ) = 0 := by
    apply int_cos_mul
    · positivity
    · have := Real.sin_nat_mul_pi (i + j + 2)
      push_cast at this
      exact this
  rw [z2]
  split_ifs with hij
  · subst hij
    simp
    ring
  · have z1 : ∫ θ in (0:ℝ)..π, Real.cos (((i:ℝ) - j) * θ) = 0 := by
      apply int_cos_mul
      · intro h0
        apply hij
        exact_mod_cast sub_eq_zero.mp h0
      · have := Real.sin_int_mul_pi ((i:ℤ) - j)
        push_cast at this
        exact this
    rw [z1]
    simp

lemma parseval {D : ℕ} (a : Fin (D + 1) → ℝ) :
    2 / π * ∫ θ in (0:ℝ)..π, (∑ i, a i * Real.sin ((((i:ℕ):ℝ) + 1) * θ)) ^ 2 = ∑ i, a i ^ 2 := by
  have h : ∀ θ : ℝ, (∑ i, a i * Real.sin ((((i:ℕ):ℝ) + 1) * θ)) ^ 2 =
      ∑ i, ∑ j, (a i * a j) *
        (Real.sin ((((i:ℕ):ℝ) + 1) * θ) * Real.sin ((((j:ℕ):ℝ) + 1) * θ)) := by
    intro θ
    rw [sq, Finset.sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  simp_rw [h]
  have hint : ∀ i j : Fin (D + 1), IntervalIntegrable (fun θ : ℝ => (a i * a j) *
      (Real.sin ((((i:ℕ):ℝ) + 1) * θ) * Real.sin ((((j:ℕ):ℝ) + 1) * θ)))
      MeasureTheory.volume 0 π :=
    fun i j => (by fun_prop : Continuous _).intervalIntegrable _ _
  have e : ∀ i : Fin (D + 1), ∫ θ in (0:ℝ)..π, ∑ j, (a i * a j) *
      (Real.sin ((((i:ℕ):ℝ) + 1) * θ) * Real.sin ((((j:ℕ):ℝ) + 1) * θ)) = a i ^ 2 * (π / 2) := by
    intro i
    rw [intervalIntegral.integral_finsetSum (fun j _ => hint i j)]
    simp_rw [intervalIntegral.integral_const_mul, int_sin_sin, Fin.val_inj]
    simp [Finset.sum_ite_eq]
    ring
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
  simp_rw [e]
  rw [← Finset.sum_mul]
  field_simp

/-! ## The sine expansion -/

/-- The span of `sin θ, …, sin ((D+1) θ)`. -/
def sineSpan (D : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (Set.range fun (j : Fin (D + 1)) (θ : ℝ) => Real.sin ((((j:ℕ):ℝ) + 1) * θ))

lemma sin_mem {D j : ℕ} (h : j ≤ D) :
    (fun θ : ℝ => Real.sin (((j:ℝ) + 1) * θ)) ∈ sineSpan D :=
  Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩

lemma sin_mem' {D : ℕ} (m : ℕ) (h : m ≤ D + 1) :
    (fun θ : ℝ => Real.sin ((m:ℝ) * θ)) ∈ sineSpan D := by
  cases m with
  | zero =>
    have e : (fun θ : ℝ => Real.sin (((0:ℕ):ℝ) * θ)) = 0 := by
      funext θ
      simp
    rw [e]
    exact zero_mem _
  | succ k =>
    have e : (fun θ : ℝ => Real.sin (((k + 1 : ℕ):ℝ) * θ)) =
        fun θ => Real.sin (((k:ℝ) + 1) * θ) := by
      funext θ
      push_cast
      rfl
    rw [e]
    exact sin_mem (by omega)

lemma sineExp_mem : ∀ (D : ℕ) (q : ℝ[X]), q.natDegree ≤ D →
    (fun θ : ℝ => q.eval (Real.cos θ) * Real.sin θ) ∈ sineSpan D := by
  intro D
  induction D with
  | zero =>
    intro q hq
    rw [Polynomial.eq_C_of_natDegree_le_zero hq]
    have := (sineSpan 0).smul_mem (q.coeff 0) (sin_mem' 1 (le_refl 1))
    convert this using 1
    ext θ
    simp
  | succ D ih =>
    intro q hq
    have hd : (divX q).natDegree ≤ D := by
      rw [natDegree_divX_eq_natDegree_tsub_one]
      omega
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (ih _ hd)
    have key : (fun θ : ℝ => q.eval (Real.cos θ) * Real.sin θ) =
        (∑ i : Fin (D + 1), ((a i / 2) • (fun θ : ℝ => Real.sin ((((i:ℕ) + 1 + 1 : ℕ):ℝ) * θ)) +
          (a i / 2) • (fun θ : ℝ => Real.sin (((i:ℕ):ℝ) * θ)))) +
        (q.coeff 0) • (fun θ : ℝ => Real.sin (((1:ℕ):ℝ) * θ)) := by
      ext θ
      have h1 := congrFun ha θ
      have h2 : q.eval (Real.cos θ) = (divX q).eval (Real.cos θ) * Real.cos θ + q.coeff 0 := by
        conv_lhs => rw [← divX_mul_X_add q]
        simp
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1 ⊢
      rw [h2, show (eval (Real.cos θ) q.divX * Real.cos θ + q.coeff 0) * Real.sin θ =
        Real.cos θ * (eval (Real.cos θ) q.divX * Real.sin θ) + q.coeff 0 * Real.sin θ by ring,
        ← h1, Finset.mul_sum]
      congr 1
      · apply sum_congr rfl
        intro i _
        push_cast
        rw [show ((i:ℕ):ℝ) * θ = (((i:ℕ):ℝ) + 1) * θ - θ by ring,
          show (((i:ℕ):ℝ) + 1 + 1) * θ = (((i:ℕ):ℝ) + 1) * θ + θ by ring,
          Real.sin_add, Real.sin_sub]
        ring
      · simp
    rw [key]
    refine add_mem (sum_mem fun i _ => add_mem (Submodule.smul_mem _ _ (sin_mem' _ ?_))
      (Submodule.smul_mem _ _ (sin_mem' _ ?_))) (Submodule.smul_mem _ _ (sin_mem' _ ?_))
    · have := i.2
      omega
    · have := i.2
      omega
    · omega

/-! ## The bound for `Σ sin²((j+1) θ0)` -/

lemma arcsin_sq_le_of_nonneg {x : ℝ} (h0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.arcsin x ^ 2 ≤ 5 / 4 * x ^ 2 := by
  set u := Real.arcsin x with hu
  have hu0 : 0 ≤ u := Real.arcsin_nonneg.2 h0
  have hu2 : u ≤ π / 2 := Real.arcsin_le_pi_div_two x
  have hs : Real.sin u = x := Real.sin_arcsin (by linarith) (by linarith)
  rcases hu0.eq_or_lt with h | hpos
  · rw [← h]
    nlinarith [sq_nonneg x]
  have j1 := Real.mul_le_sin hu0 hu2
  rw [hs, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at j1
  have hpi := Real.pi_lt_d2
  have h79 : u ≤ 0.79 := by
    nlinarith [mul_le_mul_of_nonneg_right hx Real.pi_pos.le]
  have j2 := Real.sin_gt_sub_cube hpos
  rw [hs] at j2
  have hsq1 : u ^ 2 ≤ 0.6241 := by nlinarith
  have hcu1 : u ^ 3 ≤ 0.6241 * u := by nlinarith [mul_le_mul_of_nonneg_left hsq1 hu0]
  have h593 : u ≤ 0.593 := by linarith
  have hsq2 : u ^ 2 ≤ 0.351649 := by nlinarith
  have hcu2 : u ^ 3 ≤ 0.351649 * u := by nlinarith [mul_le_mul_of_nonneg_left hsq2 hu0]
  have h912 : 0.912 * u ≤ x := by linarith
  nlinarith [mul_le_mul h912 h912 (by positivity) h0]

lemma arcsin_sq_le {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.arcsin x ^ 2 ≤ 5 / 4 * x ^ 2 := by
  have h := abs_le.1 hx
  rcases le_total 0 x with h0 | h0
  · exact arcsin_sq_le_of_nonneg h0 h.2
  · have := arcsin_sq_le_of_nonneg (x := -x) (by linarith) (by linarith)
    rw [Real.arcsin_neg] at this
    nlinarith

lemma sin_sq_bound (x0 : ℝ) (hx : |x0| ≤ 1 / 2) (j : ℕ) :
    Real.sin (((j:ℝ) + 1) * Real.arccos x0) ^ 2 ≤
      (if j % 2 = 0 then (1:ℝ) else 0) +
        5 / 4 * x0 ^ 2 * (if j % 2 = 1 then ((j:ℝ) + 1) ^ 2 else 0) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have h1 : ¬ (j % 2 = 1) := by omega
    rw [if_pos h, if_neg h1]
    nlinarith [Real.sin_sq_le_one (((j:ℝ) + 1) * Real.arccos x0)]
  · have h1 : ¬ (j % 2 = 0) := by omega
    rw [if_pos h, if_neg h1]
    obtain ⟨l, hl⟩ : ∃ l : ℕ, j + 1 = 2 * l := ⟨(j + 1) / 2, by omega⟩
    have hl' : (j:ℝ) + 1 = 2 * (l:ℝ) := by exact_mod_cast hl
    set ψ := Real.arcsin x0 with hψ
    have e : ((j:ℝ) + 1) * Real.arccos x0 = (l:ℝ) * π - 2 * l * ψ := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin, hl']
      ring
    have hc : Real.cos ((l:ℝ) * π) ^ 2 = 1 := by
      rw [Real.cos_sq', Real.sin_nat_mul_pi]
      ring
    have e2 : Real.sin (((j:ℝ) + 1) * Real.arccos x0) ^ 2 = Real.sin (2 * l * ψ) ^ 2 := by
      rw [e, Real.sin_sub, Real.sin_nat_mul_pi]
      calc (0 * Real.cos (2 * l * ψ) - Real.cos ((l:ℝ) * π) * Real.sin (2 * l * ψ)) ^ 2
          = Real.cos ((l:ℝ) * π) ^ 2 * Real.sin (2 * l * ψ) ^ 2 := by ring
        _ = Real.sin (2 * l * ψ) ^ 2 := by rw [hc, one_mul]
    have h3 : Real.sin (2 * l * ψ) ^ 2 ≤ (2 * l * ψ) ^ 2 :=
      sq_le_sq.mpr Real.abs_sin_le_abs
    have h4 := arcsin_sq_le hx
    rw [e2, hl']
    have h5 : (2 * (l:ℝ)) ^ 2 * ψ ^ 2 ≤ (2 * (l:ℝ)) ^ 2 * (5 / 4 * x0 ^ 2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith

lemma cnt_even (D : ℕ) :
    ∑ j ∈ range (D + 1), (if j % 2 = 0 then (1:ℝ) else 0) = ((D / 2 : ℕ) : ℝ) + 1 := by
  induction D with
  | zero =>
    rw [Finset.sum_range_one, if_pos (by norm_num)]
    norm_num
  | succ D ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one D with h | h
    · have h1 : ¬ ((D + 1) % 2 = 0) := by omega
      have h2 : (D + 1) / 2 = D / 2 := by omega
      rw [if_neg h1, h2]
      ring
    · have h1 : (D + 1) % 2 = 0 := by omega
      have h2 : (D + 1) / 2 = D / 2 + 1 := by omega
      rw [if_pos h1, h2]
      push_cast
      ring

lemma sum_sin_sq_le (D : ℕ) (x0 : ℝ) (hx : |x0| ≤ 1 / 2) :
    ∑ j ∈ range (D + 1), Real.sin (((j:ℝ) + 1) * Real.arccos x0) ^ 2 ≤ SS D x0 := by
  calc ∑ j ∈ range (D + 1), Real.sin (((j:ℝ) + 1) * Real.arccos x0) ^ 2
      ≤ ∑ j ∈ range (D + 1), ((if j % 2 = 0 then (1:ℝ) else 0) +
        5 / 4 * x0 ^ 2 * (if j % 2 = 1 then ((j:ℝ) + 1) ^ 2 else 0)) :=
        sum_le_sum fun j _ => sin_sq_bound x0 hx j
    _ = SS D x0 := by
        rw [sum_add_distrib, ← mul_sum, cnt_even]
        rfl

/-! ## The Christoffel bound -/

theorem chrisIface (D : ℕ) : ChrisIface D := by
  intro p hp c β x0 hx
  set q : ℝ[X] := p.comp (C (c * β) * X + C c) with hq
  have hqd : q.natDegree ≤ D := by
    calc q.natDegree ≤ p.natDegree * (C (c * β) * X + C c).natDegree := natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ (natDegree_linear_le)
      _ ≤ D := by omega
  have hqe : ∀ y : ℝ, q.eval y = p.eval (c * (1 + β * y)) := by
    intro y
    rw [hq, eval_comp]
    congr 1
    simp
    ring
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (sineExp_mem D q hqd)
  have ha' : ∀ θ : ℝ, ∑ i, a i * Real.sin ((((i:ℕ):ℝ) + 1) * θ) =
      p.eval (c * (1 + β * Real.cos θ)) * Real.sin θ := by
    intro θ
    have := congrFun ha θ
    simpa [hqe] using this
  have hx1 := abs_le.1 hx
  have hint : ∫ θ in (0:ℝ)..π, (p.eval (c * (1 + β * Real.cos θ))) ^ 2 * Real.sin θ ^ 2 =
      ∫ θ in (0:ℝ)..π, (∑ i, a i * Real.sin ((((i:ℕ):ℝ) + 1) * θ)) ^ 2 := by
    congr 1
    funext θ
    rw [ha']
    ring
  rw [hint, parseval]
  have hpt := ha' (Real.arccos x0)
  rw [Real.cos_arccos (by linarith) (by linarith), Real.sin_arccos] at hpt
  have hsq : (√(1 - x0 ^ 2)) ^ 2 = 1 - x0 ^ 2 := Real.sq_sqrt (by nlinarith)
  calc (p.eval (c * (1 + β * x0))) ^ 2 * (1 - x0 ^ 2)
      = (∑ i, a i * Real.sin ((((i:ℕ):ℝ) + 1) * Real.arccos x0)) ^ 2 := by
        rw [hpt, mul_pow, hsq]
    _ = (∑ i : Fin (D + 1), Real.sin ((((i:ℕ):ℝ) + 1) * Real.arccos x0) * a i) ^ 2 := by
        simp_rw [mul_comm]
    _ ≤ (∑ i : Fin (D + 1), Real.sin ((((i:ℕ):ℝ) + 1) * Real.arccos x0) ^ 2) * ∑ i, a i ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ SS D x0 * ∑ i, a i ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
        rw [Fin.sum_univ_eq_sum_range
          (fun j => Real.sin (((j:ℝ) + 1) * Real.arccos x0) ^ 2) (D + 1)]
        exact sum_sin_sq_le D x0 hx

end BstLean.Part88

#print axioms BstLean.Part88.chrisIface
#print axioms BstLean.Part88.Sodd_two_mul
