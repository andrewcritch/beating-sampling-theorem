import Mathlib

/-!
# Part 29, layer L4 (F3b): the Gaussian covariances of `C_S²`

The raw quadratic coefficients of `m` are an array `g (i, j, k)` (the coefficient of `x_i x_j` in output `k`,
used for `i < j`), standard Gaussian and independent (the product measure). For a four-subset
`S = {s₀ < s₁ < s₂ < s₃}` of `Fin n`, the four-index coefficient of part 20's parity floor is
`C_S = 2 (a₀₁ᵀ F a₂₃ + a₀₂ᵀ F a₁₃ + a₀₃ᵀ F a₁₂)`, with `a_{ab} = g(s_a, s_b, ·)`.
With `v = ‖F‖_F²` and `r = tr F⁴` (`F` symmetric), part 28 states:
`E C_S² = 12 v`, and `E[C_S² C_T²] − (12 v)²` is `288 v² + 288 r`, `96 r`, `32 r`, `0`, `0` at overlap
`|S ∩ T| = 4, 3, 2, 1, 0`. These are the hypotheses `hmean`, `hcov` of `floor_failure` (`Part29Overlap.lean`).
-/

namespace BstLean.Part29

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- The standard Gaussian law of the coefficient array. -/
noncomputable def coefLaw (n : ℕ) : Measure (Fin n × Fin n × Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The bilinear form `aᵀ F b` of two coefficient columns, for the pairs `(i, j)` and `(i', j')`. -/
noncomputable def bil (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n × Fin n × Fin n → ℝ)
    (i j i' j' : Fin n) : ℝ :=
  ∑ k, ∑ l, F k l * g (i, j, k) * g (i', j', l)

/-- `C_S`, for `S` given by its sorted enumeration. -/
noncomputable def coefC (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) (hS : S.card = 4)
    (g : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  let s := S.orderEmbOfFin hS
  2 * (bil F g (s 0) (s 1) (s 2) (s 3) + bil F g (s 0) (s 2) (s 1) (s 3) + bil F g (s 0) (s 3) (s 1) (s 2))

/-- `C_S²`, extended by `0` off the four-subsets, as the random variables of `floor_failure`. -/
noncomputable def coefX (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (g : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  if hS : S.card = 4 then coefC F S hS g ^ 2 else 0

/-- `v = ‖F‖_F²`. -/
noncomputable def frobSq (F : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, F i j ^ 2
/-- `r = tr F⁴`. -/
noncomputable def trF4 (F : Matrix (Fin n) (Fin n) ℝ) : ℝ := ((F * F) * (F * F)).trace

private lemma polynomial_integrable
    (p : MvPolynomial (Fin n × Fin n × Fin n) ℝ) :
    Integrable (fun g => MvPolynomial.eval g p) (coefLaw n) := by
  classical
  conv in MvPolynomial.eval _ p => rw [p.as_sum]
  simp only [MvPolynomial.eval_sum]
  apply integrable_finsetSum
  intro d hd
  simp only [MvPolynomial.eval_monomial]
  have hp (g : Fin n × Fin n × Fin n → ℝ) :
      d.prod (fun i e => g i ^ e) = ∏ i, g i ^ d i :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp_rw [hp]
  exact (Integrable.fintype_prod (f := fun i x => x ^ d i) (fun i =>
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) (by simp) _)).const_mul _

private lemma bil_polynomial (F : Matrix (Fin n) (Fin n) ℝ) (i j i' j' : Fin n) :
    ∃ p : MvPolynomial (Fin n × Fin n × Fin n) ℝ,
      ∀ g, bil F g i j i' j' = MvPolynomial.eval g p := by
  classical
  refine ⟨∑ k, ∑ l, MvPolynomial.C (F k l) * MvPolynomial.X (i, j, k) *
    MvPolynomial.X (i', j', l), ?_⟩
  intro g
  simp [bil]

private lemma coefX_polynomial (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    ∃ p : MvPolynomial (Fin n × Fin n × Fin n) ℝ,
      ∀ g, coefX F S g = MvPolynomial.eval g p := by
  classical
  by_cases hS : S.card = 4
  · let s := S.orderEmbOfFin hS
    obtain ⟨p, hp⟩ := bil_polynomial F (s 0) (s 1) (s 2) (s 3)
    obtain ⟨q, hq⟩ := bil_polynomial F (s 0) (s 2) (s 1) (s 3)
    obtain ⟨r, hr⟩ := bil_polynomial F (s 0) (s 3) (s 1) (s 2)
    refine ⟨(MvPolynomial.C 2 * (p + q + r)) ^ 2, ?_⟩
    intro g
    simp only [coefX, dite_eq_left hS, coefC]
    change (2 * (bil F g (s 0) (s 1) (s 2) (s 3) +
      bil F g (s 0) (s 2) (s 1) (s 3) + bil F g (s 0) (s 3) (s 1) (s 2))) ^ 2 = _
    simp [hp, hq, hr]
  · refine ⟨0, ?_⟩
    intro g
    simp [coefX, hS]

private lemma coordinate_pair_moment (a b : Fin n × Fin n × Fin n) :
    ∫ g, g a * g b ∂coefLaw n = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    have hs : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
      rw [variance_eq_integral (by fun_prop)] at h
      simpa using h
    simp only [ite_true]
    rw [show (fun g : Fin n × Fin n × Fin n → ℝ => g a * g a) =
      (fun g => (g a) ^ 2) by funext g; ring]
    change ∫ g, (g a) ^ 2 ∂(Measure.pi fun _ => gaussianReal 0 1) = 1
    rw [integral_comp_eval (X := fun _ : Fin n × Fin n × Fin n => ℝ)
      (μ := fun _ => gaussianReal 0 1) (i := a) (f := fun x : ℝ => x ^ 2) (by fun_prop)]
    exact hs
  · have hi : iIndepFun (fun a (g : Fin n × Fin n × Fin n → ℝ) => g a)
        (coefLaw n) := iIndepFun_pi (fun _ => aemeasurable_id)
    rw [(hi.indepFun hab).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply a).aestronglyMeasurable
      (measurable_pi_apply b).aestronglyMeasurable]
    simp [coefLaw, integral_eval, hab]

private lemma coordinate_four_moment (a b c d : Fin n × Fin n × Fin n)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) :
    ∫ g, g a * g b * g c * g d ∂coefLaw n =
      (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
  classical
  have hi : iIndepFun (fun a (g : Fin n × Fin n × Fin n → ℝ) => g a)
      (coefLaw n) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hind := hi.indepFun_prodMk_prodMk (fun _ => by fun_prop) a c b d hab had hcb hcd
  have hm : IndepFun (fun g => g a * g c) (fun g => g b * g d) (coefLaw n) :=
    hind.comp (show Measurable (fun p : ℝ × ℝ => p.1 * p.2) by fun_prop)
      (show Measurable (fun p : ℝ × ℝ => p.1 * p.2) by fun_prop)
  rw [show (fun g : Fin n × Fin n × Fin n → ℝ => g a * g b * g c * g d) =
    (fun g => (g a * g c) * (g b * g d)) by funext g; ring]
  rw [hm.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop),
    coordinate_pair_moment, coordinate_pair_moment]

private lemma weighted_four_integrable (A : ℝ) (a b c d : Fin n × Fin n × Fin n) :
    Integrable (fun g => A * (g a * g b * g c * g d)) (coefLaw n) := by
  have h := polynomial_integrable (n := n)
    (MvPolynomial.C A * (MvPolynomial.X a * MvPolynomial.X b *
      MvPolynomial.X c * MvPolynomial.X d))
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
  exact h

private lemma bil_product_moment (F : Matrix (Fin n) (Fin n) ℝ)
    (i j i' j' u v u' v' : Fin n)
    (hab : (i, j) ≠ (i', j')) (had : (i, j) ≠ (u', v'))
    (hcb : (u, v) ≠ (i', j')) (hcd : (u, v) ≠ (u', v')) :
    ∫ g, bil F g i j i' j' * bil F g u v u' v' ∂coefLaw n =
      if (i, j) = (u, v) ∧ (i', j') = (u', v') then frobSq F else 0 := by
  classical
  let f := fun (k l p q : Fin n) (g : Fin n × Fin n × Fin n → ℝ) =>
    (F k l * F p q) * (g (i, j, k) * g (i', j', l) * g (u, v, p) * g (u', v', q))
  have hf (k l p q : Fin n) : Integrable (f k l p q) (coefLaw n) :=
    weighted_four_integrable _ _ _ _ _
  have hexpand (g : Fin n × Fin n × Fin n → ℝ) :
      bil F g i j i' j' * bil F g u v u' v' = ∑ k, ∑ l, ∑ p, ∑ q, f k l p q g := by
    unfold bil
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    dsimp [f]
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hf k l p q))))]
  simp_rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ =>
    integrable_finsetSum _ (fun q _ => hf _ l p q)))]
  simp_rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hf _ _ p q))]
  simp_rw [integral_finsetSum _ (fun q _ => hf _ _ _ q)]
  have he (k l p q : Fin n) :
      ∫ g, f k l p q g ∂coefLaw n = (F k l * F p q) *
        ((if (i, j, k) = (u, v, p) then 1 else 0) *
         (if (i', j', l) = (u', v', q) then 1 else 0)) := by
    dsimp [f]
    rw [integral_const_mul]
    congr 1
    apply coordinate_four_moment <;> intro h
    · exact hab (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    · exact had (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    · exact hcb (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    · exact hcd (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
  simp_rw [he]
  by_cases hac : (i, j) = (u, v)
  · have hu : i = u := congrArg Prod.fst hac
    have hv : j = v := congrArg Prod.snd hac
    subst u; subst v
    by_cases hbd : (i', j') = (u', v')
    · have hu' : i' = u' := congrArg Prod.fst hbd
      have hv' : j' = v' := congrArg Prod.snd hbd
      subst u'; subst v'
      simp [frobSq, sq]
    · have hn (l q : Fin n) : (i', j', l) ≠ (u', v', q) := by
        intro h
        exact hbd (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
      simp [hbd, hn]
  · have hn (k p : Fin n) : (i, j, k) ≠ (u, v, p) := by
      intro h
      exact hac (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    simp [hac, hn]

theorem coefX_mean (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) (S : Finset (Fin n))
    (hS : S.card = 4) :
    ∫ g, coefX F S g ∂(coefLaw n) = 12 * frobSq F := by
  classical
  let s := S.orderEmbOfFin hS
  let B : Fin 3 → (Fin n × Fin n × Fin n → ℝ) → ℝ :=
    fun k g => match k.val with
      | 0 => bil F g (s 0) (s 1) (s 2) (s 3)
      | 1 => bil F g (s 0) (s 2) (s 1) (s 3)
      | _ => bil F g (s 0) (s 3) (s 1) (s 2)
  have hpoly (k : Fin 3) : ∃ p : MvPolynomial (Fin n × Fin n × Fin n) ℝ,
      ∀ g, B k g = MvPolynomial.eval g p := by
    fin_cases k <;> exact bil_polynomial F _ _ _ _
  have hI (k l : Fin 3) : Integrable (fun g => B k g * B l g) (coefLaw n) := by
    obtain ⟨p, hp⟩ := hpoly k
    obtain ⟨q, hq⟩ := hpoly l
    simpa only [MvPolynomial.eval_mul, ← hp, ← hq] using polynomial_integrable (p * q)
  have hm (k l : Fin 3) : ∫ g, B k g * B l g ∂coefLaw n =
      if k = l then frobSq F else 0 := by
    fin_cases k <;> fin_cases l <;> simp only [B]
    all_goals
      rw [bil_product_moment F _ _ _ _ _ _ _ _
        (by simp [Prod.mk.injEq, s.injective.eq_iff])
        (by simp [Prod.mk.injEq, s.injective.eq_iff])
        (by simp [Prod.mk.injEq, s.injective.eq_iff])
        (by simp [Prod.mk.injEq, s.injective.eq_iff])]
      simp [Prod.mk.injEq, s.injective.eq_iff]
  have hexpand (g : Fin n × Fin n × Fin n → ℝ) :
      coefX F S g = 4 * ∑ k : Fin 3, ∑ l : Fin 3, B k g * B l g := by
    simp [coefX, hS, coefC, B, s, Fin.sum_univ_succ]
    ring
  simp_rw [hexpand]
  rw [integral_const_mul,
    integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hI k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hI _ l), hm]
  simp [Fin.sum_univ_succ]
  ring

private lemma finite_coordinate_moment {R : ℕ}
    (τ : Fin R → Fin n × Fin n × Fin n) :
    (∫ g, ∏ r, g (τ r) ∂coefLaw n) =
      ∏ i, ∫ x : ℝ, x ^ (Finset.univ.filter fun r => τ r = i).card ∂gaussianReal 0 1 := by
  classical
  have hp (g : Fin n × Fin n × Fin n → ℝ) :
      (∏ r, g (τ r)) = ∏ i, g i ^ (Finset.univ.filter fun r => τ r = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ g).symm
  simp_rw [hp]
  exact integral_fintype_prod_eq_prod _

private lemma coordinate_singleton_four_zero (a b c d : Fin n × Fin n × Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    ∫ g, g a * g b * g c * g d ∂coefLaw n = 0 := by
  classical
  let τ : Fin 4 → Fin n × Fin n × Fin n := fun r => match r.val with
    | 0 => a
    | 1 => b
    | 2 => c
    | _ => d
  have hp (g : Fin n × Fin n × Fin n → ℝ) :
      (∏ r, g (τ r)) = g a * g b * g c * g d := by
    simp [τ, Fin.prod_univ_succ]
    ring
  rw [← show (fun g : Fin n × Fin n × Fin n → ℝ => ∏ r, g (τ r)) =
    (fun g => g a * g b * g c * g d) from funext hp, finite_coordinate_moment]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  have hc : (Finset.univ.filter fun r => τ r = a) = {0} := by
    ext r
    fin_cases r <;> norm_num [τ, Ne.symm hab, Ne.symm hac, Ne.symm had]
  simp [hc]

private lemma gaussian_exp_deriv : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
    (fun t => t) * (fun t => Real.exp (t ^ 2 / 2)) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    convert (hasDerivAt_pow 2 t).div_const 2 using 1 <;> ring
  simpa [mul_comm] using h.exp.deriv

private lemma gaussian_exp_deriv_rec (j : ℕ) :
    iteratedDeriv (j + 2) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
      (j + 1 : ℝ) * iteratedDeriv j (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  rw [iteratedDeriv_succ', gaussian_exp_deriv,
    iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  simp [iteratedDeriv_fun_id_zero, Finset.mem_range, Nat.choose_one_right]

private lemma gaussian_fourth_moment : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) (by simp) 4
  rw [mgf_fun_id_gaussianReal] at h
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul] at h
  change iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) at h
  have h2 : iteratedDeriv 2 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 1 := by
    simpa using gaussian_exp_deriv_rec 0
  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) =
        iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := h.symm
    _ = 3 * iteratedDeriv 2 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
      have h4 := gaussian_exp_deriv_rec 2
      norm_num at h4
      exact h4
    _ = 3 := by rw [h2]; norm_num

private lemma coordinate_wick_four (a b c d : Fin n × Fin n × Fin n) :
    ∫ g, g a * g b * g c * g d ∂coefLaw n =
      (if a = b then 1 else 0) * (if c = d then 1 else 0) +
      (if a = c then 1 else 0) * (if b = d then 1 else 0) +
      (if a = d then 1 else 0) * (if b = c then 1 else 0) := by
  classical
  have hsame (x : Fin n × Fin n × Fin n) :
      (∫ g, g x * g x * g x * g x ∂coefLaw n) = 3 := by
    have hf : (fun g : Fin n × Fin n × Fin n → ℝ => g x * g x * g x * g x) =
        (fun g => (g x) ^ 4) := by funext g; ring
    rw [hf]
    change ∫ g, (g x) ^ 4 ∂(Measure.pi fun _ => gaussianReal 0 1) = 3
    rw [integral_comp_eval (X := fun _ : Fin n × Fin n × Fin n => ℝ)
      (μ := fun _ => gaussianReal 0 1) (i := x) (f := fun t : ℝ => t ^ 4) (by fun_prop)]
    exact gaussian_fourth_moment
  have hp (x y : Fin n × Fin n × Fin n) (hxy : x ≠ y) :
      (∫ g, g x * g x * g y * g y ∂coefLaw n) = 1 := by
    have hf : (fun g : Fin n × Fin n × Fin n → ℝ => g x * g x * g y * g y) =
        (fun g => g x * g y * g x * g y) := by funext g; ring
    rw [hf, coordinate_four_moment x y x y hxy hxy hxy hxy]
    norm_num
  have hrotate (w x y z : Fin n × Fin n × Fin n) :
      (∫ g, g w * g x * g y * g z ∂coefLaw n) =
        ∫ g, g z * g w * g x * g y ∂coefLaw n := by
    congr 1
    funext g
    ring
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      by_cases had : a = d
      · subst d; convert hsame a using 1 <;> norm_num
      · simp only [ite_true, had, ite_false, mul_zero, zero_mul, add_zero, zero_add]
        rw [hrotate]
        exact coordinate_singleton_four_zero d a a a (Ne.symm had) (Ne.symm had) (Ne.symm had)
    · by_cases had : a = d
      · subst d
        simp only [ite_true, hac, Ne.symm hac, ite_false, zero_mul, mul_zero, add_zero, zero_add]
        rw [hrotate, hrotate]
        exact coordinate_singleton_four_zero c a a a (Ne.symm hac) (Ne.symm hac) (Ne.symm hac)
      · by_cases hcd : c = d
        · subst d
          simpa [hac] using hp a c hac
        · simp only [ite_true, hac, had, hcd, ite_false, zero_mul, mul_zero, add_zero]
          rw [hrotate, hrotate]
          exact coordinate_singleton_four_zero c d a a hcd (Ne.symm hac) (Ne.symm hac)
  · by_cases hac : a = c
    · subst c
      by_cases had : a = d
      · subst d
        simp only [ite_true, hab, Ne.symm hab, ite_false, zero_mul, mul_zero, add_zero, zero_add]
        rw [hrotate, hrotate, hrotate]
        exact coordinate_singleton_four_zero b a a a (Ne.symm hab) (Ne.symm hab) (Ne.symm hab)
      · by_cases hbd : b = d
        · subst d
          have hf : (fun g : Fin n × Fin n × Fin n → ℝ => g a * g b * g a * g b) =
              (fun g => g a * g a * g b * g b) := by funext g; ring
          rw [hf]
          simpa [hab] using hp a b hab
        · simp only [ite_true, hab, had, hbd, ite_false, zero_mul, mul_zero, add_zero, zero_add]
          rw [hrotate, hrotate, hrotate]
          exact coordinate_singleton_four_zero b a d a (Ne.symm hab) hbd (Ne.symm hab)
    · by_cases had : a = d
      · subst d
        by_cases hbc : b = c
        · subst c
          have hf : (fun g : Fin n × Fin n × Fin n → ℝ => g a * g b * g b * g a) =
              (fun g => g a * g a * g b * g b) := by funext g; ring
          rw [hf]
          simpa [hab, Ne.symm hab] using hp a b hab
        · simp only [ite_true, hab, hac, hbc, Ne.symm hac, Ne.symm hab,
            ite_false, zero_mul, mul_zero, add_zero, zero_add]
          rw [hrotate, hrotate, hrotate]
          exact coordinate_singleton_four_zero b c a a hbc (Ne.symm hab) (Ne.symm hab)
      · simp only [hab, hac, had, ite_false, zero_mul, add_zero]
        exact coordinate_singleton_four_zero a b c d hab hac had

/-- A product with one occurrence of a column is odd under reflection of that column. -/
private lemma bil_product_singleton_zero (F : Matrix (Fin n) (Fin n) ℝ)
    {R : ℕ} (a b : Fin R → Fin n × Fin n) (r : Fin R)
    (hab : a r ≠ b r)
    (ha : ∀ s, s ≠ r → a s ≠ a r)
    (hb : ∀ s, s ≠ r → b s ≠ a r) :
    ∫ g, ∏ s, bil F g (a s).1 (a s).2 (b s).1 (b s).2 ∂coefLaw n = 0 := by
  classical
  let flip : (Fin n × Fin n × Fin n → ℝ) → (Fin n × Fin n × Fin n → ℝ) :=
    fun g x => if (x.1, x.2.1) = a r then -g x else g x
  have hm : MeasurePreserving flip (coefLaw n) (coefLaw n) := by
    change MeasurePreserving
      (fun (g : Fin n × Fin n × Fin n → ℝ) (x : Fin n × Fin n × Fin n) =>
        (fun t : ℝ => if (x.1, x.2.1) = a r then -t else t) (g x))
      (Measure.pi fun _ => gaussianReal 0 1) (Measure.pi fun _ => gaussianReal 0 1)
    apply measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
      (f := fun (x : Fin n × Fin n × Fin n) (t : ℝ) =>
        if (x.1, x.2.1) = a r then -t else t)
    intro x
    by_cases hx : (x.1, x.2.1) = a r
    · simpa only [flip, hx, ite_true] using
        (show MeasurePreserving (fun t : ℝ => -t) (gaussianReal 0 1)
          (gaussianReal 0 1) from ⟨by fun_prop, by simp [gaussianReal_map_neg]⟩)
    · simp only [hx, ite_false]
      exact ⟨by fun_prop, by simp⟩
  have he (g : Fin n × Fin n × Fin n → ℝ) (s : Fin R) :
      bil F (flip g) (a s).1 (a s).2 (b s).1 (b s).2 =
        if s = r then -bil F g (a s).1 (a s).2 (b s).1 (b s).2
          else bil F g (a s).1 (a s).2 (b s).1 (b s).2 := by
    by_cases hs : s = r
    · subst s
      simp only [bil, flip, Prod.mk.eta, ite_true, Ne.symm hab, ite_false]
      simp only [mul_neg, neg_mul, Finset.sum_neg_distrib]
    · simp only [bil, flip, Prod.mk.eta, ha s hs, hb s hs, ite_false, hs]
  let f := fun g : Fin n × Fin n × Fin n → ℝ =>
    ∏ s, bil F g (a s).1 (a s).2 (b s).1 (b s).2
  have ho (g : Fin n × Fin n × Fin n → ℝ) : f (flip g) = -f g := by
    dsimp [f]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    rw [he, ite_eq_left rfl]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    rw [neg_mul]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    rw [he, ite_eq_right (Finset.mem_erase.mp hs).1]
  have hmeas : Measurable f := by dsimp [f, bil]; fun_prop
  have hint : (∫ g, f (flip g) ∂coefLaw n) = ∫ g, f g ∂coefLaw n := by
    rw [← integral_map hm.measurable.aemeasurable hmeas.aestronglyMeasurable, hm.map_eq]
  simp_rw [ho] at hint
  rw [integral_neg] at hint
  change (∫ g, f g ∂coefLaw n) = 0
  linarith

private lemma bil_symm (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (g : Fin n × Fin n × Fin n → ℝ) (p q : Fin n × Fin n) :
    bil F g p.1 p.2 q.1 q.2 = bil F g q.1 q.2 p.1 p.2 := by
  classical
  unfold bil
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [hF.apply]
  ring

private lemma bil_product_column_once_zero (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    {R : ℕ} (a b : Fin R → Fin n × Fin n) (r : Fin R) (p : Fin n × Fin n)
    (hocc : a r = p ∨ b r = p) (hab : a r ≠ b r)
    (hunique : ∀ s, s ≠ r → a s ≠ p ∧ b s ≠ p) :
    ∫ g, ∏ s, bil F g (a s).1 (a s).2 (b s).1 (b s).2 ∂coefLaw n = 0 := by
  rcases hocc with hleft | hright
  · apply bil_product_singleton_zero F a b r hab
    · intro s hs
      simpa only [hleft] using (hunique s hs).1
    · intro s hs
      simpa only [hleft] using (hunique s hs).2
  · have hz := bil_product_singleton_zero F b a r (Ne.symm hab)
      (fun s hs => by simpa only [hright] using (hunique s hs).2)
      (fun s hs => by simpa only [hright] using (hunique s hs).1)
    have he (g : Fin n × Fin n × Fin n → ℝ) :
        (∏ s, bil F g (b s).1 (b s).2 (a s).1 (a s).2) =
          ∏ s, bil F g (a s).1 (a s).2 (b s).1 (b s).2 := by
      apply Finset.prod_congr rfl
      intro s hs
      exact bil_symm F hF g (b s) (a s)
    simpa only [he] using hz

private lemma bil_independent (F : Matrix (Fin n) (Fin n) ℝ)
    (p q r s : Fin n × Fin n)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    IndepFun (fun g => bil F g p.1 p.2 q.1 q.2)
      (fun g => bil F g r.1 r.2 s.1 s.2) (coefLaw n) := by
  classical
  let A : Finset (Fin n × Fin n × Fin n) :=
    Finset.univ.filter fun x => (x.1, x.2.1) = p ∨ (x.1, x.2.1) = q
  let B : Finset (Fin n × Fin n × Fin n) :=
    Finset.univ.filter fun x => (x.1, x.2.1) = r ∨ (x.1, x.2.1) = s
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hpr (hx.symm.trans hy)
    · exact hps (hx.symm.trans hy)
    · exact hqr (hx.symm.trans hy)
    · exact hqs (hx.symm.trans hy)
  let a : (A → ℝ) → ℝ := fun x =>
    ∑ k, ∑ l, F k l * x ⟨(p.1, p.2, k), by simp [A]⟩ *
      x ⟨(q.1, q.2, l), by simp [A]⟩
  let b : (B → ℝ) → ℝ := fun x =>
    ∑ k, ∑ l, F k l * x ⟨(r.1, r.2, k), by simp [B]⟩ *
      x ⟨(s.1, s.2, l), by simp [B]⟩
  have hi : iIndepFun (fun i (g : Fin n × Fin n × Fin n → ℝ) => g i)
      (coefLaw n) := iIndepFun_pi (fun _ => aemeasurable_id)
  have h := (hi.indepFun_finset A B hd (fun i => measurable_pi_apply i)).comp
    (show Measurable a by dsimp [a]; fun_prop)
    (show Measurable b by dsimp [b]; fun_prop)
  exact h

private lemma bil_sq_moment (F : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n × Fin n) (hpq : p ≠ q) :
    ∫ g, bil F g p.1 p.2 q.1 q.2 ^ 2 ∂coefLaw n = frobSq F := by
  simpa only [pow_two, Prod.mk.eta, ite_true, and_self] using
    bil_product_moment F p.1 p.2 q.1 q.2 p.1 p.2 q.1 q.2 hpq hpq hpq hpq

/-- The disjoint-column case of the eighth-order moment calculation. -/
private lemma bil_sq_disjoint_moment (F : Matrix (Fin n) (Fin n) ℝ)
    (p q r s : Fin n × Fin n) (hpq : p ≠ q) (hrs : r ≠ s)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    ∫ g, bil F g p.1 p.2 q.1 q.2 ^ 2 * bil F g r.1 r.2 s.1 s.2 ^ 2
      ∂coefLaw n = frobSq F ^ 2 := by
  have hi := (bil_independent F p q r s hpr hps hqr hqs).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
  change IndepFun (fun g => bil F g p.1 p.2 q.1 q.2 ^ 2)
    (fun g => bil F g r.1 r.2 s.1 s.2 ^ 2) (coefLaw n) at hi
  rw [hi.integral_fun_mul_eq_mul_integral (by unfold bil; fun_prop)
    (by unfold bil; fun_prop), bil_sq_moment F p q hpq, bil_sq_moment F r s hrs]
  ring

/-- The crossing contraction in the fourth and shared-column moments. -/
private lemma crossing_contraction (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) :
    (∑ k, ∑ l, ∑ p, ∑ q, F k l * F p q * F k q * F p l) = trF4 F := by
  classical
  have hFF : (F * F).IsSymm := by
    show (F * F).transpose = F * F
    rw [Matrix.transpose_mul, hF]
  have ht : trF4 F = ∑ k, ∑ p, (∑ l, F k l * F p l) ^ 2 := by
    simp only [trF4, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    have h := hFF.apply k p
    simp only [Matrix.mul_apply] at h
    rw [h, ← sq]
    simp_rw [hF.apply]
  rw [ht]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro q hq
  ring

private lemma coefX_measurable (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Measurable (coefX F S) := by
  unfold coefX
  split_ifs
  · unfold coefC bil
    fun_prop
  · exact measurable_const

private lemma coefX_depends_on_vertices (F : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (hS : S.card = 4)
    (g h : Fin n × Fin n × Fin n → ℝ)
    (heq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ k, g (i, j, k) = h (i, j, k)) :
    coefX F S g = coefX F S h := by
  classical
  let s := S.orderEmbOfFin hS
  have hb (a b c d : Fin 4) (hab : a ≠ b) (hcd : c ≠ d) :
      bil F g (s a) (s b) (s c) (s d) = bil F h (s a) (s b) (s c) (s d) := by
    unfold bil
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [heq _ (S.orderEmbOfFin_mem hS a) _ (S.orderEmbOfFin_mem hS b)
      (s.injective.ne hab) k,
      heq _ (S.orderEmbOfFin_mem hS c) _ (S.orderEmbOfFin_mem hS d)
      (s.injective.ne hcd) l]
  simp only [coefX, dite_eq_left hS, coefC]
  change (2 * (bil F g (s 0) (s 1) (s 2) (s 3) +
      bil F g (s 0) (s 2) (s 1) (s 3) + bil F g (s 0) (s 3) (s 1) (s 2))) ^ 2 =
    (2 * (bil F h (s 0) (s 1) (s 2) (s 3) +
      bil F h (s 0) (s 2) (s 1) (s 3) + bil F h (s 0) (s 3) (s 1) (s 2))) ^ 2
  rw [hb 0 1 2 3 (by decide) (by decide), hb 0 2 1 3 (by decide) (by decide),
    hb 0 3 1 2 (by decide) (by decide)]

private lemma functions_independent_on_disjoint
    (A B : Finset (Fin n × Fin n × Fin n))
    (f h : (Fin n × Fin n × Fin n → ℝ) → ℝ)
    (hf : Measurable f) (hh : Measurable h) (hd : Disjoint A B)
    (hA : ∀ g g', (∀ i ∈ A, g i = g' i) → f g = f g')
    (hB : ∀ g g', (∀ i ∈ B, g i = g' i) → h g = h g') :
    IndepFun f h (coefLaw n) := by
  classical
  let restore (U : Finset (Fin n × Fin n × Fin n)) (x : U → ℝ)
      (i : Fin n × Fin n × Fin n) : ℝ := if hi : i ∈ U then x ⟨i, hi⟩ else 0
  have hm (U : Finset (Fin n × Fin n × Fin n)) : Measurable (restore U) := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [restore]
    split_ifs <;> fun_prop
  have heA (g : Fin n × Fin n × Fin n → ℝ) :
      f (restore A (fun x => g x)) = f g := by
    apply hA
    intro i hi
    simp only [restore, dite_eq_left hi]
  have heB (g : Fin n × Fin n × Fin n → ℝ) :
      h (restore B (fun x => g x)) = h g := by
    apply hB
    intro i hi
    simp only [restore, dite_eq_left hi]
  have hi : iIndepFun (fun i (g : Fin n × Fin n × Fin n → ℝ) => g i)
      (coefLaw n) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hind := (hi.indepFun_finset A B hd (fun i => measurable_pi_apply i)).comp
    (hf.comp (hm A)) (hh.comp (hm B))
  change IndepFun (fun g => f (restore A (fun x => g x)))
    (fun g => h (restore B (fun x => g x))) (coefLaw n) at hind
  simpa only [heA, heB] using hind

private lemma coordinate_products_independent {R U : ℕ}
    (a : Fin R → Fin n × Fin n × Fin n) (b : Fin U → Fin n × Fin n × Fin n)
    (hab : ∀ r s, a r ≠ b s) :
    IndepFun (fun g => ∏ r, g (a r)) (fun g => ∏ s, g (b s)) (coefLaw n) := by
  classical
  let A := Finset.univ.image a
  let B := Finset.univ.image b
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hx
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hy
    exact hab r s (hr.trans hs.symm)
  apply functions_independent_on_disjoint A B _ _ (by fun_prop) (by fun_prop) hd
  · intro g g' heq
    apply Finset.prod_congr rfl
    intro r hr
    exact heq (a r) (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
  · intro g g' heq
    apply Finset.prod_congr rfl
    intro s hs
    exact heq (b s) (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩)

/-- Eight coordinates in two different columns split into two Wick factors. -/
private lemma coordinate_eight_two_columns (p q : Fin n × Fin n) (hpq : p ≠ q)
    (a b : Fin 4 → Fin n) :
    (∫ g, (∏ r, g (p.1, p.2, a r)) * (∏ r, g (q.1, q.2, b r)) ∂coefLaw n) =
      ((if a 0 = a 1 then 1 else 0) * (if a 2 = a 3 then 1 else 0) +
       (if a 0 = a 2 then 1 else 0) * (if a 1 = a 3 then 1 else 0) +
       (if a 0 = a 3 then 1 else 0) * (if a 1 = a 2 then 1 else 0)) *
      ((if b 0 = b 1 then 1 else 0) * (if b 2 = b 3 then 1 else 0) +
       (if b 0 = b 2 then 1 else 0) * (if b 1 = b 3 then 1 else 0) +
       (if b 0 = b 3 then 1 else 0) * (if b 1 = b 2 then 1 else 0)) := by
  classical
  have hi := coordinate_products_independent
    (fun r => (p.1, p.2, a r)) (fun r => (q.1, q.2, b r))
    (fun r s h => hpq (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h))
  rw [hi.integral_fun_mul_eq_mul_integral
    (show Measurable (fun g : Fin n × Fin n × Fin n → ℝ =>
      ∏ r, g (p.1, p.2, a r)) by fun_prop).aestronglyMeasurable
    (show Measurable (fun g : Fin n × Fin n × Fin n → ℝ =>
      ∏ r, g (q.1, q.2, b r)) by fun_prop).aestronglyMeasurable]
  have hprod (c : Fin n × Fin n) (v : Fin 4 → Fin n)
      (g : Fin n × Fin n × Fin n → ℝ) :
      (∏ r, g (c.1, c.2, v r)) =
        g (c.1, c.2, v 0) * g (c.1, c.2, v 1) *
        g (c.1, c.2, v 2) * g (c.1, c.2, v 3) := by
    simp [Fin.prod_univ_succ]
    ring
  simp_rw [hprod, coordinate_wick_four]
  simp only [Prod.mk.injEq, true_and]

/-- The coordinate pattern used by two squared bilinear forms with one shared column. -/
private lemma coordinate_eight_three_columns (p q s : Fin n × Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (a : Fin 4 → Fin n) (b c : Fin 2 → Fin n) :
    (∫ g, (∏ r, g (p.1, p.2, a r)) *
      ((∏ r, g (q.1, q.2, b r)) * (∏ r, g (s.1, s.2, c r))) ∂coefLaw n) =
      ((if a 0 = a 1 then 1 else 0) * (if a 2 = a 3 then 1 else 0) +
       (if a 0 = a 2 then 1 else 0) * (if a 1 = a 3 then 1 else 0) +
       (if a 0 = a 3 then 1 else 0) * (if a 1 = a 2 then 1 else 0)) *
      ((if b 0 = b 1 then 1 else 0) * (if c 0 = c 1 then 1 else 0)) := by
  classical
  let d : Fin 4 → Fin n × Fin n × Fin n := fun r => match r.val with
    | 0 => (q.1, q.2, b 0)
    | 1 => (q.1, q.2, b 1)
    | 2 => (s.1, s.2, c 0)
    | _ => (s.1, s.2, c 1)
  have hd (g : Fin n × Fin n × Fin n → ℝ) :
      (∏ r, g (d r)) = (∏ r, g (q.1, q.2, b r)) * (∏ r, g (s.1, s.2, c r)) := by
    simp [d, Fin.prod_univ_succ]
    ring
  have hi := coordinate_products_independent (fun r => (p.1, p.2, a r)) d (by
    intro r t h
    fin_cases t
    · exact hpq (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    · exact hpq (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    · exact hps (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h)
    · exact hps (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h))
  simp_rw [hd] at hi
  rw [hi.integral_fun_mul_eq_mul_integral
    (show Measurable (fun g : Fin n × Fin n × Fin n → ℝ =>
      ∏ r, g (p.1, p.2, a r)) by fun_prop).aestronglyMeasurable
    (show Measurable (fun g : Fin n × Fin n × Fin n → ℝ =>
      (∏ r, g (q.1, q.2, b r)) * (∏ r, g (s.1, s.2, c r))) by fun_prop).aestronglyMeasurable]
  have hqr := coordinate_products_independent
    (fun r => (q.1, q.2, b r)) (fun r => (s.1, s.2, c r))
    (fun r t h => hqs (congrArg (fun x : Fin n × Fin n × Fin n => (x.1, x.2.1)) h))
  rw [hqr.integral_fun_mul_eq_mul_integral
    (show Measurable (fun g : Fin n × Fin n × Fin n → ℝ =>
      ∏ r, g (q.1, q.2, b r)) by fun_prop).aestronglyMeasurable
    (show Measurable (fun g : Fin n × Fin n × Fin n → ℝ =>
      ∏ r, g (s.1, s.2, c r)) by fun_prop).aestronglyMeasurable]
  have h4 (g : Fin n × Fin n × Fin n → ℝ) :
      (∏ r, g (p.1, p.2, a r)) = g (p.1, p.2, a 0) * g (p.1, p.2, a 1) *
        g (p.1, p.2, a 2) * g (p.1, p.2, a 3) := by
    simp [Fin.prod_univ_succ]
    ring
  have h2 (u : Fin n × Fin n) (v : Fin 2 → Fin n)
      (g : Fin n × Fin n × Fin n → ℝ) :
      (∏ r, g (u.1, u.2, v r)) = g (u.1, u.2, v 0) * g (u.1, u.2, v 1) := by
    simp [Fin.prod_univ_succ]
  simp_rw [h4, h2, coordinate_wick_four, coordinate_pair_moment]
  simp only [Prod.mk.injEq, true_and]

private lemma sum_eight_interleave (f : Fin n → Fin n → Fin n → Fin n →
    Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ i, ∑ b, ∑ j, ∑ c, ∑ k, ∑ d, ∑ l, f a b c d i j k l) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, f a b c d i j k l := by
  classical
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]

private lemma integral_sum_eight
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n →
      (Fin n × Fin n × Fin n → ℝ) → ℝ)
    (hf : ∀ a b c d i j k l, Integrable (f a b c d i j k l) (coefLaw n)) :
    (∫ g, ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, f a b c d i j k l g ∂coefLaw n) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, ∫ g, f a b c d i j k l g ∂coefLaw n := by
  classical
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf a b c d i j k l))))))))]
  simp_rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf _ b c d i j k l)))))))]
  simp_rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf _ _ c d i j k l))))))]
  simp_rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf _ _ _ d i j k l)))))]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf _ _ _ _ i j k l))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf _ _ _ _ _ j k l)))]
  simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hf _ _ _ _ _ _ k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hf _ _ _ _ _ _ _ l)]

private lemma double_sum_product (f h : Fin n → Fin n → ℝ) :
    (∑ a, ∑ i, f a i) * (∑ b, ∑ j, h b j) =
      ∑ a, ∑ i, ∑ b, ∑ j, f a i * h b j := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]

private lemma four_double_sums (f₁ f₂ f₃ f₄ : Fin n → Fin n → ℝ) :
    (∑ a, ∑ i, f₁ a i) * (∑ b, ∑ j, f₂ b j) *
      (∑ c, ∑ k, f₃ c k) * (∑ d, ∑ l, f₄ d l) =
      ∑ a, ∑ i, ∑ b, ∑ j, ∑ c, ∑ k, ∑ d, ∑ l,
        f₁ a i * f₂ b j * f₃ c k * f₄ d l := by
  classical
  rw [double_sum_product f₁ f₂]
  simp only [Finset.sum_mul]
  simp_rw [mul_assoc, double_sum_product f₃ f₄]
  simp only [Finset.mul_sum, mul_assoc]

private lemma weighted_eight_integrable (A : ℝ)
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : Fin n × Fin n × Fin n) :
    Integrable (fun g => A * (g x₁ * g x₂ * g x₃ * g x₄ *
      g x₅ * g x₆ * g x₇ * g x₈)) (coefLaw n) := by
  have h := polynomial_integrable (n := n)
    (MvPolynomial.C A * (MvPolynomial.X x₁ * MvPolynomial.X x₂ *
      MvPolynomial.X x₃ * MvPolynomial.X x₄ * MvPolynomial.X x₅ *
      MvPolynomial.X x₆ * MvPolynomial.X x₇ * MvPolynomial.X x₈))
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
  exact h

private lemma four_bil_integral_expansion (F : Matrix (Fin n) (Fin n) ℝ)
    (p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : Fin n × Fin n) :
    (∫ g, bil F g p₁.1 p₁.2 q₁.1 q₁.2 * bil F g p₂.1 p₂.2 q₂.1 q₂.2 *
      bil F g p₃.1 p₃.2 q₃.1 q₃.2 * bil F g p₄.1 p₄.2 q₄.1 q₄.2 ∂coefLaw n) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
        (F a i * F b j * F c k * F d l) *
          ∫ g, g (p₁.1, p₁.2, a) * g (q₁.1, q₁.2, i) *
            g (p₂.1, p₂.2, b) * g (q₂.1, q₂.2, j) *
            g (p₃.1, p₃.2, c) * g (q₃.1, q₃.2, k) *
            g (p₄.1, p₄.2, d) * g (q₄.1, q₄.2, l) ∂coefLaw n := by
  classical
  let f := fun (a b c d i j k l : Fin n) (g : Fin n × Fin n × Fin n → ℝ) =>
    (F a i * F b j * F c k * F d l) *
      (g (p₁.1, p₁.2, a) * g (q₁.1, q₁.2, i) *
       g (p₂.1, p₂.2, b) * g (q₂.1, q₂.2, j) *
       g (p₃.1, p₃.2, c) * g (q₃.1, q₃.2, k) *
       g (p₄.1, p₄.2, d) * g (q₄.1, q₄.2, l))
  have hf (a b c d i j k l : Fin n) : Integrable (f a b c d i j k l) (coefLaw n) :=
    weighted_eight_integrable _ _ _ _ _ _ _ _ _
  have hexpand (g : Fin n × Fin n × Fin n → ℝ) :
      bil F g p₁.1 p₁.2 q₁.1 q₁.2 * bil F g p₂.1 p₂.2 q₂.1 q₂.2 *
        bil F g p₃.1 p₃.2 q₃.1 q₃.2 * bil F g p₄.1 p₄.2 q₄.1 q₄.2 =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, f a b c d i j k l g := by
    unfold bil
    rw [four_double_sums]
    rw [sum_eight_interleave]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [f]
    ring
  simp_rw [hexpand]
  rw [integral_sum_eight f hf]
  simp only [f, integral_const_mul]

private lemma square_contraction (F : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a c ^ 2 * F b d ^ 2) = frobSq F ^ 2 := by
  classical
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, frobSq, pow_two]

private lemma rectangle_contraction (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a c * F b d * F a d * F b c) = trF4 F := by
  classical
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  exact crossing_contraction F hF

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private lemma wick_matrix_sum (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
      (F a i * F b j * F c k * F d l) *
        (((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0)) *
         ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0) +
          (if i = l then 1 else 0) * (if j = k then 1 else 0)))) =
      3 * frobSq F ^ 2 + 6 * trF4 F := by
  classical
  let G : Fin n → Fin n → ℝ := fun a b => F a b
  change (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
      (G a i * G b j * G c k * G d l) *
        (((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0)) *
         ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0) +
          (if i = l then 1 else 0) * (if j = k then 1 else 0)))) =
      3 * frobSq F ^ 2 + 6 * trF4 F
  have hs : (∑ a, ∑ b, ∑ c, ∑ d, G a c ^ 2 * G b d ^ 2) = frobSq F ^ 2 := square_contraction F
  have hr : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c) = trF4 F := rectangle_contraction F hF
  simp (config := { maxSteps := 1500000 }) only [mul_add, add_mul, Finset.sum_add_distrib]
  simp (config := { maxSteps := 1500000 }) only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
    Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  have h1 (a b c d : Fin n) : G a c * G a c * G b d * G b d =
      G a c ^ 2 * G b d ^ 2 := by ring
  have h2 (a b c d : Fin n) : G a c * G b d * G a c * G b d =
      G a c ^ 2 * G b d ^ 2 := by ring
  have h3 (a b c d : Fin n) : G a c * G b d * G b d * G a c =
      G a c ^ 2 * G b d ^ 2 := by ring
  have h4 (a b c d : Fin n) : G a c * G a d * G b c * G b d =
      G a c * G b d * G a d * G b c := by ring
  have h5 (a b c d : Fin n) : G a c * G a d * G b d * G b c =
      G a c * G b d * G a d * G b c := by ring
  have h6 (a b c d : Fin n) : G a c * G b c * G a d * G b d =
      G a c * G b d * G a d * G b c := by ring
  have h7 (a b c d : Fin n) : G a c * G b c * G b d * G a d =
      G a c * G b d * G a d * G b c := by ring
  have h8 (a b c d : Fin n) : G a c * G b d * G b c * G a d =
      G a c * G b d * G a d * G b c := by ring
  have hc0 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G b c * G a d * G b d) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  have hc1 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G b c * G b d * G a d) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  have hc2 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G a d * G b c * G b d) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  have hc3 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G a d * G b d * G b c) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  simp only [h1, h2, h3, h8, hs, hr, hc0, hc1, hc2, hc3]
  ring

private lemma bil_fourth_moment (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q : Fin n × Fin n) (hpq : p ≠ q) :
    ∫ g, bil F g p.1 p.2 q.1 q.2 ^ 4 ∂coefLaw n =
      3 * frobSq F ^ 2 + 6 * trF4 F := by
  classical
  have hpow : (fun g => bil F g p.1 p.2 q.1 q.2 ^ 4) =
      (fun g => bil F g p.1 p.2 q.1 q.2 * bil F g p.1 p.2 q.1 q.2 *
        bil F g p.1 p.2 q.1 q.2 * bil F g p.1 p.2 q.1 q.2) := by
    funext g
    ring
  rw [hpow, four_bil_integral_expansion]
  have hm (a b c d i j k l : Fin n) :
      (∫ g, g (p.1, p.2, a) * g (q.1, q.2, i) *
        g (p.1, p.2, b) * g (q.1, q.2, j) *
        g (p.1, p.2, c) * g (q.1, q.2, k) *
        g (p.1, p.2, d) * g (q.1, q.2, l) ∂coefLaw n) =
        ((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0)) *
        ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0) +
          (if i = l then 1 else 0) * (if j = k then 1 else 0)) := by
    let u : Fin 4 → Fin n := fun r => match r.val with
      | 0 => a | 1 => b | 2 => c | _ => d
    let v : Fin 4 → Fin n := fun r => match r.val with
      | 0 => i | 1 => j | 2 => k | _ => l
    have he := coordinate_eight_two_columns p q hpq u v
    have hfun : (fun g : Fin n × Fin n × Fin n → ℝ =>
        g (p.1, p.2, a) * g (q.1, q.2, i) *
        g (p.1, p.2, b) * g (q.1, q.2, j) *
        g (p.1, p.2, c) * g (q.1, q.2, k) *
        g (p.1, p.2, d) * g (q.1, q.2, l)) =
        (fun g => (∏ r, g (p.1, p.2, u r)) * (∏ r, g (q.1, q.2, v r))) := by
      funext g
      simp [u, v, Fin.prod_univ_succ]
      ring
    rw [hfun]
    exact he
  simp_rw [hm]
  exact wick_matrix_sum F hF

set_option maxHeartbeats 1500000 in
private lemma shared_matrix_sum (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
      (F a i * F b j * F c k * F d l) *
        (((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0)) *
          ((if i = j then 1 else 0) * (if k = l then 1 else 0)))) =
      frobSq F ^ 2 + 2 * trF4 F := by
  classical
  let G : Fin n → Fin n → ℝ := fun a b => F a b
  change (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
      (G a i * G b j * G c k * G d l) *
        (((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0)) *
          ((if i = j then 1 else 0) * (if k = l then 1 else 0)))) =
      frobSq F ^ 2 + 2 * trF4 F
  have hs : (∑ a, ∑ b, ∑ c, ∑ d, G a c ^ 2 * G b d ^ 2) = frobSq F ^ 2 := square_contraction F
  have hr : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c) = trF4 F := rectangle_contraction F hF
  simp (config := { maxSteps := 1500000 }) only [mul_add, add_mul, Finset.sum_add_distrib]
  simp (config := { maxSteps := 1500000 }) only [mul_ite, ite_mul, mul_zero, zero_mul,
    mul_one, one_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_const_zero]
  have h1 (a b c d : Fin n) : G a c * G a c * G b d * G b d =
      G a c ^ 2 * G b d ^ 2 := by ring
  have h2 (a b c d : Fin n) : G a c * G b c * G a d * G b d =
      G a c * G b d * G a d * G b c := by ring
  have h3 (a b c d : Fin n) : G a c * G b c * G b d * G a d =
      G a c * G b d * G a d * G b c := by ring
  have hc0 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G b c * G a d * G b d) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  have hc1 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G b c * G b d * G a d) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  have hc2 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G a d * G b c * G b d) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  have hc3 : (∑ a, ∑ b, ∑ c, ∑ d, G a c * G a d * G b d * G b c) = trF4 F := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * G a d * G b c := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        apply Finset.sum_congr rfl; intro c hc
        apply Finset.sum_congr rfl; intro d hd
        ring
      _ = _ := hr
  simp only [h1, hs, hc0, hc1, hc2, hc3]
  ring

private lemma bil_sq_shared_moment (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q s : Fin n × Fin n) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) :
    ∫ g, bil F g p.1 p.2 q.1 q.2 ^ 2 * bil F g p.1 p.2 s.1 s.2 ^ 2 ∂coefLaw n =
      frobSq F ^ 2 + 2 * trF4 F := by
  classical
  have hpow : (fun g => bil F g p.1 p.2 q.1 q.2 ^ 2 * bil F g p.1 p.2 s.1 s.2 ^ 2) =
      (fun g => bil F g p.1 p.2 q.1 q.2 * bil F g p.1 p.2 q.1 q.2 *
        bil F g p.1 p.2 s.1 s.2 * bil F g p.1 p.2 s.1 s.2) := by
    funext g
    ring
  rw [hpow, four_bil_integral_expansion]
  have hm (a b c d i j k l : Fin n) :
      (∫ g, g (p.1, p.2, a) * g (q.1, q.2, i) *
        g (p.1, p.2, b) * g (q.1, q.2, j) *
        g (p.1, p.2, c) * g (s.1, s.2, k) *
        g (p.1, p.2, d) * g (s.1, s.2, l) ∂coefLaw n) =
        ((if a = b then 1 else 0) * (if c = d then 1 else 0) +
          (if a = c then 1 else 0) * (if b = d then 1 else 0) +
          (if a = d then 1 else 0) * (if b = c then 1 else 0)) *
          ((if i = j then 1 else 0) * (if k = l then 1 else 0)) := by
    let u : Fin 4 → Fin n := fun r => match r.val with
      | 0 => a | 1 => b | 2 => c | _ => d
    let v : Fin 2 → Fin n := fun r => match r.val with | 0 => i | _ => j
    let w : Fin 2 → Fin n := fun r => match r.val with | 0 => k | _ => l
    have he := coordinate_eight_three_columns p q s hpq hps hqs u v w
    have hfun : (fun g : Fin n × Fin n × Fin n → ℝ =>
        g (p.1, p.2, a) * g (q.1, q.2, i) *
        g (p.1, p.2, b) * g (q.1, q.2, j) *
        g (p.1, p.2, c) * g (s.1, s.2, k) *
        g (p.1, p.2, d) * g (s.1, s.2, l)) =
        (fun g => (∏ r, g (p.1, p.2, u r)) *
          ((∏ r, g (q.1, q.2, v r)) * (∏ r, g (s.1, s.2, w r)))) := by
      funext g
      simp [u, v, w, Fin.prod_univ_succ]
      ring
    rw [hfun]
    exact he
  simp_rw [hm]
  exact shared_matrix_sum F hF

private lemma coefX_independent_low_overlap (F : Matrix (Fin n) (Fin n) ℝ)
    (S T : Finset (Fin n)) (hS : S.card = 4) (hT : T.card = 4)
    (hST : (S ∩ T).card ≤ 1) : IndepFun (coefX F S) (coefX F T) (coefLaw n) := by
  classical
  let A : Finset (Fin n × Fin n × Fin n) :=
    Finset.univ.filter fun x => x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.1 ≠ x.2.1
  let B : Finset (Fin n × Fin n × Fin n) :=
    Finset.univ.filter fun x => x.1 ∈ T ∧ x.2.1 ∈ T ∧ x.1 ≠ x.2.1
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hx.2.2 (Finset.card_le_one.mp hST x.1
      (Finset.mem_inter.mpr ⟨hx.1, hy.1⟩) x.2.1 (Finset.mem_inter.mpr ⟨hx.2.1, hy.2.1⟩))
  apply functions_independent_on_disjoint A B (coefX F S) (coefX F T)
    (coefX_measurable F S) (coefX_measurable F T) hd
  · intro g g' heq
    apply coefX_depends_on_vertices F S hS
    intro i hi j hj hij k
    apply heq
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, hj, hij⟩
  · intro g g' heq
    apply coefX_depends_on_vertices F T hT
    intro i hi j hj hij k
    apply heq
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, hj, hij⟩

private lemma coefX_product_low_overlap (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (S T : Finset (Fin n)) (hS : S.card = 4) (hT : T.card = 4)
    (hST : (S ∩ T).card ≤ 1) :
    ∫ g, coefX F S g * coefX F T g ∂coefLaw n = (12 * frobSq F) ^ 2 := by
  rw [(coefX_independent_low_overlap F S T hS hT hST).integral_fun_mul_eq_mul_integral
    (coefX_measurable F S).aestronglyMeasurable (coefX_measurable F T).aestronglyMeasurable,
    coefX_mean F hF S hS, coefX_mean F hF T hT, pow_two]

private lemma common_pair_subsets (S T : Finset (Fin n)) :
    S.powersetCard 2 ∩ T.powersetCard 2 = (S ∩ T).powersetCard 2 := by
  classical
  ext U
  simp only [Finset.mem_inter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hUS, hU⟩, ⟨hUT, _⟩⟩
    exact ⟨Finset.subset_inter hUS hUT, hU⟩
  · rintro ⟨hU, hcard⟩
    exact ⟨⟨hU.trans Finset.inter_subset_left, hcard⟩,
      ⟨hU.trans Finset.inter_subset_right, hcard⟩⟩

private lemma common_pair_subsets_card (S T : Finset (Fin n)) :
    (S.powersetCard 2 ∩ T.powersetCard 2).card = (S ∩ T).card.choose 2 := by
  rw [common_pair_subsets, Finset.card_powersetCard]

private lemma overlap_four_eq (S T : Finset (Fin n)) (hS : S.card = 4)
    (hT : T.card = 4) (hST : (S ∩ T).card = 4) : S = T := by
  have h := Finset.eq_of_subset_of_card_le
    (Finset.inter_subset_left (s₁ := S) (s₂ := T)) (by omega)
  apply Finset.eq_of_subset_of_card_le
  · rw [← h]
    exact Finset.inter_subset_right
  · omega


private lemma three_sum_sq_mul_sq (B D : Fin 3 → ℝ) :
    (∑ i, B i) ^ 2 * (∑ j, D j) ^ 2 =
      ∑ i, ∑ i', ∑ j, ∑ j', B i * B i' * D j * D j' := by
  simp only [Fin.sum_univ_succ]
  ring

private lemma four_bil_integrable (F : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin 4 → Fin n × Fin n) :
    Integrable (fun g => ∏ i, bil F g (p i).1 (p i).2 (q i).1 (q i).2)
      (coefLaw n) := by
  classical
  choose f hf using fun i => bil_polynomial F (p i).1 (p i).2 (q i).1 (q i).2
  have h := polynomial_integrable (n := n) (∏ i, f i)
  simpa only [map_prod, ← hf] using h

private lemma three_bil_singleton (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q : Fin 3 → Fin n × Fin n) (hp : Function.Injective p)
    (hpq : ∀ i j, p i ≠ q j) (a : Fin 4 → Fin 3) (r : Fin 4)
    (hr : ∀ s, s ≠ r → a s ≠ a r) :
    ∫ g, ∏ s, bil F g (p (a s)).1 (p (a s)).2 (q (a s)).1 (q (a s)).2
      ∂coefLaw n = 0 := by
  apply bil_product_column_once_zero F hF (fun s => p (a s)) (fun s => q (a s))
    r (p (a r)) (Or.inl rfl) (hpq _ _)
  intro s hs
  exact ⟨fun he => hr s hs (hp he), fun he => hpq _ _ he.symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private lemma three_bil_fourth (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q : Fin 3 → Fin n × Fin n) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) :
    ∫ g, (2 * (∑ i, bil F g (p i).1 (p i).2 (q i).1 (q i).2)) ^ 4
      ∂coefLaw n = 432 * frobSq F ^ 2 + 288 * trF4 F := by
  classical
  let B := fun i g => bil F g (p i).1 (p i).2 (q i).1 (q i).2
  have hm (i j k l : Fin 3) :
      (∫ g, B i g * B j g * B k g * B l g ∂coefLaw n) =
        if i = j ∧ j = k ∧ k = l then 3 * frobSq F ^ 2 + 6 * trF4 F
        else if (i = j ∧ k = l) ∨ (i = k ∧ j = l) ∨ (i = l ∧ j = k)
          then frobSq F ^ 2 else 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    · change (∫ g, B 0 g * B 0 g * B 0 g * B 0 g ∂coefLaw n) = 3 * frobSq F ^ 2 + 6 * trF4 F
      have he : (fun g => B 0 g * B 0 g * B 0 g * B 0 g) = (fun g => B 0 g ^ 4) := by
        funext g; ring
      rw [he]
      exact bil_fourth_moment F hF (p 0) (q 0) (hpq _ _)
    · change (∫ g, B 0 g * B 0 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 0 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 3 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 0 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 0 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 0 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 3 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 0 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 0 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 0 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 0 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 0 g * B 1 g * B 1 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 0 g * B 0 g * B 1 g * B 1 g) = (fun g => B 0 g ^ 2 * B 1 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 1) (q 1)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 0 g * B 0 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 0 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 0 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 0 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 0 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 0 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 0 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 0 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 0 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 0 g * B 2 g * B 2 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 0 g * B 0 g * B 2 g * B 2 g) = (fun g => B 0 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 0 g * B 1 g * B 0 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 0 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 0 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 1 g * B 0 g * B 1 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 0 g * B 1 g * B 0 g * B 1 g) = (fun g => B 0 g ^ 2 * B 1 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 1) (q 1)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 0 g * B 1 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 1 g * B 1 g * B 0 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 0 g * B 1 g * B 1 g * B 0 g) = (fun g => B 0 g ^ 2 * B 1 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 1) (q 1)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 0 g * B 1 g * B 1 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 1 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 1 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 1 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 1 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 1 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 1 g * B 2 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 1 | 2 => 2 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 1 g * B 2 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 0 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 0 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 0 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 0 g * B 2 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 0 g * B 2 g * B 0 g * B 2 g) = (fun g => B 0 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 0 g * B 2 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 1 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 1 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 1 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 2 g * B 0 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 0 g * B 2 g * B 2 g * B 0 g) = (fun g => B 0 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 0 g * B 2 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 0 g * B 2 g * B 2 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 0 | 1 => 2 | 2 => 2 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 0 g * B 2 g * B 2 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 0 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 0 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 0 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 0 g * B 1 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 1 g * B 0 g * B 0 g * B 1 g) = (fun g => B 0 g ^ 2 * B 1 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 1) (q 1)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 1 g * B 0 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 1 g * B 0 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 1 g * B 0 g * B 1 g * B 0 g) = (fun g => B 0 g ^ 2 * B 1 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 1) (q 1)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 1 g * B 0 g * B 1 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 1 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 1 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 0 g * B 2 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 0 | 2 => 2 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 0 g * B 2 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 0 g * B 0 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 1 g * B 1 g * B 0 g * B 0 g) = (fun g => B 0 g ^ 2 * B 1 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 1) (q 1)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 1 g * B 1 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 1 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 1 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 1 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 1 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 1 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 3 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 1 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 1 g * B 1 g ∂coefLaw n) = 3 * frobSq F ^ 2 + 6 * trF4 F
      have he : (fun g => B 1 g * B 1 g * B 1 g * B 1 g) = (fun g => B 1 g ^ 4) := by
        funext g; ring
      rw [he]
      exact bil_fourth_moment F hF (p 1) (q 1) (hpq _ _)
    · change (∫ g, B 1 g * B 1 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 1 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 3 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 1 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 1 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 1 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 1 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 1 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 1 g * B 2 g * B 2 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 1 g * B 1 g * B 2 g * B 2 g) = (fun g => B 1 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 1) (q 1) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 1 g * B 2 g * B 0 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 0 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 0 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 2 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 2 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 2 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 2 g * B 1 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 1 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 1 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 2 g * B 1 g * B 2 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 1 g * B 2 g * B 1 g * B 2 g) = (fun g => B 1 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 1) (q 1) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 1 g * B 2 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 1 g * B 2 g * B 2 g * B 1 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 1 g * B 2 g * B 2 g * B 1 g) = (fun g => B 1 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 1) (q 1) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 1 g * B 2 g * B 2 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 1 | 1 => 2 | 2 => 2 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 1 g * B 2 g * B 2 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 0 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 0 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 0 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 0 g * B 2 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 2 g * B 0 g * B 0 g * B 2 g) = (fun g => B 0 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 2 g * B 0 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 1 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 1 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 1 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 2 g * B 0 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 2 g * B 0 g * B 2 g * B 0 g) = (fun g => B 0 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 2 g * B 0 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 0 g * B 2 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 0 | 2 => 2 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 0 g * B 2 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 0 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 0 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 1 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 1 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 0 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 1 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 1 g * B 2 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 2 g * B 1 g * B 1 g * B 2 g) = (fun g => B 1 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 1) (q 1) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 2 g * B 1 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 1 g * B 2 g * B 1 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 2 g * B 1 g * B 2 g * B 1 g) = (fun g => B 1 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 1) (q 1) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 2 g * B 1 g * B 2 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 1 | 2 => 2 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 1 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 1 g * B 2 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 0 g * B 0 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 2 g * B 2 g * B 0 g * B 0 g) = (fun g => B 0 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 0) (q 0) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 2 g * B 2 g * B 0 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 2 | 2 => 0 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 2 g * B 0 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 0 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 2 | 2 => 0 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 2 g * B 0 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 1 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 2 | 2 => 1 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 2 g * B 1 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 1 g * B 1 g ∂coefLaw n) = frobSq F ^ 2
      have he : (fun g => B 2 g * B 2 g * B 1 g * B 1 g) = (fun g => B 1 g ^ 2 * B 2 g ^ 2) := by
        funext g; ring
      rw [he]
      exact bil_sq_disjoint_moment F (p 1) (q 1) (p 2) (q 2)
        (hpq _ _) (hpq _ _) (hp.ne (by decide)) (hpq _ _) (Ne.symm (hpq _ _))
        (hq.ne (by decide))
    · change (∫ g, B 2 g * B 2 g * B 1 g * B 2 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 2 | 2 => 1 | _ => 2
      have hz := three_bil_singleton F hF p q hp hpq a 2 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 2 g * B 1 g * B 2 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 2 g * B 0 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 2 | 2 => 2 | _ => 0
      have hz := three_bil_singleton F hF p q hp hpq a 3 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 2 g * B 2 g * B 0 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 2 g * B 1 g ∂coefLaw n) = 0
      let a : Fin 4 → Fin 3 := fun s => match s.val with
        | 0 => 2 | 1 => 2 | 2 => 2 | _ => 1
      have hz := three_bil_singleton F hF p q hp hpq a 3 (by
        intro s hs; fin_cases s <;> norm_num [a] at *)
      have he : (fun g => B 2 g * B 2 g * B 2 g * B 1 g) =
          (fun g => ∏ s, B (a s) g) := by
        funext g; simp [a, Fin.prod_univ_succ]; ring
      rw [he]
      exact hz
    · change (∫ g, B 2 g * B 2 g * B 2 g * B 2 g ∂coefLaw n) = 3 * frobSq F ^ 2 + 6 * trF4 F
      have he : (fun g => B 2 g * B 2 g * B 2 g * B 2 g) = (fun g => B 2 g ^ 4) := by
        funext g; ring
      rw [he]
      exact bil_fourth_moment F hF (p 2) (q 2) (hpq _ _)

  have hi (i j k l : Fin 3) : Integrable (fun g => B i g * B j g * B k g * B l g)
      (coefLaw n) := by
    let a : Fin 4 → Fin 3 := fun s => match s.val with
      | 0 => i | 1 => j | 2 => k | _ => l
    have h := four_bil_integrable F (fun s => p (a s)) (fun s => q (a s))
    have he : (fun g => B i g * B j g * B k g * B l g) =
        (fun g => ∏ s, bil F g (p (a s)).1 (p (a s)).2 (q (a s)).1 (q (a s)).2) := by
      funext g; simp [a, Fin.prod_univ_succ, B]; ring
    rw [he]
    exact h
  have he : (fun g => (2 * ∑ i, B i g) ^ 4) =
      (fun g => 16 * ∑ i, ∑ j, ∑ k, ∑ l, B i g * B j g * B k g * B l g) := by
    funext g
    simp only [Fin.sum_univ_succ]
    ring
  change (∫ g, (2 * ∑ i, B i g) ^ 4 ∂coefLaw n) = _
  rw [he, integral_const_mul, integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
        integrable_finsetSum _ (fun l _ => hi _ j k l)))]
    simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi _ _ k l))]
    simp_rw [integral_finsetSum _ (fun l _ => hi _ _ _ l), hm]
    norm_num [Fin.sum_univ_succ]
    <;> ring
  · intro i _
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun l _ => hi i j k l)))

private lemma coefC_fourth_moment (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (S : Finset (Fin n)) (hS : S.card = 4) :
    ∫ g, coefC F S hS g ^ 4 ∂coefLaw n = 432 * frobSq F ^ 2 + 288 * trF4 F := by
  classical
  let s := S.orderEmbOfFin hS
  let p : Fin 3 → Fin n × Fin n := fun i => match i.val with
    | 0 => (s 0, s 1) | 1 => (s 0, s 2) | _ => (s 0, s 3)
  let q : Fin 3 → Fin n × Fin n := fun i => match i.val with
    | 0 => (s 2, s 3) | 1 => (s 1, s 3) | _ => (s 1, s 2)
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p, s.injective.eq_iff] at *
  have hq : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [q, s.injective.eq_iff] at *
  have hpq : ∀ i j, p i ≠ q j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [p, q, s.injective.eq_iff]
  have h := three_bil_fourth F hF p q hp hq hpq
  simpa [coefC, p, q, Fin.sum_univ_succ, add_assoc] using h

private lemma cross_bil_singleton (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q u w : Fin 3 → Fin n × Fin n) (hp : Function.Injective p)
    (hpq : ∀ i j, p i ≠ q j) (i i' j j' : Fin 3) (hii : i ≠ i')
    (hpu : ∀ k, p i ≠ u k) (hpw : ∀ k, p i ≠ w k) :
    ∫ g, bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
      bil F g (p i').1 (p i').2 (q i').1 (q i').2 *
      bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
      bil F g (u j').1 (u j').2 (w j').1 (w j').2 ∂coefLaw n = 0 := by
  classical
  let a : Fin 4 → Fin n × Fin n := fun s => match s.val with
    | 0 => p i | 1 => p i' | 2 => u j | _ => u j'
  let b : Fin 4 → Fin n × Fin n := fun s => match s.val with
    | 0 => q i | 1 => q i' | 2 => w j | _ => w j'
  have hz := bil_product_column_once_zero F hF a b 0 (p i)
    (Or.inl rfl) (hpq i i) (by
      intro s hs
      fin_cases s
      · exact (hs rfl).elim
      · exact ⟨hp.ne hii.symm, Ne.symm (hpq _ _)⟩
      · exact ⟨Ne.symm (hpu _), Ne.symm (hpw _)⟩
      · exact ⟨Ne.symm (hpu _), Ne.symm (hpw _)⟩)
  have he : (fun g => bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
      bil F g (p i').1 (p i').2 (q i').1 (q i').2 *
      bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
      bil F g (u j').1 (u j').2 (w j').1 (w j').2) =
      (fun g => ∏ s, bil F g (a s).1 (a s).2 (b s).1 (b s).2) := by
    funext g
    simp [a, b, Fin.prod_univ_succ]
    ring
  rw [he]
  exact hz

private lemma cross_bil_first_offdiag (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q u w : Fin 3 → Fin n × Fin n) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j)
    (i i' j j' : Fin 3) (hii : i ≠ i')
    (hout : (∀ k, p i ≠ u k ∧ p i ≠ w k) ∨
      (∀ k, q i ≠ u k ∧ q i ≠ w k)) :
    ∫ g, bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
      bil F g (p i').1 (p i').2 (q i').1 (q i').2 *
      bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
      bil F g (u j').1 (u j').2 (w j').1 (w j').2 ∂coefLaw n = 0 := by
  rcases hout with hout | hout
  · exact cross_bil_singleton F hF p q u w hp hpq i i' j j' hii
      (fun k => (hout k).1) (fun k => (hout k).2)
  · have hz := cross_bil_singleton F hF q p u w hq
      (fun i j => Ne.symm (hpq j i)) i i' j j' hii
      (fun k => (hout k).1) (fun k => (hout k).2)
    simp_rw [bil_symm F hF _ (q i) (p i), bil_symm F hF _ (q i') (p i')] at hz
    exact hz

private lemma cross_bil_offdiag_zero (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q u w : Fin 3 → Fin n × Fin n) (hp : Function.Injective p)
    (hq : Function.Injective q) (hu : Function.Injective u) (hw : Function.Injective w)
    (hpq : ∀ i j, p i ≠ q j) (huw : ∀ i j, u i ≠ w j)
    (hB : ∀ i, (∀ k, p i ≠ u k ∧ p i ≠ w k) ∨ (∀ k, q i ≠ u k ∧ q i ≠ w k))
    (hD : ∀ j, (∀ k, u j ≠ p k ∧ u j ≠ q k) ∨ (∀ k, w j ≠ p k ∧ w j ≠ q k))
    (i i' j j' : Fin 3) (hne : i ≠ i' ∨ j ≠ j') :
    ∫ g, bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
      bil F g (p i').1 (p i').2 (q i').1 (q i').2 *
      bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
      bil F g (u j').1 (u j').2 (w j').1 (w j').2 ∂coefLaw n = 0 := by
  rcases hne with hii | hjj
  · exact cross_bil_first_offdiag F hF p q u w hp hq hpq i i' j j' hii (hB i)
  · have hz := cross_bil_first_offdiag F hF u w p q hu hw huw j j' i i' hjj (hD j)
    have he : (fun g => bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
        bil F g (p i').1 (p i').2 (q i').1 (q i').2 *
        bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
        bil F g (u j').1 (u j').2 (w j').1 (w j').2) =
        (fun g => bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
        bil F g (u j').1 (u j').2 (w j').1 (w j').2 *
        bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
        bil F g (p i').1 (p i').2 (q i').1 (q i').2) := by
      funext g
      ring
    rw [he]
    exact hz

private lemma four_bil_fun_integrable (F : Matrix (Fin n) (Fin n) ℝ)
    (p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : Fin n × Fin n) :
    Integrable (fun g => bil F g p₁.1 p₁.2 q₁.1 q₁.2 *
      bil F g p₂.1 p₂.2 q₂.1 q₂.2 * bil F g p₃.1 p₃.2 q₃.1 q₃.2 *
      bil F g p₄.1 p₄.2 q₄.1 q₄.2) (coefLaw n) := by
  let a : Fin 4 → Fin n × Fin n := fun s => match s.val with
    | 0 => p₁ | 1 => p₂ | 2 => p₃ | _ => p₄
  let b : Fin 4 → Fin n × Fin n := fun s => match s.val with
    | 0 => q₁ | 1 => q₂ | 2 => q₃ | _ => q₄
  have h := four_bil_integrable F a b
  have he : (fun g => bil F g p₁.1 p₁.2 q₁.1 q₁.2 *
      bil F g p₂.1 p₂.2 q₂.1 q₂.2 * bil F g p₃.1 p₃.2 q₃.1 q₃.2 *
      bil F g p₄.1 p₄.2 q₄.1 q₄.2) =
      (fun g => ∏ s, bil F g (a s).1 (a s).2 (b s).1 (b s).2) := by
    funext g
    simp [a, b, Fin.prod_univ_succ]
    ring
  rw [he]
  exact h

private lemma cross_bil_diagonal_reduction (F : Matrix (Fin n) (Fin n) ℝ)
    (p q u w : Fin 3 → Fin n × Fin n)
    (hz : ∀ i i' j j', i ≠ i' ∨ j ≠ j' →
      ∫ g, bil F g (p i).1 (p i).2 (q i).1 (q i).2 *
        bil F g (p i').1 (p i').2 (q i').1 (q i').2 *
        bil F g (u j).1 (u j).2 (w j).1 (w j).2 *
        bil F g (u j').1 (u j').2 (w j').1 (w j').2 ∂coefLaw n = 0) :
    (∫ g, (2 * ∑ i, bil F g (p i).1 (p i).2 (q i).1 (q i).2) ^ 2 *
      (2 * ∑ j, bil F g (u j).1 (u j).2 (w j).1 (w j).2) ^ 2 ∂coefLaw n) =
      16 * ∑ i, ∑ j, ∫ g, bil F g (p i).1 (p i).2 (q i).1 (q i).2 ^ 2 *
        bil F g (u j).1 (u j).2 (w j).1 (w j).2 ^ 2 ∂coefLaw n := by
  classical
  let B := fun i g => bil F g (p i).1 (p i).2 (q i).1 (q i).2
  let D := fun j g => bil F g (u j).1 (u j).2 (w j).1 (w j).2
  have hi (i i' j j' : Fin 3) : Integrable
      (fun g => B i g * B i' g * D j g * D j' g) (coefLaw n) :=
    four_bil_fun_integrable F _ _ _ _ _ _ _ _
  have he : (fun g => (2 * ∑ i, B i g) ^ 2 * (2 * ∑ j, D j g) ^ 2) =
      (fun g => 16 * ∑ i, ∑ i', ∑ j, ∑ j', B i g * B i' g * D j g * D j' g) := by
    funext g
    rw [← three_sum_sq_mul_sq]
    ring
  change (∫ g, (2 * ∑ i, B i g) ^ 2 * (2 * ∑ j, D j g) ^ 2 ∂coefLaw n) = _
  rw [he, integral_const_mul, integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun i' _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun j' _ => hi _ i' j j')))]
    simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun j' _ => hi _ _ j j'))]
    simp_rw [integral_finsetSum _ (fun j' _ => hi _ _ _ j')]
    have hm (i i' j j' : Fin 3) :
        (∫ g, B i g * B i' g * D j g * D j' g ∂coefLaw n) =
          if i = i' then if j = j' then
            ∫ g, B i g ^ 2 * D j g ^ 2 ∂coefLaw n else 0 else 0 := by
      by_cases hii : i = i'
      · subst i'
        by_cases hjj : j = j'
        · subst j'
          simp only [ite_true]
          congr 1
          funext g
          ring
        · simp only [ite_true, hjj, ite_false]
          exact hz _ _ _ _ (Or.inr hjj)
      · simp only [hii, ite_false]
        exact hz _ _ _ _ (Or.inl hii)
    simp_rw [hm]
    simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const_zero]
    rfl
  · intro i _
    exact integrable_finsetSum _ (fun i' _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun j' _ => hi i i' j j')))

private lemma bil_sq_one_common_moment (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q u w : Fin n × Fin n) (hpq : p ≠ q) (huw : u ≠ w)
    (hshare : p = u ∨ p = w ∨ q = u ∨ q = w)
    (hno : ¬ ((p = u ∨ p = w) ∧ (q = u ∨ q = w))) :
    ∫ g, bil F g p.1 p.2 q.1 q.2 ^ 2 * bil F g u.1 u.2 w.1 w.2 ^ 2
      ∂coefLaw n = frobSq F ^ 2 + 2 * trF4 F := by
  rcases hshare with hpu | hpw | hqu | hqw
  · subst u
    exact bil_sq_shared_moment F hF p q w hpq huw
      (fun h => hno ⟨Or.inl rfl, Or.inr h⟩)
  · subst w
    simp_rw [bil_symm F hF _ u p]
    exact bil_sq_shared_moment F hF p q u hpq huw.symm
      (fun h => hno ⟨Or.inr rfl, Or.inl h⟩)
  · subst u
    simp_rw [bil_symm F hF _ p q]
    exact bil_sq_shared_moment F hF q p w hpq.symm huw
      (fun h => hno ⟨Or.inr h, Or.inl rfl⟩)
  · subst w
    simp_rw [bil_symm F hF _ p q, bil_symm F hF _ u q]
    exact bil_sq_shared_moment F hF q p u hpq.symm huw.symm
      (fun h => hno ⟨Or.inl h, Or.inr rfl⟩)

private lemma bil_sq_at_most_one_common_moment (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (p q u w : Fin n × Fin n) (hpq : p ≠ q) (huw : u ≠ w)
    (hno : ¬ ((p = u ∨ p = w) ∧ (q = u ∨ q = w))) :
    (∫ g, bil F g p.1 p.2 q.1 q.2 ^ 2 * bil F g u.1 u.2 w.1 w.2 ^ 2
      ∂coefLaw n) = frobSq F ^ 2 +
        if p = u ∨ p = w ∨ q = u ∨ q = w then 2 * trF4 F else 0 := by
  classical
  by_cases hs : p = u ∨ p = w ∨ q = u ∨ q = w
  · simp only [hs, ite_true]
    exact bil_sq_one_common_moment F hF p q u w hpq huw hs hno
  · simp only [hs, ite_false, add_zero]
    exact bil_sq_disjoint_moment F p q u w hpq huw
      (fun h => hs (Or.inl h)) (fun h => hs (Or.inr (Or.inl h)))
      (fun h => hs (Or.inr (Or.inr (Or.inl h))))
      (fun h => hs (Or.inr (Or.inr (Or.inr h))))

private lemma cross_bil_product_moment (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (p q u w : Fin 3 → Fin n × Fin n) (hp : Function.Injective p)
    (hq : Function.Injective q) (hu : Function.Injective u) (hw : Function.Injective w)
    (hpq : ∀ i j, p i ≠ q j) (huw : ∀ i j, u i ≠ w j)
    (hB : ∀ i, (∀ k, p i ≠ u k ∧ p i ≠ w k) ∨ (∀ k, q i ≠ u k ∧ q i ≠ w k))
    (hD : ∀ j, (∀ k, u j ≠ p k ∧ u j ≠ q k) ∨ (∀ k, w j ≠ p k ∧ w j ≠ q k)) :
    (∫ g, (2 * ∑ i, bil F g (p i).1 (p i).2 (q i).1 (q i).2) ^ 2 *
      (2 * ∑ j, bil F g (u j).1 (u j).2 (w j).1 (w j).2) ^ 2 ∂coefLaw n) =
      144 * frobSq F ^ 2 + 32 * trF4 F *
        ∑ i, ∑ j, (if p i = u j ∨ p i = w j ∨ q i = u j ∨ q i = w j
          then (1 : ℝ) else 0) := by
  classical
  rw [cross_bil_diagonal_reduction F p q u w
    (cross_bil_offdiag_zero F hF p q u w hp hq hu hw hpq huw hB hD)]
  have hno (i j : Fin 3) : ¬ ((p i = u j ∨ p i = w j) ∧ (q i = u j ∨ q i = w j)) := by
    rintro ⟨h1, h2⟩
    rcases hB i with h | h
    · rcases h1 with h1 | h1
      · exact (h j).1 h1
      · exact (h j).2 h1
    · rcases h2 with h2 | h2
      · exact (h j).1 h2
      · exact (h j).2 h2
  simp_rw [bil_sq_at_most_one_common_moment F hF _ _ _ _ (hpq _ _) (huw _ _) (hno _ _)]
  have he (i j : Fin 3) :
      (if p i = u j ∨ p i = w j ∨ q i = u j ∨ q i = w j then 2 * trF4 F else 0) =
        (2 * trF4 F) * (if p i = u j ∨ p i = w j ∨ q i = u j ∨ q i = w j
          then (1 : ℝ) else 0) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
private lemma sorted_matching_incidence
    (s t : Fin 4 ↪o Fin n) (m : ℕ) (hm : m = 2 ∨ m = 3)
    (hcard :
      (if s 0 = t 0 ∨ s 0 = t 1 ∨ s 0 = t 2 ∨ s 0 = t 3 then 1 else 0) +
      (if s 1 = t 0 ∨ s 1 = t 1 ∨ s 1 = t 2 ∨ s 1 = t 3 then 1 else 0) +
      (if s 2 = t 0 ∨ s 2 = t 1 ∨ s 2 = t 2 ∨ s 2 = t 3 then 1 else 0) +
      (if s 3 = t 0 ∨ s 3 = t 1 ∨ s 3 = t 2 ∨ s 3 = t 3 then 1 else 0) = m) :
    let p : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (s 0, s 1) | 1 => (s 0, s 2) | _ => (s 0, s 3)
    let q : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (s 2, s 3) | 1 => (s 1, s 3) | _ => (s 1, s 2)
    let u : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (t 0, t 1) | 1 => (t 0, t 2) | _ => (t 0, t 3)
    let w : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (t 2, t 3) | 1 => (t 1, t 3) | _ => (t 1, t 2)
    (∑ i, ∑ j, (if p i = u j ∨ p i = w j ∨ q i = u j ∨ q i = w j
      then (1 : ℕ) else 0)) = if m = 2 then 1 else 3 := by
  classical
  have hite : (if m = 2 then (1 : ℕ) else 3) + 3 = 2 * m := by
    rcases hm with rfl | rfl <;> decide
  have hs01 := s.strictMono (show (0 : Fin 4) < 1 by decide)
  have hs12 := s.strictMono (show (1 : Fin 4) < 2 by decide)
  have hs23 := s.strictMono (show (2 : Fin 4) < 3 by decide)
  have ht01 := t.strictMono (show (0 : Fin 4) < 1 by decide)
  have ht12 := t.strictMono (show (1 : Fin 4) < 2 by decide)
  have ht23 := t.strictMono (show (2 : Fin 4) < 3 by decide)
  dsimp only
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((if (s 0, s 1) = (t 0, t 1) ∨ (s 0, s 1) = (t 2, t 3) ∨ (s 2, s 3) = (t 0, t 1) ∨ (s 2, s 3) = (t 2, t 3) then (1 : ℕ) else 0) + ((if (s 0, s 1) = (t 0, t 2) ∨ (s 0, s 1) = (t 1, t 3) ∨ (s 2, s 3) = (t 0, t 2) ∨ (s 2, s 3) = (t 1, t 3) then (1 : ℕ) else 0) + (if (s 0, s 1) = (t 0, t 3) ∨ (s 0, s 1) = (t 1, t 2) ∨ (s 2, s 3) = (t 0, t 3) ∨ (s 2, s 3) = (t 1, t 2) then (1 : ℕ) else 0))) + (((if (s 0, s 2) = (t 0, t 1) ∨ (s 0, s 2) = (t 2, t 3) ∨ (s 1, s 3) = (t 0, t 1) ∨ (s 1, s 3) = (t 2, t 3) then (1 : ℕ) else 0) + ((if (s 0, s 2) = (t 0, t 2) ∨ (s 0, s 2) = (t 1, t 3) ∨ (s 1, s 3) = (t 0, t 2) ∨ (s 1, s 3) = (t 1, t 3) then (1 : ℕ) else 0) + (if (s 0, s 2) = (t 0, t 3) ∨ (s 0, s 2) = (t 1, t 2) ∨ (s 1, s 3) = (t 0, t 3) ∨ (s 1, s 3) = (t 1, t 2) then (1 : ℕ) else 0))) + ((if (s 0, s 3) = (t 0, t 1) ∨ (s 0, s 3) = (t 2, t 3) ∨ (s 1, s 2) = (t 0, t 1) ∨ (s 1, s 2) = (t 2, t 3) then (1 : ℕ) else 0) + ((if (s 0, s 3) = (t 0, t 2) ∨ (s 0, s 3) = (t 1, t 3) ∨ (s 1, s 2) = (t 0, t 2) ∨ (s 1, s 2) = (t 1, t 3) then (1 : ℕ) else 0) + (if (s 0, s 3) = (t 0, t 3) ∨ (s 0, s 3) = (t 1, t 2) ∨ (s 1, s 2) = (t 0, t 3) ∨ (s 1, s 2) = (t 1, t 2) then (1 : ℕ) else 0)))) = if m = 2 then 1 else 3
  simp only [Prod.mk.injEq]
  all_goals by_cases h00 : s 0 = t 0
  all_goals simp_all only [h00, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals by_cases h01 : s 0 = t 1
  all_goals simp_all only [h01, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h02 : s 0 = t 2
  all_goals simp_all only [h02, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h03 : s 0 = t 3
  all_goals simp_all only [h03, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h10 : s 1 = t 0
  all_goals simp_all only [h10, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h11 : s 1 = t 1
  all_goals simp_all only [h11, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h12 : s 1 = t 2
  all_goals simp_all only [h12, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h13 : s 1 = t 3
  all_goals simp_all only [h13, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h20 : s 2 = t 0
  all_goals simp_all only [h20, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h21 : s 2 = t 1
  all_goals simp_all only [h21, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h22 : s 2 = t 2
  all_goals simp_all only [h22, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h23 : s 2 = t 3
  all_goals simp_all only [h23, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h30 : s 3 = t 0
  all_goals simp_all only [h30, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h31 : s 3 = t 1
  all_goals simp_all only [h31, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h32 : s 3 = t 2
  all_goals simp_all only [h32, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega
  all_goals by_cases h33 : s 3 = t 3
  all_goals simp_all only [h33, ite_true, ite_false, and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals try omega

set_option maxHeartbeats 2000000 in
private lemma sorted_matching_outside
    (s t : Fin 4 ↪o Fin n)
    (hcard :
      (if s 0 = t 0 ∨ s 0 = t 1 ∨ s 0 = t 2 ∨ s 0 = t 3 then (1 : ℕ) else 0) +
      (if s 1 = t 0 ∨ s 1 = t 1 ∨ s 1 = t 2 ∨ s 1 = t 3 then 1 else 0) +
      (if s 2 = t 0 ∨ s 2 = t 1 ∨ s 2 = t 2 ∨ s 2 = t 3 then 1 else 0) +
      (if s 3 = t 0 ∨ s 3 = t 1 ∨ s 3 = t 2 ∨ s 3 = t 3 then 1 else 0) < 4) :
    let p : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (s 0, s 1) | 1 => (s 0, s 2) | _ => (s 0, s 3)
    let q : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (s 2, s 3) | 1 => (s 1, s 3) | _ => (s 1, s 2)
    let u : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (t 0, t 1) | 1 => (t 0, t 2) | _ => (t 0, t 3)
    let w : Fin 3 → Fin n × Fin n := fun i => match i.val with
      | 0 => (t 2, t 3) | 1 => (t 1, t 3) | _ => (t 1, t 2)
    ∀ i, (∀ k, p i ≠ u k ∧ p i ≠ w k) ∨ (∀ k, q i ≠ u k ∧ q i ≠ w k) := by
  classical
  dsimp only
  intro i
  fin_cases i
  · simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    change (((s 0, s 1) ≠ (t 0, t 1) ∧ (s 0, s 1) ≠ (t 2, t 3)) ∧ (((s 0, s 1) ≠ (t 0, t 2) ∧ (s 0, s 1) ≠ (t 1, t 3)) ∧ ((s 0, s 1) ≠ (t 0, t 3) ∧ (s 0, s 1) ≠ (t 1, t 2)))) ∨ (((s 2, s 3) ≠ (t 0, t 1) ∧ (s 2, s 3) ≠ (t 2, t 3)) ∧ (((s 2, s 3) ≠ (t 0, t 2) ∧ (s 2, s 3) ≠ (t 1, t 3)) ∧ ((s 2, s 3) ≠ (t 0, t 3) ∧ (s 2, s 3) ≠ (t 1, t 2))))
    simp only [ne_eq, Prod.mk.injEq]
    split_ifs at hcard <;> simp_all
  · simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    change (((s 0, s 2) ≠ (t 0, t 1) ∧ (s 0, s 2) ≠ (t 2, t 3)) ∧ (((s 0, s 2) ≠ (t 0, t 2) ∧ (s 0, s 2) ≠ (t 1, t 3)) ∧ ((s 0, s 2) ≠ (t 0, t 3) ∧ (s 0, s 2) ≠ (t 1, t 2)))) ∨ (((s 1, s 3) ≠ (t 0, t 1) ∧ (s 1, s 3) ≠ (t 2, t 3)) ∧ (((s 1, s 3) ≠ (t 0, t 2) ∧ (s 1, s 3) ≠ (t 1, t 3)) ∧ ((s 1, s 3) ≠ (t 0, t 3) ∧ (s 1, s 3) ≠ (t 1, t 2))))
    simp only [ne_eq, Prod.mk.injEq]
    split_ifs at hcard <;> simp_all
  · simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    change (((s 0, s 3) ≠ (t 0, t 1) ∧ (s 0, s 3) ≠ (t 2, t 3)) ∧ (((s 0, s 3) ≠ (t 0, t 2) ∧ (s 0, s 3) ≠ (t 1, t 3)) ∧ ((s 0, s 3) ≠ (t 0, t 3) ∧ (s 0, s 3) ≠ (t 1, t 2)))) ∨ (((s 1, s 2) ≠ (t 0, t 1) ∧ (s 1, s 2) ≠ (t 2, t 3)) ∧ (((s 1, s 2) ≠ (t 0, t 2) ∧ (s 1, s 2) ≠ (t 1, t 3)) ∧ ((s 1, s 2) ≠ (t 0, t 3) ∧ (s 1, s 2) ≠ (t 1, t 2))))
    simp only [ne_eq, Prod.mk.injEq]
    split_ifs at hcard <;> simp_all

private lemma four_mem_enumeration (T : Finset (Fin n)) (hT : T.card = 4) (x : Fin n) :
    x ∈ T ↔ x = T.orderEmbOfFin hT 0 ∨ x = T.orderEmbOfFin hT 1 ∨
      x = T.orderEmbOfFin hT 2 ∨ x = T.orderEmbOfFin hT 3 := by
  constructor
  · intro hx
    change x ∈ (T : Set (Fin n)) at hx
    rw [← T.range_orderEmbOfFin hT] at hx
    obtain ⟨i, hi⟩ := hx
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr (Or.inl hi.symm))
    · exact Or.inr (Or.inr (Or.inr hi.symm))
  · rintro (h | h | h | h) <;> subst x <;> exact T.orderEmbOfFin_mem hT _

private lemma overlap_card_enumeration (S T : Finset (Fin n))
    (hS : S.card = 4) (hT : T.card = 4) :
    (S ∩ T).card =
      (if S.orderEmbOfFin hS 0 ∈ T then 1 else 0) +
      (if S.orderEmbOfFin hS 1 ∈ T then 1 else 0) +
      (if S.orderEmbOfFin hS 2 ∈ T then 1 else 0) +
      (if S.orderEmbOfFin hS 3 ∈ T then 1 else 0) := by
  classical
  have he : S ∩ T = S.filter (fun x => x ∈ T) := by ext x; simp
  calc
    _ = ∑ x ∈ S, if x ∈ T then (1 : ℕ) else 0 := by
      rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i : Fin 4, if S.orderEmbOfFin hS i ∈ T then 1 else 0 := by
      conv_lhs => rw [← S.image_orderEmbOfFin_univ hS]
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact (S.orderEmbOfFin hS).injective hab
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change (if S.orderEmbOfFin hS 0 ∈ T then (1 : ℕ) else 0) +
        ((if S.orderEmbOfFin hS 1 ∈ T then 1 else 0) +
        ((if S.orderEmbOfFin hS 2 ∈ T then 1 else 0) +
        (if S.orderEmbOfFin hS 3 ∈ T then 1 else 0))) = _
      omega

private lemma coefX_product_middle_overlap (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (S T : Finset (Fin n)) (hS : S.card = 4) (hT : T.card = 4)
    (m : ℕ) (hm : m = 2 ∨ m = 3) (hST : (S ∩ T).card = m) :
    (∫ g, coefX F S g * coefX F T g ∂coefLaw n) =
      144 * frobSq F ^ 2 + 32 * trF4 F * (if m = 2 then (1 : ℝ) else 3) := by
  classical
  let s := S.orderEmbOfFin hS
  let t := T.orderEmbOfFin hT
  let p : Fin 3 → Fin n × Fin n := fun i => match i.val with
    | 0 => (s 0, s 1) | 1 => (s 0, s 2) | _ => (s 0, s 3)
  let q : Fin 3 → Fin n × Fin n := fun i => match i.val with
    | 0 => (s 2, s 3) | 1 => (s 1, s 3) | _ => (s 1, s 2)
  let u : Fin 3 → Fin n × Fin n := fun i => match i.val with
    | 0 => (t 0, t 1) | 1 => (t 0, t 2) | _ => (t 0, t 3)
  let w : Fin 3 → Fin n × Fin n := fun i => match i.val with
    | 0 => (t 2, t 3) | 1 => (t 1, t 3) | _ => (t 1, t 2)
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p, s.injective.eq_iff] at *
  have hq : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [q, s.injective.eq_iff] at *
  have hu : Function.Injective u := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [u, t.injective.eq_iff] at *
  have hw : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [w, t.injective.eq_iff] at *
  have hpq : ∀ i j, p i ≠ q j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [p, q, s.injective.eq_iff]
  have huw : ∀ i j, u i ≠ w j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [u, w, t.injective.eq_iff]
  have hcard := overlap_card_enumeration S T hS hT
  simp_rw [four_mem_enumeration T hT] at hcard
  have hless :
      (if s 0 = t 0 ∨ s 0 = t 1 ∨ s 0 = t 2 ∨ s 0 = t 3 then (1 : ℕ) else 0) +
      (if s 1 = t 0 ∨ s 1 = t 1 ∨ s 1 = t 2 ∨ s 1 = t 3 then 1 else 0) +
      (if s 2 = t 0 ∨ s 2 = t 1 ∨ s 2 = t 2 ∨ s 2 = t 3 then 1 else 0) +
      (if s 3 = t 0 ∨ s 3 = t 1 ∨ s 3 = t 2 ∨ s 3 = t 3 then 1 else 0) < 4 := by
    rw [← hcard, hST]
    omega
  have hcard' := overlap_card_enumeration T S hT hS
  simp_rw [four_mem_enumeration S hS] at hcard'
  have hless' :
      (if t 0 = s 0 ∨ t 0 = s 1 ∨ t 0 = s 2 ∨ t 0 = s 3 then (1 : ℕ) else 0) +
      (if t 1 = s 0 ∨ t 1 = s 1 ∨ t 1 = s 2 ∨ t 1 = s 3 then 1 else 0) +
      (if t 2 = s 0 ∨ t 2 = s 1 ∨ t 2 = s 2 ∨ t 2 = s 3 then 1 else 0) +
      (if t 3 = s 0 ∨ t 3 = s 1 ∨ t 3 = s 2 ∨ t 3 = s 3 then 1 else 0) < 4 := by
    rw [← hcard', Finset.inter_comm, hST]
    omega
  have hB := sorted_matching_outside s t hless
  have hD := sorted_matching_outside t s hless'
  have hn := sorted_matching_incidence s t m hm (by rw [← hcard, hST])
  change (∑ i, ∑ j, if p i = u j ∨ p i = w j ∨ q i = u j ∨ q i = w j
    then (1 : ℕ) else 0) = if m = 2 then 1 else 3 at hn
  have hr : (∑ i, ∑ j, if p i = u j ∨ p i = w j ∨ q i = u j ∨ q i = w j
    then (1 : ℝ) else 0) = if m = 2 then (1 : ℝ) else 3 := by
    exact_mod_cast hn
  have he : (fun g => coefX F S g * coefX F T g) =
      (fun g => (2 * ∑ i, bil F g (p i).1 (p i).2 (q i).1 (q i).2) ^ 2 *
        (2 * ∑ j, bil F g (u j).1 (u j).2 (w j).1 (w j).2) ^ 2) := by
    funext g
    simp [coefX, hS, hT, coefC, p, q, u, w, s, t, Fin.sum_univ_succ, add_assoc]
  rw [he, cross_bil_product_moment F hF p q u w hp hq hu hw hpq huw hB hD, hr]

private lemma coefX_product_overlap_two (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (S T : Finset (Fin n)) (hS : S.card = 4) (hT : T.card = 4)
    (hST : (S ∩ T).card = 2) :
    ∫ g, coefX F S g * coefX F T g ∂coefLaw n =
      (12 * frobSq F) ^ 2 + 32 * trF4 F := by
  have h := coefX_product_middle_overlap F hF S T hS hT 2 (Or.inl rfl) hST
  simp only [ite_true, mul_one] at h
  rw [h]
  ring

private lemma coefX_product_overlap_three (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (S T : Finset (Fin n)) (hS : S.card = 4) (hT : T.card = 4)
    (hST : (S ∩ T).card = 3) :
    ∫ g, coefX F S g * coefX F T g ∂coefLaw n =
      (12 * frobSq F) ^ 2 + 96 * trF4 F := by
  have h := coefX_product_middle_overlap F hF S T hS hT 3 (Or.inr rfl) hST
  simp only [show ¬ ((3 : ℕ) = 2) by decide, ite_false] at h
  rw [h]
  ring

theorem coefX_cov (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) (S T : Finset (Fin n))
    (hS : S.card = 4) (hT : T.card = 4) :
    ∫ g, coefX F S g * coefX F T g ∂(coefLaw n) - (12 * frobSq F) ^ 2 =
      if (S ∩ T).card = 4 then 288 * frobSq F ^ 2 + 288 * trF4 F
      else if (S ∩ T).card = 3 then 96 * trF4 F
      else if (S ∩ T).card = 2 then 32 * trF4 F else 0 := by
  classical
  by_cases h4 : (S ∩ T).card = 4
  · simp only [h4, ite_true]
    have heq := overlap_four_eq S T hS hT h4
    subst T
    have hp (g : Fin n × Fin n × Fin n → ℝ) :
        coefX F S g * coefX F S g = coefC F S hS g ^ 4 := by
      simp only [coefX, dite_eq_left hS]
      ring
    simp_rw [hp]
    rw [coefC_fourth_moment F hF S hS]
    ring
  · by_cases h3 : (S ∩ T).card = 3
    · simp only [h4, ite_false]
      simp only [h3, ite_true]
      rw [coefX_product_overlap_three F hF S T hS hT h3]
      ring
    · by_cases h2 : (S ∩ T).card = 2
      · simp only [h4, h3, ite_false]
        simp only [h2, ite_true]
        rw [coefX_product_overlap_two F hF S T hS hT h2]
        ring
      · have hle : (S ∩ T).card ≤ 4 :=
          (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
        have hlow : (S ∩ T).card ≤ 1 := by omega
        simp only [h4, h3, h2, ite_false]
        rw [coefX_product_low_overlap F hF S T hS hT hlow]
        ring

theorem coefX_integrable (F : Matrix (Fin n) (Fin n) ℝ) (S T : Finset (Fin n)) :
    Integrable (fun g => coefX F S g * coefX F T g) (coefLaw n) ∧
      Integrable (fun g => coefX F S g) (coefLaw n) := by
  obtain ⟨p, hp⟩ := coefX_polynomial F S
  obtain ⟨q, hq⟩ := coefX_polynomial F T
  constructor
  · simpa only [← MvPolynomial.eval_mul, hp, hq] using polynomial_integrable (p * q)
  · simpa only [hp] using polynomial_integrable p

/-- `0 ≤ tr F⁴ ≤ ‖F‖_F⁴` for symmetric `F`. -/
theorem trF4_bounds (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) :
    0 ≤ trF4 F ∧ trF4 F ≤ frobSq F ^ 2 := by
  classical
  have hFF : (F * F).IsSymm := by
    show (F * F).transpose = F * F
    rw [Matrix.transpose_mul, hF]
  have hr : trF4 F = ∑ i, ∑ j, (∑ k, F i k * F k j) ^ 2 := by
    simp only [trF4, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hij := hFF.apply i j
    simp only [Matrix.mul_apply] at hij
    rw [hij, sq]
  rw [hr]
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  · calc
      (∑ i, ∑ j, (∑ k, F i k * F k j) ^ 2) ≤
          ∑ i, ∑ j, (∑ k, F i k ^ 2) * ∑ k, F k j ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = frobSq F ^ 2 := by
        simp_rw [hF.apply]
        simp only [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        simp [frobSq, sq]


end BstLean.Part29
