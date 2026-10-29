import BstLean.Part109Defs

/-!
# Part 109, Gaussian tools (diagonal form): Laurent–Massart lower tail, chi-square upper tail

`lmLower109 : LMLower109`, `chiUpper109 : ChiUpper109`. Chernoff proofs.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part109

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)

/-! ## Two inequalities of the logarithm -/

lemma log_lower {t : ℝ} (ht : 0 ≤ t) : t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  have hmono : MonotoneOn (fun u : ℝ => Real.log (1 + u) - u + u ^ 2 / 2) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id) (by fun_prop)
      refine ContinuousOn.log (by fun_prop) ?_
      intro u hu
      have : (0 : ℝ) ≤ u := hu
      positivity
    · intro u hu
      rw [interior_Ici] at hu
      have hu' : (0 : ℝ) < u := hu
      have : DifferentiableAt ℝ (fun u : ℝ => Real.log (1 + u)) u :=
        DifferentiableAt.log (by fun_prop) (by positivity)
      exact ((this.sub differentiableAt_id).add (by fun_prop)).differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu' : (0 : ℝ) < u := hu
      have h1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) ((1 + u)⁻¹) u := by
        have := ((hasDerivAt_id u).const_add 1).log (by simpa using (by positivity : (1 + u) ≠ 0))
        simpa using this
      have h2 : HasDerivAt (fun u : ℝ => Real.log (1 + u) - u + u ^ 2 / 2)
          ((1 + u)⁻¹ - 1 + u) u := by
        have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
          have := (hasDerivAt_pow 2 u).div_const 2
          simpa using this
        exact (h1.sub (hasDerivAt_id u)).add h3
      rw [h2.deriv]
      have : (1 + u)⁻¹ - 1 + u = u ^ 2 / (1 + u) := by field_simp; ring
      rw [this]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp at this
  linarith

lemma log_upper {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  have hmono : MonotoneOn (fun u : ℝ => u - u ^ 2 / 2 + u ^ 3 / 3 - Real.log (1 + u))
      (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.sub (by fun_prop) ?_
      refine ContinuousOn.log (by fun_prop) ?_
      intro u hu
      have : (0 : ℝ) ≤ u := hu
      positivity
    · intro u hu
      rw [interior_Ici] at hu
      have hu' : (0 : ℝ) < u := hu
      have : DifferentiableAt ℝ (fun u : ℝ => Real.log (1 + u)) u :=
        DifferentiableAt.log (by fun_prop) (by positivity)
      exact (DifferentiableAt.sub (by fun_prop) this).differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu' : (0 : ℝ) < u := hu
      have h1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) ((1 + u)⁻¹) u := by
        have := ((hasDerivAt_id u).const_add 1).log (by simpa using (by positivity : (1 + u) ≠ 0))
        simpa using this
      have h2 : HasDerivAt (fun u : ℝ => u - u ^ 2 / 2 + u ^ 3 / 3 - Real.log (1 + u))
          (1 - u + u ^ 2 - (1 + u)⁻¹) u := by
        have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
          have := (hasDerivAt_pow 2 u).div_const 2
          simpa using this
        have h4 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) (u ^ 2) u := by
          have := (hasDerivAt_pow 3 u).div_const 3
          simpa using this
        exact (((hasDerivAt_id u).sub h3).add h4).sub h1
      rw [h2.deriv]
      have : 1 - u + u ^ 2 - (1 + u)⁻¹ = u ^ 3 / (1 + u) := by field_simp; ring
      rw [this]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp at this
  linarith

/-! ## The one-dimensional integral -/

lemma mgf1 {b : ℝ} (hb : -1 / 2 < b) :
    ∫ x, Real.exp (-b * x ^ 2) ∂gaussianReal 0 1 = (Real.sqrt (1 + 2 * b))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hb' : 0 < b + 1 / 2 := by linarith
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (-b * x ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(b + 1 / 2) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_gaussian]
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  have : (0 : ℝ) < π := Real.pi_pos
  field_simp
  ring

lemma mgf1_int {b : ℝ} (hb : -1 / 2 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) (gaussianReal 0 1) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [mgf1 hb]
  have : 0 < 1 + 2 * b := by linarith
  positivity

/-! ## The product -/

section prod

variable {ι : Type} [Fintype ι]

lemma mgfPi (c : ι → ℝ) (hc : ∀ i, -1 / 2 < c i) :
    Integrable (fun ξ : ι → ℝ => Real.exp (-∑ i, c i * ξ i ^ 2)) (stdGauss ι) ∧
    ∫ ξ, Real.exp (-∑ i, c i * ξ i ^ 2) ∂stdGauss ι = ∏ i, (Real.sqrt (1 + 2 * c i))⁻¹ := by
  have e : (fun ξ : ι → ℝ => Real.exp (-∑ i, c i * ξ i ^ 2)) =
      fun ξ : ι → ℝ => ∏ i, Real.exp (-c i * ξ i ^ 2) := by
    funext ξ
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  unfold stdGauss
  refine ⟨Integrable.fintype_prod (f := fun i x => Real.exp (-c i * x ^ 2))
    (fun i => mgf1_int (hc i)), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (-c i * x ^ 2))]
  exact Finset.prod_congr rfl fun i _ => mgf1 (hc i)

/-- Chernoff: if `1 ≤ h` on the event, `h ≥ 0` integrable, then the probability is at most
`∫ h`. -/
lemma chern {S : Set (ι → ℝ)} {h : (ι → ℝ) → ℝ} (h0 : ∀ ξ, 0 ≤ h ξ)
    (hi : Integrable h (stdGauss ι)) (hS : ∀ ξ ∈ S, 1 ≤ h ξ) :
    (stdGauss ι).real S ≤ ∫ ξ, h ξ ∂stdGauss ι := by
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss ι) (f := h)
    (Filter.Eventually.of_forall h0) hi 1
  rw [one_mul] at hmk
  exact (measureReal_mono (fun ξ hξ => hS ξ hξ)).trans hmk

end prod

lemma sqrt_eq_exp {p : ℝ} (hp : 0 < p) : Real.sqrt p = Real.exp (Real.log p / 2) := by
  rw [Real.exp_half, Real.exp_log hp]

lemma exp_div_sqrt_le {y : ℝ} (hy : 0 ≤ y) :
    Real.exp y * (Real.sqrt (1 + 2 * y))⁻¹ ≤ Real.exp (y ^ 2) := by
  have hpos : 0 < 1 + 2 * y := by linarith
  have hl := log_lower (t := 2 * y) (by linarith)
  have h1 : Real.exp (y - y ^ 2) ≤ Real.sqrt (1 + 2 * y) := by
    rw [sqrt_eq_exp hpos]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.2 hpos)]
  calc Real.exp y = Real.exp (y ^ 2) * Real.exp (y - y ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (y ^ 2) * Real.sqrt (1 + 2 * y) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- **Laurent–Massart, lower tail** (diagonal form). -/
theorem lmLower109 : LMLower109 := by
  intro ι _ lam hlam x hx
  set Λ := ∑ i, lam i ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hΛ0.eq_or_lt with h0 | hpos
  · -- every `λ_i` is zero
    have hz : ∀ i, lam i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (lam i))).1 h0.symm i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have : {ξ : ι → ℝ | ∑ i, lam i * (ξ i ^ 2 - 1) < -(2 * Real.sqrt (x * Λ))} = ∅ := by
      ext ξ
      simp [hz, ← h0]
    rw [this]
    simp [(Real.exp_pos _).le]
  · set s := Real.sqrt (x / Λ) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = x / Λ := Real.sq_sqrt (div_nonneg hx hpos.le)
    have hsa : s * Real.sqrt (x * Λ) = x := by
      rw [hs, ← Real.sqrt_mul (div_nonneg hx hpos.le)]
      have : x / Λ * (x * Λ) = x ^ 2 := by field_simp
      rw [this, Real.sqrt_sq hx]
    set a := 2 * Real.sqrt (x * Λ) with ha
    set C := Real.exp (-(s * a) + s * ∑ i, lam i) with hC
    obtain ⟨hint, hval⟩ := mgfPi (fun i => s * lam i)
      (fun i => by have := mul_nonneg hs0 (hlam i); linarith)
    have hb := chern (ι := ι)
      (S := {ξ | ∑ i, lam i * (ξ i ^ 2 - 1) < -a})
      (h := fun ξ => C * Real.exp (-∑ i, s * lam i * ξ i ^ 2))
      (fun ξ => by positivity) (hint.const_mul C) (by
        intro ξ hξ
        simp only [Set.mem_ofPred_eq] at hξ
        rw [hC, ← Real.exp_add]
        refine Real.one_le_exp ?_
        have e : ∑ i, lam i * (ξ i ^ 2 - 1) = ∑ i, lam i * ξ i ^ 2 - ∑ i, lam i := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        have e2 : ∑ i, s * lam i * ξ i ^ 2 = s * ∑ i, lam i * ξ i ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e2]
        rw [e] at hξ
        have := mul_le_mul_of_nonneg_left hξ.le hs0
        nlinarith)
    refine hb.trans ?_
    rw [integral_const_mul, hval]
    have hprod : Real.exp (s * ∑ i, lam i) * ∏ i, (Real.sqrt (1 + 2 * (s * lam i)))⁻¹ ≤
        Real.exp (s ^ 2 * Λ) := by
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib, hΛ, Finset.mul_sum,
        Real.exp_sum]
      refine Finset.prod_le_prod₀ (fun i _ => by positivity) ?_
      intro i _
      have := exp_div_sqrt_le (mul_nonneg hs0 (hlam i))
      rw [mul_pow] at this
      exact this
    calc C * ∏ i, (Real.sqrt (1 + 2 * (s * lam i)))⁻¹
        = Real.exp (-(s * a)) *
            (Real.exp (s * ∑ i, lam i) * ∏ i, (Real.sqrt (1 + 2 * (s * lam i)))⁻¹) := by
          rw [hC, Real.exp_add]; ring
      _ ≤ Real.exp (-(s * a)) * Real.exp (s ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (-x) := by
          rw [← Real.exp_add]
          congr 1
          have : s ^ 2 * Λ = x := by rw [hs2]; field_simp
          rw [this, ha, show s * (2 * Real.sqrt (x * Λ)) = 2 * (s * Real.sqrt (x * Λ)) by ring,
            hsa]
          ring

/-- **Chernoff, upper tail of a chi-square.** -/
theorem chiUpper109 : ChiUpper109 := by
  intro ι _ η hη hη1
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  set s := η / (2 * (1 + η)) with hs
  have h1η : 0 < 1 + η := by linarith
  have hs0 : 0 < s := by positivity
  have hs12 : 1 + 2 * (-s) = (1 + η)⁻¹ := by rw [hs]; field_simp; ring
  obtain ⟨hint, hval⟩ := mgfPi (ι := ι) (fun _ => -s) (fun _ => by
    have : 0 < 1 + 2 * (-s) := by rw [hs12]; positivity
    linarith)
  set C := Real.exp (-(s * ((1 + η) * m))) with hC
  have hb := chern (ι := ι)
    (S := {ξ | (1 + η) * m ≤ ∑ i, ξ i ^ 2})
    (h := fun ξ => C * Real.exp (-∑ i, -s * ξ i ^ 2))
    (fun ξ => by positivity) (hint.const_mul C) (by
      intro ξ hξ
      simp only [Set.mem_ofPred_eq] at hξ
      rw [hC, ← Real.exp_add]
      refine Real.one_le_exp ?_
      have e2 : ∑ i, -s * ξ i ^ 2 = -(s * ∑ i, ξ i ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e2]
      have := mul_le_mul_of_nonneg_left hξ hs0.le
      linarith)
  refine hb.trans ?_
  rw [integral_const_mul, hval]
  simp only [hs12, Finset.prod_const, Finset.card_univ]
  -- one coordinate
  have hone : Real.exp (-(s * (1 + η))) * (Real.sqrt ((1 + η)⁻¹))⁻¹ ≤
      Real.exp (-(η ^ 2 / 4 - η ^ 3 / 6)) := by
    have hl := log_upper hη.le
    have e1 : (Real.sqrt ((1 + η)⁻¹))⁻¹ = Real.exp (Real.log (1 + η) / 2) := by
      rw [Real.sqrt_inv, inv_inv, sqrt_eq_exp h1η]
    rw [e1, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : s * (1 + η) = η / 2 := by rw [hs]; field_simp
    rw [this]
    linarith
  have hC' : C = Real.exp (-(s * (1 + η))) ^ Fintype.card ι := by
    rw [hC, ← Real.exp_nat_mul, hm]
    congr 1
    ring
  rw [hC', ← mul_pow]
  calc (Real.exp (-(s * (1 + η))) * (Real.sqrt ((1 + η)⁻¹))⁻¹) ^ Fintype.card ι
      ≤ Real.exp (-(η ^ 2 / 4 - η ^ 3 / 6)) ^ Fintype.card ι :=
        pow_le_pow_left₀ (by positivity) hone _
    _ = Real.exp (-(m * (η ^ 2 / 4 - η ^ 3 / 6))) := by
        rw [← Real.exp_nat_mul, hm]
        congr 1
        ring

end BstLean.Part109

#print axioms BstLean.Part109.lmLower109
#print axioms BstLean.Part109.chiUpper109
