import BstLean.Part107Defs

/-!
# Part 107, auxiliary: `InvMom107`, `E |g|^{-2} ≤ 1/(n-2)`

Proof: `1/R = ∫_0^∞ e^{-tR} dt`, Tonelli, `E e^{-t|g|²} = (1+2t)^{-n/2}`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-- `q(t) = (1+2t)^{-1/2}`. -/
noncomputable def qInv (t : ℝ) : ℝ := (Real.sqrt (1 + 2 * t))⁻¹

lemma gauss_exp (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, Real.exp (-t * x ^ 2) ∂gaussianReal 0 1 = qInv t := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h (x : ℝ) : (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-t * x ^ 2) =
      (√(2 * Real.pi))⁻¹ * Real.exp (-(t + 1 / 2) * x ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h2 : Real.pi / (t + 1 / 2) = (2 * Real.pi) / (1 + 2 * t) := by field_simp; ring
  have h1 : √(2 * Real.pi) ≠ 0 := by positivity
  have h3 : √(1 + 2 * t) ≠ 0 := by positivity
  rw [h2, Real.sqrt_div (by positivity), qInv]
  field_simp

lemma stdGauss_exp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ g, Real.exp (-t * ∑ i, g i ^ 2) ∂stdGauss (Fin n) = qInv t ^ n := by
  have h (g : Fin n → ℝ) : Real.exp (-t * ∑ i, g i ^ 2) = ∏ i, Real.exp (-t * g i ^ 2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) (x : ℝ) => Real.exp (-t * x ^ 2))]
  simp only [gauss_exp t ht, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma inv_le_laplace (R : ℝ) :
    ENNReal.ofReal (1 / R) ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t * R)) := by
  rcases le_or_gt R 0 with hR | hR
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonneg_of_nonpos zero_le_one hR)]
    simp
  · have h1 := integral_exp_mul_Ioi (a := -R) (by linarith) 0
    have h2 : IntegrableOn (fun t : ℝ => Real.exp (-R * t)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    have h3 := ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun t => (Real.exp_pos _).le)
    have h4 : (1 : ℝ) / R = ∫ t in Ioi (0 : ℝ), Real.exp (-R * t) := by
      rw [h1]; simp
    rw [h4, h3]
    refine le_of_eq (lintegral_congr fun t => ?_)
    rw [show -R * t = -t * R by ring]

lemma qInv_integral (k : ℕ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (qInv t ^ (k + 3)) =
      ENNReal.ofReal (1 / (((k + 3 : ℕ) : ℝ) - 2)) := by
  set G : ℝ → ℝ := fun t => -(qInv t ^ (k + 1)) / (((k + 3 : ℕ) : ℝ) - 2) with hG
  have hk : (((k + 3 : ℕ) : ℝ) - 2) = (k : ℝ) + 1 := by push_cast; ring
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt G (qInv t ^ (k + 3)) t := by
    intro t ht
    have ht' : (0 : ℝ) ≤ t := ht
    have hpos : 0 < 1 + 2 * t := by linarith
    have hs : √(1 + 2 * t) ≠ 0 := by positivity
    have d1 : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).const_add 1
    have d2 := d1.sqrt hpos.ne'
    have d3 := d2.inv hs
    have d4 := ((d3.pow (k + 1)).neg).div_const (((k + 3 : ℕ) : ℝ) - 2)
    refine (show HasDerivAt G _ t from d4).congr_deriv ?_
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    simp only [Pi.inv_apply, Nat.add_sub_cancel, qInv, hk]
    push_cast
    field_simp
    rw [pow_add, div_pow 1, one_pow]
    field_simp
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ qInv t ^ (k + 3) := by
    intro t _
    unfold qInv
    positivity
  have hq : Tendsto qInv atTop (𝓝 0) := by
    unfold qInv
    refine tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ?_)
    exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (by norm_num))
  have hlim : Tendsto G atTop (𝓝 0) := by
    have := ((hq.pow (k + 1)).neg).div_const (((k + 3 : ℕ) : ℝ) - 2)
    convert this using 2
    simp
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)), hval]
  congr 1
  simp [hG, qInv]
  ring

theorem invMom107 : InvMom107 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  set R : (Fin (k + 3) → ℝ) → ℝ := fun g => ∑ i, g i ^ 2 with hR
  have hRm : Measurable R := Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2
  have hfm : Measurable (fun g : Fin (k + 3) → ℝ => 1 / R g) := measurable_const.div hRm
  have hnn : ∀ g, 0 ≤ 1 / R g := fun g =>
    div_nonneg zero_le_one (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hmeas2 : Measurable (Function.uncurry fun (g : Fin (k + 3) → ℝ) (t : ℝ) =>
      ENNReal.ofReal (Real.exp (-t * R g))) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (measurable_snd.neg).mul (hRm.comp measurable_fst)
  have key : ∫⁻ g, ENNReal.ofReal (1 / R g) ∂stdGauss (Fin (k + 3)) ≤
      ENNReal.ofReal (1 / (((k + 3 : ℕ) : ℝ) - 2)) := by
    calc ∫⁻ g, ENNReal.ofReal (1 / R g) ∂stdGauss (Fin (k + 3))
        ≤ ∫⁻ g, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t * R g)))
            ∂stdGauss (Fin (k + 3)) := lintegral_mono fun g => inv_le_laplace (R g)
      _ = ∫⁻ t in Ioi (0 : ℝ), (∫⁻ g, ENNReal.ofReal (Real.exp (-t * R g))
            ∂stdGauss (Fin (k + 3))) := lintegral_lintegral_swap hmeas2.aemeasurable
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (qInv t ^ (k + 3)) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          have ht' : (0 : ℝ) ≤ t := le_of_lt ht
          have hm : Measurable (fun g : Fin (k + 3) → ℝ => Real.exp (-t * R g)) :=
            Real.measurable_exp.comp (hRm.const_mul _)
          have hi : Integrable (fun g : Fin (k + 3) → ℝ => Real.exp (-t * R g))
              (stdGauss (Fin (k + 3))) := by
            refine Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
              (ae_of_all _ fun g => ?_)
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
            have : 0 ≤ R g := Finset.sum_nonneg fun i _ => sq_nonneg _
            nlinarith
          rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun g => (Real.exp_pos _).le),
            stdGauss_exp _ t ht']
      _ = _ := qInv_integral k
  have hI : Integrable (fun g : Fin (k + 3) → ℝ => 1 / R g) (stdGauss (Fin (k + 3))) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    exact lt_of_le_of_lt key ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnn)
  rw [← h1] at key
  have hpos : (0 : ℝ) ≤ 1 / (((k + 3 : ℕ) : ℝ) - 2) := by
    have : (((k + 3 : ℕ) : ℝ) - 2) = (k : ℝ) + 1 := by push_cast; ring
    rw [this]; positivity
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 key

end BstLean.Part107
