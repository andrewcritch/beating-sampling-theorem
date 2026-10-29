import BstLean.Part212InverseScalar
import BstLean.Part153Inv

/-! A sharp noncentral inverse-radius moment keeps the retained mean. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg normSq_smul)

theorem noncentral_inverse_standard {n : ℕ} (k : ℕ) (hn : 2 * k + 5 ≤ n)
    (c : Fin n → ℝ) :
    ∫⁻ ξ, ENNReal.ofReal ((normSq (c + ξ))⁻¹ ^ (k + 1)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (((n : ℝ) - 2 * k - 4 + normSq c)⁻¹ ^ (k + 1)) := by
  letI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  letI : SFinite (stdGauss (Fin n)) := inferInstance
  let B : ℝ := (n : ℝ) - 2 * k - 4 + normSq c
  have hnR : 2 * (k : ℝ) + 5 ≤ n := by exact_mod_cast hn
  have hB : 0 < B := by dsimp [B]; have := normSq_nonneg c; linarith
  have hf0 : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hfactor0 : ENNReal.ofReal (k.factorial : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hf0).ne'
  have hpos : ∀ᵐ ξ ∂stdGauss (Fin n), 0 < normSq (c + ξ) := by
    have h := BstLean.Part153.ae_normSq_ne_zero (by omega : 1 ≤ n) c (τ := 1) (by norm_num)
    filter_upwards [h] with ξ hξ
    simp only [one_smul] at hξ
    exact lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hξ)
  have hm : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      ENNReal.ofReal (p.2 ^ k * exp (-(p.2 * normSq (c + p.1))))) := by
    unfold normSq
    fun_prop
  have hpay : ENNReal.ofReal (k.factorial : ℝ) *
      (∫⁻ ξ, ENNReal.ofReal ((normSq (c + ξ))⁻¹ ^ (k + 1)) ∂stdGauss (Fin n)) ≤
      ENNReal.ofReal ((k.factorial : ℝ) / B ^ (k + 1)) := by
    calc ENNReal.ofReal (k.factorial : ℝ) *
        (∫⁻ ξ, ENNReal.ofReal ((normSq (c + ξ))⁻¹ ^ (k + 1)) ∂stdGauss (Fin n))
        = ∫⁻ ξ, ENNReal.ofReal (k.factorial : ℝ) *
          ENNReal.ofReal ((normSq (c + ξ))⁻¹ ^ (k + 1)) ∂stdGauss (Fin n) :=
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ ξ, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (t ^ k * exp (-(t * normSq (c + ξ))))) ∂stdGauss (Fin n) := by
            apply lintegral_congr_ae
            filter_upwards [hpos] with ξ hξ
            simpa only [mul_comm] using inverse_gamma_identity k hξ
      _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ξ, ENNReal.ofReal
          (t ^ k * exp (-(t * normSq (c + ξ)))) ∂stdGauss (Fin n) :=
            lintegral_lintegral_swap hm.aemeasurable
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (t ^ k * exp (-(normSq c * gammaMobius t)) * ((√(1 + 2 * t))⁻¹) ^ n) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have hi : Integrable (fun ξ : Fin n → ℝ => exp (-(t * normSq (c + ξ))))
                (stdGauss (Fin n)) := by
              simpa only [one_smul] using laplace_vector_integrable ht.le c 1
            have he : (∫ ξ, exp (-(t * normSq (c + ξ))) ∂stdGauss (Fin n)) =
                exp (-(t * normSq c / (1 + 2 * t))) * ((√(1 + 2 * t))⁻¹) ^ n := by
              simpa only [one_smul, one_pow, mul_one] using laplace_vector_exact ht.le c 1
            rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul (t ^ k))
              (ae_of_all _ fun ξ => mul_nonneg (pow_nonneg ht.le _) (exp_pos _).le),
              integral_const_mul, he]
            have hexp : -(t * normSq c / (1 + 2 * t)) =
                -(normSq c * gammaMobius t) := by unfold gammaMobius; ring
            rw [hexp]
            congr 1
            ring
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (gammaMobius t ^ k * exp (-B * gammaMobius t) / (1 + 2 * t) ^ 2) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact ENNReal.ofReal_le_ofReal (gaussian_gamma_pointwise k n hn (normSq_nonneg c) ht.le)
      _ ≤ ENNReal.ofReal ((k.factorial : ℝ) / B ^ (k + 1)) := mobius_gamma_bound k hB
  have he : ENNReal.ofReal ((k.factorial : ℝ) / B ^ (k + 1)) =
      ENNReal.ofReal (k.factorial : ℝ) * ENNReal.ofReal (B⁻¹ ^ (k + 1)) := by
    rw [← ENNReal.ofReal_mul hf0.le, inv_pow]
    congr 1
  rw [he] at hpay
  have h := mul_le_mul_right hpay (ENNReal.ofReal (k.factorial : ℝ))⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hfactor0 ENNReal.ofReal_ne_top, one_mul]
    using h

theorem noncentral_inverse_radius {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * j + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ ξ, ENNReal.ofReal ((τ ^ 2 / normSq (c + τ • ξ)) ^ j) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal ((τ ^ 2 / (normSq c + ((n : ℝ) - 2 * j - 2) * τ ^ 2)) ^ j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  let c' : Fin n → ℝ := τ⁻¹ • c
  have he (ξ : Fin n → ℝ) : c + τ • ξ = τ • (c' + ξ) := by
    dsimp [c']
    rw [smul_add, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hfun (ξ : Fin n → ℝ) : τ ^ 2 / normSq (c + τ • ξ) = (normSq (c' + ξ))⁻¹ := by
    rw [he, normSq_smul]
    field_simp
  simp_rw [hfun]
  have h := noncentral_inverse_standard k (by omega) c'
  refine h.trans (le_of_eq ?_)
  congr 2
  have hc' : normSq c' = normSq c / τ ^ 2 := by
    dsimp [c']
    rw [normSq_smul, inv_pow]
    ring
  rw [hc']
  congr 1
  push_cast
  field_simp
  ring
end BstLean.Part212
