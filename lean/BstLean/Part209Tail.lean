import BstLean.Part200Lengths

/-! Integration of a Gaussian tail and an exponential tail at even integer orders. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153

lemma exp_moment_integral {B : ℝ} (hB : 0 < B) (q : ℕ) :
    IntegrableOn (fun u : ℝ => exp (-u / B) * (((q : ℝ) + 1) * u ^ q)) (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), exp (-u / B) * (((q : ℝ) + 1) * u ^ q)) =
      B ^ (q + 1) * ((q + 1).factorial : ℝ) := by
  have hb : 0 < B⁻¹ := inv_pos.mpr hB
  have hq : (-1 : ℝ) < (q : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) q]
  have he : ∀ u ∈ Ioi (0 : ℝ), ((q : ℝ) + 1) *
      (u ^ (q : ℝ) * exp (-B⁻¹ * u ^ (1 : ℝ))) =
        exp (-u / B) * (((q : ℝ) + 1) * u ^ q) := by
    intro u _
    rw [rpow_natCast, rpow_one]
    have h : -B⁻¹ * u = -u / B := by ring
    rw [h]
    ring
  constructor
  · exact IntegrableOn.congr_fun
      ((integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num : (0 : ℝ) < 1) hb).const_mul
        ((q : ℝ) + 1)) he measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 1) hq hb]
    simp only [div_one]
    rw [show -((q : ℝ) + 1) = -((q + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.Gamma_nat_eq_factorial, rpow_neg hb.le, rpow_natCast, inv_pow, inv_inv,
      Nat.factorial_succ]
    push_cast
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The tail bound itself proves integrability; no moment assumption is used. -/
theorem mixed_tail_even_moment {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {L B K : ℝ} (hL : 0 < L) (hB : 0 < B) (hK : 0 ≤ K)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < X ω} ≤
      K * (exp (-t ^ 2 / (2 * L ^ 2)) + exp (-t / B))) (q : ℕ) :
    Integrable (fun ω => X ω ^ (2 * (q + 1))) μ ∧
    (∫ ω, X ω ^ (2 * (q + 1)) ∂μ) ≤
      K * (L ^ (2 * (q + 1)) * (2 ^ (q + 1) * ((q + 1).factorial : ℝ)) +
        B ^ (2 * (q + 1)) * ((2 * (q + 1)).factorial : ℝ)) := by
  let g : ℝ → ℝ := fun t => (2 * (q : ℝ) + 2) * t ^ (2 * q + 1)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact ae_of_all _ fun t ht => by dsimp [g]; have : 0 < t := ht; positivity
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := X) (g := g)
    (ae_of_all _ hX0) hX.aemeasurable (fun t _ => hg.intervalIntegrable _ _) hg0
  have hint : ∀ t : ℝ, ∫ u in (0 : ℝ)..t, g u = t ^ (2 * (q + 1)) := by
    intro t
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have he : ((2 * q + 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) + 2 := by push_cast; ring
    rw [he, zero_pow (by omega), sub_zero, mul_div_cancel₀ _ (by positivity)]
    congr 1
  simp only [hint] at key
  obtain ⟨hiG, heG⟩ := gauss_moment_integral hL q
  obtain ⟨hiE, heE⟩ := exp_moment_integral hB (2 * q + 1)
  have heq : (((2 * q + 1 : ℕ) : ℝ) + 1) = 2 * (q : ℝ) + 2 := by push_cast; ring
  have hnq : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
  rw [heq] at hiE heE
  rw [hnq] at heE
  let F : ℝ → ℝ := fun t => K *
    (exp (-t ^ 2 / (2 * L ^ 2)) * g t + exp (-t / B) * g t)
  have hFi : IntegrableOn F (Ioi 0) := (hiG.add hiE).const_mul K
  have hF0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ F t := by
    filter_upwards [hg0] with t ht
    exact mul_nonneg hK (add_nonneg (mul_nonneg (exp_pos _).le ht)
      (mul_nonneg (exp_pos _).le ht))
  have hFe : (∫ t in Ioi (0 : ℝ), F t) = K *
      (L ^ (2 * (q + 1)) * (2 ^ (q + 1) * ((q + 1).factorial : ℝ)) +
        B ^ (2 * (q + 1)) * ((2 * (q + 1)).factorial : ℝ)) := by
    rw [integral_const_mul, integral_add hiG hiE, heG, heE]
  have hb : (∫⁻ ω, ENNReal.ofReal (X ω ^ (2 * (q + 1))) ∂μ) ≤
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), F t) := by
    rw [key, ofReal_integral_eq_lintegral_ofReal hFi hF0]
    apply lintegral_mono_ae
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine ae_of_all _ fun t ht => ?_
    have ht' : 0 < t := ht
    have hg' : 0 ≤ g t := by dsimp [g]; positivity
    rw [← ofReal_measureReal (μ := μ)]
    have h := ENNReal.ofReal_le_ofReal (htail t ht')
    calc ENNReal.ofReal (μ.real {ω | t < X ω}) * ENNReal.ofReal (g t) ≤
        ENNReal.ofReal (K * (exp (-t ^ 2 / (2 * L ^ 2)) + exp (-t / B))) *
          ENNReal.ofReal (g t) := mul_le_mul' h le_rfl
      _ = ENNReal.ofReal (F t) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (by positivity))]
        congr 1
        dsimp [F]
        ring
  have hi : Integrable (fun ω => X ω ^ (2 * (q + 1))) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const _).aestronglyMeasurable
      (ae_of_all _ fun ω => pow_nonneg (hX0 ω) _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => pow_nonneg (hX0 ω) _)] at hb
  rw [hFe] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

/-- A square-root-plus-linear tail implies the sum of a Gaussian tail and an exponential tail. -/
lemma bernstein_mixed_tail {X : Ω → ℝ} {A B K : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hK : 0 ≤ K)
    (htail : ∀ τ : ℝ, 0 ≤ τ → μ.real {ω | A * sqrt τ + B * τ < X ω} ≤ K * exp (-τ))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t < X ω} ≤
      K * (exp (-t ^ 2 / (2 * (sqrt 2 * A) ^ 2)) + exp (-t / (2 * B))) := by
  let a := t ^ 2 / (4 * A ^ 2)
  let b := t / (2 * B)
  let τ := min a b
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hτ : 0 ≤ τ := le_min ha hb
  have h₁ : A * sqrt τ ≤ t / 2 := by
    have hs : sqrt τ ≤ t / (2 * A) := by
      apply (sqrt_le_iff).mpr
      refine ⟨by positivity, ?_⟩
      calc τ ≤ a := min_le_left _ _
        _ = (t / (2 * A)) ^ 2 := by dsimp [a]; ring
    have hh := mul_le_mul_of_nonneg_left hs hA.le
    have he : A * (t / (2 * A)) = t / 2 := by field_simp
    rwa [he] at hh
  have h₂ : B * τ ≤ t / 2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right a b) hB.le
    have he : B * b = t / 2 := by dsimp [b]; field_simp
    rwa [he] at hh
  have h := (measureReal_mono (fun ω hω => by
    change t < X ω at hω
    change A * sqrt τ + B * τ < X ω
    linarith)).trans (htail τ hτ)
  have he : exp (-τ) ≤ exp (-a) + exp (-b) := by
    rcases le_total a b with hab | hba
    · dsimp [τ]; rw [min_eq_left hab]; linarith [exp_pos (-b)]
    · dsimp [τ]; rw [min_eq_right hba]; linarith [exp_pos (-a)]
  have hG : -a = -t ^ 2 / (2 * (sqrt 2 * A) ^ 2) := by
    dsimp [a]
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact h.trans (by simpa only [hG, b, neg_div] using mul_le_mul_of_nonneg_left he hK)

noncomputable def bernMoment (A B K : ℝ) (P : ℕ) : ℝ :=
  2 * A * (K * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) +
    2 * B * (K * ((2 * P).factorial : ℝ)) ^ (1 / (2 * (P : ℝ)))

lemma even_root_pow {P : ℕ} (hP : 1 ≤ P) {c : ℝ} (hc : 0 ≤ c) :
    (c ^ (1 / (2 * (P : ℝ)))) ^ (2 * P) = c := by
  rw [← rpow_natCast, ← rpow_mul hc]
  have he : 1 / (2 * (P : ℝ)) * ((2 * P : ℕ) : ℝ) = 1 := by
    have hp : (P : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [he, rpow_one]

/-- The integrated constant has the factorial terms used in the paper overlap estimate. -/
theorem bernstein_even_moment {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {A B K : ℝ} (hA : 0 < A) (hB : 0 < B) (hK : 0 ≤ K)
    (htail : ∀ τ : ℝ, 0 ≤ τ → μ.real {ω | A * sqrt τ + B * τ < X ω} ≤ K * exp (-τ))
    {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun ω => X ω ^ (2 * P)) μ ∧
    (∫ ω, X ω ^ (2 * P) ∂μ) ≤ bernMoment A B K P ^ (2 * P) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P ≠ 0)
  obtain ⟨hi, hb⟩ := mixed_tail_even_moment hX hX0
    (mul_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) hA) (by positivity : 0 < 2 * B) hK
    (fun t ht => bernstein_mixed_tail hA hB hK htail ht) q
  refine ⟨hi, hb.trans ?_⟩
  have h₁ : 0 ≤ 2 * A * (K * ((q + 1).factorial : ℝ)) ^ (1 / (2 * ((q + 1 : ℕ) : ℝ))) := by
    positivity
  have h₂ : 0 ≤ 2 * B * (K * ((2 * (q + 1)).factorial : ℝ)) ^
      (1 / (2 * ((q + 1 : ℕ) : ℝ))) := by positivity
  have hh := _root_.pow_add_pow_le h₁ h₂ (show 2 * (q + 1) ≠ 0 by omega)
  simp only [mul_pow] at hh
  rw [even_root_pow (by omega) (by positivity),
    even_root_pow (by omega) (by positivity)] at hh
  have he : (sqrt 2 * A) ^ (2 * (q + 1)) * 2 ^ (q + 1) = (2 * A) ^ (2 * (q + 1)) := by
    have ht : (2 : ℝ) ^ (2 * (q + 1)) = (2 ^ (q + 1)) ^ 2 := by
      rw [Nat.mul_comm 2 (q + 1), pow_mul]
    rw [mul_pow, pow_mul (sqrt 2) 2 (q + 1), sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      mul_pow, ht]
    ring
  change _ ≤ bernMoment A B K (q + 1) ^ (2 * (q + 1))
  convert hh using 1
  · rw [show (sqrt 2 * A) ^ (2 * (q + 1)) *
        (2 ^ (q + 1) * ((q + 1).factorial : ℝ)) =
        ((sqrt 2 * A) ^ (2 * (q + 1)) * 2 ^ (q + 1)) * ((q + 1).factorial : ℝ) by ring, he]
    simp only [mul_pow]
    ring
  · rfl

end BstLean.Part209
