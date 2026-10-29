import BstLean.Part167Lam

/-! The gated plane matrix has finite moments at order eighty. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask mask_of_pos mask_of_nonpos mask_sq mask_nonneg measurable_mask)
open BstLean.Part167
variable {m : ℕ}

theorem plane_cross_moment80 (hm : (8000 : ℝ) ≤ m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((80 : ℝ) ^ 40 * (m / 2 + 160) ^ 40) := by
  have hm1 : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  have : Nonempty (Fin m) := ⟨⟨0, hm1⟩⟩
  have hin : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80) ∂stdGauss (Fin m) =
      ENNReal.ofReal (BstLean.Part162.gmom 80 * L11 ξ₁ ^ 40) := by
    intro ξ₁
    set v : Fin m → ℝ := fun j => mask (ξ₁ j) * ξ₁ j with hv
    have hL : ∀ ξ₂, L12 ξ₁ ξ₂ = ξ₂ ⬝ᵥ v := by
      intro ξ₂; unfold L12; simp only [dotProduct, hv]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hvv : v ⬝ᵥ v = L11 ξ₁ := by
      unfold L11; simp only [dotProduct, hv]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := mask_sq (ξ₁ j); rw [sq] at this
      calc mask (ξ₁ j) * ξ₁ j * (mask (ξ₁ j) * ξ₁ j) = (mask (ξ₁ j) * mask (ξ₁ j)) * ξ₁ j ^ 2 := by
            ring
        _ = mask (ξ₁ j) * ξ₁ j ^ 2 := by rw [this]
    simp_rw [hL]
    have hInt : Integrable (fun y : Fin m → ℝ => |y ⬝ᵥ v| ^ 80) (stdGauss (Fin m)) := by
      refine ((BstLean.Part162.integrable_radF_pow (d := m) 80).const_mul
        (BstLean.Part153.nrm v ^ 80)).mono'
        ((((continuous_id.dotProduct continuous_const).abs).pow 80).measurable.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := BstLean.Part153.abs_dot_le_nrm y v
      have h2 : BstLean.Part153.nrm y = BstLean.Part53.radF53 y := rfl
      rw [h2] at h1
      calc |y ⬝ᵥ v| ^ 80 ≤ (BstLean.Part53.radF53 y * BstLean.Part153.nrm v) ^ 80 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 80
        _ = BstLean.Part153.nrm v ^ 80 * BstLean.Part53.radF53 y ^ 80 := by ring
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun y => by positivity),
      BstLean.Part162.gauss_dot_mom v 80, hvv]
    congr 2
    rw [show (80 : ℕ) = 2 * 40 by norm_num, pow_mul, Real.sq_sqrt (L11_nonneg ξ₁)]
  simp_rw [hin]
  have hg : BstLean.Part162.gmom 80 ≤ (80 : ℝ) ^ 40 := by
    have := BstLean.Part162.gmom_even_le 40; norm_num at this ⊢; exact this
  have hg0 := BstLean.Part162.gmom_nonneg 80
  calc ∫⁻ ξ₁, ENNReal.ofReal (BstLean.Part162.gmom 80 * L11 ξ₁ ^ 40) ∂stdGauss (Fin m)
      = ENNReal.ofReal (BstLean.Part162.gmom 80) *
          ∫⁻ ξ₁, ENNReal.ofReal (L11 ξ₁ ^ 40) ∂stdGauss (Fin m) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun ξ₁ => ENNReal.ofReal_mul hg0
    _ ≤ ENNReal.ofReal ((80 : ℝ) ^ 40) * ENNReal.ofReal ((m / 2 + 4 * (40 : ℕ) : ℝ) ^ 40) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hg)
          (mgf_L11 (k := 40) (by norm_num) (by push_cast; linarith))
    _ = ENNReal.ofReal ((80 : ℝ) ^ 40 * (m / 2 + 160) ^ 40) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; norm_num

noncomputable def planeEnvelope80 (m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 : ℝ) / 80) * ((m : ℝ) / 2 + 320) + √80 * √((m : ℝ) / 2 + 160)

/-- **`E (λ⁺)^{80} ≤ planeEnvelope80(m)^{80}`** (`m ≥ 16 000`). -/
theorem plane_eigenmoment80 (hm : (16000 : ℝ) ≤ m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (planeEnvelope80 m ^ 80) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (m : ℝ) / 2 + 320 := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = (m : ℝ) / 2 + 160 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 : ℝ) ^ ((1 : ℝ) / 80) * M := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = √80 * √M' := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  have hM'0 : 0 < M' := by rw [hM']; positivity
  have hA0 : 0 < A := by rw [hA]; positivity
  have hB0 : 0 < B := by rw [hB]; positivity
  have hA80 : A ^ 80 = 2 * M ^ 80 := by
    rw [hA, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 80)), ← Real.rpow_mul (by norm_num)]
    norm_num
  have hB80 : B ^ 80 = (80 : ℝ) ^ 40 * M' ^ 40 := by
    rw [hB, mul_pow, show (80 : ℕ) = 2 * 40 by norm_num, pow_mul (√M'), Real.sq_sqrt hM'0.le]
    rw [pow_mul (√(80 : ℝ)), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 80)]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = A + B := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  have hBL : planeEnvelope80 m = T := by rw [hT, hA, hB, hM, hM']; rfl
  obtain ⟨c₁, hc1⟩ : ∃ c : ℝ, c = T ^ 79 / A ^ 79 := ⟨_, rfl⟩
  obtain ⟨c₂, hc2⟩ : ∃ c : ℝ, c = T ^ 79 / B ^ 79 := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := by rw [hc1]; positivity
  have hc₂ : 0 ≤ c₂ := by rw [hc2]; positivity
  have hpt : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (L11 ξ₁ ^ 80) +
        ENNReal.ofReal c₁ * ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 80) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80) := by
    intro ξ₁ ξ₂
    have p1 : 0 ≤ c₁ * L11 ξ₁ ^ 80 := mul_nonneg hc₁ (pow_nonneg (L11_nonneg ξ₁) 80)
    have p2 : 0 ≤ c₁ * L22 ξ₁ ξ₂ ^ 80 := mul_nonneg hc₁ (pow_nonneg (L22_nonneg ξ₁ ξ₂) 80)
    have p3 : 0 ≤ c₂ * |L12 ξ₁ ξ₂| ^ 80 := mul_nonneg hc₂ (pow_nonneg (abs_nonneg _) 80)
    rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
      ← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ max (L11 ξ₁) (L22 ξ₁ ξ₂) := (L11_nonneg ξ₁).trans (le_max_left _ _)
    have h1 := pow_add_split h0 (abs_nonneg (L12 ξ₁ ξ₂)) hA0 hB0 79
    rw [← hT] at h1
    have h2 : max (L11 ξ₁) (L22 ξ₁ ξ₂) ^ 80 ≤ L11 ξ₁ ^ 80 + L22 ξ₁ ξ₂ ^ 80 := by
      rcases le_total (L11 ξ₁) (L22 ξ₁ ξ₂) with h | h
      · rw [max_eq_right h]; have := pow_nonneg (L11_nonneg ξ₁) 80; linarith
      · rw [max_eq_left h]; have := pow_nonneg (L22_nonneg ξ₁ ξ₂) 80; linarith
    unfold lamP
    refine h1.trans ?_
    have e : T ^ 79 * (max (L11 ξ₁) (L22 ξ₁ ξ₂) ^ 80 / A ^ 79 + |L12 ξ₁ ξ₂| ^ 80 / B ^ 79) =
        c₁ * max (L11 ξ₁) (L22 ξ₁ ξ₂) ^ 80 + c₂ * |L12 ξ₁ ξ₂| ^ 80 := by
      rw [hc1, hc2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h2 hc₁
    linarith
  have hm11 : ∀ ξ₁ : Fin m → ℝ, Measurable (fun ξ₂ : Fin m → ℝ => ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 80)) :=
    fun ξ₁ => ENNReal.measurable_ofReal.comp ((measurable_L22.comp
      (measurable_const.prodMk measurable_id)).pow_const 80)
  have hm12 : ∀ ξ₁ : Fin m → ℝ, Measurable (fun ξ₂ : Fin m → ℝ =>
      ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80)) :=
    fun ξ₁ => ENNReal.measurable_ofReal.comp ((measurable_L12.comp
      (measurable_const.prodMk measurable_id)).abs.pow_const 80)
  have hinner : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (L11 ξ₁ ^ 80) +
        ENNReal.ofReal c₁ * ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 80) ∂stdGauss (Fin m) +
        ENNReal.ofReal c₂ * ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80) ∂stdGauss (Fin m) := by
    intro ξ₁
    refine (lintegral_mono (hpt ξ₁)).trans (le_of_eq ?_)
    rw [lintegral_add_right _ ((hm12 ξ₁).const_mul _),
      lintegral_add_right _ ((hm11 ξ₁).const_mul _), lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (hm11 ξ₁), lintegral_const_mul _ (hm12 ξ₁)]
  have hmo1 : Measurable (fun ξ₁ : Fin m → ℝ => ENNReal.ofReal (L11 ξ₁ ^ 80)) :=
    ENNReal.measurable_ofReal.comp (measurable_L11.pow_const 80)
  have hmo2 : Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 80) ∂stdGauss (Fin m)) :=
    (ENNReal.measurable_ofReal.comp (measurable_L22.pow_const 80)).lintegral_prod_right'
  have hmo3 : Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80) ∂stdGauss (Fin m)) :=
    (ENNReal.measurable_ofReal.comp (measurable_L12.abs.pow_const 80)).lintegral_prod_right'
  refine (lintegral_mono hinner).trans ?_
  rw [lintegral_add_right _ (hmo3.const_mul _), lintegral_add_right _ (hmo2.const_mul _),
    lintegral_const_mul _ hmo1, lintegral_const_mul _ hmo2, lintegral_const_mul _ hmo3]
  have b1 := mgf_L11 (m := m) (k := 80) (by norm_num) (by push_cast; linarith)
  have b2 := mgf_L22 (m := m) (k := 80) (by norm_num) (by push_cast; linarith)
  have b3 := plane_cross_moment80 (m := m) (by linarith)
  have e4 : ((m : ℝ) / 2 + 4 * (80 : ℕ)) = M := by rw [hM]; norm_num
  rw [e4] at b1 b2
  rw [← hM'] at b3
  have q1 : 0 ≤ c₁ * (M ^ 80) := mul_nonneg hc₁ (pow_nonneg hM0.le 80)
  have q3 : 0 ≤ c₂ * ((80 : ℝ) ^ 40 * M' ^ 40) :=
    mul_nonneg hc₂ (mul_nonneg (by norm_num) (pow_nonneg hM'0.le 40))
  calc ENNReal.ofReal c₁ * ∫⁻ ξ₁, ENNReal.ofReal (L11 ξ₁ ^ 80) ∂stdGauss (Fin m) +
        ENNReal.ofReal c₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 80) ∂stdGauss (Fin m)
          ∂stdGauss (Fin m) +
        ENNReal.ofReal c₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 80) ∂stdGauss (Fin m)
          ∂stdGauss (Fin m)
      ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (M ^ 80) + ENNReal.ofReal c₁ * ENNReal.ofReal (M ^ 80) +
          ENNReal.ofReal c₂ * ENNReal.ofReal ((80 : ℝ) ^ 40 * M' ^ 40) := by
        gcongr
    _ = ENNReal.ofReal (c₁ * M ^ 80 + c₁ * M ^ 80 + c₂ * ((80 : ℝ) ^ 40 * M' ^ 40)) := by
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
          ← ENNReal.ofReal_add q1 q1, ← ENNReal.ofReal_add (add_nonneg q1 q1) q3]
    _ = ENNReal.ofReal (planeEnvelope80 m ^ 80) := by
        congr 1
        have k1 : c₁ * M ^ 80 + c₁ * M ^ 80 = c₁ * A ^ 80 := by rw [hA80]; ring
        rw [k1, ← hB80, hBL, hc1, hc2, pow_succ A 79, pow_succ B 79, ← mul_assoc, ← mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero _ hA0.ne'), div_mul_cancel₀ _ (pow_ne_zero _ hB0.ne'),
          ← mul_add, ← hT, ← pow_succ]

end BstLean.Part212
