import BstLean.Part143HidK1

/-!
# Part 143, helper `hidK`: sharper means of `errK`, `errD`, and the probability of `good136`

`θ = (M₁, M₂)`, `h(u) = hid2 M₁ M₂ u`, scale `s = m/N` (Part 136).

* `fD_point`: for a unit `u`: `E_θ (|h(u)|² − s)² ≤ s²·(10 + 25/m)/m`.
* `fK_point`: for unit `u, u′`, `t = ⟨u, u′⟩`:
  `E_θ (⟨h(u), h(u′)⟩ − s·κ(κ(t)))² ≤ s²·KB m t/m`.
* `errD_mean143`: `E_θ errD ≤ s²·cD143 m/m`; `errK_mean143`: `E_θ errK ≤ s²·cK143 N m/m`.
* `good136_prob143`: `Pr((good136 n)ᶜ) ≤ P143 = 0.000775` for `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136

variable {N m : ℕ}

/-- The constant of the diagonal: `E_θ errD ≤ (m/N)²·cD143 m/m`. -/
noncomputable def cD143 (m : ℕ) : ℝ := 10 + 25 / (m : ℝ)

/-- The pointwise constant of the kernel, `t = ⟨u, u′⟩`. -/
noncomputable def KB (m : ℕ) (t : ℝ) : ℝ :=
  2 * (1 + 5 / (m : ℝ)) + 4 * kappa t ^ 2 + (8 + 16 * t ^ 2) / (m : ℝ) +
    (√10 * kappa 0 + √(2 + 4 * t ^ 2)) ^ 2

/-- The constant of the kernel: `E_θ errK ≤ (m/N)²·cK143 N m/m`. -/
noncomputable def cK143 (N m : ℕ) : ℝ :=
  2 * (1 + 5 / (m : ℝ)) + 4 * (kappa 0 ^ 2 + 2 * kappa 0 / √(N : ℝ) + 1 / (N : ℝ)) +
    (8 + 16 / (N : ℝ)) / (m : ℝ) + (√10 * kappa 0 + √2) ^ 2 +
    (2 * √2 * (√10 * kappa 0 + √2) + 2) / (N : ℝ)

/-- **The diagonal at a fixed unit input.** -/
theorem fD_point (hN : 1 ≤ N) (hm : 1 ≤ m) {u : Fin N → ℝ} (hu : normSq u = 1) :
    Integrable (fun θ : HidParam N m => fD N m (u, θ) ^ 2) (hidGauss N m) ∧
      ∫ θ, fD N m (u, θ) ^ 2 ∂hidGauss N m ≤ ((m : ℝ) / N) ^ 2 * cD143 m / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h₁ : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have h₂ : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hsm : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm'.le
  have hs5 : √(5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs1 : √(1 + 5 / (m : ℝ)) ^ 2 = 1 + 5 / (m : ℝ) := Real.sq_sqrt (by positivity)
  have mN : ∀ y : Fin N → ℝ, Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      normSq (reluV (M₁.mulVec y))) := fun y =>
    measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right y))
  have mR : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      normSq (hid2 θ.1 θ.2 u) -
        (m : ℝ) / 2 * (2 / (m : ℝ) * normSq (reluV (θ.1.mulVec u)))) :=
    (continuous_normSq.comp (continuous_hid2_param u)).measurable.sub
      ((((mN u).comp measurable_fst).const_mul _).const_mul _)
  -- the part that reads `M₁` only
  obtain ⟨iV, eV⟩ := layer_relu_sq_var (m := m) h₁ u
  rw [hu, mul_one] at iV eV
  have hB0 : L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      normSq (reluV (M₁.mulVec u)) - (m : ℝ) / 2 * (2 / (N : ℝ)))
      (√5 / √(m : ℝ) * ((m : ℝ) / 2 * (2 / (N : ℝ)))) := by
    refine L2le.mk' ((mN u).sub measurable_const).aestronglyMeasurable iV (le_of_eq ?_)
    rw [eV]
    simp only [mul_pow, div_pow, hs5, hsm]
    field_simp
    norm_num
  have hB := hB0.const_mul_nonneg hc2
  -- the bound of the conditional second moment
  obtain ⟨i4, e4⟩ := layer_relu_four (m := m) h₁ u
  rw [hu, mul_one] at e4
  have hg0 : L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      normSq (reluV (M₁.mulVec u))) (√(1 + 5 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (N : ℝ)))) := by
    refine L2le.mk' (mN u).aestronglyMeasurable i4 (le_of_eq ?_)
    rw [e4]
    simp only [mul_pow, div_pow, hs1]
    field_simp
    ring
  have hg := (hg0.const_mul_nonneg hc2).const_mul_nonneg
    (show (0 : ℝ) ≤ √5 / √(m : ℝ) by positivity)
  have key := L2le.prod_orth (ν := gaussMat m m (2 / (m : ℝ))) mR.aestronglyMeasurable hB hg
    (fun M₁ => by
      obtain ⟨iD, eD⟩ := layer_relu_sq (m := m) h₂ (reluV (M₁.mulVec u))
      obtain ⟨iC, eC⟩ := layer_relu_sq_var (m := m) h₂ (reluV (M₁.mulVec u))
      have iR : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ =>
          normSq (reluV (M₂.mulVec (reluV (M₁.mulVec u)))) -
            (m : ℝ) / 2 * (2 / (m : ℝ) * normSq (reluV (M₁.mulVec u))))
          (gaussMat m m (2 / (m : ℝ))) := iD.sub (integrable_const _)
      refine ⟨iR, ?_, iC, le_of_eq ?_⟩
      · have := integral_sub iD (integrable_const ((m : ℝ) / 2 * (2 / (m : ℝ) *
          normSq (reluV (M₁.mulVec u)))))
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
        rw [eD, sub_self] at this
        exact this
      · change ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (normSq (reluV (M₂.mulVec (reluV (M₁.mulVec u)))) -
          (m : ℝ) / 2 * (2 / (m : ℝ) * normSq (reluV (M₁.mulVec u)))) ^ 2
            ∂gaussMat m m (2 / (m : ℝ)) = _
        rw [eC]
        simp only [mul_pow, div_pow, hs5, hsm]
        field_simp
        ring)
  have key2 := key.congr_fun (g := fun θ : HidParam N m => fD N m (u, θ)) (fun θ => by
    simp only [fD]
    field_simp
    ring)
  refine ⟨key2.int_sq, key2.le.trans (le_of_eq ?_)⟩
  rw [Real.sq_sqrt (by positivity)]
  simp only [mul_pow, div_pow, hs5, hsm, hs1]
  unfold cD143
  field_simp
  ring

/-- **The Gram kernel at fixed unit inputs.** -/
theorem fK_point (hN : 1 ≤ N) (hm : 1 ≤ m) {u u' : Fin N → ℝ} (hu : normSq u = 1)
    (hu' : normSq u' = 1) :
    Integrable (fun θ : HidParam N m => fK N m ((u, u'), θ) ^ 2) (hidGauss N m) ∧
      ∫ θ, fK N m ((u, u'), θ) ^ 2 ∂hidGauss N m ≤
        ((m : ℝ) / N) ^ 2 * KB m (dotp u u') / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h₁ : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have h₂ : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hsm : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm'.le
  have hs1 : √(1 + 5 / (m : ℝ)) ^ 2 = 1 + 5 / (m : ℝ) := Real.sq_sqrt (by positivity)
  set t : ℝ := dotp u u' with ht
  have hst : √(2 + 4 * t ^ 2) ^ 2 = 2 + 4 * t ^ 2 := Real.sq_sqrt (by positivity)
  set c₁ : ℝ := (m : ℝ) / 2 * (2 / (N : ℝ)) with hc₁
  have mN : ∀ y : Fin N → ℝ, Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      normSq (reluV (M₁.mulVec y))) := fun y =>
    measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right y))
  have mD : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u'))) :=
    measurable_dotp_comp (measurable_reluV.comp (measurable_mulVec_right u))
      (measurable_reluV.comp (measurable_mulVec_right u'))
  have mR : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
        (m : ℝ) / 2 * (2 / (m : ℝ) *
          kernelPhi (reluV (θ.1.mulVec u)) (reluV (θ.1.mulVec u')))) :=
    (continuous_dotp.comp ((continuous_hid2_param u).prodMk
      (continuous_hid2_param u'))).measurable.sub
      ((((measurable_psi_relu continuous_kappa u u').comp measurable_fst).const_mul _).const_mul _)
  -- the part that reads `M₁` only
  have hB := (relu_layer_unit_L2 (m := m) h₁ hm hu hu').const_mul_nonneg hc2
  rw [← ht, ← hc₁] at hB
  -- the bound of the conditional second moment
  set G : Matrix (Fin m) (Fin N) ℝ → ℝ := fun M₁ =>
    (m : ℝ) * ((2 / (m : ℝ)) ^ 2 * (normSq (reluV (M₁.mulVec u)) * normSq (reluV (M₁.mulVec u')) +
      2 * dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) ^ 2) / 2) with hG
  have mG : Measurable G :=
    (((((mN u).mul (mN u')).add ((mD.pow_const 2).const_mul 2)).const_mul _).div_const 2).const_mul _
  have hG0 : ∀ M₁, 0 ≤ G M₁ := fun M₁ => by
    have := normSq_nonneg (reluV (M₁.mulVec u))
    have := normSq_nonneg (reluV (M₁.mulVec u'))
    simp only [hG]
    positivity
  -- `E |h₁|²|h₁′|²`
  have hP := relu_nrm_L2 (m := m) h₁ hm u u'
  rw [nrm_of_normSq_one hu, nrm_of_normSq_one hu', mul_one, mul_one, ← hc₁] at hP
  have eP : (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      (nrm (reluV (M₁.mulVec u)) * nrm (reluV (M₁.mulVec u'))) ^ 2) =
      fun M₁ => normSq (reluV (M₁.mulVec u)) * normSq (reluV (M₁.mulVec u')) := by
    funext M₁; rw [mul_pow, nrm_sq, nrm_sq]
  have iP := hP.int_sq
  have uP := hP.le
  rw [eP] at iP
  simp only [eP] at uP
  rw [mul_pow, hs1] at uP
  -- `E ⟨h₁, h₁′⟩²`
  have hC := relu_dot_unit_L2 (m := m) h₁ hm hu hu'
  rw [← ht, ← hc₁] at hC
  obtain ⟨iD1, eD1⟩ := layer_dot_relu (m := m) h₁ u u'
  rw [kernelPhi_eq_psi, psi_unit _ hu hu', ← ht] at eD1
  have eD1' : ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u'))
      ∂gaussMat m N (2 / (N : ℝ)) = c₁ * kappa t := by rw [eD1, hc₁]; ring
  have eDD : (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) ^ 2) =
      fun M₁ => (dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) - c₁ * kappa t) ^ 2 +
        (2 * (c₁ * kappa t) * dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) -
          (c₁ * kappa t) ^ 2) := by
    funext M₁; ring
  have iD2' : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      2 * (c₁ * kappa t) * dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) -
        (c₁ * kappa t) ^ 2) (gaussMat m N (2 / (N : ℝ))) :=
    (iD1.const_mul _).sub (integrable_const _)
  have iDD : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) ^ 2) (gaussMat m N (2 / (N : ℝ))) := by
    rw [eDD]; exact hC.int_sq.add iD2'
  have uDD : ∫ M₁ : Matrix (Fin m) (Fin N) ℝ,
      dotp (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) ^ 2 ∂gaussMat m N (2 / (N : ℝ)) ≤
      (2 + 4 * t ^ 2) / (m : ℝ) * c₁ ^ 2 + (c₁ * kappa t) ^ 2 := by
    rw [eDD, integral_add hC.int_sq iD2', integral_sub (iD1.const_mul _) (integrable_const _),
      integral_const_mul, eD1', integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have := hC.le
    rw [mul_pow, div_pow, hst, hsm] at this
    linarith
  have iG : Integrable G (gaussMat m N (2 / (N : ℝ))) :=
    (((iP.add (iDD.const_mul 2)).const_mul _).div_const 2).const_mul _
  have uG : ∫ M₁, G M₁ ∂gaussMat m N (2 / (N : ℝ)) ≤
      (m : ℝ) * ((2 / (m : ℝ)) ^ 2 * ((1 + 5 / (m : ℝ)) * c₁ ^ 2 +
        2 * ((2 + 4 * t ^ 2) / (m : ℝ) * c₁ ^ 2 + (c₁ * kappa t) ^ 2)) / 2) := by
    simp only [hG]
    rw [integral_const_mul, integral_div, integral_const_mul,
      integral_add iP (iDD.const_mul 2), integral_const_mul]
    have h3 : (0 : ℝ) ≤ (2 / (m : ℝ)) ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left (add_le_add uP (mul_le_mul_of_nonneg_left uDD
      (by norm_num : (0 : ℝ) ≤ 2))) h3
    exact mul_le_mul_of_nonneg_left (by linarith) hm'.le
  have hg : L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => √(G M₁))
      (√((m : ℝ) * ((2 / (m : ℝ)) ^ 2 * ((1 + 5 / (m : ℝ)) * c₁ ^ 2 +
        2 * ((2 + 4 * t ^ 2) / (m : ℝ) * c₁ ^ 2 + (c₁ * kappa t) ^ 2)) / 2))) := by
    refine L2le.of_sq_le mG.sqrt.aestronglyMeasurable iG
      (fun M₁ => le_of_eq (Real.sq_sqrt (hG0 M₁))) ?_
    rw [Real.sq_sqrt ((integral_nonneg hG0).trans uG)]
    exact uG
  have key := L2le.prod_orth (ν := gaussMat m m (2 / (m : ℝ))) mR.aestronglyMeasurable hB hg
    (fun M₁ => by
      obtain ⟨iD, eD⟩ := layer_dot_relu (m := m) h₂ (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u'))
      obtain ⟨iC, uC⟩ := layer_dot_relu_var143 (m := m) h₂ (reluV (M₁.mulVec u))
        (reluV (M₁.mulVec u'))
      have iR : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ =>
          dotp (reluV (M₂.mulVec (reluV (M₁.mulVec u)))) (reluV (M₂.mulVec (reluV (M₁.mulVec u')))) -
            (m : ℝ) / 2 * (2 / (m : ℝ) *
              kernelPhi (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u'))))
          (gaussMat m m (2 / (m : ℝ))) := iD.sub (integrable_const _)
      refine ⟨iR, ?_, iC, ?_⟩
      · have := integral_sub iD (integrable_const ((m : ℝ) / 2 * (2 / (m : ℝ) *
          kernelPhi (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')))))
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
        rw [eD, sub_self] at this
        exact this
      · rw [Real.sq_sqrt (hG0 M₁)]
        refine uC.trans ?_
        simp only [hG]
        refine mul_le_mul_of_nonneg_left ?_ hm'.le
        have := sq_nonneg (2 / (m : ℝ) *
          kernelPhi (reluV (M₁.mulVec u)) (reluV (M₁.mulVec u')) / 2)
        linarith)
  have hc21 : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have hc1N : c₁ = (m : ℝ) / N := by rw [hc₁]; field_simp
  have key2 := key.congr_fun (g := fun θ : HidParam N m => fK N m ((u, u'), θ)) (fun θ => by
    simp only [fK, kernelPhi_eq_psi]
    rw [hc21, ← mul_assoc, hc21, hc1N]
    ring)
  refine ⟨key2.int_sq, key2.le.trans (le_of_eq ?_)⟩
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hc21, hc1N]
  simp only [mul_pow, div_pow, one_mul]
  unfold KB
  rw [hsm]
  field_simp
  ring

/-! ## The mean over the inputs -/

theorem errD_mean143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (errD (N := N) (m := m)) (hidGauss N m) ∧
      ∫ θ, errD θ ∂hidGauss N m ≤ ((m : ℝ) / N) ^ 2 * cD143 m / m := by
  have := uniformSphere_isProbability N hN
  have h := fD_L2 hN hm
  refine ⟨(errD_mean hN hm).1, ?_⟩
  have e := integral_prod_symm _ h.int_sq
  have e' := integral_prod _ h.int_sq
  unfold errD
  rw [← e, e']
  have hmono := integral_mono_ae h.int_sq.integral_prod_left
    (integrable_const (((m : ℝ) / N) ^ 2 * cD143 m / m)) (by
      filter_upwards [uniformSphere_ae_sphere N] with u hu0
      exact (fD_point hN hm hu0).2)
  simpa using hmono

/-- The constant part of the bound of `KB m t`. -/
noncomputable def CK (N m : ℕ) : ℝ :=
  2 * (1 + 5 / (m : ℝ)) + 4 * kappa 0 ^ 2 + 4 * kappa 0 / √(N : ℝ) + 8 / (m : ℝ) +
    (√10 * kappa 0 + √2) ^ 2

/-- The coefficient of `t²` in the bound of `KB m t`. -/
noncomputable def EK (N m : ℕ) : ℝ :=
  4 * kappa 0 * √(N : ℝ) + 4 + 16 / (m : ℝ) + 2 * √2 * (√10 * kappa 0 + √2) + 2

lemma KB_le (hN : 1 ≤ N) (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    KB m t ≤ CK N m + EK N m * t ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN'
  have hx0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ √(10 : ℝ) := Real.sqrt_nonneg _
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have ht20 : 0 ≤ t ^ 2 := sq_nonneg t
  have hk0 := (kappa_mem ht.1 ht.2).1
  -- `κ(t) ≤ κ(0) + |t|`
  have hk1 : kappa t ≤ kappa 0 + |t| := by
    rcases le_total 0 t with h0 | h0
    · have := (kappa_lipschitz (by norm_num : (-1 : ℝ) ≤ 0) h0 ht.2).2
      rw [abs_of_nonneg h0]; linarith
    · have := (kappa_lipschitz ht.1 h0 (by norm_num : (0 : ℝ) ≤ 1)).1
      have := abs_nonneg t
      linarith
  have hk2 : kappa t ^ 2 ≤ kappa 0 ^ 2 + 2 * kappa 0 * |t| + t ^ 2 := by
    have := pow_le_pow_left₀ hk0 hk1 2
    have e : (kappa 0 + |t|) ^ 2 = kappa 0 ^ 2 + 2 * kappa 0 * |t| + t ^ 2 := by
      rw [← sq_abs t]; ring
    linarith
  -- `2|t| ≤ √N·t² + 1/√N`
  have habs : 2 * |t| ≤ √(N : ℝ) * t ^ 2 + 1 / √(N : ℝ) := by
    have e : √(N : ℝ) * t ^ 2 + 1 / √(N : ℝ) - 2 * |t| = (√(N : ℝ) * |t| - 1) ^ 2 / √(N : ℝ) := by
      rw [← sq_abs t]
      field_simp
      ring
    have : 0 ≤ (√(N : ℝ) * |t| - 1) ^ 2 / √(N : ℝ) := by positivity
    linarith
  have habs' := mul_le_mul_of_nonneg_left habs (by positivity : (0 : ℝ) ≤ 4 * kappa 0)
  -- `√(2 + 4t²) ≤ √2 + √2·t²`
  have hsq : √(2 + 4 * t ^ 2) ≤ √2 + √2 * t ^ 2 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : (√2 + √2 * t ^ 2) ^ 2 = √(2 : ℝ) ^ 2 * (1 + t ^ 2) ^ 2 := by ring
    rw [e, h2]
    nlinarith [sq_nonneg (t ^ 2)]
  have hq : (√10 * kappa 0 + √(2 + 4 * t ^ 2)) ^ 2 ≤
      (√10 * kappa 0 + √2) ^ 2 + (2 * √2 * (√10 * kappa 0 + √2) + 2) * t ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ √10 * kappa 0 + √(2 + 4 * t ^ 2))
      (by linarith : √10 * kappa 0 + √(2 + 4 * t ^ 2) ≤ √10 * kappa 0 + √2 + √2 * t ^ 2) 2
    have e : (√10 * kappa 0 + √2 + √2 * t ^ 2) ^ 2 = (√10 * kappa 0 + √2) ^ 2 +
        2 * √2 * (√10 * kappa 0 + √2) * t ^ 2 + √(2 : ℝ) ^ 2 * (t ^ 2) ^ 2 := by ring
    rw [e, h2] at h1
    have h4 : (t ^ 2) ^ 2 ≤ t ^ 2 := by nlinarith
    linarith
  have e16 : (8 + 16 * t ^ 2) / (m : ℝ) = 8 / (m : ℝ) + 16 / (m : ℝ) * t ^ 2 := by ring
  have e4 : 4 * kappa 0 * (√(N : ℝ) * t ^ 2 + 1 / √(N : ℝ)) =
      4 * kappa 0 * √(N : ℝ) * t ^ 2 + 4 * kappa 0 / √(N : ℝ) := by ring
  unfold KB CK EK
  rw [e16]
  rw [e4] at habs'
  have e5 : (4 * kappa 0 * √(N : ℝ) + 4 + 16 / (m : ℝ) + 2 * √2 * (√10 * kappa 0 + √2) + 2) *
      t ^ 2 = 4 * kappa 0 * √(N : ℝ) * t ^ 2 + 4 * t ^ 2 + 16 / (m : ℝ) * t ^ 2 +
        (2 * √2 * (√10 * kappa 0 + √2) + 2) * t ^ 2 := by ring
  rw [e5]
  linarith

lemma CK_EK (hN : 1 ≤ N) : CK N m + EK N m * (1 / (N : ℝ)) = cK143 N m := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN'
  have e : √(N : ℝ) * (1 / (N : ℝ)) = 1 / √(N : ℝ) := by
    have hsm : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hN'.le
    field_simp
    exact hsm
  have e2 : EK N m * (1 / (N : ℝ)) = 4 * kappa 0 * (√(N : ℝ) * (1 / (N : ℝ))) +
      (4 + 16 / (m : ℝ) + 2 * √2 * (√10 * kappa 0 + √2) + 2) * (1 / (N : ℝ)) := by
    unfold EK; ring
  rw [e2, e]
  unfold CK cK143
  ring

theorem errK_mean143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (errK (N := N) (m := m)) (hidGauss N m) ∧
      ∫ θ, errK θ ∂hidGauss N m ≤ ((m : ℝ) / N) ^ 2 * cK143 N m / m := by
  have := lawU2_prob hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := fK_L2 hN hm
  obtain ⟨iT, eT⟩ := lawU2_dot_sq hN
  refine ⟨(errK_mean hN hm).1, ?_⟩
  have e := integral_prod_symm _ h.int_sq
  have e' := integral_prod _ h.int_sq
  unfold errK
  rw [← e, e']
  have iL : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      ((m : ℝ) / N) ^ 2 * (CK N m + EK N m * dotp uu.1 uu.2 ^ 2) / m) (lawU2 N) :=
    (((integrable_const _).add (iT.const_mul _)).const_mul _).div_const _
  have hmono := integral_mono_ae h.int_sq.integral_prod_left iL (by
    filter_upwards [lawU2_ae_unit hN] with uu huu
    refine (fK_point hN hm huu.1 huu.2).2.trans ?_
    have hk := KB_le hN hm (unit_dot_mem huu.1 huu.2)
    have h0 : (0 : ℝ) ≤ ((m : ℝ) / N) ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk h0) hm'.le)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_div, integral_const_mul, integral_add (integrable_const _) (iT.const_mul _),
    integral_const_mul, eT, integral_const, probReal_univ, one_smul, CK_EK hN]

/-! ## The numbers at the widths of the Focus -/

lemma num_K {x a b c im iN is : ℝ} (hx1 : 318309 / 1000000 ≤ x) (hx2 : x ≤ 31831 / 100000)
    (ha0 : 0 ≤ a) (ha : a ≤ 31623 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 141422 / 100000)
    (hc : 24494 / 10000 ≤ c) (him0 : 0 ≤ im) (him : im ≤ 1 / 1000000) (hiN0 : 0 ≤ iN)
    (hiN : iN ≤ 1 / 8192) (his0 : 0 ≤ is) (his : is ≤ 1 / 90) :
    2 * (1 + 5 * im) + 4 * (x ^ 2 + 2 * x * is + iN) + (8 + 16 * iN) * im + (a * x + b) ^ 2 +
      (2 * b * (a * x + b) + 2) * iN ≤ 372 / 1000 * (6 * (1 + 5 * im) + (5 * x + c) ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : a * x ≤ 31623 / 10000 * (31831 / 100000) := mul_le_mul ha hx2 hx0 (by norm_num)
  have hT0 : 0 ≤ a * x + b := by positivity
  have hTu : a * x + b ≤ 31623 / 10000 * (31831 / 100000) + 141422 / 100000 := by linarith
  have hT2 := pow_le_pow_left₀ hT0 hTu 2
  have hbT : b * (a * x + b) ≤
      141422 / 100000 * (31623 / 10000 * (31831 / 100000) + 141422 / 100000) :=
    mul_le_mul hb hTu hT0 (by norm_num)
  have h3 : (2 * b * (a * x + b) + 2) * iN ≤
      (2 * (141422 / 100000 * (31623 / 10000 * (31831 / 100000) + 141422 / 100000)) + 2) *
        (1 / 8192) := mul_le_mul (by linarith) hiN hiN0 (by norm_num)
  have hx22 := pow_le_pow_left₀ hx0 hx2 2
  have hxs : x * is ≤ 31831 / 100000 * (1 / 90) := mul_le_mul hx2 his his0 (by norm_num)
  have hNm : iN * im ≤ 1 / 8192 * (1 / 1000000) := mul_le_mul hiN him him0 (by norm_num)
  have hL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 * (318309 / 1000000) + 24494 / 10000)
    (by linarith : 5 * (318309 / 1000000) + 24494 / 10000 ≤ 5 * x + c) 2
  norm_num at hT2 h3 hx22 hxs hNm hL
  nlinarith [hT2, h3, hx22, hxs, hNm, hL]

lemma consts_bounds :
    0 ≤ √(10 : ℝ) ∧ √(10 : ℝ) ≤ 31623 / 10000 ∧ 0 ≤ √(2 : ℝ) ∧ √(2 : ℝ) ≤ 141422 / 100000 ∧
      24494 / 10000 ≤ √(6 : ℝ) :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩, Real.sqrt_nonneg _,
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩, Real.le_sqrt' (by norm_num) |>.mpr (by norm_num)⟩

/-- `cK143 N m ≤ 0.372·m·cF2o m²` for `N ≥ 8192`, `m ≥ 10⁶`. -/
lemma cK143_le (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    cK143 N m ≤ 372 / 1000 * (6 * (1 + 5 / (m : ℝ)) + (5 * kappa 0 + √6) ^ 2) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (8192 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨ha0, ha, hb0, hb, hc⟩ := consts_bounds
  have hs : (90 : ℝ) ≤ √(N : ℝ) := Real.le_sqrt' (by norm_num) |>.mpr (by linarith)
  have him : 1 / (m : ℝ) ≤ 1 / 1000000 := one_div_le_one_div_of_le (by norm_num) hm'
  have hiN : 1 / (N : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hN'
  have his : 1 / √(N : ℝ) ≤ 1 / 90 := one_div_le_one_div_of_le (by norm_num) hs
  have key := num_K kappa_zero_ge kappa_zero_le ha0 ha hb0 hb hc
    (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)) him (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)) hiN
    (by positivity : (0 : ℝ) ≤ 1 / √(N : ℝ)) his
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · unfold cK143; ring
  · ring

/-- `cD143 m ≤ 0.448·m·cF2o m²` for `m ≥ 10⁶`. -/
lemma cD143_le (hm : 1000000 ≤ m) :
    cD143 m ≤ 448 / 1000 * (6 * (1 + 5 / (m : ℝ)) + (5 * kappa 0 + √6) ^ 2) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨-, -, -, -, hc⟩ := consts_bounds
  have him : 1 / (m : ℝ) ≤ 1 / 1000000 := one_div_le_one_div_of_le (by norm_num) hm'
  have him0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hx1 := kappa_zero_ge
  have hL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 * (318309 / 1000000) + 24494 / 10000)
    (by linarith : 5 * (318309 / 1000000) + 24494 / 10000 ≤ 5 * kappa 0 + √6) 2
  have e : cD143 m = 10 + 25 * (1 / (m : ℝ)) := by unfold cD143; ring
  have e2 : (5 : ℝ) / m = 5 * (1 / (m : ℝ)) := by ring
  rw [e, e2]
  norm_num at hL
  nlinarith [hL]

/-- The bound of the probability of the complement of `good136`. -/
noncomputable def P143 : ℝ := 775 / 1000000

/-- **The probability of the good event, sharper**: `Pr((good136 n)ᶜ) ≤ 0.000775`. -/
theorem good136_prob143 {n : ℕ} (hn : 4096 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (good136 n)ᶜ ≤ P143 := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hN8 : 8192 ≤ 2 * n := by omega
  have hm' : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hN' : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast hN
  have hc := cF2o_pos hm
  have hcF : cF2o (mW n) ^ 2 =
      (6 * (1 + 5 / (mW n : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (mW n : ℝ) := by
    unfold cF2o
    rw [Real.sq_sqrt (by positivity)]
    ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((mW n : ℝ) / ((2 * n : ℕ) : ℝ) * cF2o (mW n)) ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have h2 : 0 ≤ ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) := by positivity
  obtain ⟨iK, eK⟩ := errK_mean143 (m := mW n) hN hm
  obtain ⟨iD, eD⟩ := errD_mean143 (m := mW n) hN hm
  have eK' : ∫ θ, errK θ ∂hidGauss (2 * n) (mW n) ≤ 372 / 1000 * B := by
    refine eK.trans ?_
    rw [hB, mul_pow, hcF]
    have := mul_le_mul_of_nonneg_left (cK143_le hN8 hmM) h2
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring
  have eD' : ∫ θ, errD θ ∂hidGauss (2 * n) (mW n) ≤ 448 / 1000 * B := by
    refine eD.trans ?_
    rw [hB, mul_pow, hcF]
    have := mul_le_mul_of_nonneg_left (cD143_le hmM) h2
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring
  have m1 := markov_ge (hidGauss (2 * n) (mW n)) errK_nonneg iK
    (B := 372 / 1000 * B) (p := 372 / 1000 * (4 / 100) ^ 2) (by positivity) (by norm_num) eK'
  have m2 := markov_ge (hidGauss (2 * n) (mW n)) errD_nonneg iD
    (B := 448 / 1000 * B) (p := 448 / 1000 * (4 / 10000)) (by positivity) (by norm_num) eD'
  have e1 : 372 / 1000 * B / (372 / 1000 * (4 / 100) ^ 2) = B / (4 / 100) ^ 2 :=
    mul_div_mul_left _ _ (by norm_num)
  have e2 : 448 / 1000 * B / (448 / 1000 * (4 / 10000)) = B / (4 / 10000) :=
    mul_div_mul_left _ _ (by norm_num)
  rw [e1] at m1
  rw [e2] at m2
  have hsub : (good136 n)ᶜ ⊆
      {θ | B / (4 / 100) ^ 2 ≤ errK θ} ∪ {θ | B / (4 / 10000) ≤ errD θ} := by
    intro θ hθ
    simp only [good136, goodHid, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_lt] at hθ
    rw [← hB] at hθ
    exact hθ
  have h3 := (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add m1 m2))
  refine h3.trans ?_
  unfold P143
  norm_num

end BstLean.Part143

open BstLean.Part143 in
#print axioms fD_point
open BstLean.Part143 in
#print axioms fK_point
open BstLean.Part143 in
#print axioms errD_mean143
open BstLean.Part143 in
#print axioms errK_mean143
open BstLean.Part143 in
#print axioms good136_prob143
