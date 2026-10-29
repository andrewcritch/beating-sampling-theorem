import BstLean.Part254GaussianLinear

/-! Actual Gaussian tail bounds for the input windows and pair rows. -/
namespace BstLean.Part254
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part160 BstLean.Part182
open BstLean.Part199
open BstLean.Part153 (nrm)
variable {n : ℕ}

theorem omega_compl_gaussian (hn : 0 < n) (c : Fin n → ℝ) {t0 z0 : ℝ} (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0) :
    (stdGauss (Fin n)).real (OmegaS c t0 z0)ᶜ ≤ gaussianTail t0 + 2 * exp (-z0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hA := linear_gaussian_tail (uC c) one_pos (nrm_uC_le c) ht0
  have hB := chiSq_upper_LM (ι := Fin n) hz0
  have hC := chiSq_lower_LM (ι := Fin n) hz0
  simp only [Fintype.card_fin, one_pow, mul_one] at hA hB hC
  have hsub : (OmegaS c t0 z0)ᶜ ⊆ ({ξ | t0 < |uC c ⬝ᵥ ξ|} ∪
      {ξ : Fin n → ℝ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * z0)}) ∪
      {ξ | (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 ≤ ∑ i, ξ i ^ 2} := by
    intro ξ hξ
    simp only [OmegaS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hξ
    have e : normSq ξ = ∑ i, ξ i ^ 2 := rfl
    rw [e] at hξ
    rcases hξ with h | h | h
    · left; left; exact h
    · left; right; exact h.le
    · right; exact h.le
  calc (stdGauss (Fin n)).real (OmegaS c t0 z0)ᶜ
      ≤ (stdGauss (Fin n)).real (({ξ | t0 < |uC c ⬝ᵥ ξ|} ∪
      {ξ : Fin n → ℝ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * z0)}) ∪
      {ξ | (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 ≤ ∑ i, ξ i ^ 2}) := measureReal_mono hsub
    _ ≤ (stdGauss (Fin n)).real {ξ | t0 < |uC c ⬝ᵥ ξ|} +
        (stdGauss (Fin n)).real {ξ : Fin n → ℝ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * z0)} +
        (stdGauss (Fin n)).real {ξ | (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 ≤ ∑ i, ξ i ^ 2} :=
        (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ gaussianTail t0 + 2 * exp (-z0) := by linarith
theorem gamma_row_gaussian (hn : 0 < n) (c : Fin n → ℝ) {t0 z0 t1 : ℝ} (hz0 : 0 ≤ z0) (ht1 : 0 ≤ t1)
    {ξ : Fin n → ℝ} (hξ : ξ ∈ OmegaS c t0 z0) :
    (stdGauss (Fin n)).real {ξ' | ξ' ∈ OmegaS c t0 z0 ∧ (ξ, ξ') ∉ GammaS c t0 z0 t1} ≤
      gaussianTail t1 := by
  have hg := gPlus_pos hn hz0
  have hv : nrm (perpC c ξ) ≤ gPlus n z0 := by
    unfold nrm gPlus
    refine Real.sqrt_le_sqrt ((normSq_perpC_le c ξ).trans hξ.2.2)
  have h := linear_gaussian_tail (perpC c ξ) hg hv ht1
  refine le_trans (measureReal_mono ?_) h
  intro ξ' hξ'
  obtain ⟨h1, h2⟩ := hξ'
  simp only [GammaS, Set.mem_ofPred_eq, not_and, not_le] at h2
  have := h2 hξ h1
  rw [perpC_dot] at this
  exact this

lemma pairs_out_gamma_gaussian (hn : 0 < n) (c : Fin n → ℝ) {t0 z0 t1 : ℝ} (hz0 : 0 ≤ z0) (ht1 : 0 ≤ t1) :
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) ≤ gaussianTail t1 := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hΩ := measurableSet_OmegaS c t0 z0
  have hm : MeasurableSet ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) :=
    (hΩ.prod hΩ).diff (measurableSet_GammaS c t0 z0 t1)
  have hB : 0 ≤ gaussianTail t1 := gaussianTail_nonneg t1
  rw [Measure.real, Measure.prod_apply hm]
  have hle : ∫⁻ ξ, (stdGauss (Fin n)) (Prod.mk ξ ⁻¹'
      ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1)) ∂stdGauss (Fin n) ≤
      ∫⁻ _ξ, ENNReal.ofReal (gaussianTail t1) ∂stdGauss (Fin n) := by
    refine lintegral_mono fun ξ => ?_
    by_cases hξ : ξ ∈ OmegaS c t0 z0
    · have e : Prod.mk ξ ⁻¹' ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) =
          {ξ' | ξ' ∈ OmegaS c t0 z0 ∧ (ξ, ξ') ∉ GammaS c t0 z0 t1} := by
        ext ξ'
        simp only [Set.mem_preimage, Set.mem_diff, Set.mem_prod, Set.mem_setOf_eq]
        tauto
      rw [e]
      have h := gamma_row_gaussian hn c hz0 ht1 (t0 := t0) hξ
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h
    · have e : Prod.mk ξ ⁻¹' ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) = ∅ := by
        ext ξ'
        simp only [Set.mem_preimage, Set.mem_diff, Set.mem_prod, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1
        exact absurd h1.1 hξ
      rw [e, measure_empty]
      exact bot_le
  rw [lintegral_const, measure_univ, mul_one] at hle
  calc (∫⁻ ξ, (stdGauss (Fin n)) (Prod.mk ξ ⁻¹'
        ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1)) ∂stdGauss (Fin n)).toReal
      ≤ (ENNReal.ofReal (gaussianTail t1)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = gaussianTail t1 := ENNReal.toReal_ofReal hB

theorem coreKernelSet_row_gaussian (hn : 0 < n) (c : Fin n → ℝ) (w : Window) (a : Fin n → ℝ) :
    (stdGauss (Fin n)).real {b | b ∈ OmegaS c w.t w.z ∧ (a, b) ∉ coreKernelSet c w} ≤
      gaussianTail w.pair := by
  by_cases ha : a ∈ OmegaS c w.t w.z
  · refine le_trans (measureReal_mono (fun b hb => ?_) (measure_ne_top _ _))
      (gamma_row_gaussian hn c w.z_nonneg w.pair_nonneg ha)
    exact ⟨hb.1, fun h => hb.2 (Or.inl h)⟩
  · have he : {b | b ∈ OmegaS c w.t w.z ∧ (a, b) ∉ coreKernelSet c w} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact hb.2 (Or.inr (fun hp => ha hp.1))
    rw [he, measureReal_empty]
    exact gaussianTail_nonneg w.pair
theorem commonGood_exception_gaussian (hn : 0 < n) (c : Fin n → ℝ) (w : Window)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B)
    {b : ℝ} (hb : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b) :
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      ((commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) ≤
      gaussianTail w.pair + 2 * b := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let μ := (stdGauss (Fin n)).prod (stdGauss (Fin n))
  have hs : μ.real (Prod.swap ⁻¹' B) = μ.real B := by
    rw [Measure.real, Measure.real,
      (Measure.measurePreserving_swap (μ := stdGauss (Fin n))
        (ν := stdGauss (Fin n))).measure_preimage hB.nullMeasurableSet]
  have hsub : (commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z ⊆
      ((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \ GammaS c w.t w.z w.pair) ∪
      B ∪ Prod.swap ⁻¹' B := by
    rintro p ⟨hno, hp⟩
    by_cases hΓ : p ∈ GammaS c w.t w.z w.pair
    · have hbad : p ∈ B ∪ Prod.swap ⁻¹' B := by
        by_contra hbad
        exact hno ⟨hΓ, hbad⟩
      rcases hbad with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · exact Or.inl (Or.inl ⟨hp, hΓ⟩)
  have hout := pairs_out_gamma_gaussian hn c w.z_nonneg w.pair_nonneg (t0 := w.t)
  calc μ.real ((commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z)
      ≤ μ.real (((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \
          GammaS c w.t w.z w.pair) ∪ B ∪ Prod.swap ⁻¹' B) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real ((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \ GammaS c w.t w.z w.pair) +
        μ.real B + μ.real (Prod.swap ⁻¹' B) :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ gaussianTail w.pair + 2 * b := by rw [hs]; linarith


end BstLean.Part254
