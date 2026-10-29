import BstLean.Part151ST

/-!
# Part 151: the feature energy with charges, and the sampling term in event form

Role: `delegations/statements/p151-spec.md`, item 4 (b). No Jacobian is used.

* **`lemmaFE`**: for inputs `X` that do not depend on `F`, with `E|X|² < ∞`:
  `Pr_{F₁,F₂}(t_F·E|z_F(X)|² > (1 + δ)(1 + δ′)·(2/n)·E|X|²) ≤ (432/m²)(1 + 63/m)(1/δ⁴ + 1/δ′⁴)`
  (Lemma TR, event `E_{T1}`, applied to each of the two layers with the pair `(·, 0)`).
* `lemmaFE_gauss`: the same for `X = c + σγ`, `γ` standard Gaussian: `E|X|² = |c|² + nσ²`.
* **`lemmaSA_event`**: on the complement of that event:
  `E_η T_s² ≤ (1 + δ)(1 + δ′)·(2/n)(|c|² + nσ²)/k`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part139 (gamK)

section FE

variable {Ω' : Type*} [MeasurableSpace Ω'] {n m : ℕ}

omit [MeasurableSpace Ω'] in
lemma hidA_zero {d : ℕ} (F₁ : Matrix (Fin m) (Fin d) ℝ) (ω : Ω') :
    hidA F₁ (fun _ : Ω' => (0 : Fin d → ℝ)) ω = 0 := by
  unfold hidA
  funext i
  simp [reluV, relu]

lemma Tfun_zero {d : ℕ} (P : Measure Ω') (X : Ω' → Fin d → ℝ) (F₁ : Matrix (Fin m) (Fin d) ℝ) :
    Tfun P X (fun _ => 0) F₁ = ∫ ω, normSq (hidA F₁ X ω) ∂P := by
  unfold Tfun TR
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [hidA_zero, sub_zero]

/-- **The feature energy with its charge.** For `δ, δ′ > 0`, `n, m ≥ 1`:
`Pr_{F₁,F₂}(t_F·E|z_F(X)|² > (1 + δ)(1 + δ′)·(2/n)·E|X|²) ≤ (432/m²)(1 + 63/m)(1/δ⁴ + 1/δ′⁴)`. -/
theorem lemmaFE (P : Measure Ω') [IsProbabilityMeasure P] (hn : 1 ≤ n) (hm : 1 ≤ m)
    {X : Ω' → Fin n → ℝ} (hX : Measurable X) (hXi : Integrable (fun ω => normSq (X ω)) P)
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') :
    (hidGauss n m).real
        {θ | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * ∫ ω, normSq (X ω) ∂P) <
          2 / (m : ℝ) * ∫ ω, normSq (hid2 θ.1 θ.2 (X ω)) ∂P} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) * (1 / δ ^ 4 + 1 / δ' ^ 4) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set D : ℝ := ∫ ω, normSq (X ω) ∂P with hD
  set c : ℝ := 432 / (m : ℝ) ^ 2 * (1 + 63 / m) with hc
  have hc0 : 0 ≤ c := by positivity
  have hZ : Measurable (fun _ : Ω' => (0 : Fin n → ℝ)) := measurable_const
  have hXY : Integrable (fun ω => normSq (X ω - (fun _ : Ω' => (0 : Fin n → ℝ)) ω)) P := by
    simpa using hXi
  have eD : ∫ ω, normSq (X ω - (fun _ : Ω' => (0 : Fin n → ℝ)) ω) ∂P = D := by
    simp [hD]
  set E1 : Matrix (Fin m) (Fin n) ℝ → ℝ := fun F₁ => ∫ ω, normSq (hidA F₁ X ω) ∂P with hE1
  have mE1 : Measurable E1 := by
    have h := Tfun_meas (m := m) P hX hZ hXY
    have e : E1 = fun F₁ => Tfun P X (fun _ => 0) F₁ := funext fun F₁ => (Tfun_zero P X F₁).symm
    rw [e]; exact h
  set E2 : HidParam n m → ℝ := fun θ => ∫ ω, normSq (hid2 θ.1 θ.2 (X ω)) ∂P with hE2
  have mE2 : Measurable E2 := by
    refine StronglyMeasurable.measurable ?_
    refine StronglyMeasurable.integral_prod_right'
      (f := fun q : HidParam n m × Ω' => normSq (hid2 q.1.1 q.1.2 (X q.2))) ?_
    refine Measurable.stronglyMeasurable ?_
    exact continuous_normSq.measurable.comp
      ((continuous_hid2_joint (N := n) (m := m)).measurable.comp
        (measurable_fst.prodMk (hX.comp measurable_snd)))
  set B₁ : Set (Matrix (Fin m) (Fin n) ℝ) :=
    {F₁ | (1 + δ') * (2 / (n : ℝ) * D) < 2 / (m : ℝ) * E1 F₁} with hB₁
  set A : Set (HidParam n m) :=
    {θ | (1 + δ) * (2 / (m : ℝ) * E1 θ.1) < 2 / (m : ℝ) * E2 θ} with hA
  have mA : MeasurableSet A :=
    measurableSet_lt (measurable_const.mul (measurable_const.mul (mE1.comp measurable_fst)))
      (measurable_const.mul mE2)
  have hsub : {θ : HidParam n m | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * D) <
      2 / (m : ℝ) * E2 θ} ⊆ (B₁ ×ˢ univ) ∪ A := by
    intro θ hθ
    simp only [mem_ofPred_eq] at hθ
    by_cases h1 : θ.1 ∈ B₁
    · exact Or.inl ⟨h1, mem_univ _⟩
    · refine Or.inr ?_
      have h1' : 2 / (m : ℝ) * E1 θ.1 ≤ (1 + δ') * (2 / (n : ℝ) * D) := not_lt.mp h1
      show (1 + δ) * (2 / (m : ℝ) * E1 θ.1) < 2 / (m : ℝ) * E2 θ
      have h2 : (1 + δ) * (2 / (m : ℝ) * E1 θ.1) ≤
          (1 + δ) * ((1 + δ') * (2 / (n : ℝ) * D)) :=
        mul_le_mul_of_nonneg_left h1' (by linarith)
      calc (1 + δ) * (2 / (m : ℝ) * E1 θ.1)
          ≤ (1 + δ) * (1 + δ') * (2 / (n : ℝ) * D) := by rw [mul_assoc]; exact h2
        _ < _ := hθ
  have hT1 := lemmaTR_T1 (m := m) P hn hm hX hZ hXY hδ'
  rw [eD, ← hc] at hT1
  have hB : (hidGauss n m).real (B₁ ×ˢ (univ : Set (Matrix (Fin m) (Fin m) ℝ))) ≤
      c / δ' ^ 4 := by
    unfold hidGauss
    rw [measureReal_prod_prod]
    have e : B₁ = {F₁ | (1 + δ') * (2 / (n : ℝ) * D) <
        2 / (m : ℝ) * Tfun P X (fun _ => 0) F₁} := by
      ext F₁; simp only [hB₁, hE1, mem_ofPred_eq, Tfun_zero]
    rw [e]
    simpa using hT1
  have hAle : (hidGauss n m).real A ≤ c / δ ^ 4 := by
    have hc1 : 0 ≤ c / δ ^ 4 := by positivity
    have hle : (hidGauss n m) A ≤ ENNReal.ofReal (c / δ ^ 4) := by
      unfold hidGauss
      rw [Measure.prod_apply mA]
      calc ∫⁻ F₁, (gaussMat m m (2 / (m : ℝ))) (Prod.mk F₁ ⁻¹' A) ∂gaussMat m n (2 / (n : ℝ))
          ≤ ∫⁻ _, ENNReal.ofReal (c / δ ^ 4) ∂gaussMat m n (2 / (n : ℝ)) := by
            refine lintegral_mono fun F₁ => ?_
            have hX' : Measurable (hidA F₁ X) := measurable_hidA F₁ hX
            have hZ' : Measurable (fun _ : Ω' => (0 : Fin m → ℝ)) := measurable_const
            have hint0 := hidA_int P F₁ hX hZ hXY
            have hXY' : Integrable (fun ω => normSq (hidA F₁ X ω -
                (fun _ : Ω' => (0 : Fin m → ℝ)) ω)) P := by
              refine hint0.congr (Filter.Eventually.of_forall fun ω => ?_)
              simp only
              rw [hidA_zero, sub_zero]
            have h := lemmaTR_T1 (n := m) (m := m) P hm hm hX' hZ' hXY' hδ
            have eD' : ∫ ω, normSq (hidA F₁ X ω - (fun _ : Ω' => (0 : Fin m → ℝ)) ω) ∂P =
                E1 F₁ := by simp [hE1]
            have eS : {F₂ : Matrix (Fin m) (Fin m) ℝ | (1 + δ) * (2 / (m : ℝ) * E1 F₁) <
                2 / (m : ℝ) * Tfun P (hidA F₁ X) (fun _ => 0) F₂} = Prod.mk F₁ ⁻¹' A := by
              ext F₂
              simp only [hA, hE2, mem_ofPred_eq, mem_preimage, Tfun_zero]
              rfl
            rw [eD', eS, measureReal_def] at h
            exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc1).mpr h
        _ = ENNReal.ofReal (c / δ ^ 4) := by simp
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hc1 hle
  calc (hidGauss n m).real {θ | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * D) < 2 / (m : ℝ) * E2 θ}
      ≤ (hidGauss n m).real ((B₁ ×ˢ univ) ∪ A) := measureReal_mono hsub
    _ ≤ (hidGauss n m).real (B₁ ×ˢ univ) + (hidGauss n m).real A := measureReal_union_le _ _
    _ ≤ c / δ' ^ 4 + c / δ ^ 4 := add_le_add hB hAle
    _ = c * (1 / δ ^ 4 + 1 / δ' ^ 4) := by ring

/-- The feature energy for a Gaussian input `c + σγ`:
`Pr_{F₁,F₂}(t_F·E_γ|z_F(c + σγ)|² > (1 + δ)(1 + δ′)·(2/n)(|c|² + nσ²)) ≤ charge`. -/
theorem lemmaFE_gauss (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (σ : ℝ) {δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') :
    (hidGauss n m).real
        {θ | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * (normSq c + n * σ ^ 2)) <
          2 / (m : ℝ) * ∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) * (1 / δ ^ 4 + 1 / δ' ^ 4) := by
  have hX : Measurable (fun γ : Fin n → ℝ => c + σ • γ) :=
    measurable_const.add (measurable_const_smul σ)
  have h := lemmaFE (stdGauss (Fin n)) hn hm hX (shift_integrable c σ) hδ hδ'
  rw [shift_second] at h
  exact h

/-- **Lemma SA in event form, without a Jacobian.** If `(F₁, F₂)` is outside the event of
`lemmaFE_gauss`, then `E_η T_s² ≤ (1 + δ)(1 + δ′)·(2/n)(|c|² + nσ²)/k`. -/
theorem lemmaSA_event (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    {δ δ' : ℝ}
    (hθ : 2 / (m : ℝ) * ∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n) ≤
      (1 + δ) * (1 + δ') * (2 / (n : ℝ) * (normSq c + n * σ ^ 2))) :
    ∫⁻ η, ENNReal.ofReal (2 / (m : ℝ) * normSq (dSamp θ c σ k η)) ∂gamK k n ≤
      ENNReal.ofReal ((1 + δ) * (1 + δ') * (2 / (n : ℝ) * (normSq c + n * σ ^ 2)) / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hv : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have h := lemmaSA_fixed θ c σ hk
  have e : ∀ η : Fin k → Fin n → ℝ, ENNReal.ofReal (2 / (m : ℝ) * normSq (dSamp θ c σ k η)) =
      ENNReal.ofReal (2 / (m : ℝ)) * ENNReal.ofReal (normSq (dSamp θ c σ k η)) :=
    fun η => ENNReal.ofReal_mul hv
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h).trans ?_
  rw [← ENNReal.ofReal_mul hv]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hθ hk0.le

end FE

end BstLean.Part151
