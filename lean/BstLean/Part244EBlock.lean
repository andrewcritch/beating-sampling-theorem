import BstLean.Part244ECond

/-! Part 244: **the sharp E block of Lemma `t7:p04:ti` under the joint Agent distribution.**
The first-layer events and the second-layer mask count are those of Part 182 (`e4_G1`,
`mask_second_tail`); the second-layer step is the sharp one (`e3_cond_sharp`). -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part182
open BstLean.Part151 (mask measurable_mask jac)

variable {n : ℕ}

/-- The sharp E block on a measurable set of good first layers. -/
theorem e3_joint_sharp (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) {ℓ L11 π₁ K υ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hπ0 : 0 ≤ π₁) (hυ : 0 ≤ υ) (hm : 0 < mA n)
    (G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) (hG₁ : MeasurableSet G₁)
    (hG : ∀ A₁ ∈ G₁, e3_good1 x x' PE ℓ L11 π₁ A₁) :
    (BstLean.Part153.nuA n).real {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K ∧
      e3s_bound n K υ ℓ L11 π₁ < opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))} ≤
      4 * exp (-υ ^ 2 / 2) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K ∧
      e3s_bound n K υ ℓ L11 π₁ < opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))} with hSd
  have hSm : MeasurableSet S :=
    (measurable_fst hG₁).inter ((measurableSet_le (measurable_cnt2 x x') measurable_const).inter
      (measurableSet_lt measurable_const (e3_measurable_pair x x' PE)))
  have hB : 0 ≤ 4 * exp (-υ ^ 2 / 2) := by positivity
  rw [Measure.real]
  unfold BstLean.Part153.nuA
  rw [Measure.prod_apply hSm]
  have hle : ∀ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S) ≤
      ENNReal.ofReal (4 * exp (-υ ^ 2 / 2)) := by
    intro A₁
    by_cases hA : A₁ ∈ G₁
    · have e : Prod.mk A₁ ⁻¹' S = {A₂ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
          e3s_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} := by
        ext A₂
        simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · intro h; exact ⟨h.2.1, h.2.2⟩
        · intro h; exact ⟨hA, h.1, h.2⟩
      rw [e]
      exact e3_cond_sharp x x' PE hℓ0 hπ0 hυ hm A₁ (hG A₁ hA)
    · have e : Prod.mk A₁ ⁻¹' S = ∅ := by
        ext A₂
        simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; exact hA h.1
      rw [e, measure_empty]; exact bot_le
  calc (∫⁻ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (∫⁻ _A₁, ENNReal.ofReal (4 * exp (-υ ^ 2 / 2)) ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal :=
        ENNReal.toReal_mono (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top)
          (lintegral_mono hle)
    _ = 4 * exp (-υ ^ 2 / 2) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hB]

/-- **The sharp E block of Lemma TI.** With the Part 182 thresholds `K₁ = m(1/2+η)`,
`K₁₁ = m(κ̇(c₊)/2+η)`, `K₂ = m(κ̇(c₁⁺)/2+η)`, `ℓ`, `L₁₁`, `π₁`, `υ = √(2τ)`:
`Pr(‖P_E Jᵀ J' P_E‖ > e3s_bound n K₂ υ ℓ L₁₁ π₁) ≤ 14e^{-τ} + 4e^{-2η²m}`. This is the `KE`
hypothesis of mode separation with the paper's sharp E-block constant (up to the stated
`r₂` correction). -/
theorem e4_Eblock_sharp {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (hn : 1 ≤ n) {cp η τ : ℝ} (hcp : x ⬝ᵥ x' ≤ cp) (hcp1 : cp ≤ 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') ≤ 1) :
    (BstLean.Part153.nuA n).real {θ |
      e3s_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) <
      opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} ≤
      14 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  set K₁ := ((mA n : ℕ) : ℝ) * (1 / 2 + η)
  set K₁₁ := ((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)
  set K₂ := ((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)
  set G₁ := e4_G1 (m := mA n) x x' K₁ K₁₁ τ
  have hG₁m : MeasurableSet G₁ := e4_measurableSet_G1 x x' K₁ K₁₁ τ
  have hm : 0 < mA n := by unfold mA; positivity
  set bd := e3s_bound n K₂ (√(2 * τ)) (e4_b n K₁ τ) (e4_b n K₁₁ τ ^ 2) (e4_b n 2 τ)
  have hPE : ∀ J J' : Matrix (Fin (mA n)) (Fin n) ℝ,
      PEm x x' * (Jᵀ * J') * PEm x x' = (J * PEm x x')ᵀ * (J' * PEm x x') := by
    intro J J'
    rw [Matrix.transpose_mul, e4_PEm_symm]; simp only [Matrix.mul_assoc]
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      bd < opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} ⊆
      ((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) ∪
        {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))} := by
    intro θ hθ
    simp only [Set.mem_setOf_eq, hPE] at hθ
    by_cases h1 : θ.1 ∈ G₁
    · by_cases h2 : cnt2 x x' θ ≤ K₂
      · right; exact ⟨h1, h2, hθ⟩
      · left; right; exact not_le.mp h2
    · left; left; exact ⟨h1, Set.mem_univ _⟩
  have hprod : (BstLean.Part153.nuA n).real (G₁ᶜ ×ˢ Set.univ) =
      (gaussMat (mA n) n (2 / (n : ℝ))).real G₁ᶜ := by
    unfold BstLean.Part153.nuA
    rw [Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rfl
  have tG := e4_G1_charge hx hx' hc hn hcp hcp1 hη hτ
  have tM : (BstLean.Part153.nuA n).real {θ | K₂ < cnt2 x x' θ} ≤
      5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) :=
    mask_second_tail hn hx hx' hτ hη ham hdm h6 hc1
  have tJ := e3_joint_sharp x x' (PEm x x') (ℓ := e4_b n K₁ τ) (L11 := e4_b n K₁₁ τ ^ 2)
    (π₁ := e4_b n 2 τ) (K := K₂) (υ := √(2 * τ)) (by unfold e4_b; positivity)
    (by unfold e4_b; positivity) (Real.sqrt_nonneg _) hm G₁ hG₁m
    (fun A hA => e4_good_of_G1 x x' K₁ K₁₁ τ hA)
  have e2 : -(√(2 * τ)) ^ 2 / 2 = -τ := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [e2] at tJ
  calc _ ≤ (BstLean.Part153.nuA n).real (((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) ∪
        {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))}) :=
        measureReal_mono hsub
    _ ≤ (BstLean.Part153.nuA n).real (G₁ᶜ ×ˢ Set.univ) +
        (BstLean.Part153.nuA n).real {θ | K₂ < cnt2 x x' θ} +
        (BstLean.Part153.nuA n).real {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))} := by
        have a1 := measureReal_union_le (μ := BstLean.Part153.nuA n)
          ((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ})
          {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
            bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))}
        have a2 := measureReal_union_le (μ := BstLean.Part153.nuA n)
          (G₁ᶜ ×ˢ Set.univ) {θ | K₂ < cnt2 x x' θ}
        linarith
    _ ≤ 14 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
        rw [hprod]; linarith

end BstLean.Part244
