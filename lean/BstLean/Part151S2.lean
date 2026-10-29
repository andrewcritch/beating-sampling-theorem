import BstLean.Part151S

/-!
# Part 151: Lemma S for `y = c + τξ`

Role: Lemma S of `proofs/option-n/theorem5-04-standin-structure.tex`.

* `gauss_Icc_le`: `Pr(a ≤ Z ≤ b) ≤ b − a` for a standard Gaussian variable.
* `ball_prob_le`: `Pr(|c + τξ| ≤ r) ≤ (2r/τ)³`, `ξ` standard Gaussian in `ℝⁿ`, `n ≥ 3`.
* `gradSq_affine`: `|∇(Υ(c + τ·))|²(ξ) = τ²·|∇Υ|²(c + τξ)`.
* **`lemmaS`**: `Var Υ(c + τξ) ≤ τ²·E Γ(c + τξ)`; `lemmaS_vol`: the same with the hypothesis
  `|∇Υ|² ≤ Γ` almost everywhere for the Lebesgue measure.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_smul normSq_nonneg)
open BstLean.Part132 (nrm)
open BstLean.Part148 (EuLip stdGauss_ac)

/-- `Pr(a ≤ Z ≤ b) ≤ b − a` for a standard Gaussian variable `Z`. -/
lemma gauss_Icc_le (a b : ℝ) : gaussianReal 0 1 (Icc a b) ≤ ENNReal.ofReal (b - a) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  have hle : ∀ x : ℝ, gaussianPDF 0 1 x ≤ 1 := by
    intro x
    unfold gaussianPDF
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [BstLean.Part131.pdf_eq]
    have h1 : (1 : ℝ) ≤ √(2 * Real.pi) := by
      rw [Real.one_le_sqrt]
      have := Real.pi_gt_three
      linarith
    have h2 : (√(2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h3 : Real.exp (-(x ^ 2 / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := sq_nonneg x
      linarith
    have h4 : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
    calc (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) ≤ 1 * 1 :=
          mul_le_mul h2 h3 (Real.exp_pos _).le (by norm_num)
      _ = 1 := by ring
  calc ∫⁻ x in Icc a b, gaussianPDF 0 1 x ≤ ∫⁻ _x in Icc a b, 1 := lintegral_mono fun x => hle x
    _ = volume (Icc a b) := by simp
    _ = ENNReal.ofReal (b - a) := Real.volume_Icc

variable {n : ℕ}

/-- **The small-ball bound**: `Pr(|c + τξ| ≤ r) ≤ (2r/τ)³` for `n ≥ 3`. -/
theorem ball_prob_le (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (stdGauss (Fin n)).real {ξ | nrm (c + τ • ξ) ≤ r} ≤ (2 * r / τ) ^ 3 := by
  classical
  set T : Finset (Fin n) := Finset.image (Fin.castLE hn) Finset.univ with hT
  have hTc : T.card = 3 := by
    rw [hT, Finset.card_image_of_injective _ (Fin.castLE_injective hn)]
    simp
  set J : Fin n → Set ℝ := fun i => Icc ((-r - c i) / τ) ((r - c i) / τ) with hJ
  set s : Fin n → Set ℝ := fun i => if i ∈ T then J i else univ with hs
  have hsub : {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} ⊆ Set.pi univ s := by
    intro ξ hξ i _
    simp only [hs]
    split_ifs with hi
    · have h1 : (c i + τ * ξ i) ^ 2 ≤ normSq (c + τ • ξ) := by
        unfold normSq
        have := Finset.single_le_sum (f := fun j => (c + τ • ξ) j ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        simpa using this
      have h2 : normSq (c + τ • ξ) ≤ r ^ 2 := by
        have hξ' : nrm (c + τ • ξ) ≤ r := hξ
        unfold nrm at hξ'
        calc normSq (c + τ • ξ) = √(normSq (c + τ • ξ)) ^ 2 :=
              (Real.sq_sqrt (normSq_nonneg _)).symm
          _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hξ' 2
      have h3 : |c i + τ * ξ i| ≤ r := abs_le_of_sq_le_sq (h1.trans h2) hr
      obtain ⟨h4, h5⟩ := abs_le.mp h3
      simp only [hJ, mem_Icc]
      constructor
      · rw [div_le_iff₀ hτ]; linarith
      · rw [le_div_iff₀ hτ]; linarith
    · exact mem_univ _
  have hq0 : 0 ≤ 2 * r / τ := by positivity
  have hfac : ∀ i, gaussianReal 0 1 (s i) ≤
      (if i ∈ T then ENNReal.ofReal (2 * r / τ) else 1) := by
    intro i
    simp only [hs]
    split_ifs with hi
    · refine (gauss_Icc_le _ _).trans (le_of_eq ?_)
      congr 1
      field_simp
      ring
    · exact prob_le_one
  have hpi : (stdGauss (Fin n)) (Set.pi univ s) ≤ ENNReal.ofReal (2 * r / τ) ^ 3 := by
    unfold stdGauss
    rw [Measure.pi_pi]
    calc ∏ i, gaussianReal 0 1 (s i)
        ≤ ∏ i, (if i ∈ T then ENNReal.ofReal (2 * r / τ) else 1) :=
          Finset.prod_le_prod fun i _ => hfac i
      _ = ENNReal.ofReal (2 * r / τ) ^ 3 := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hTc]
  have h1 := (measure_mono hsub).trans hpi
  rw [measureReal_def]
  have h2 := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) h1
  rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hq0] at h2

/-- The radius `ξ ↦ |c + τξ|` is Lipschitz with the constant `τ`. -/
lemma nrm_affine_lip {τ : ℝ} (hτ : 0 ≤ τ) (c : Fin n → ℝ) :
    EuLip (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) τ := by
  intro x x'
  refine (nrm_sub_abs _ _).trans (le_of_eq ?_)
  have e : c + τ • x - (c + τ • x') = τ • (x - x') := by
    rw [smul_sub]; abel
  rw [e]
  unfold nrm
  rw [normSq_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ]
  rfl

/-- `|∇(Υ(c + τ·))|²(ξ) = τ²·|∇Υ|²(c + τξ)`. -/
lemma gradSq_affine (Υ : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    gradSq (fun ζ => Υ (c + τ • ζ)) ξ = τ ^ 2 * gradSq Υ (c + τ • ξ) := by
  have h := gradSq_comp_smul (fun z => Υ (c + z)) τ ξ
  rw [h]
  congr 1
  unfold gradSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_comp_add_left]

/-- **Lemma S (the Poincaré inequality across the point `y = 0`).** `n ≥ 3`, `τ > 0`,
`y = c + τξ` with `ξ` a standard Gaussian vector of `ℝⁿ`. `Υ` is measurable, bounded, and
Lipschitz on every set `{|y| ≥ ε}`, `ε > 0`. `Γ ≥ |∇Υ|²` at almost every `y` (in the
distribution of `y`), with `E Γ(y) < ∞`. Then `Var Υ(y) ≤ τ²·E Γ(y)`. -/
theorem lemmaS (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) {Υ Γ : (Fin n → ℝ) → ℝ}
    {Bd : ℝ} (hΥm : Measurable Υ) (hΥb : ∀ y, |Υ y| ≤ Bd)
    (hΥ : ∀ ε, 0 < ε → ∃ L, 0 ≤ L ∧ ∀ y y', ε ^ 2 ≤ normSq y → ε ^ 2 ≤ normSq y' →
      |Υ y - Υ y'| ≤ L * √(normSq (y - y')))
    (hΓ : Integrable (fun ξ => Γ (c + τ • ξ)) (stdGauss (Fin n)))
    (hΓb : ∀ᵐ ξ ∂stdGauss (Fin n), gradSq Υ (c + τ • ξ) ≤ Γ (c + τ • ξ)) :
    ∫ ξ, (Υ (c + τ • ξ) - ∫ ζ, Υ (c + τ • ζ) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      τ ^ 2 * ∫ ξ, Γ (c + τ • ξ) ∂stdGauss (Fin n) := by
  have haff : Measurable (fun ξ : Fin n → ℝ => c + τ • ξ) :=
    measurable_const.add (measurable_const_smul τ)
  have hρ := nrm_affine_lip hτ.le c
  have hU : ∀ ε, 0 < ε → ∃ L, 0 ≤ L ∧ ∀ x x' : Fin n → ℝ, ε ≤ nrm (c + τ • x) →
      ε ≤ nrm (c + τ • x') →
      |Υ (c + τ • x) - Υ (c + τ • x')| ≤ L * √(∑ i, (x i - x' i) ^ 2) := by
    intro ε hε
    obtain ⟨L, hL0, hL⟩ := hΥ ε hε
    refine ⟨L * τ, by positivity, fun x x' h1 h2 => ?_⟩
    have g1 : ε ^ 2 ≤ normSq (c + τ • x) := by
      rw [← Real.sq_sqrt (normSq_nonneg (c + τ • x))]
      exact pow_le_pow_left₀ hε.le h1 2
    have g2 : ε ^ 2 ≤ normSq (c + τ • x') := by
      rw [← Real.sq_sqrt (normSq_nonneg (c + τ • x'))]
      exact pow_le_pow_left₀ hε.le h2 2
    refine (hL _ _ g1 g2).trans (le_of_eq ?_)
    have e : c + τ • x - (c + τ • x') = τ • (x - x') := by
      rw [smul_sub]; abel
    rw [e, normSq_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ.le]
    have e2 : normSq (x - x') = ∑ i, (x i - x' i) ^ 2 := rfl
    rw [e2]
    ring
  have hG : Integrable (fun ξ => τ ^ 2 * Γ (c + τ • ξ)) (stdGauss (Fin n)) := hΓ.const_mul _
  have hGb : ∀ᵐ ξ ∂stdGauss (Fin n),
      gradSq (fun ζ => Υ (c + τ • ζ)) ξ ≤ τ ^ 2 * Γ (c + τ • ξ) := by
    filter_upwards [hΓb] with ξ hξ
    rw [gradSq_affine]
    exact mul_le_mul_of_nonneg_left hξ (sq_nonneg τ)
  have hP : Tendsto (fun j : ℕ => (stdGauss (Fin n)).real
      {x | nrm (c + τ • x) ≤ 2 * (1 / ((j : ℝ) + 1))} / (1 / ((j : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun j : ℕ => 64 / τ ^ 3 * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (64 / τ ^ 3)
      simpa using this
    refine squeeze_zero (fun j => div_nonneg measureReal_nonneg (sq_nonneg _)) (fun j => ?_) hup
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hb := ball_prob_le hn hτ c (r := 2 * (1 / ((j : ℝ) + 1))) (by positivity)
    rw [div_le_iff₀ (by positivity)]
    refine hb.trans (le_of_eq ?_)
    field_simp
    ring
  have h := lemmaS_core (ρ := fun ξ : Fin n → ℝ => nrm (c + τ • ξ))
    (U := fun ξ => Υ (c + τ • ξ)) (G := fun ξ => τ ^ 2 * Γ (c + τ • ξ)) hτ.le hρ
    (hΥm.comp haff) (fun x => hΥb _) hU hG hGb hP
  rwa [integral_const_mul] at h

/-- **Lemma S**, with the hypothesis `|∇Υ|² ≤ Γ` almost everywhere for the Lebesgue measure. -/
theorem lemmaS_vol (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) {Υ Γ : (Fin n → ℝ) → ℝ}
    {Bd : ℝ} (hΥm : Measurable Υ) (hΥb : ∀ y, |Υ y| ≤ Bd)
    (hΥ : ∀ ε, 0 < ε → ∃ L, 0 ≤ L ∧ ∀ y y', ε ^ 2 ≤ normSq y → ε ^ 2 ≤ normSq y' →
      |Υ y - Υ y'| ≤ L * √(normSq (y - y')))
    (hΓ : Integrable (fun ξ => Γ (c + τ • ξ)) (stdGauss (Fin n)))
    (hΓb : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), gradSq Υ y ≤ Γ y) :
    ∫ ξ, (Υ (c + τ • ξ) - ∫ ζ, Υ (c + τ • ζ) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      τ ^ 2 * ∫ ξ, Γ (c + τ • ξ) ∂stdGauss (Fin n) := by
  refine lemmaS hn hτ c hΥm hΥb hΥ hΓ ?_
  have hvol : ∀ᵐ ξ ∂(volume : Measure (Fin n → ℝ)), gradSq Υ (c + τ • ξ) ≤ Γ (c + τ • ξ) := by
    rw [ae_iff] at hΓb ⊢
    have e : {a : Fin n → ℝ | ¬gradSq Υ (c + τ • a) ≤ Γ (c + τ • a)} =
        (fun x : Fin n → ℝ => τ • x) ⁻¹' ((fun x => c + x) ⁻¹' {y | ¬gradSq Υ y ≤ Γ y}) := rfl
    rw [e, Measure.addHaar_preimage_smul _ hτ.ne', measure_preimage_add, hΓb, mul_zero]
  exact stdGauss_ac hvol

end BstLean.Part151
