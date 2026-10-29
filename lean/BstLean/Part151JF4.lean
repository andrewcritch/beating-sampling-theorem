import BstLean.Part151J3

/-!
# Part 151: Lemma JF in the document's form, tools

Role: `proofs/option-n/theorem5-08-F-rows.tex`, Lemma JF (the `L⁴` bound of `t_F‖J_F(y)‖²_F − 2`).
This file has the tools:

* `four_centred`: (G7) for `k` independent copies of `f ≥ 0` with `E f = c`, `E f² ≤ b₂`,
  `E f⁴ ≤ b₄`: `E(Σ_j f(ω_j) − k·c)⁴ ≤ k·(8b₄ + 8c⁴) + 3k²·(b₂ − c²)²`.
* `chi_two`: `E|ξ|⁴ = n² + 2n`; `chi_four_le`: `E|ξ|⁸ ≤ n⁴ + 36n³ + 112n² + 48n`, for a standard
  Gaussian vector `ξ` of `ℝⁿ` (the exact value is `n(n + 2)(n + 4)(n + 6)`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part131

/-! ## (G7) with an exact mean -/

section G7

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **(G7) for independent copies of a nonnegative variable with mean `c`.** If `E f = c`,
`E f² ≤ b₂`, `E f⁴ ≤ b₄`: `E(Σ_j f(ω_j) − k·c)⁴ ≤ k·(8b₄ + 8c⁴) + 3k²·(b₂ − c²)²`. -/
theorem four_centred {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {c b₂ b₄ : ℝ}
    (hc0 : 0 ≤ c) (hb₂ : 0 ≤ b₂) (hb₄ : 0 ≤ b₄)
    (h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ENNReal.ofReal c)
    (h2 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ ≤ ENNReal.ofReal b₂)
    (h4 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 4) ∂μ ≤ ENNReal.ofReal b₄) (k : ℕ) :
    Integrable (fun us : Fin k → Ω => (∑ j, f (us j) - k * c) ^ 4)
      (Measure.pi fun _ : Fin k => μ) ∧
    ∫ us, (∑ j, f (us j) - k * c) ^ 4 ∂(Measure.pi fun _ : Fin k => μ) ≤
      k * (8 * b₄ + 8 * c ^ 4) + 3 * k ^ 2 * (b₂ - c ^ 2) ^ 2 := by
  obtain ⟨i1, -⟩ := int_of_lint hf hf0 hc0 h1.le
  obtain ⟨i2, m2⟩ := int_of_lint (hf.pow_const 2) (fun ω => sq_nonneg _) hb₂ h2
  obtain ⟨i4, m4⟩ := int_of_lint (hf.pow_const 4) (fun ω => by positivity) hb₄ h4
  have hc : ∫ ω, f ω ∂μ = c := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.aestronglyMeasurable, h1, ENNReal.toReal_ofReal hc0]
  set g : Ω → ℝ := fun ω => f ω - c with hg
  have mg : Measurable g := hf.sub measurable_const
  have ptw : ∀ ω, g ω ^ 4 ≤ 8 * f ω ^ 4 + 8 * c ^ 4 := by
    intro ω
    simp only [hg]
    nlinarith [sq_nonneg (f ω + c), sq_nonneg (f ω - c), sq_nonneg (f ω ^ 2 - c ^ 2),
      sq_nonneg ((f ω + c) ^ 2), mul_nonneg (sq_nonneg (f ω + c)) (sq_nonneg (f ω - c)),
      sq_nonneg (f ω * c), sq_nonneg (f ω ^ 2 + c ^ 2 + 2 * (f ω * c))]
  have idom : Integrable (fun ω => 8 * f ω ^ 4 + 8 * c ^ 4) μ :=
    (i4.const_mul 8).add (integrable_const _)
  have ig4 : Integrable (fun ω => g ω ^ 4) μ := by
    refine idom.mono' (mg.pow_const 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ptw ω
  have eg0 : ∫ ω, g ω ∂μ = 0 := by
    simp only [hg]
    rw [integral_sub i1 (integrable_const _)]
    simp [hc]
  have mg4 : ∫ ω, g ω ^ 4 ∂μ ≤ 8 * b₄ + 8 * c ^ 4 := by
    have h := integral_mono ig4 idom ptw
    rw [integral_add (i4.const_mul 8) (integrable_const _), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    linarith
  have eg2 : ∫ ω, g ω ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - c ^ 2 := by
    have e : (fun ω => g ω ^ 2) = fun ω => f ω ^ 2 - 2 * c * f ω + c ^ 2 := by
      funext ω; simp only [hg]; ring
    have i3 : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) μ := i2.sub (i1.const_mul (2 * c))
    rw [e, integral_add i3 (integrable_const _), integral_sub i2 (i1.const_mul (2 * c)),
      integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    rw [hc]
    ring
  have mg2 : ∫ ω, g ω ^ 2 ∂μ ≤ b₂ - c ^ 2 := by
    rw [eg2]; linarith
  have mg2' : 0 ≤ ∫ ω, g ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  obtain ⟨iS4, -, -, eS4⟩ := sum_four_pi μ mg ig4 eg0 k
  have e : ∀ us : Fin k → Ω, sumG g k us = ∑ j, f (us j) - k * c := by
    intro us
    simp only [sumG, hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  simp_rw [e] at iS4 eS4
  refine ⟨iS4, ?_⟩
  rw [eS4]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h5 : (∫ ω, g ω ^ 2 ∂μ) ^ 2 ≤ (b₂ - c ^ 2) ^ 2 := pow_le_pow_left₀ mg2' mg2 2
  have h6 : 3 * (k : ℝ) * (k - 1) * (∫ ω, g ω ^ 2 ∂μ) ^ 2 ≤ 3 * k ^ 2 * (b₂ - c ^ 2) ^ 2 := by
    have h7 : 0 ≤ (∫ ω, g ω ^ 2 ∂μ) ^ 2 := sq_nonneg _
    have h8 : 3 * (k : ℝ) * (k - 1) ≤ 3 * k ^ 2 := by nlinarith
    rcases le_total (3 * (k : ℝ) * (k - 1)) 0 with hneg | hpos
    · have : 3 * (k : ℝ) * (k - 1) * (∫ ω, g ω ^ 2 ∂μ) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg h7
      have : 0 ≤ 3 * (k : ℝ) ^ 2 * (b₂ - c ^ 2) ^ 2 := by positivity
      linarith
    · exact mul_le_mul h8 h5 h7 (by positivity)
  have h9 := mul_le_mul_of_nonneg_left mg4 hk0
  linarith

end G7

/-! ## Moments of `|ξ|²` -/

section chi

lemma gm2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  rw [gaussMom_eq]; simp [gaussMom]

lemma gm4 : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  rw [gaussMom_eq]
  have : Even 4 := by decide
  simp only [gaussMom, this, ↓reduceIte]
  norm_num [Nat.doubleFactorial]

lemma gm6 : ∫ x : ℝ, x ^ 6 ∂gaussianReal 0 1 = 15 := by
  rw [gaussMom_eq]
  have : Even 6 := by decide
  simp only [gaussMom, this, ↓reduceIte]
  norm_num [Nat.doubleFactorial]

lemma gm8 : ∫ x : ℝ, x ^ 8 ∂gaussianReal 0 1 = 105 := by
  rw [gaussMom_eq]
  have : Even 8 := by decide
  simp only [gaussMom, this, ↓reduceIte]
  norm_num [Nat.doubleFactorial]

lemma gint (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) k).integrable_norm_pow'.mono'
    (measurable_id.pow_const k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simp)

/-- The centred square `x² − 1` of a standard Gaussian variable: mean `0`, second moment `2`,
fourth moment `60`. -/
lemma sq_centred :
    Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 4) (gaussianReal 0 1) ∧
    ∫ x : ℝ, (x ^ 2 - 1) ∂gaussianReal 0 1 = 0 ∧
    ∫ x : ℝ, (x ^ 2 - 1) ^ 2 ∂gaussianReal 0 1 = 2 ∧
    ∫ x : ℝ, (x ^ 2 - 1) ^ 4 ∂gaussianReal 0 1 = 60 := by
  have i2 := gint 2
  have i4 := gint 4
  have i6 := gint 6
  have i8 := gint 8
  have ic : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := integrable_const _
  have e4 : (fun x : ℝ => (x ^ 2 - 1) ^ 4) =
      fun x => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2 + 1 := by
    funext x; ring
  have e2 : (fun x : ℝ => (x ^ 2 - 1) ^ 2) = fun x => x ^ 4 - 2 * x ^ 2 + 1 := by
    funext x; ring
  have j1 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6) (gaussianReal 0 1) :=
    i8.sub (i6.const_mul 4)
  have j2 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4) (gaussianReal 0 1) :=
    j1.add (i4.const_mul 6)
  have j3 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2)
      (gaussianReal 0 1) := j2.sub (i2.const_mul 4)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e4]; exact j3.add ic
  · rw [integral_sub i2 ic, gm2]; simp
  · have k1 : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) :=
      i4.sub (i2.const_mul 2)
    rw [e2, integral_add k1 ic, integral_sub i4 (i2.const_mul 2),
      integral_const_mul, gm4, gm2]
    simp
    norm_num
  · rw [e4, integral_add j3 ic, integral_sub j2 (i2.const_mul 4), integral_add j1 (i4.const_mul 6),
      integral_sub i8 (i6.const_mul 4), integral_const_mul, integral_const_mul,
      integral_const_mul, gm8, gm6, gm4, gm2]
    simp
    norm_num

variable (n : ℕ)

/-- `|ξ|² − n` under `stdGauss (Fin n)`: fourth power integrable, second moment `2n`, fourth
moment `12n² + 48n`. -/
lemma chi_centred :
    Integrable (fun ξ : Fin n → ℝ => (normSq ξ - n) ^ 4) (stdGauss (Fin n)) ∧
    ∫ ξ : Fin n → ℝ, (normSq ξ - n) ∂stdGauss (Fin n) = 0 ∧
    ∫ ξ : Fin n → ℝ, (normSq ξ - n) ^ 2 ∂stdGauss (Fin n) = 2 * n ∧
    ∫ ξ : Fin n → ℝ, (normSq ξ - n) ^ 4 ∂stdGauss (Fin n) = 12 * (n : ℝ) ^ 2 + 48 * n := by
  obtain ⟨hi, h0, h2, h4⟩ := sq_centred
  have hm : Measurable (fun x : ℝ => x ^ 2 - 1) := by fun_prop
  obtain ⟨iS, eS1, eS2, eS4⟩ := sum_four_pi (gaussianReal 0 1) hm hi h0 n
  have e : ∀ ξ : Fin n → ℝ, sumG (fun x : ℝ => x ^ 2 - 1) n ξ = normSq ξ - n := by
    intro ξ
    simp only [sumG, normSq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp_rw [e] at iS eS1 eS2 eS4
  have hst : stdGauss (Fin n) = Measure.pi fun _ : Fin n => gaussianReal 0 1 := rfl
  rw [hst]
  refine ⟨iS, eS1, ?_, ?_⟩
  · rw [eS2, h2]; ring
  · rw [eS4, h4, h2]; ring

/-- `E|ξ|⁴ = n² + 2n`. -/
lemma chi_two :
    ∫⁻ ξ : Fin n → ℝ, ENNReal.ofReal (normSq ξ ^ 2) ∂stdGauss (Fin n) =
      ENNReal.ofReal ((n : ℝ) ^ 2 + 2 * n) := by
  obtain ⟨i4, e1, e2, -⟩ := chi_centred n
  have mS : Measurable (fun ξ : Fin n → ℝ => normSq ξ - n) :=
    measurable_normSq.sub measurable_const
  have iS2 : Integrable (fun ξ : Fin n → ℝ => (normSq ξ - n) ^ 2) (stdGauss (Fin n)) :=
    int_pow_of_four mS i4 2 (by norm_num)
  have iS1 : Integrable (fun ξ : Fin n → ℝ => normSq ξ - n) (stdGauss (Fin n)) := by
    have := int_pow_of_four mS i4 1 (by norm_num)
    simpa using this
  have ee : (fun ξ : Fin n → ℝ => normSq ξ ^ 2) =
      fun ξ => (normSq ξ - n) ^ 2 + 2 * n * (normSq ξ - n) + (n : ℝ) ^ 2 := by
    funext ξ; ring
  have ii : Integrable (fun ξ : Fin n → ℝ => normSq ξ ^ 2) (stdGauss (Fin n)) := by
    rw [ee]; exact (iS2.add (iS1.const_mul _)).add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal ii (Filter.Eventually.of_forall fun ξ => sq_nonneg _)]
  congr 1
  have k1 : Integrable (fun ξ : Fin n → ℝ => (normSq ξ - n) ^ 2 + 2 * n * (normSq ξ - n))
      (stdGauss (Fin n)) := iS2.add (iS1.const_mul _)
  rw [ee, integral_add k1 (integrable_const _),
    integral_add iS2 (iS1.const_mul _), integral_const_mul, e1, e2]
  simp
  ring

/-- `E|ξ|⁸ ≤ n⁴ + 36n³ + 112n² + 48n`. -/
lemma chi_four_le :
    ∫⁻ ξ : Fin n → ℝ, ENNReal.ofReal (normSq ξ ^ 4) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal ((n : ℝ) ^ 4 + 36 * n ^ 3 + 112 * n ^ 2 + 48 * n) := by
  obtain ⟨i4, e1, e2, e4⟩ := chi_centred n
  have mS : Measurable (fun ξ : Fin n → ℝ => normSq ξ - n) :=
    measurable_normSq.sub measurable_const
  have iS2 : Integrable (fun ξ : Fin n → ℝ => (normSq ξ - n) ^ 2) (stdGauss (Fin n)) :=
    int_pow_of_four mS i4 2 (by norm_num)
  have iS1 : Integrable (fun ξ : Fin n → ℝ => normSq ξ - n) (stdGauss (Fin n)) := by
    have := int_pow_of_four mS i4 1 (by norm_num)
    simpa using this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the pointwise bound `(S + n)⁴ ≤ (1 + 2n)S⁴ + (2n + 6n²)S² + 4n³S + n⁴`
  set D : (Fin n → ℝ) → ℝ := fun ξ => (1 + 2 * n) * (normSq ξ - n) ^ 4 +
    (2 * n + 6 * (n : ℝ) ^ 2) * (normSq ξ - n) ^ 2 + 4 * (n : ℝ) ^ 3 * (normSq ξ - n) +
      (n : ℝ) ^ 4 with hD
  have iD : Integrable D (stdGauss (Fin n)) :=
    (((i4.const_mul _).add (iS2.const_mul _)).add (iS1.const_mul _)).add (integrable_const _)
  have ptw : ∀ ξ : Fin n → ℝ, normSq ξ ^ 4 ≤ D ξ := by
    intro ξ
    simp only [hD]
    set S := normSq ξ - n with hS
    have e : normSq ξ = S + n := by rw [hS]; ring
    rw [e]
    have h3 : S ^ 3 ≤ (S ^ 2 + S ^ 4) / 2 := by nlinarith [sq_nonneg (S - S ^ 2), sq_nonneg S]
    have h3' : 4 * (n : ℝ) * S ^ 3 ≤ 4 * n * ((S ^ 2 + S ^ 4) / 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have eD : ∫ ξ, D ξ ∂stdGauss (Fin n) = (n : ℝ) ^ 4 + 36 * n ^ 3 + 112 * n ^ 2 + 48 * n := by
    simp only [hD]
    have k1 : Integrable (fun ξ : Fin n → ℝ => (1 + 2 * (n : ℝ)) * (normSq ξ - n) ^ 4 +
        (2 * n + 6 * (n : ℝ) ^ 2) * (normSq ξ - n) ^ 2) (stdGauss (Fin n)) :=
      (i4.const_mul _).add (iS2.const_mul _)
    have k2 : Integrable (fun ξ : Fin n → ℝ => (1 + 2 * (n : ℝ)) * (normSq ξ - n) ^ 4 +
        (2 * n + 6 * (n : ℝ) ^ 2) * (normSq ξ - n) ^ 2 + 4 * (n : ℝ) ^ 3 * (normSq ξ - n))
        (stdGauss (Fin n)) := k1.add (iS1.const_mul _)
    rw [integral_add k2 (integrable_const _), integral_add k1 (iS1.const_mul _),
      integral_add (i4.const_mul _) (iS2.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul, e1, e2, e4]
    simp
    ring
  have mN : Measurable (fun ξ : Fin n → ℝ => normSq ξ ^ 4) := measurable_normSq.pow_const 4
  calc ∫⁻ ξ : Fin n → ℝ, ENNReal.ofReal (normSq ξ ^ 4) ∂stdGauss (Fin n)
      ≤ ∫⁻ ξ, ENNReal.ofReal (D ξ) ∂stdGauss (Fin n) :=
        lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (ptw ξ)
    _ = ENNReal.ofReal (∫ ξ, D ξ ∂stdGauss (Fin n)) :=
        (ofReal_integral_eq_lintegral_ofReal iD (Filter.Eventually.of_forall fun ξ =>
          le_trans (by positivity) (ptw ξ))).symm
    _ = _ := by rw [eD]

end chi

end BstLean.Part151
