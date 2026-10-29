import BstLean.Part151R
import BstLean.Part130Extra

/-!
# Part 151, Lemma TR, the probability tools: (G7) and the rows of a Gaussian matrix

Role: `delegations/statements/p151-spec.md`, item 4 (c). Paper source:
`proofs/option-n/theorem5-08-F-rows.tex`, Lemma TR, and (G7) of
`proofs/option-n/theorem5-03-inputs.tex`.

* `sum_four_pi`: **(G7)** for `k` independent copies of a centred variable `g` with a finite
  fourth moment: `E S = 0`, `E S² = k·E g²`, `E S⁴ = k·E g⁴ + 3k(k − 1)(E g²)²`,
  `S = Σ_j g(ω_j)`.
* `tail_pi`: for `f ≥ 0` with `E f ≤ b₁`, `E f² ≤ b₂`, `E f⁴ ≤ b₄`:
  `Pr(Σ_j f(ω_j) > k·b₁ + a) ≤ (k(8b₄ + 8b₁⁴) + 3k²b₂²)/a⁴` (Markov's inequality at order 4).
* `tail_pi_U`: with `b₁ = U`, `b₂ = 12U²`, `b₄ = 1680U⁴` (the moments of Lemma R (iii) in the
  unit `U`): `Pr(Σ_j f(ω_j) > (1 + δ)·k·U) ≤ (432/k²)(1 + 63/k)/δ⁴`.
* `rowDist d v`: the distribution of `√v • ξ`, `ξ` a standard Gaussian vector of `ℝ^d`.
  `gaussMat_rows`: **the rows of a Gaussian matrix are independent**, each with the
  distribution `rowDist d v`.
* `tail_rows`: `tail_pi_U` for the rows of `M ∼ gaussMat m d v`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130

/-! ## Small tools -/

section tools

variable {α : Type*} [MeasurableSpace α]

/-- A nonnegative measurable function with a bounded lower integral is integrable, and its
integral has the same bound. -/
lemma int_of_lint {ν : Measure α} {F : α → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) {b : ℝ}
    (hb : 0 ≤ b) (h : ∫⁻ x, ENNReal.ofReal (F x) ∂ν ≤ ENNReal.ofReal b) :
    Integrable F ν ∧ ∫ x, F x ∂ν ≤ b := by
  have h0 : 0 ≤ᵐ[ν] F := Filter.Eventually.of_forall hF0
  have hi : Integrable F ν :=
    ⟨hF.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).mpr
      (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hF.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hb h

/-- On a finite measure, a measurable function with an integrable fourth power has integrable
powers of order `i ≤ 4`. -/
lemma int_pow_of_four {ν : Measure α} [IsFiniteMeasure ν] {F : α → ℝ} (hF : Measurable F)
    (h4 : Integrable (fun x => F x ^ 4) ν) (i : ℕ) (hi : i ≤ 4) :
    Integrable (fun x => F x ^ i) ν := by
  have hdom : Integrable (fun x => 1 + F x ^ 4) ν := (integrable_const 1).add h4
  refine hdom.mono' (hF.pow_const i).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have h0 := abs_nonneg (F x)
  have e : F x ^ 4 = |F x| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [e]
  have h4' : 0 ≤ |F x| ^ 4 := by positivity
  rcases le_total (|F x|) 1 with h | h
  · have := pow_le_one₀ (n := i) h0 h
    linarith
  · have := pow_le_pow_right₀ h hi
    linarith

end tools

/-! ## (G7): the fourth moment of a sum of independent centred variables -/

section G7

variable {Ω : Type*} [MeasurableSpace Ω]

lemma cons_symm (k : ℕ) (p : Ω × (Fin k → Ω)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Ω) 0).symm p =
      Fin.cons (α := fun _ => Ω) p.1 p.2 := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma pi_succ_int (k : ℕ) (f : (Fin (k + 1) → Ω) → ℝ) :
    ∫ us, f us ∂Measure.pi (fun _ : Fin (k + 1) => μ) =
      ∫ p : Ω × (Fin k → Ω), f (Fin.cons (α := fun _ => Ω) p.1 p.2)
        ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
  have h2 := (MeasurePreserving.symm _ h).integral_comp' f
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show f _ = f _
  rw [cons_symm]

lemma pi_succ_integrable (k : ℕ) (f : (Fin (k + 1) → Ω) → ℝ)
    (hf : Integrable (fun p : Ω × (Fin k → Ω) => f (Fin.cons (α := fun _ => Ω) p.1 p.2))
      (μ.prod (Measure.pi fun _ : Fin k => μ))) :
    Integrable f (Measure.pi fun _ : Fin (k + 1) => μ) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
  have hs := MeasurePreserving.symm _ h
  rw [← hs.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine hf.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp]
  rw [cons_symm]

/-- `S = Σ_j g(ω_j)`. -/
def sumG (g : Ω → ℝ) (k : ℕ) (us : Fin k → Ω) : ℝ := ∑ j, g (us j)

omit [MeasurableSpace Ω] in
lemma sumG_cons (g : Ω → ℝ) (k : ℕ) (u : Ω) (us : Fin k → Ω) :
    sumG g (k + 1) (Fin.cons (α := fun _ => Ω) u us) = g u + sumG g k us := by
  simp only [sumG, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma measurable_sumG {g : Ω → ℝ} (hg : Measurable g) (k : ℕ) : Measurable (sumG g k) :=
  Finset.measurable_sum _ fun j _ => hg.comp (measurable_pi_apply j)

/-- **(G7).** `k` independent copies of a centred variable `g` with a finite fourth moment;
`S = Σ_j g(ω_j)`. Then `S⁴` is integrable, `E S = 0`, `E S² = k·E g²`, and
`E S⁴ = k·E g⁴ + 3k(k − 1)·(E g²)²`. -/
theorem sum_four_pi {g : Ω → ℝ} (hg : Measurable g) (h4 : Integrable (fun ω => g ω ^ 4) μ)
    (h0 : ∫ ω, g ω ∂μ = 0) (k : ℕ) :
    Integrable (fun us : Fin k → Ω => sumG g k us ^ 4) (Measure.pi fun _ : Fin k => μ) ∧
    ∫ us, sumG g k us ∂(Measure.pi fun _ : Fin k => μ) = 0 ∧
    ∫ us, sumG g k us ^ 2 ∂(Measure.pi fun _ : Fin k => μ) = k * ∫ ω, g ω ^ 2 ∂μ ∧
    ∫ us, sumG g k us ^ 4 ∂(Measure.pi fun _ : Fin k => μ) =
      k * ∫ ω, g ω ^ 4 ∂μ + 3 * k * (k - 1) * (∫ ω, g ω ^ 2 ∂μ) ^ 2 := by
  induction k with
  | zero =>
    have e : ∀ us : Fin 0 → Ω, sumG g 0 us = 0 := fun us => by simp [sumG]
    simp only [e]
    refine ⟨by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨iS4, eS1, eS2, eS4⟩ := ih
    set ν := Measure.pi fun _ : Fin k => μ with hν
    set S := sumG g k with hS
    have mS : Measurable S := measurable_sumG hg k
    have g1 : Integrable g μ := by simpa using int_pow_of_four hg h4 1 (by norm_num)
    have g2 : Integrable (fun ω => g ω ^ 2) μ := int_pow_of_four hg h4 2 (by norm_num)
    have g3 : Integrable (fun ω => g ω ^ 3) μ := int_pow_of_four hg h4 3 (by norm_num)
    have s1 : Integrable S ν := by simpa using int_pow_of_four mS iS4 1 (by norm_num)
    have s2 : Integrable (fun us => S us ^ 2) ν := int_pow_of_four mS iS4 2 (by norm_num)
    have s3 : Integrable (fun us => S us ^ 3) ν := int_pow_of_four mS iS4 3 (by norm_num)
    have c1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have d1 : Integrable (fun _ : Fin k → Ω => (1 : ℝ)) ν := integrable_const 1
    set Pm := μ.prod ν with hPm
    -- the terms
    have t40 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 ^ 4 * 1) Pm := h4.mul_prod d1
    have t31 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 ^ 3 * S p.2) Pm := g3.mul_prod s1
    have t22 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 ^ 2 * S p.2 ^ 2) Pm :=
      g2.mul_prod s2
    have t13 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 * S p.2 ^ 3) Pm := g1.mul_prod s3
    have t04 : Integrable (fun p : Ω × (Fin k → Ω) => 1 * S p.2 ^ 4) Pm := c1.mul_prod iS4
    have t20 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 ^ 2 * 1) Pm := g2.mul_prod d1
    have t11 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 * S p.2) Pm := g1.mul_prod s1
    have t02 : Integrable (fun p : Ω × (Fin k → Ω) => 1 * S p.2 ^ 2) Pm := c1.mul_prod s2
    have t10 : Integrable (fun p : Ω × (Fin k → Ω) => g p.1 * 1) Pm := g1.mul_prod d1
    have t01 : Integrable (fun p : Ω × (Fin k → Ω) => 1 * S p.2) Pm := c1.mul_prod s1
    -- the fourth power
    have e4 : (fun p : Ω × (Fin k → Ω) => (g p.1 + S p.2) ^ 4) = fun p =>
        g p.1 ^ 4 * 1 + 4 * (g p.1 ^ 3 * S p.2) + 6 * (g p.1 ^ 2 * S p.2 ^ 2) +
          4 * (g p.1 * S p.2 ^ 3) + 1 * S p.2 ^ 4 := by
      funext p; ring
    have j2 : Integrable (fun p : Ω × (Fin k → Ω) =>
        g p.1 ^ 4 * 1 + 4 * (g p.1 ^ 3 * S p.2)) Pm := t40.add (t31.const_mul 4)
    have j3 : Integrable (fun p : Ω × (Fin k → Ω) =>
        g p.1 ^ 4 * 1 + 4 * (g p.1 ^ 3 * S p.2) + 6 * (g p.1 ^ 2 * S p.2 ^ 2)) Pm :=
      j2.add (t22.const_mul 6)
    have j4 : Integrable (fun p : Ω × (Fin k → Ω) =>
        g p.1 ^ 4 * 1 + 4 * (g p.1 ^ 3 * S p.2) + 6 * (g p.1 ^ 2 * S p.2 ^ 2) +
          4 * (g p.1 * S p.2 ^ 3)) Pm := j3.add (t13.const_mul 4)
    have j5 : Integrable (fun p : Ω × (Fin k → Ω) => (g p.1 + S p.2) ^ 4) Pm := by
      rw [e4]; exact j4.add t04
    have e2 : (fun p : Ω × (Fin k → Ω) => (g p.1 + S p.2) ^ 2) = fun p =>
        g p.1 ^ 2 * 1 + 2 * (g p.1 * S p.2) + 1 * S p.2 ^ 2 := by
      funext p; ring
    have q2 : Integrable (fun p : Ω × (Fin k → Ω) =>
        g p.1 ^ 2 * 1 + 2 * (g p.1 * S p.2)) Pm := t20.add (t11.const_mul 2)
    have e1 : (fun p : Ω × (Fin k → Ω) => g p.1 + S p.2) = fun p =>
        g p.1 * 1 + 1 * S p.2 := by
      funext p; ring
    have one_μ : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp
    have one_ν : ∫ _ : Fin k → Ω, (1 : ℝ) ∂ν = 1 := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine pi_succ_integrable μ k _ ?_
      simp only [sumG_cons]
      exact j5
    · rw [pi_succ_int]
      simp only [sumG_cons]
      rw [e1, integral_add t10 t01, hPm,
        integral_prod_mul (fun ω => g ω) (fun _ : Fin k → Ω => (1 : ℝ)),
        integral_prod_mul (fun _ : Ω => (1 : ℝ)) (fun us : Fin k → Ω => S us), h0, eS1]
      simp
    · rw [pi_succ_int]
      simp only [sumG_cons]
      rw [e2, integral_add q2 t02, integral_add t20 (t11.const_mul 2), integral_const_mul, hPm,
        integral_prod_mul (fun ω => g ω ^ 2) (fun _ : Fin k → Ω => (1 : ℝ)),
        integral_prod_mul (fun ω => g ω) (fun us : Fin k → Ω => S us),
        integral_prod_mul (fun _ : Ω => (1 : ℝ)) (fun us : Fin k → Ω => S us ^ 2),
        h0, eS1, eS2, one_μ, one_ν]
      push_cast
      ring
    · rw [pi_succ_int]
      simp only [sumG_cons]
      rw [e4, integral_add j4 t04, integral_add j3 (t13.const_mul 4),
        integral_add j2 (t22.const_mul 6), integral_add t40 (t31.const_mul 4),
        integral_const_mul, integral_const_mul, integral_const_mul, hPm,
        integral_prod_mul (fun ω => g ω ^ 4) (fun _ : Fin k → Ω => (1 : ℝ)),
        integral_prod_mul (fun ω => g ω ^ 3) (fun us : Fin k → Ω => S us),
        integral_prod_mul (fun ω => g ω ^ 2) (fun us : Fin k → Ω => S us ^ 2),
        integral_prod_mul (fun ω => g ω) (fun us : Fin k → Ω => S us ^ 3),
        integral_prod_mul (fun _ : Ω => (1 : ℝ)) (fun us : Fin k → Ω => S us ^ 4),
        h0, eS1, eS2, eS4, one_μ, one_ν]
      push_cast
      ring

/-- **Markov's inequality at order 4 for a sum of independent copies of `f ≥ 0`.** If
`E f ≤ b₁`, `E f² ≤ b₂`, `E f⁴ ≤ b₄` and `a > 0`:
`Pr(Σ_j f(ω_j) > k·b₁ + a) ≤ (k·(8b₄ + 8b₁⁴) + 3k²·b₂²)/a⁴`. -/
theorem tail_pi {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {b₁ b₂ b₄ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₄ : 0 ≤ b₄)
    (h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal b₁)
    (h2 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ ≤ ENNReal.ofReal b₂)
    (h4 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 4) ∂μ ≤ ENNReal.ofReal b₄) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (Measure.pi fun _ : Fin k => μ).real {us | k * b₁ + a < ∑ j, f (us j)} ≤
      (k * (8 * b₄ + 8 * b₁ ^ 4) + 3 * k ^ 2 * b₂ ^ 2) / a ^ 4 := by
  obtain ⟨i1, m1⟩ := int_of_lint hf hf0 hb₁ h1
  obtain ⟨i2, m2⟩ := int_of_lint (hf.pow_const 2) (fun ω => sq_nonneg _) hb₂ h2
  obtain ⟨i4, m4⟩ := int_of_lint (hf.pow_const 4) (fun ω => by positivity) hb₄ h4
  set c : ℝ := ∫ ω, f ω ∂μ with hc
  have hc0 : 0 ≤ c := integral_nonneg hf0
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
  have c4 : c ^ 4 ≤ b₁ ^ 4 := pow_le_pow_left₀ hc0 m1 4
  have mg4 : ∫ ω, g ω ^ 4 ∂μ ≤ 8 * b₄ + 8 * b₁ ^ 4 := by
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
    rw [← hc]
    ring
  have mg2 : ∫ ω, g ω ^ 2 ∂μ ≤ b₂ := by
    rw [eg2]; nlinarith [sq_nonneg c]
  have mg2' : 0 ≤ ∫ ω, g ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  obtain ⟨iS4, -, -, eS4⟩ := sum_four_pi μ mg ig4 eg0 k
  have hsub : {us : Fin k → Ω | k * b₁ + a < ∑ j, f (us j)} ⊆
      {us | a ^ 4 ≤ sumG g k us ^ 4} := by
    intro us hus
    simp only [mem_ofPred_eq] at hus ⊢
    have e : sumG g k us = ∑ j, f (us j) - k * c := by
      simp only [sumG, hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : a ≤ sumG g k us := by
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left m1 hk0]
    exact pow_le_pow_left₀ ha.le this 4
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := Measure.pi fun _ : Fin k => μ) (f := fun us => sumG g k us ^ 4)
    (Filter.Eventually.of_forall fun us => by positivity) iS4 (a ^ 4)
  have ha4 : 0 < a ^ 4 := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hI : ∫ us, sumG g k us ^ 4 ∂(Measure.pi fun _ : Fin k => μ) ≤
      k * (8 * b₄ + 8 * b₁ ^ 4) + 3 * k ^ 2 * b₂ ^ 2 := by
    rw [eS4]
    have h5 : (∫ ω, g ω ^ 2 ∂μ) ^ 2 ≤ b₂ ^ 2 := pow_le_pow_left₀ mg2' mg2 2
    have h6 : 3 * (k : ℝ) * (k - 1) * (∫ ω, g ω ^ 2 ∂μ) ^ 2 ≤ 3 * k ^ 2 * b₂ ^ 2 := by
      have h7 : 0 ≤ (∫ ω, g ω ^ 2 ∂μ) ^ 2 := sq_nonneg _
      have h8 : 3 * (k : ℝ) * (k - 1) ≤ 3 * k ^ 2 := by nlinarith
      rcases le_total (3 * (k : ℝ) * (k - 1)) 0 with hneg | hpos
      · have : 3 * (k : ℝ) * (k - 1) * (∫ ω, g ω ^ 2 ∂μ) ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hneg h7
        have : 0 ≤ 3 * (k : ℝ) ^ 2 * b₂ ^ 2 := by positivity
        linarith
      · exact mul_le_mul h8 h5 h7 (by positivity)
    have h9 := mul_le_mul_of_nonneg_left mg4 hk0
    linarith
  rw [le_div_iff₀ ha4]
  calc (Measure.pi fun _ : Fin k => μ).real {us | k * b₁ + a < ∑ j, f (us j)} * a ^ 4
      ≤ (Measure.pi fun _ : Fin k => μ).real {us | a ^ 4 ≤ sumG g k us ^ 4} * a ^ 4 :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) ha4.le
    _ = a ^ 4 * (Measure.pi fun _ : Fin k => μ).real {us | a ^ 4 ≤ sumG g k us ^ 4} :=
        mul_comm _ _
    _ ≤ _ := hmk.trans hI

/-- The arithmetic of the charge of Lemma TR. -/
lemma charge_arith {m δ U : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hU : 0 < U) :
    (m * (8 * (1680 * U ^ 4) + 8 * U ^ 4) + 3 * m ^ 2 * (12 * U ^ 2) ^ 2) / (δ * (m * U)) ^ 4 ≤
      432 / m ^ 2 * (1 + 63 / m) / δ ^ 4 := by
  have e1 : (m * (8 * (1680 * U ^ 4) + 8 * U ^ 4) + 3 * m ^ 2 * (12 * U ^ 2) ^ 2) /
      (δ * (m * U)) ^ 4 = (13448 * m + 432 * m ^ 2) / (m ^ 4 * δ ^ 4) := by
    field_simp
    ring
  have e2 : 432 / m ^ 2 * (1 + 63 / m) / δ ^ 4 = (27216 * m + 432 * m ^ 2) / (m ^ 4 * δ ^ 4) := by
    field_simp
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- **The tail in the unit `U`.** `f ≥ 0` with `E f ≤ U`, `E f² ≤ 12U²`, `E f⁴ ≤ 1680U⁴`
(`U > 0`), `k ≥ 1` independent copies, `δ > 0`:
`Pr(Σ_j f(ω_j) > (1 + δ)·k·U) ≤ (432/k²)(1 + 63/k)/δ⁴`. -/
theorem tail_pi_U {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {U : ℝ} (hU : 0 < U)
    (h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal U)
    (h2 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ ≤ ENNReal.ofReal (12 * U ^ 2))
    (h4 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 4) ∂μ ≤ ENNReal.ofReal (1680 * U ^ 4)) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin k => μ).real {us | (1 + δ) * (k * U) < ∑ j, f (us j)} ≤
      432 / (k : ℝ) ^ 2 * (1 + 63 / k) / δ ^ 4 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := tail_pi μ hf hf0 hU.le (by positivity) (by positivity) h1 h2 h4 k
    (a := δ * (k * U)) (by positivity)
  have e : {us : Fin k → Ω | (1 + δ) * (k * U) < ∑ j, f (us j)} =
      {us | k * U + δ * (k * U) < ∑ j, f (us j)} := by
    ext us
    simp only [mem_ofPred_eq]
    rw [show (1 + δ) * (k * U) = k * U + δ * (k * U) by ring]
  rw [e]
  exact h.trans (charge_arith hk0 hδ hU)

end G7

/-! ## The rows of a Gaussian matrix -/

section rows

variable {m d : ℕ}

/-- The distribution of one row of a Gaussian matrix with entry variance `v`: `√v • ξ`, `ξ` a
standard Gaussian vector of `ℝ^d`. -/
noncomputable def rowDist (d : ℕ) (v : ℝ) : Measure (Fin d → ℝ) :=
  (stdGauss (Fin d)).map (fun ξ => √v • ξ)

instance (d : ℕ) (v : ℝ) : IsProbabilityMeasure (rowDist d v) := by
  unfold rowDist
  exact (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).mpr
    inferInstance

lemma lintegral_rowDist (v : ℝ) {F : (Fin d → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ r, F r ∂rowDist d v = ∫⁻ ξ, F (√v • ξ) ∂stdGauss (Fin d) := by
  unfold rowDist
  rw [lintegral_map hF (measurable_const_smul _)]

lemma measurable_ofRows :
    Measurable (fun r : Fin m → Fin d → ℝ => (Matrix.of r : Matrix (Fin m) (Fin d) ℝ)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- A standard Gaussian family indexed by pairs is a family of independent standard Gaussian
rows. -/
lemma stdGauss_pairs :
    (Measure.pi fun _ : Fin m => stdGauss (Fin d)).map
      (fun r (p : Fin m × Fin d) => r p.1 p.2) = stdGauss (Fin m × Fin d) := by
  have hmeas : Measurable (fun (r : Fin m → Fin d → ℝ) (p : Fin m × Fin d) => r p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  unfold stdGauss
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have e : (fun (r : Fin m → Fin d → ℝ) (p : Fin m × Fin d) => r p.1 p.2) ⁻¹' (univ.pi s) =
      univ.pi fun i : Fin m => univ.pi fun j : Fin d => s (i, j) := by
    ext r
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, Prod.forall]
  rw [e, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- **The rows of a Gaussian matrix are independent**, each with the distribution of `√v • ξ`:
`gaussMat m d v` is the image of the product of `m` copies of `rowDist d v` under the map from
rows to matrices. -/
theorem gaussMat_rows (m d : ℕ) (v : ℝ) :
    gaussMat m d v = (Measure.pi fun _ : Fin m => rowDist d v).map
      (fun r : Fin m → Fin d → ℝ => (Matrix.of r : Matrix (Fin m) (Fin d) ℝ)) := by
  have hpairs : Measurable (fun (r : Fin m → Fin d → ℝ) (p : Fin m × Fin d) => r p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hT : Measurable (fun ξ : Fin m × Fin d → ℝ =>
      (Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin m) (Fin d) ℝ)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      measurable_const.mul (measurable_pi_apply (i, j))
  have h2 := Measure.pi_map_pi (μ := fun _ : Fin m => stdGauss (Fin d))
    (f := fun _ => fun ξ : Fin d → ℝ => √v • ξ)
    (hμ := fun i => by
      have : IsProbabilityMeasure ((stdGauss (Fin d)).map fun ξ : Fin d → ℝ => √v • ξ) :=
        (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).mpr
          inferInstance
      infer_instance)
    (fun _ => (measurable_const_smul _).aemeasurable)
  have hsm : Measurable (fun (r : Fin m → Fin d → ℝ) (i : Fin m) => √v • r i) :=
    measurable_pi_iff.mpr fun i => (measurable_const_smul _).comp (measurable_pi_apply i)
  unfold gaussMat rowDist
  rw [← stdGauss_pairs, Measure.map_map hT hpairs, ← h2, Measure.map_map measurable_ofRows hsm]
  rfl

/-- The probability of an event of the rows. -/
lemma gaussMat_rows_real (v : ℝ) {S : Set (Fin m → Fin d → ℝ)} (hS : MeasurableSet S) :
    (gaussMat m d v).real {M | (fun j => rowOf j M) ∈ S} =
      (Measure.pi fun _ : Fin m => rowDist d v).real S := by
  have hrows : Measurable (fun M : Matrix (Fin m) (Fin d) ℝ => fun j => rowOf j M) :=
    measurable_pi_iff.mpr fun j => measurable_rowOf j
  have hSet : MeasurableSet {M : Matrix (Fin m) (Fin d) ℝ | (fun j => rowOf j M) ∈ S} :=
    hrows hS
  rw [gaussMat_rows, map_measureReal_apply measurable_ofRows hSet]
  rfl

/-- **The tail for the rows of a Gaussian matrix.** `M ∼ gaussMat m d v`, `f ≥ 0` measurable
with `E f(w) ≤ U`, `E f(w)² ≤ 12U²`, `E f(w)⁴ ≤ 1680U⁴` for `w = √v • ξ` (`U > 0`), `m ≥ 1`,
`δ > 0`: `Pr(Σ_j f(row_j M) > (1 + δ)·m·U) ≤ (432/m²)(1 + 63/m)/δ⁴`. -/
theorem tail_rows {v : ℝ} {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    {U : ℝ} (hU : 0 < U)
    (h1 : ∫⁻ ξ, ENNReal.ofReal (f (√v • ξ)) ∂stdGauss (Fin d) ≤ ENNReal.ofReal U)
    (h2 : ∫⁻ ξ, ENNReal.ofReal (f (√v • ξ) ^ 2) ∂stdGauss (Fin d) ≤ ENNReal.ofReal (12 * U ^ 2))
    (h4 : ∫⁻ ξ, ENNReal.ofReal (f (√v • ξ) ^ 4) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (1680 * U ^ 4)) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMat m d v).real {M | (1 + δ) * (m * U) < ∑ j, f (rowOf j M)} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ ^ 4 := by
  have hS : MeasurableSet {r : Fin m → Fin d → ℝ | (1 + δ) * (m * U) < ∑ j, f (r j)} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j))
  have e := gaussMat_rows_real (m := m) (d := d) v hS
  have e' : {M : Matrix (Fin m) (Fin d) ℝ | (1 + δ) * (m * U) < ∑ j, f (rowOf j M)} =
      {M | (fun j => rowOf j M) ∈ {r : Fin m → Fin d → ℝ |
        (1 + δ) * (m * U) < ∑ j, f (r j)}} := rfl
  rw [e', e]
  refine tail_pi_U (rowDist d v) hf hf0 hU ?_ ?_ ?_ hm hδ
  · rw [lintegral_rowDist v (F := fun w => ENNReal.ofReal (f w))
      (ENNReal.measurable_ofReal.comp hf)]
    exact h1
  · rw [lintegral_rowDist v (F := fun w => ENNReal.ofReal (f w ^ 2))
      (ENNReal.measurable_ofReal.comp (hf.pow_const 2))]
    exact h2
  · rw [lintegral_rowDist v (F := fun w => ENNReal.ofReal (f w ^ 4))
      (ENNReal.measurable_ofReal.comp (hf.pow_const 4))]
    exact h4

end rows

end BstLean.Part151
