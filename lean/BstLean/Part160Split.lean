import BstLean.Part160Defs

/-!
# Part 160 (file `Split`): the deterministic frame split

Role: `delegations/statements/p160-spec.md`, item 1. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:split` (formulas
`t7:p04:cr` and `t7:p04:frame`); `theorem7-09-assembly.tex`, the frame arithmetic.

General part (a probability measure `μ` on any measurable space, a measurable field
`h : Ω → ℝ^m`, any vector `b`; `r = res b h`, `e = eDir b h = r/|r|`):

* `eDir_sq_le`: pointwise, `⟨e, w⟩² ≤ ⟨r, w⟩²/a + 1{|r|² < a}·|w|²`, every `a > 0`.
* `frame_split`: `∫ ⟨e, w⟩² dμ ≤ (1/a)·∫ ⟨r, w⟩² dμ + μ{|r|² < a}·|w|²`.
* `resid_second_moment`: the EXACT identity `C_r = P Cov(h) P + (Pμ)(Pμ)ᵀ` as quadratic forms:
  `∫ ⟨r, w⟩² dμ = ∫ ⟨h − μ, P w⟩² dμ + ⟨P μ, w⟩²`, `P = res b`.
* `resid_second_moment_le`: `t·∫ ⟨r, w⟩² dμ ≤ (V + t·|μ − b|²)·|w|²` if `t·Var⟨h, u⟩ ≤ V·|u|²`.

For the networks:

* `frameA_at`: at one retained value, `COV_at`, `CENTRE_at`, `MASS_at` with
  `(N + ξ)/d + β ≤ c_f` give the frame bound `c_f/n`.
* `frameA_of_three`: `FRAME_A_hyp D (c_f/n) E` from `COV_hyp`, `CENTRE_hyp`, `MASS_hyp` on `E`.
* `frameA_paper_numbers`: the numeric instance with the paper's values
  `(0.341973 + 0.0832)/0.258897 + 0.1 ≤ 1.743`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part156 (cfL)

section general

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- `⟨res b h, w⟩ = ⟨h, res b w⟩`: the map `res b` is symmetric (every `b`, also `b = 0`). -/
lemma res_symm (b h w : Fin m → ℝ) :
    ∑ j, res b h j * w j = ∑ j, h j * res b w j := by
  unfold res lam
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  have e1 : ∑ j, (∑ i, h i * b i) / normSq b * b j * w j =
      (∑ i, h i * b i) / normSq b * ∑ j, w j * b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, h j * ((∑ i, w i * b i) / normSq b * b j) =
      (∑ i, w i * b i) / normSq b * ∑ j, h j * b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring

/-- `res b b = 0` (every `b`). -/
lemma res_self (b : Fin m → ℝ) : res b b = 0 := by
  by_cases hb : normSq b = 0
  · have := eq_zero_of_normSq hb
    subst this
    unfold res
    simp
  · unfold res lam
    have e : ∑ j, b j * b j = normSq b := by
      unfold normSq
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, div_self hb, one_smul, sub_self]

/-- `res b` is additive in the second argument. -/
lemma res_sub (b h h' : Fin m → ℝ) : res b (h - h') = res b h - res b h' := by
  unfold res lam
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  ring

/-- `|res b w|² ≤ |w|²` (every `b`). -/
lemma normSq_res_le (b w : Fin m → ℝ) : normSq (res b w) ≤ normSq w := by
  by_cases hb : normSq b = 0
  · have := eq_zero_of_normSq hb
    subst this
    unfold res
    simp
  · have h := BstLean.Part153.normSq_projB_le_cr hb w
    have e : res b w = BstLean.Part153.projB_cr b w := by
      unfold res lam BstLean.Part153.projB_cr
      rfl
    rw [e]
    exact h

lemma sum_mul_sq_le (u v : Fin m → ℝ) : (∑ j, u j * v j) ^ 2 ≤ normSq u * normSq v :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The pointwise frame split**: `⟨e, w⟩² ≤ ⟨r, w⟩²/a + 1{|r|² < a}·|w|²`. -/
lemma eDir_sq_le (b h w : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    (∑ j, eDir b h j * w j) ^ 2 ≤
      1 / a * (∑ j, res b h j * w j) ^ 2 +
        (if normSq (res b h) < a then ∑ j, w j ^ 2 else 0) := by
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : 0 ≤ 1 / a * (∑ j, res b h j * w j) ^ 2 := by positivity
  by_cases hlt : normSq (res b h) < a
  · simp only [hlt, ↓reduceIte]
    have cs := sum_mul_sq_le (eDir b h) w
    have he : normSq (eDir b h) ≤ 1 := by
      rcases eDir_unit_or_zero b h with h1 | h1
      · exact h1.le
      · rw [h1]; simp [normSq]
    have : normSq (eDir b h) * normSq w ≤ 1 * normSq w :=
      mul_le_mul_of_nonneg_right he (normSq_nonneg w)
    have e : normSq w = ∑ j, w j ^ 2 := rfl
    linarith
  · simp only [hlt, ↓reduceIte, add_zero]
    have hN : a ≤ normSq (res b h) := not_lt.mp hlt
    have hN0 : 0 < normSq (res b h) := lt_of_lt_of_le ha hN
    have e : ∑ j, eDir b h j * w j =
        (Real.sqrt (normSq (res b h)))⁻¹ * ∑ j, res b h j * w j := by
      unfold eDir
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]
    rw [e, mul_pow, inv_pow, Real.sq_sqrt hN0.le]
    have h2 : (normSq (res b h))⁻¹ ≤ 1 / a := by
      rw [one_div]
      exact inv_anti₀ ha hN
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- **The frame split** (Lemma `t7:p04:split`, formula `t7:p04:frame`, before the division by
`γ_A d`): for every `a > 0`,
`∫ ⟨e, w⟩² dμ ≤ (1/a)·∫ ⟨r, w⟩² dμ + μ{|r|² < a}·|w|²`. No probability event is used. -/
theorem frame_split (μ : Measure Ω) [IsProbabilityMeasure μ] {h : Ω → Fin m → ℝ}
    (hh : Measurable h) (b w : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (hint : Integrable (fun x => (∑ j, res b (h x) j * w j) ^ 2) μ) :
    ∫ x, (∑ j, eDir b (h x) j * w j) ^ 2 ∂μ ≤
      1 / a * ∫ x, (∑ j, res b (h x) j * w j) ^ 2 ∂μ +
        μ.real {x | normSq (res b (h x)) < a} * ∑ j, w j ^ 2 := by
  have hS : MeasurableSet {x | normSq (res b (h x)) < a} :=
    measurableSet_lt (measurable_normSq.comp ((measurable_res b).comp hh)) measurable_const
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hmL : Measurable (fun x => (∑ j, eDir b (h x) j * w j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_eDir b).comp hh)).mul_const _).pow_const 2
  have hiL : Integrable (fun x => (∑ j, eDir b (h x) j * w j) ^ 2) μ := by
    refine Integrable.of_bound hmL.aestronglyMeasurable (∑ j, w j ^ 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have cs := sum_mul_sq_le (eDir b (h x)) w
    have he : normSq (eDir b (h x)) ≤ 1 := by
      rcases eDir_unit_or_zero b (h x) with h1 | h1
      · exact h1.le
      · rw [h1]; simp [normSq]
    have : normSq (eDir b (h x)) * normSq w ≤ 1 * normSq w :=
      mul_le_mul_of_nonneg_right he (normSq_nonneg w)
    have e : normSq w = ∑ j, w j ^ 2 := rfl
    linarith
  have hiI : Integrable (fun x => if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) μ := by
    have : (fun x => if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) =
        Set.indicator {x | normSq (res b (h x)) < a} (fun _ => ∑ j, w j ^ 2) := by
      funext x
      simp [Set.indicator]
    rw [this]
    exact (integrable_const _).indicator hS
  have hI : ∫ x, (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) ∂μ =
      μ.real {x | normSq (res b (h x)) < a} * ∑ j, w j ^ 2 := by
    have : (fun x => if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) =
        Set.indicator {x | normSq (res b (h x)) < a} (fun _ => ∑ j, w j ^ 2) := by
      funext x
      simp [Set.indicator]
    rw [this, integral_indicator_const _ hS, smul_eq_mul]
  calc ∫ x, (∑ j, eDir b (h x) j * w j) ^ 2 ∂μ
      ≤ ∫ x, (1 / a * (∑ j, res b (h x) j * w j) ^ 2 +
          (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0)) ∂μ :=
        integral_mono hiL ((hint.const_mul _).add hiI) fun x => eDir_sq_le b (h x) w ha
    _ = _ := by
        rw [integral_add (hint.const_mul _) hiI, integral_const_mul, hI]

/-- **The second moment of the residual, exact identity** (Lemma `t7:p04:split`, formula
`t7:p04:cr`, as quadratic forms): `C_r = P Cov(h) P + (Pμ)(Pμ)ᵀ`, that is
`∫ ⟨r, w⟩² dμ = ∫ ⟨h − μ, P w⟩² dμ + ⟨P μ, w⟩²` with `P = res b` and `μ = ∫ h dμ`. -/
theorem resid_second_moment (μ : Measure Ω) [IsProbabilityMeasure μ] {h : Ω → Fin m → ℝ}
    (b w mu : Fin m → ℝ)
    (hi1 : ∀ u : Fin m → ℝ, Integrable (fun x => ∑ j, h x j * u j) μ)
    (hi2 : ∀ u : Fin m → ℝ, Integrable (fun x => (∑ j, h x j * u j) ^ 2) μ)
    (hmu : ∀ u : Fin m → ℝ, ∫ x, ∑ j, h x j * u j ∂μ = ∑ j, mu j * u j) :
    ∫ x, (∑ j, res b (h x) j * w j) ^ 2 ∂μ =
      ∫ x, (∑ j, (h x j - mu j) * res b w j) ^ 2 ∂μ + (∑ j, res b mu j * w j) ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u : Fin m → ℝ, u = res b w := ⟨_, rfl⟩
  rw [← hu, res_symm b mu w, ← hu]
  simp_rw [res_symm b _ w, ← hu]
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j, mu j * u j := ⟨_, rfl⟩
  have e : ∀ x, (∑ j, (h x j - mu j) * u j) ^ 2 =
      (∑ j, h x j * u j) ^ 2 - 2 * M * (∑ j, h x j * u j) + M ^ 2 := by
    intro x
    have : ∑ j, (h x j - mu j) * u j = ∑ j, h x j * u j - M := by
      rw [hM, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  simp_rw [e]
  have i1 := hi2 u
  have i2 := (hi1 u).const_mul (2 * M)
  have hsplit : ∫ x, ((∑ j, h x j * u j) ^ 2 - 2 * M * (∑ j, h x j * u j) + M ^ 2) ∂μ =
      ∫ x, (∑ j, h x j * u j) ^ 2 ∂μ - 2 * M * M + M ^ 2 := by
    have hA : ∫ x, ((∑ j, h x j * u j) ^ 2 - 2 * M * (∑ j, h x j * u j) + M ^ 2) ∂μ =
        ∫ x, ((∑ j, h x j * u j) ^ 2 - 2 * M * (∑ j, h x j * u j)) ∂μ + ∫ _x, M ^ 2 ∂μ :=
      integral_add (i1.sub i2) (integrable_const _)
    have hB : ∫ x, ((∑ j, h x j * u j) ^ 2 - 2 * M * (∑ j, h x j * u j)) ∂μ =
        ∫ x, (∑ j, h x j * u j) ^ 2 ∂μ - ∫ x, 2 * M * (∑ j, h x j * u j) ∂μ :=
      integral_sub i1 i2
    rw [hA, hB, integral_const_mul, hmu u, ← hM, integral_const, probReal_univ, one_smul]
  rw [hsplit, ← hM]
  ring

/-- **The norm of `C_r`**: if `t·Var⟨h, u⟩ ≤ V·|u|²` for every `u`, then
`t·∫ ⟨r, w⟩² dμ ≤ (V + t·|μ − b|²)·|w|²` (`‖C_r‖ ≤ ‖t Cov(h)‖ + t|μ − b|²`). -/
theorem resid_second_moment_le (μ : Measure Ω) [IsProbabilityMeasure μ] {h : Ω → Fin m → ℝ}
    (b w mu : Fin m → ℝ)
    (hi1 : ∀ u : Fin m → ℝ, Integrable (fun x => ∑ j, h x j * u j) μ)
    (hi2 : ∀ u : Fin m → ℝ, Integrable (fun x => (∑ j, h x j * u j) ^ 2) μ)
    (hmu : ∀ u : Fin m → ℝ, ∫ x, ∑ j, h x j * u j ∂μ = ∑ j, mu j * u j)
    {t V : ℝ} (ht : 0 ≤ t) (hV0 : 0 ≤ V)
    (hV : ∀ u : Fin m → ℝ, t * ∫ x, (∑ j, (h x j - mu j) * u j) ^ 2 ∂μ ≤ V * ∑ j, u j ^ 2) :
    t * ∫ x, (∑ j, res b (h x) j * w j) ^ 2 ∂μ ≤
      (V + t * normSq (mu - b)) * ∑ j, w j ^ 2 := by
  rw [resid_second_moment μ b w mu hi1 hi2 hmu, mul_add]
  have h1 := hV (res b w)
  have h2 : ∑ j, res b w j ^ 2 ≤ ∑ j, w j ^ 2 := normSq_res_le b w
  have h3 : (∑ j, res b mu j * w j) ^ 2 ≤ normSq (mu - b) * ∑ j, w j ^ 2 := by
    have e : res b mu = res b (mu - b) := by rw [res_sub, res_self, sub_zero]
    rw [e, res_symm]
    have cs := sum_mul_sq_le (mu - b) (res b w)
    have : normSq (mu - b) * normSq (res b w) ≤ normSq (mu - b) * normSq w :=
      mul_le_mul_of_nonneg_left (normSq_res_le b w) (normSq_nonneg _)
    exact cs.trans this
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h4 : V * ∑ j, res b w j ^ 2 ≤ V * ∑ j, w j ^ 2 := mul_le_mul_of_nonneg_left h2 hV0
  have h5 : t * (∑ j, res b mu j * w j) ^ 2 ≤ t * (normSq (mu - b) * ∑ j, w j ^ 2) :=
    mul_le_mul_of_nonneg_left h3 ht
  nlinarith

end general

variable {n : ℕ}

/-! ## The reduction for the networks -/

lemma hStand_int1 (hn : 1 ≤ n) (D : Design n) (c : Ret n) (u : Fin (mA n) → ℝ) :
    Integrable (fun ξ => ∑ j, hStand D c ξ j * u j) (stdGauss (Fin n)) := by
  have h := BstLean.Part153.integrable_dot_hid2_cr hn c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) u
  have e : (fun ξ => ∑ j, hStand D c ξ j * u j) =
      fun ξ => u ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) := by
    funext ξ
    unfold dotProduct
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]; exact h

lemma hStand_int2 (hn : 1 ≤ n) (D : Design n) (c : Ret n) (u : Fin (mA n) → ℝ) :
    Integrable (fun ξ => (∑ j, hStand D c ξ j * u j) ^ 2) (stdGauss (Fin n)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  obtain ⟨hm, hb⟩ :=
    BstLean.Part153.dot_hid2_bdd_cr hn c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) u
  have e : (fun ξ => (∑ j, hStand D c ξ j * u j) ^ 2) =
      fun ξ => (u ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))) ^ 2 := by
    funext ξ
    unfold dotProduct
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable
    ((BstLean.Part153.nrm u * (BstLean.Part152.opN c.2.1.1.2 * BstLean.Part152.opN c.2.1.1.1)) ^ 2)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq' (by linarith [(abs_le.mp (hb ξ)).1]) (abs_le.mp (hb ξ)).2

lemma hStand_mean (hn : 1 ≤ n) (D : Design n) (c : Ret n) (u : Fin (mA n) → ℝ) :
    ∫ ξ, ∑ j, hStand D c ξ j * u j ∂stdGauss (Fin n) = ∑ j, muStand D c j * u j := by
  have h := BstLean.Part153.integral_dot_hid2_cr hn c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) u
  have e : (fun ξ => ∑ j, hStand D c ξ j * u j) =
      fun ξ => u ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) := by
    funext ξ
    unfold dotProduct
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e, h, muStand_eq]
  unfold dotProduct
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma measurable_hStand (D : Design n) (c : Ret n) : Measurable (hStand D c) :=
  BstLean.Part153.measurable_hid2_sph_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)

/-- **The second moment of the scaled residual at one retained value**:
`t_A·∫ ⟨r, w⟩² ≤ (N + ξ)·(γ_A/n)·|w|²` from `COV_at` and `CENTRE_at`
(`‖C_r‖ ≤ ‖t_A Cov(h)‖ + t_A|μ − b|²`). -/
theorem Cr_at (hn : 1 ≤ n) (D : Design n) (c : Ret n) {N xi : ℝ} (hN : 0 ≤ N)
    (hcov : COV_at D c N) (hcen : CENTRE_at D c xi) (w : Fin (mA n) → ℝ) :
    2 / (mA n : ℝ) * ∫ ξ, (∑ j, res (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2
        ∂stdGauss (Fin n) ≤ (N + xi) * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h := resid_second_moment_le (stdGauss (Fin n)) (D.bA c.1 c.2.1.1) w (muStand D c)
    (hStand_int1 hn D c) (hStand_int2 hn D c) (hStand_mean hn D c)
    (t := 2 / (mA n : ℝ)) (V := N * (2 / (n : ℝ)) / n) (by positivity) (by positivity) hcov
  unfold CENTRE_at at hcen
  have : (N * (2 / (n : ℝ)) / n + 2 / (mA n : ℝ) * normSq (muStand D c - D.bA c.1 c.2.1.1)) *
      ∑ j, w j ^ 2 ≤ (N * (2 / (n : ℝ)) / n + xi * (2 / (n : ℝ)) / n) * ∑ j, w j ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hW
  calc _ ≤ _ := h
    _ ≤ _ := this
    _ = _ := by ring

/-- **The frame bound at one retained value from the three scalar bounds** (Lemma
`t7:p04:split` with the frame arithmetic of Part 09): `n·L_A ≤ (N_cov + ξ)/d + β`. -/
theorem frameA_at (hn : 1 ≤ n) (D : Design n) (c : Ret n) {N xi d β cf : ℝ} (hd : 0 < d)
    (hN : 0 ≤ N) (hcov : COV_at D c N) (hcen : CENTRE_at D c xi) (hmass : MASS_at D c d β)
    (hsum : (N + xi) / d + β ≤ cf) (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨b, hb⟩ : ∃ b : Fin (mA n) → ℝ, b = D.bA c.1 c.2.1.1 := ⟨_, rfl⟩
  rw [← hb]
  -- the cutoff of `|r|²`: `a = γ_A d / t_A`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 / (n : ℝ) * d / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hint : Integrable (fun ξ => (∑ j, res b (hStand D c ξ) j * w j) ^ 2) (stdGauss (Fin n)) := by
    simp_rw [res_symm b _ w]
    exact hStand_int2 hn D c (res b w)
  have h1 := frame_split (stdGauss (Fin n)) (measurable_hStand D c) b w ha0 hint
  have h2 := Cr_at hn D c hN hcov hcen w
  rw [← hb] at h2
  have hset : {ξ : Fin n → ℝ | normSq (res b (hStand D c ξ)) < a} =
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hStand D c ξ)) < 2 / (n : ℝ) * d} := by
    ext ξ
    change normSq (res b (hStand D c ξ)) < a ↔
      2 / (mA n : ℝ) * normSq (res b (hStand D c ξ)) < 2 / (n : ℝ) * d
    rw [ha, lt_div_iff₀ (by positivity), mul_comm]
  unfold MASS_at at hmass
  rw [← hb, ← hset] at hmass
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (stdGauss (Fin n)).real
      {ξ : Fin n → ℝ | normSq (res b (hStand D c ξ)) < a} := ⟨_, rfl⟩
  rw [← hP] at h1 hmass
  have hP0 : 0 ≤ P := by rw [hP]; exact measureReal_nonneg
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ ξ, (∑ j, res b (hStand D c ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hI] at h1 h2
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, w j ^ 2 := ⟨_, rfl⟩
  rw [← hS] at h1 h2 hW ⊢
  -- `(1/a)·I ≤ (N + ξ)/(d n)·|w|²`
  have h3 : 1 / a * I ≤ (N + xi) / d / n * S := by
    have e : 1 / a * I = (2 / (mA n : ℝ) * I) / (2 / (n : ℝ) * d) := by
      rw [ha]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (N + xi) / d / n * S * (2 / (n : ℝ) * d) = (N + xi) * (2 / (n : ℝ)) / n * S := by
      field_simp
    rw [e2]; exact h2
  have h4 : P * S ≤ β / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hW
    rw [le_div_iff₀ hnR]; linarith
  have h5 : ((N + xi) / d / n + β / n) * S ≤ cf / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hW
    rw [← add_div]
    exact div_le_div_of_nonneg_right hsum hnR.le
  linarith

/-- **`FRAME_A_hyp` from the three scalar hypotheses** (item 1 of the specification): IF on a
set `E` of retained values `n‖t_A Cov(h)‖/γ_A ≤ N_cov` (`COV_hyp`), `n t_A|μ − b|²/γ_A ≤ ξ`
(`CENTRE_hyp`) and `n β_d ≤ β` (`MASS_hyp`), with `(N_cov + ξ)/d + β ≤ c_f`, THEN the Agent frame
bound `c_f/n` holds on `E`. -/
theorem frameA_of_three (hn : 1 ≤ n) (D : Design n) {E : Set (Ret n)} {N xi d β cf : ℝ}
    (hd : 0 < d) (hN : 0 ≤ N) (hcov : COV_hyp D N E) (hcen : CENTRE_hyp D xi E)
    (hmass : MASS_hyp D d β E) (hsum : (N + xi) / d + β ≤ cf) :
    FRAME_A_hyp D (cf / n) E :=
  fun c hc w => frameA_at hn D c hd hN (hcov c hc) (hcen c hc) (hmass c hc) hsum w

/-- The frame arithmetic of the paper (Part 09):
`(0.341973 + 0.0832)/0.258897 + 0.1 ≤ 1.743`. -/
lemma paper_frame_arith :
    ((341973 : ℝ) / 10 ^ 6 + 832 / 10 ^ 4) / (258897 / 10 ^ 6) + 1 / 10 ≤ cfL := by
  unfold cfL; norm_num

/-- **The numeric instance with the paper's values**: `N_cov = 0.341973` (Proposition
`t7:p04:certificate`), `ξ′ = 0.0832` (Proposition `t7:p05:certificate`), cutoff `d = 0.258897`
and `n β_d ≤ 0.1` (Proposition `t7:p06:cutoffs`) give `FRAME_A_hyp D (1.743/n) E`. The three
hypotheses are NOT proved in Lean at these values. -/
theorem frameA_paper_numbers (hn : 1 ≤ n) (D : Design n) {E : Set (Ret n)}
    (hcov : COV_hyp D (341973 / 10 ^ 6) E) (hcen : CENTRE_hyp D (832 / 10 ^ 4) E)
    (hmass : MASS_hyp D (258897 / 10 ^ 6) (1 / 10) E) :
    FRAME_A_hyp D (cfL / n) E :=
  frameA_of_three hn D (by norm_num) (by norm_num) hcov hcen hmass paper_frame_arith

end BstLean.Part160

open BstLean.Part160 in
#print axioms frame_split
open BstLean.Part160 in
#print axioms resid_second_moment
open BstLean.Part160 in
#print axioms resid_second_moment_le
open BstLean.Part160 in
#print axioms frameA_of_three
open BstLean.Part160 in
#print axioms frameA_paper_numbers
