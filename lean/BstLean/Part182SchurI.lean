import BstLean.Part182Schur

/-!
# Part 182 (file `SchurI`): the weighted Schur test for the network quadratic form `Dq`

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:schur`
(formula (t7:p04:schur-formula)) with Lemma `t7:p04:MS` (`K_i^MS = λ_i`), WITHOUT the tangential
gain `χ`. Fix `A₁`, `A₂`, `c`, `τ > 0`, `n ≥ 6`; `w = τ²/|c + τξ|²` (`wN`), `B = 𝒥(x)Π_x` (`BJ`).

* `Dq_eq_w`, `Xi4_eq_A4`: `Dq = t∫ w|vᵀB|²`, `Ξ₄ = t√A`, `A = ∫ w²‖B‖⁴` (`A4`).
* `schur_level`: one level (inputs `S`) of the Schur test, from `schur_abstract`.
* `out_level`: the outside inputs, `∫ 1_S w|vᵀB|² ≤ √(μ(S)·A)|v|²`.
* `Dq_split`: `Dq` over the partition `Ω₁`, `Ω₀ ∖ Ω₁`, `Ω₀ᶜ`.
* **`Dq_le_twolevel`**: core + shell + outside with free kernels and row bounds.
* `kern`, `row_bound`: the two-valued kernel and its row bound from simple data.
* **`Dq_le_kern`**: the paper's form:
  `Dq ≤ [t(nλ₁E_w + nλ₀W̄P_p + nλ₀W̄P_s) + Ξ₄(H₁^{1/4} + H₀^{1/4} + P_o^{1/2})]|v|²`, where
  `H₁ = μ⊗μ(G₁ᶜ ∩ Ω₁²)`, `H₀ = μ⊗μ(G₀ᶜ ∩ (Ω₀∖Ω₁)²)`, `P_o = μ(Ω₀ᶜ)`.
  Differences from (t7:p04:schur-formula): no `χ` (so `λ` in place of `K₁`); the outside term is
  `Ξ₄√P_o` as in the paper; each exceptional term is the pair mass of its own level.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm nrm_nonneg nrm_sq jacT Xi4 opN_jacT_le_sj measurable_opN_jacT_sj
  measurable_jacT invMoment_one_le invMoment_two_le cont_ns)

variable {n m : ℕ}

/-- The weight `w(ξ) = τ²/|c + τξ|²`. -/
noncomputable def wN (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ := τ ^ 2 * (normSq (c + τ • ξ))⁻¹

/-- The tangent Jacobian at the input of `ξ`. -/
noncomputable def BJ (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  jacT A₁ A₂ (sphPt (c + τ • ξ))

lemma wN_nonneg (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : 0 ≤ wN c τ ξ :=
  mul_nonneg (sq_nonneg _) (inv_nonneg.2 (normSq_nonneg _))

lemma measurable_wN (c : Fin n → ℝ) (τ : ℝ) : Measurable (wN c τ) :=
  measurable_const.mul (cont_ns c τ).measurable.inv

lemma integrable_wN (hn : 4 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (wN c τ) (stdGauss (Fin n)) :=
  (invMoment_one_le hn c hτ).1.const_mul _

lemma integrable_wN2 (hn : 6 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ => wN c τ ξ ^ 2) (stdGauss (Fin n)) := by
  have h := (invMoment_two_le hn c hτ).1.const_mul (τ ^ 4)
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [wN]; ring

lemma measurable_BJ_entry (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) (j : Fin n) :
    Measurable (fun ξ => BJ A₁ A₂ c τ ξ i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp ((measurable_jacT A₁ A₂).comp
    (measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ)))))

/-- `Dq = t·∫ w |vᵀB|²`. -/
lemma Dq_eq_w (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (v : Fin m → ℝ) :
    Dq A₁ A₂ c τ v = 2 / (m : ℝ) * ∫ ξ, wN c τ ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ))
      ∂stdGauss (Fin n) := by
  unfold Dq
  rw [mul_assoc, ← integral_const_mul]
  congr 2; funext ξ
  simp only [wN, BJ]; ring

/-- The fourth-moment quantity `A = ∫ w²‖B‖⁴` and `Ξ₄ = t·√A`. -/
noncomputable def A4 (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∫ ξ, wN c τ ξ ^ 2 * opN (BJ A₁ A₂ c τ ξ) ^ 4 ∂stdGauss (Fin n)

lemma Xi4_eq_A4 (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : Xi4 A₁ A₂ c τ = 2 / (m : ℝ) * √(A4 A₁ A₂ c τ) := by
  unfold Xi4 A4
  have e : ∫ ξ, wN c τ ξ ^ 2 * opN (BJ A₁ A₂ c τ ξ) ^ 4 ∂stdGauss (Fin n) =
      (τ ^ 2) ^ 2 * ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 *
        (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n) := by
    rw [← integral_const_mul]
    congr 1; funext ξ
    simp only [wN, BJ]; ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
  ring

section level

variable (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
  {τ : ℝ}

lemma opN_BJ_le (hn : 1 ≤ n) (ξ : Fin n → ℝ) : opN (BJ A₁ A₂ c τ ξ) ≤ opN A₂ * opN A₁ :=
  opN_jacT_le_sj A₁ A₂ (normSq_sphPt hn _)

lemma measurable_opN_BJ : Measurable (fun ξ => opN (BJ A₁ A₂ c τ ξ)) :=
  measurable_opN_jacT_sj A₁ A₂ c τ

lemma normSq_vecMul_BJ_le (hn : 1 ≤ n) (v : Fin m → ℝ) (ξ : Fin n → ℝ) :
    normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ≤ opN (BJ A₁ A₂ c τ ξ) ^ 2 * normSq v := by
  rw [← nrm_sq, ← nrm_sq, ← mul_pow]
  exact pow_le_pow_left₀ (nrm_nonneg _) (nrm_vecMul_le _ _) 2

lemma integrable_wN2_opN4 (hn : 6 ≤ n) (hτ : 0 < τ) :
    Integrable (fun ξ => wN c τ ξ ^ 2 * opN (BJ A₁ A₂ c τ ξ) ^ 4) (stdGauss (Fin n)) := by
  refine Integrable.mono' ((integrable_wN2 hn c hτ).mul_const ((opN A₂ * opN A₁) ^ 4))
    (((measurable_wN c τ).pow_const 2).mul
      ((measurable_opN_BJ A₁ A₂ c).pow_const 4)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opN_nonneg _)
    (opN_BJ_le A₁ A₂ c (by omega) ξ) 4) (sq_nonneg _)

lemma integrable_level (hn : 6 ≤ n) (hτ : 0 < τ) (S : Set (Fin n → ℝ)) (hS : MeasurableSet S)
    (v : Fin m → ℝ) :
    Integrable (fun ξ => S.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)))
      (stdGauss (Fin n)) := by
  have hNm : Measurable (fun ξ => normSq (vecMul v (BJ A₁ A₂ c τ ξ))) := by
    show Measurable (fun ξ => ∑ j, (∑ i, v i * BJ A₁ A₂ c τ ξ i j) ^ 2)
    exact Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (measurable_BJ_entry A₁ A₂ c τ i j)).pow_const 2
  refine Integrable.mono' ((integrable_wN (by omega) c hτ).mul_const
    ((opN A₂ * opN A₁) ^ 2 * normSq v))
    (((measurable_wN c τ).indicator hS).mul hNm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have h0 : 0 ≤ S.indicator (wN c τ) ξ := Set.indicator_nonneg (fun _ _ => wN_nonneg _ _ _) ξ
  have h1 : S.indicator (wN c τ) ξ ≤ wN c τ ξ :=
    Set.indicator_le_self' (fun _ _ => wN_nonneg _ _ _) ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (normSq_nonneg _))]
  have h2 := normSq_vecMul_BJ_le A₁ A₂ c (τ := τ) (by omega) v ξ
  have h3 : opN (BJ A₁ A₂ c τ ξ) ^ 2 ≤ (opN A₂ * opN A₁) ^ 2 :=
    pow_le_pow_left₀ (opN_nonneg _) (opN_BJ_le A₁ A₂ c (by omega) ξ) 2
  have h4 : normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ≤ (opN A₂ * opN A₁) ^ 2 * normSq v :=
    h2.trans (mul_le_mul_of_nonneg_right h3 (normSq_nonneg _))
  exact mul_le_mul h1 h4 (normSq_nonneg _) (wN_nonneg _ _ _)

/-- **One level of the Schur test for the network**: the weight `w = 1_S·τ²/|y|²`, a kernel `κ`
on a symmetric good pair set `G` with `‖(𝒥(x)Π_x)ᵀ𝒥(x')Π_{x'}‖_op ≤ κ`, row integrals `≤ R`. -/
theorem schur_level (hn : 6 ≤ n) (hτ : 0 < τ) (S : Set (Fin n → ℝ)) (hS : MeasurableSet S)
    (κ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (hκm : Measurable (Function.uncurry κ))
    (hκ0 : ∀ a b, 0 ≤ κ a b) (hκs : ∀ a b, κ a b = κ b a) {K : ℝ} (hκK : ∀ a b, κ a b ≤ K)
    (G : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG : MeasurableSet G)
    (hGs : ∀ a b, (a, b) ∈ G → (b, a) ∈ G)
    (hpair : ∀ a b, (a, b) ∈ G → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤ κ a b)
    {R : ℝ} (hrow : ∀ ξ, ∫ ξ', G.indicator (Function.uncurry κ) (ξ, ξ') * S.indicator (wN c τ) ξ'
      ∂stdGauss (Fin n) ≤ R)
    (v : Fin m → ℝ) :
    ∫ ξ, S.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂stdGauss (Fin n) ≤
      (R + √(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (Gᶜ ∩ S ×ˢ S)) *
        A4 A₁ A₂ c τ)) * normSq v := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hwm : Measurable (S.indicator (wN c τ)) := (measurable_wN c τ).indicator hS
  have hw0 : ∀ ξ, 0 ≤ S.indicator (wN c τ) ξ :=
    fun ξ => Set.indicator_nonneg (fun _ _ => wN_nonneg _ _ _) ξ
  have hwle : ∀ ξ, S.indicator (wN c τ) ξ ≤ wN c τ ξ :=
    fun ξ => Set.indicator_le_self' (fun _ _ => wN_nonneg _ _ _) ξ
  have hwi : Integrable (S.indicator (wN c τ)) (stdGauss (Fin n)) :=
    (integrable_wN (by omega) c hτ).indicator hS
  have hw2 : Integrable (fun ξ => S.indicator (wN c τ) ξ ^ 2) (stdGauss (Fin n)) := by
    refine Integrable.mono' (integrable_wN2 hn c hτ) (hwm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hw0 ξ) (hwle ξ) 2
  have h := schur_abstract (stdGauss (Fin n)) (BJ A₁ A₂ c τ) (measurable_BJ_entry A₁ A₂ c τ)
    (fun ξ => opN (BJ A₁ A₂ c τ ξ)) (measurable_opN_BJ A₁ A₂ c) (fun ξ => le_rfl)
    (opN_BJ_le A₁ A₂ c (by omega)) (S.indicator (wN c τ)) hwm hw0 hwi hw2 S hS
    (fun ξ hξ => Set.indicator_of_notMem hξ _) κ hκm hκ0 hκs hκK G hG hGs
    (fun a b hab u u' => pair_of_opN _ _ (hpair a b hab) u u') hrow v
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg _))
  refine add_le_add_right (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))) R
  refine integral_mono ((hw2.mul_const ((opN A₂ * opN A₁) ^ 4)).mono' ?_ ?_)
    (integrable_wN2_opN4 A₁ A₂ c hn hτ) (fun ξ => ?_)
  · exact (hwm.pow_const 2).mul ((measurable_opN_BJ A₁ A₂ c).pow_const 4) |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opN_nonneg _)
      (opN_BJ_le A₁ A₂ c (by omega) ξ) 4) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw0 ξ) (hwle ξ) 2) (by positivity)

/-- **The outside inputs**: `∫ 1_S w |vᵀB|² ≤ √(μ(S)·A)·|v|²` (Cauchy–Schwarz). -/
theorem out_level (hn : 6 ≤ n) (hτ : 0 < τ) (S : Set (Fin n → ℝ)) (hS : MeasurableSet S)
    (v : Fin m → ℝ) :
    ∫ ξ, S.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂stdGauss (Fin n) ≤
      √((stdGauss (Fin n)).real S * A4 A₁ A₂ c τ) * normSq v := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  set F : (Fin n → ℝ) → ℝ := fun ξ => wN c τ ξ * opN (BJ A₁ A₂ c τ ξ) ^ 2 with hFd
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => mul_nonneg (wN_nonneg _ _ _) (sq_nonneg _)
  have hFm : Measurable F := (measurable_wN c τ).mul ((measurable_opN_BJ A₁ A₂ c).pow_const 2)
  have hF2 : (fun ξ => F ξ ^ 2) = fun ξ => wN c τ ξ ^ 2 * opN (BJ A₁ A₂ c τ ξ) ^ 4 := by
    funext ξ; simp only [hFd]; ring
  have hF2i : Integrable (fun ξ => F ξ ^ 2) (stdGauss (Fin n)) := by
    rw [hF2]; exact integrable_wN2_opN4 A₁ A₂ c hn hτ
  have hFi : Integrable F (stdGauss (Fin n)) := by
    refine Integrable.mono' ((integrable_wN (by omega) c hτ).mul_const ((opN A₂ * opN A₁) ^ 2))
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opN_nonneg _)
      (opN_BJ_le A₁ A₂ c (by omega) ξ) 2) (wN_nonneg _ _ _)
  have hSFi : Integrable (S.indicator F) (stdGauss (Fin n)) := hFi.indicator hS
  have h1 : ∫ ξ, S.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂stdGauss (Fin n) ≤
      (∫ ξ, S.indicator F ξ ∂stdGauss (Fin n)) * normSq v := by
    rw [← integral_mul_const]
    refine integral_mono (integrable_level A₁ A₂ c hn hτ S hS v) (hSFi.mul_const _) fun ξ => ?_
    by_cases hξ : ξ ∈ S
    · simp only [Set.indicator_of_mem hξ, hFd]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (normSq_vecMul_BJ_le A₁ A₂ c (by omega) v ξ)
        (wN_nonneg _ _ _)
    · simp [Set.indicator_of_notMem hξ]
  have h2 : ∫ ξ, S.indicator F ξ ∂stdGauss (Fin n) ≤
      √((stdGauss (Fin n)).real S * A4 A₁ A₂ c τ) := by
    refine le_sqrt_of_forall_pos measureReal_nonneg
      (integral_nonneg fun ξ => by positivity) fun s hs => ?_
    have hi1 : Integrable (S.indicator (fun _ => (1 : ℝ))) (stdGauss (Fin n)) :=
      (integrable_const (1 : ℝ)).indicator hS
    have hint : Integrable (fun ξ => (s * S.indicator (fun _ => (1 : ℝ)) ξ + F ξ ^ 2 / s) / 2)
        (stdGauss (Fin n)) := ((hi1.const_mul s).add (hF2i.div_const s)).div_const 2
    refine (integral_mono hSFi hint fun ξ => ?_).trans (le_of_eq ?_)
    · by_cases hξ : ξ ∈ S
      · simp only [Set.indicator_of_mem hξ, mul_one]
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
        have e : s + F ξ ^ 2 / s - F ξ * 2 = (s - F ξ) ^ 2 / s := by field_simp; ring
        rw [e]; positivity
      · simp only [Set.indicator_of_notMem hξ, mul_zero, zero_add]; positivity
    · rw [integral_div, integral_add (f := fun ξ => s * S.indicator (fun _ => (1 : ℝ)) ξ)
        (g := fun ξ => F ξ ^ 2 / s) (hi1.const_mul s) (hF2i.div_const s), integral_const_mul,
        integral_div, hF2]
      have e1 : ∫ ξ, S.indicator (fun _ => (1 : ℝ)) ξ ∂stdGauss (Fin n) =
          (stdGauss (Fin n)).real S := integral_indicator_one hS
      rw [e1]; rfl
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (normSq_nonneg _))

/-- The partition `1 = 1_{Ω₁} + 1_{Ω₀∖Ω₁} + 1_{Ω₀ᶜ}` of the quadratic form. -/
lemma Dq_split (hn : 6 ≤ n) (hτ : 0 < τ) {Ω₀ Ω₁ : Set (Fin n → ℝ)} (h01 : Ω₁ ⊆ Ω₀)
    (h0 : MeasurableSet Ω₀) (h1 : MeasurableSet Ω₁) (v : Fin m → ℝ) :
    Dq A₁ A₂ c τ v = 2 / (m : ℝ) *
      (∫ ξ, Ω₁.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂stdGauss (Fin n) +
       ∫ ξ, (Ω₀ \ Ω₁).indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ))
          ∂stdGauss (Fin n) +
       ∫ ξ, Ω₀ᶜ.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂stdGauss (Fin n)) := by
  have i1 := integrable_level A₁ A₂ c hn hτ _ h1 v
  have i2 := integrable_level A₁ A₂ c hn hτ _ (h0.diff h1) v
  have i3 := integrable_level A₁ A₂ c hn hτ _ h0.compl v
  have i12 : Integrable (fun ξ => Ω₁.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) +
      (Ω₀ \ Ω₁).indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ))) (stdGauss (Fin n)) :=
    i1.add i2
  rw [Dq_eq_w, ← integral_add i1 i2, ← integral_add i12 i3]
  congr 2; funext ξ

  by_cases hξ1 : ξ ∈ Ω₁
  · have hξ0 : ξ ∈ Ω₀ := h01 hξ1
    simp [Set.indicator_of_mem hξ1, hξ1, hξ0]
  · by_cases hξ0 : ξ ∈ Ω₀
    · simp [Set.indicator_of_notMem hξ1, hξ1, hξ0]
    · simp [hξ1, hξ0]

/-- **The two-level Schur bound for `Dq`** (paper (t7:p04:schur-formula) with `K^MS = λ`, no
tangential gain): core inputs `Ω₁`, shell `Ω₀ ∖ Ω₁`, outside `Ω₀ᶜ`. -/
theorem Dq_le_twolevel (hn : 6 ≤ n) (hτ : 0 < τ) {Ω₀ Ω₁ : Set (Fin n → ℝ)} (h01 : Ω₁ ⊆ Ω₀)
    (h0 : MeasurableSet Ω₀) (h1 : MeasurableSet Ω₁)
    (κ₁ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (hκm₁ : Measurable (Function.uncurry κ₁))
    (hκ0₁ : ∀ a b, 0 ≤ κ₁ a b) (hκs₁ : ∀ a b, κ₁ a b = κ₁ b a) {K₁ : ℝ}
    (hκK₁ : ∀ a b, κ₁ a b ≤ K₁)
    (G₁ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG₁ : MeasurableSet G₁)
    (hGs₁ : ∀ a b, (a, b) ∈ G₁ → (b, a) ∈ G₁)
    (hpair₁ : ∀ a b, (a, b) ∈ G₁ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤ κ₁ a b)
    {R₁ : ℝ} (hrow₁ : ∀ ξ, ∫ ξ', G₁.indicator (Function.uncurry κ₁) (ξ, ξ') *
      Ω₁.indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤ R₁)
    (κ₀ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (hκm₀ : Measurable (Function.uncurry κ₀))
    (hκ0₀ : ∀ a b, 0 ≤ κ₀ a b) (hκs₀ : ∀ a b, κ₀ a b = κ₀ b a) {K₀ : ℝ}
    (hκK₀ : ∀ a b, κ₀ a b ≤ K₀)
    (G₀ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG₀ : MeasurableSet G₀)
    (hGs₀ : ∀ a b, (a, b) ∈ G₀ → (b, a) ∈ G₀)
    (hpair₀ : ∀ a b, (a, b) ∈ G₀ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤ κ₀ a b)
    {R₀ : ℝ} (hrow₀ : ∀ ξ, ∫ ξ', G₀.indicator (Function.uncurry κ₀) (ξ, ξ') *
      (Ω₀ \ Ω₁).indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤ R₀)
    (v : Fin m → ℝ) :
    Dq A₁ A₂ c τ v ≤ (2 / (m : ℝ) * (R₁ + R₀) + Xi4 A₁ A₂ c τ *
      (√(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁))) +
       √(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)))) +
       √((stdGauss (Fin n)).real Ω₀ᶜ))) * normSq v := by
  have b1 := schur_level A₁ A₂ c hn hτ Ω₁ h1 κ₁ hκm₁ hκ0₁ hκs₁ hκK₁ G₁ hG₁ hGs₁ hpair₁ hrow₁ v
  have b0 := schur_level A₁ A₂ c hn hτ (Ω₀ \ Ω₁) (h0.diff h1) κ₀ hκm₀ hκ0₀ hκs₀ hκK₀ G₀ hG₀ hGs₀
    hpair₀ hrow₀ v
  have bo := out_level A₁ A₂ c hn hτ Ω₀ᶜ h0.compl v
  rw [Dq_split A₁ A₂ c hn hτ h01 h0 h1 v, Xi4_eq_A4]
  have hA : 0 ≤ A4 A₁ A₂ c τ := integral_nonneg fun ξ => by positivity
  set A := A4 A₁ A₂ c τ
  rw [Real.sqrt_mul (Real.sqrt_nonneg _)] at b1 b0
  rw [Real.sqrt_mul measureReal_nonneg] at bo
  have ht : 0 ≤ 2 / (m : ℝ) := by positivity
  have hsum := add_le_add (add_le_add b1 b0) bo
  have := mul_le_mul_of_nonneg_left hsum ht
  refine this.trans (le_of_eq ?_)
  ring

end level

section row

variable {X : Type*} [MeasurableSpace X]

/-- The two-valued kernel: `L₁` on the pair set `C`, `L₀` off it. -/
noncomputable def kern (C : Set (X × X)) (L₁ L₀ : ℝ) (a b : X) : ℝ :=
  C.indicator (fun _ => L₁) (a, b) + Cᶜ.indicator (fun _ => L₀) (a, b)

lemma kern_of_mem {C : Set (X × X)} {L₁ L₀ : ℝ} {a b : X} (h : (a, b) ∈ C) :
    kern C L₁ L₀ a b = L₁ := by
  simp [kern, Set.indicator_of_mem h, h]

lemma kern_of_notMem {C : Set (X × X)} {L₁ L₀ : ℝ} {a b : X} (h : (a, b) ∉ C) :
    kern C L₁ L₀ a b = L₀ := by
  simp [kern, Set.indicator_of_notMem h, h]

lemma measurable_kern {C : Set (X × X)} (hC : MeasurableSet C) (L₁ L₀ : ℝ) :
    Measurable (Function.uncurry (kern C L₁ L₀)) :=
  show Measurable (fun p : X × X => C.indicator (fun _ => L₁) p + Cᶜ.indicator (fun _ => L₀) p)
  from (measurable_const.indicator hC).add (measurable_const.indicator hC.compl)

lemma kern_nonneg (C : Set (X × X)) {L₁ L₀ : ℝ} (h₁ : 0 ≤ L₁) (h₀ : 0 ≤ L₀) (a b : X) :
    0 ≤ kern C L₁ L₀ a b := by
  by_cases h : (a, b) ∈ C
  · rw [kern_of_mem h]; exact h₁
  · rw [kern_of_notMem h]; exact h₀

lemma kern_le (C : Set (X × X)) {L₁ L₀ : ℝ} (h₁ : 0 ≤ L₁) (h₀ : 0 ≤ L₀) (a b : X) :
    kern C L₁ L₀ a b ≤ L₁ + L₀ := by
  by_cases h : (a, b) ∈ C
  · rw [kern_of_mem h]; linarith
  · rw [kern_of_notMem h]; linarith

lemma kern_symm {C : Set (X × X)} (hCs : ∀ a b, (a, b) ∈ C → (b, a) ∈ C) (L₁ L₀ : ℝ) (a b : X) :
    kern C L₁ L₀ a b = kern C L₁ L₀ b a := by
  by_cases h : (a, b) ∈ C
  · rw [kern_of_mem h, kern_of_mem (hCs _ _ h)]
  · have h' : (b, a) ∉ C := fun h' => h (hCs _ _ h')
    rw [kern_of_notMem h, kern_of_notMem h']

/-- **The row bound from simple data**: with `w = 0` off `T`, `w ≤ W̄` on `T`:
`∫ 1_G κ w' ≤ L₁ ∫ w + L₀ W̄ μ{ξ' ∈ T : (ξ, ξ') ∉ C}`. -/
theorem row_bound (μ : Measure X) [IsProbabilityMeasure μ] {C G : Set (X × X)}
    (hC : MeasurableSet C) (hG : MeasurableSet G) {L₁ L₀ : ℝ} (hL₁ : 0 ≤ L₁) (hL₀ : 0 ≤ L₀)
    (w : X → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ) (hwi : Integrable w μ)
    {T : Set X} (hT : MeasurableSet T) (hwT : ∀ ξ, ξ ∉ T → w ξ = 0) {W : ℝ}
    (hW : ∀ ξ ∈ T, w ξ ≤ W) (ξ : X) :
    ∫ ξ', G.indicator (Function.uncurry (kern C L₁ L₀)) (ξ, ξ') * w ξ' ∂μ ≤
      L₁ * ∫ ξ', w ξ' ∂μ + L₀ * W * μ.real {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C} := by
  have hsec : MeasurableSet {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C} :=
    hT.inter (measurable_prodMk_left hC).compl
  have hkm : Measurable (fun ξ' => G.indicator (Function.uncurry (kern C L₁ L₀)) (ξ, ξ')) :=
    ((measurable_kern hC L₁ L₀).indicator hG).comp measurable_prodMk_left
  have hk0 : ∀ ξ', 0 ≤ G.indicator (Function.uncurry (kern C L₁ L₀)) (ξ, ξ') :=
    fun ξ' => Set.indicator_nonneg (fun (p : X × X) _ => kern_nonneg C hL₁ hL₀ p.1 p.2) _
  have hkle : ∀ ξ', G.indicator (Function.uncurry (kern C L₁ L₀)) (ξ, ξ') ≤
      kern C L₁ L₀ ξ ξ' :=
    fun ξ' => Set.indicator_le_self' (fun (p : X × X) _ => kern_nonneg C hL₁ hL₀ p.1 p.2) (ξ, ξ')
  have hLi : Integrable (fun ξ' => G.indicator (Function.uncurry (kern C L₁ L₀)) (ξ, ξ') * w ξ')
      μ := by
    refine Integrable.mono' (hwi.const_mul (L₁ + L₀)) (hkm.mul hwm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ' => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 ξ') (hw0 ξ'))]
    exact mul_le_mul_of_nonneg_right ((hkle ξ').trans (kern_le C hL₁ hL₀ _ _)) (hw0 ξ')
  have hi1 : Integrable ({ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C}.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hsec
  have hRi : Integrable (fun ξ' => L₁ * w ξ' + L₀ * W *
      {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C}.indicator (fun _ => (1 : ℝ)) ξ') μ :=
    (hwi.const_mul L₁).add (hi1.const_mul (L₀ * W))
  refine (integral_mono hLi hRi fun ξ' => ?_).trans (le_of_eq ?_)
  · refine (mul_le_mul_of_nonneg_right (hkle ξ') (hw0 ξ')).trans ?_
    by_cases hc : (ξ, ξ') ∈ C
    · rw [kern_of_mem hc]
      have : 0 ≤ L₀ * W * {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C}.indicator (fun _ => (1 : ℝ)) ξ' := by
        have hn : ξ' ∉ {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C} := fun h => h.2 hc
        rw [Set.indicator_of_notMem hn, mul_zero]
      linarith
    · rw [kern_of_notMem hc]
      by_cases ht : ξ' ∈ T
      · have hm : ξ' ∈ {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C} := ⟨ht, hc⟩
        rw [Set.indicator_of_mem hm, mul_one]
        have := mul_le_mul_of_nonneg_left (hW ξ' ht) hL₀
        nlinarith [hw0 ξ']
      · rw [hwT ξ' ht]
        have hn : ξ' ∉ {ξ' | ξ' ∈ T ∧ (ξ, ξ') ∉ C} := fun h => ht h.1
        rw [Set.indicator_of_notMem hn]; simp
  · rw [integral_add (hwi.const_mul L₁) (hi1.const_mul (L₀ * W)), integral_const_mul,
      integral_const_mul]
    congr 2
    exact integral_indicator_one hsec

end row

end BstLean.Part182

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (Xi4)

variable {n m : ℕ}

/-- **The two-level Schur bound with the paper's kernels** (`K^MS = λ`): on the core good set
`G₁` the pair bound is `nλ₁` on the core pairs `C₁` and `nλ₀` on the other pairs; on the wide
good set `G₀` it is `nλ₀`. With `∫ w ≤ E_w`, `w ≤ W̄` on `Ω₀`, the core row defect
`μ{ξ' ∈ Ω₁ : (ξ, ξ') ∉ C₁} ≤ P_p` for every `ξ`, and the shell mass `μ(Ω₀ ∖ Ω₁) ≤ P_s`:
`Dq ≤ [t(nλ₁E_w + nλ₀W̄P_p + nλ₀W̄P_s) + Ξ₄(H₁^{1/4} + H₀^{1/4} + P_o^{1/2})]·|v|²`. -/
theorem Dq_le_kern (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hn : 6 ≤ n) (hτ : 0 < τ) {Ω₀ Ω₁ : Set (Fin n → ℝ)}
    (h01 : Ω₁ ⊆ Ω₀) (h0 : MeasurableSet Ω₀) (h1 : MeasurableSet Ω₁)
    {lam₁ lam₀ : ℝ} (hl₁ : 0 ≤ lam₁) (hl₀ : 0 ≤ lam₀)
    (C₁ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hC₁ : MeasurableSet C₁)
    (hCs₁ : ∀ a b, (a, b) ∈ C₁ → (b, a) ∈ C₁)
    (G₁ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG₁ : MeasurableSet G₁)
    (hGs₁ : ∀ a b, (a, b) ∈ G₁ → (b, a) ∈ G₁)
    (hpair₁ : ∀ a b, (a, b) ∈ G₁ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern C₁ ((n : ℝ) * lam₁) ((n : ℝ) * lam₀) a b)
    (G₀ : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hG₀ : MeasurableSet G₀)
    (hGs₀ : ∀ a b, (a, b) ∈ G₀ → (b, a) ∈ G₀)
    (hpair₀ : ∀ a b, (a, b) ∈ G₀ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤ (n : ℝ) * lam₀)
    {Ew Wb Pp Ps : ℝ} (hEw : ∫ ξ, wN c τ ξ ∂stdGauss (Fin n) ≤ Ew) (hWb0 : 0 ≤ Wb)
    (hWb : ∀ ξ ∈ Ω₀, wN c τ ξ ≤ Wb)
    (hPp : ∀ ξ, (stdGauss (Fin n)).real {ξ' | ξ' ∈ Ω₁ ∧ (ξ, ξ') ∉ C₁} ≤ Pp)
    (hPs : (stdGauss (Fin n)).real (Ω₀ \ Ω₁) ≤ Ps) (v : Fin m → ℝ) :
    Dq A₁ A₂ c τ v ≤ (2 / (m : ℝ) * ((n : ℝ) * lam₁ * Ew + (n : ℝ) * lam₀ * Wb * Pp +
        (n : ℝ) * lam₀ * Wb * Ps) + Xi4 A₁ A₂ c τ *
      (√(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁))) +
       √(√(((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)))) +
       √((stdGauss (Fin n)).real Ω₀ᶜ))) * normSq v := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnl₁ : 0 ≤ (n : ℝ) * lam₁ := mul_nonneg (Nat.cast_nonneg _) hl₁
  have hnl₀ : 0 ≤ (n : ℝ) * lam₀ := mul_nonneg (Nat.cast_nonneg _) hl₀
  have hwi := integrable_wN (by omega) c hτ
  have hw0 := wN_nonneg c τ
  -- core row
  have hrow₁ : ∀ ξ, ∫ ξ', G₁.indicator (Function.uncurry (kern C₁ ((n : ℝ) * lam₁)
      ((n : ℝ) * lam₀))) (ξ, ξ') * Ω₁.indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤
      (n : ℝ) * lam₁ * Ew + (n : ℝ) * lam₀ * Wb * Pp := by
    intro ξ
    refine (row_bound (stdGauss (Fin n)) hC₁ hG₁ hnl₁ hnl₀ (Ω₁.indicator (wN c τ))
      ((measurable_wN c τ).indicator h1) (fun ξ => Set.indicator_nonneg (fun _ _ => hw0 _) ξ)
      (hwi.indicator h1) h1 (fun ξ hξ => Set.indicator_of_notMem hξ _)
      (W := Wb) (fun ξ hξ => by rw [Set.indicator_of_mem hξ]; exact hWb ξ (h01 hξ)) ξ).trans ?_
    have hi : ∫ ξ', Ω₁.indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤ Ew := by
      refine le_trans ?_ hEw
      exact integral_mono (hwi.indicator h1) hwi
        (fun ξ => Set.indicator_le_self' (fun _ _ => hw0 _) ξ)
    have h2 := mul_le_mul_of_nonneg_left hi hnl₁
    have h3 := mul_le_mul_of_nonneg_left (hPp ξ) (mul_nonneg hnl₀ hWb0)
    linarith
  -- shell row
  have hrow₀ : ∀ ξ, ∫ ξ', G₀.indicator (Function.uncurry (kern ∅ 0 ((n : ℝ) * lam₀))) (ξ, ξ') *
      (Ω₀ \ Ω₁).indicator (wN c τ) ξ' ∂stdGauss (Fin n) ≤ (n : ℝ) * lam₀ * Wb * Ps := by
    intro ξ
    refine (row_bound (stdGauss (Fin n)) MeasurableSet.empty hG₀ le_rfl hnl₀
      ((Ω₀ \ Ω₁).indicator (wN c τ)) ((measurable_wN c τ).indicator (h0.diff h1))
      (fun ξ => Set.indicator_nonneg (fun _ _ => hw0 _) ξ) (hwi.indicator (h0.diff h1))
      (h0.diff h1) (fun ξ hξ => Set.indicator_of_notMem hξ _) (W := Wb)
      (fun ξ hξ => by rw [Set.indicator_of_mem hξ]; exact hWb ξ hξ.1) ξ).trans ?_
    have e : {ξ' | ξ' ∈ Ω₀ \ Ω₁ ∧ (ξ, ξ') ∉ (∅ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} = Ω₀ \ Ω₁ := by
      ext ξ'; simp
    rw [e, zero_mul, zero_add]
    exact mul_le_mul_of_nonneg_left hPs (mul_nonneg hnl₀ hWb0)
  have h := Dq_le_twolevel A₁ A₂ c hn hτ h01 h0 h1
    (kern C₁ ((n : ℝ) * lam₁) ((n : ℝ) * lam₀)) (measurable_kern hC₁ _ _)
    (kern_nonneg C₁ hnl₁ hnl₀) (kern_symm hCs₁ _ _) (kern_le C₁ hnl₁ hnl₀) G₁ hG₁ hGs₁ hpair₁ hrow₁
    (kern ∅ 0 ((n : ℝ) * lam₀)) (measurable_kern MeasurableSet.empty _ _)
    (kern_nonneg ∅ le_rfl hnl₀) (kern_symm (fun a b h => h) _ _) (kern_le ∅ le_rfl hnl₀)
    G₀ hG₀ hGs₀ (fun a b hab => by rw [kern_of_notMem (Set.notMem_empty _)]; exact hpair₀ a b hab)
    hrow₀ v
  refine h.trans (le_of_eq ?_)
  ring

end BstLean.Part182

open BstLean.Part182 in
#print axioms Dq_le_twolevel
open BstLean.Part182 in
#print axioms Dq_le_kern
open BstLean.Part182 in
#print axioms row_bound
