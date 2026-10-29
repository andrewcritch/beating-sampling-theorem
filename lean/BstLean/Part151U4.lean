import BstLean.Part151J
import BstLean.Part151R
import BstLean.Part134Split
import BstLean.Part134Mean

/-!
# Part 151, item 4 (d): the Poincaré step of Lemma U (i), general form

Role: `delegations/statements/p151-spec.md`, item 4 (d). Paper source:
`proofs/option-n/theorem5-09-fluctuation.tex`, Lemma U (i).

General setting. `(Ξ, μ)` is a probability space (the variable `ξ`), `lamf ξ` a bounded
measurable scalar, `r ξ ∈ ℝ^m` a bounded measurable vector (the residual), `c ∈ ℝⁿ` fixed, `M`
an `n × m` Gaussian matrix with entry variance `v > 0`. The input is
`yG lamf r c M ξ = lamf ξ • c + M·r ξ`. `ψ` is a Lipschitz test function on `ℝⁿ` whose partial
derivatives are `a y i` on a measurable set `S` of full Lebesgue measure.

* `PsiG M = E_ξ ψ(y_ξ(M))`, `AG M = E_ξ Σ_i a(y_ξ(M))_i²`.
* `ae_good`: for almost every `M`, for almost every `ξ`: `r ξ = 0` or `y_ξ(M) ∈ S` (the vector
  `M·r` is a nondegenerate Gaussian vector when `r ≠ 0`; Fubini).
* `grad_bound`: at such an `M`, `|∇_M Ψ|² ≤ (Mr/v)·…`, in the standardized variable:
  `gradSq (Ψ ∘ T) ≤ Mr·AG`, if `v·E_ξ⟨r, w⟩² ≤ Mr·|w|²` (differentiation under the integral with
  a Lipschitz bound, along one line; Cauchy–Schwarz).
* **`poincU`**: `Var_M Ψ ≤ Mr·E_M AG`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part134 (normSq_ne_zero measurable_mulVec_joint)
open BstLean.Part148 (EuLip stdGauss_ac)

/-- A derivative along a vector is the sum of the partial derivatives. -/
lemma fderiv_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ) (y w : ι → ℝ) :
    fderiv ℝ f y w = ∑ i, w i * fderiv ℝ f y (Pi.single i 1) := by
  have h := (fderiv ℝ f y).toLinearMap.pi_apply_eq_sum_univ w
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

section gen

variable {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}

/-- The input `y_ξ(M) = lamf ξ • c + M·r ξ`. -/
def yG (lamf : Ξ → ℝ) (r : Ξ → Fin m → ℝ) (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (ξ : Ξ) : Fin n → ℝ :=
  lamf ξ • c + M *ᵥ r ξ

/-- `Ψ(M) = E_ξ ψ(y_ξ(M))`. -/
noncomputable def PsiG (μ : Measure Ξ) (ψ : (Fin n → ℝ) → ℝ) (lamf : Ξ → ℝ)
    (r : Ξ → Fin m → ℝ) (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ ξ, ψ (yG lamf r c M ξ) ∂μ

/-- `E_ξ Σ_i a(y_ξ(M))_i²`. -/
noncomputable def AG (μ : Measure Ξ) (a : (Fin n → ℝ) → Fin n → ℝ) (lamf : Ξ → ℝ)
    (r : Ξ → Fin m → ℝ) (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ ξ, ∑ i, a (yG lamf r c M ξ) i ^ 2 ∂μ

/-- The standardized entries: `T ξ′ = √v·ξ′` as a matrix. -/
noncomputable def Tv (v : ℝ) (x : Fin n × Fin m → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => √v * x (i, j)

lemma gaussMat_eq_Tv (v : ℝ) :
    gaussMat n m v = (stdGauss (Fin n × Fin m)).map (Tv v) := rfl

lemma measurable_Tv (v : ℝ) : Measurable (Tv (n := n) (m := m) v) := measurable_ofFlat _

lemma Tv_add_smul (v : ℝ) (x N : Fin n × Fin m → ℝ) (t : ℝ) :
    Tv v (x + t • N) = Tv v x + t • Tv v N := by
  ext i j
  simp only [Tv, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.smul_apply]
  ring

lemma frob_Tv_sub {v : ℝ} (hv : 0 ≤ v) (x y : Fin n × Fin m → ℝ) :
    frob (Tv v x - Tv v y) = v * ∑ p, (x p - y p) ^ 2 := by
  unfold frob
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Tv, Matrix.sub_apply, Matrix.of_apply]
  rw [← mul_sub, mul_pow, Real.sq_sqrt hv]

lemma frob_Tv {v : ℝ} (hv : 0 ≤ v) (x : Fin n × Fin m → ℝ) :
    frob (Tv v x) = v * ∑ p, x p ^ 2 := by
  unfold frob
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Tv, Matrix.of_apply]
  rw [mul_pow, Real.sq_sqrt hv]

variable {lamf : Ξ → ℝ} {r : Ξ → Fin m → ℝ}

lemma yG_add_smul (c : Fin n → ℝ) (M N : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) (ξ : Ξ) :
    yG lamf r c (M + t • N) ξ = yG lamf r c M ξ + t • (N *ᵥ r ξ) := by
  unfold yG
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, add_assoc]

lemma yG_sub (c : Fin n → ℝ) (M N : Matrix (Fin n) (Fin m) ℝ) (ξ : Ξ) :
    yG lamf r c M ξ - yG lamf r c N ξ = (M - N) *ᵥ r ξ := by
  unfold yG
  rw [Matrix.sub_mulVec]
  abel

lemma measurable_yG (hl : Measurable lamf) (hr : Measurable r) (c : Fin n → ℝ) :
    Measurable (fun q : Matrix (Fin n) (Fin m) ℝ × Ξ => yG lamf r c q.1 q.2) := by
  unfold yG
  exact ((hl.comp measurable_snd).smul_const c).add
    (measurable_mulVec_joint.comp (measurable_fst.prodMk (hr.comp measurable_snd)))

lemma measurable_yG_right (hl : Measurable lamf) (hr : Measurable r) (c : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) : Measurable (yG lamf r c M) :=
  (measurable_yG hl hr c).comp (measurable_const.prodMk measurable_id)

lemma normSq_add_le2 {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (a + b) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (a i - b i)]

lemma yG_normSq_le {Λ H : ℝ} (hΛ : ∀ ξ, lamf ξ ^ 2 ≤ Λ) (hH : ∀ ξ, normSq (r ξ) ≤ H)
    (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) (ξ : Ξ) :
    normSq (yG lamf r c M ξ) ≤ 2 * (Λ * normSq c) + 2 * (frob M * H) := by
  unfold yG
  have h1 := normSq_add_le2 (lamf ξ • c) (M *ᵥ r ξ)
  rw [normSq_smul] at h1
  have h2 : lamf ξ ^ 2 * normSq c ≤ Λ * normSq c :=
    mul_le_mul_of_nonneg_right (hΛ ξ) (normSq_nonneg c)
  have h3 : normSq (M *ᵥ r ξ) ≤ frob M * H :=
    (normSq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hH ξ) (frob_nonneg _))
  linarith

variable {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}

lemma eulip_abs_le (hL : EuLip ψ L) (y : Fin n → ℝ) : |ψ y| ≤ |ψ 0| + L * √(normSq y) := by
  have h := hL y 0
  have e : ∑ i, (y i - (0 : Fin n → ℝ) i) ^ 2 = normSq y := by
    unfold normSq; simp
  rw [e] at h
  have := abs_sub_abs_le_abs_sub (ψ y) (ψ 0)
  linarith

/-- `ψ` of a measurable bounded map is integrable. -/
lemma int_psi_bdd (μ : Measure Ξ) [IsProbabilityMeasure μ] (hL0 : 0 ≤ L) (hL : EuLip ψ L)
    {q : Ξ → Fin n → ℝ} (hq : Measurable q) {C : ℝ} (hC : ∀ ξ, normSq (q ξ) ≤ C) :
    Integrable (fun ξ => ψ (q ξ)) μ := by
  refine Integrable.of_bound ((hL.continuous hL0).measurable.comp hq).aestronglyMeasurable
    (|ψ 0| + L * √C) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  have h1 := eulip_abs_le hL (q ξ)
  have h2 : √(normSq (q ξ)) ≤ √C := Real.sqrt_le_sqrt (hC ξ)
  have h3 := mul_le_mul_of_nonneg_left h2 hL0
  linarith

section main

variable (μ : Measure Ξ) [IsProbabilityMeasure μ]

lemma int_psi_yG (hL0 : 0 ≤ L) (hL : EuLip ψ L) (hl : Measurable lamf) (hr : Measurable r)
    {Λ H : ℝ} (hΛ : ∀ ξ, lamf ξ ^ 2 ≤ Λ) (hH : ∀ ξ, normSq (r ξ) ≤ H) (c : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) : Integrable (fun ξ => ψ (yG lamf r c M ξ)) μ :=
  int_psi_bdd μ hL0 hL (measurable_yG_right hl hr c M) (yG_normSq_le hΛ hH c M)

/-- `Ψ` is Lipschitz for the Frobenius norm. -/
lemma PsiG_lip (hL0 : 0 ≤ L) (hL : EuLip ψ L) (hl : Measurable lamf) (hr : Measurable r)
    {Λ H : ℝ} (hΛ : ∀ ξ, lamf ξ ^ 2 ≤ Λ) (hH : ∀ ξ, normSq (r ξ) ≤ H) (c : Fin n → ℝ)
    (M N : Matrix (Fin n) (Fin m) ℝ) :
    |PsiG μ ψ lamf r c M - PsiG μ ψ lamf r c N| ≤ L * √(frob (M - N) * H) := by
  unfold PsiG
  have i1 := int_psi_yG μ hL0 hL hl hr hΛ hH c M
  have i2 := int_psi_yG μ hL0 hL hl hr hΛ hH c N
  rw [← integral_sub i1 i2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ ξ, |ψ (yG lamf r c M ξ) - ψ (yG lamf r c N ξ)| ≤ L * √(frob (M - N) * H) := by
    intro ξ
    refine (hL _ _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hL0)
    have e : ∑ i, (yG lamf r c M ξ i - yG lamf r c N ξ i) ^ 2 =
        normSq ((M - N) *ᵥ r ξ) := by
      rw [← yG_sub c M N ξ]; rfl
    rw [e]
    exact (normSq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hH ξ) (frob_nonneg _))
  have := integral_mono (i1.sub i2).abs (integrable_const (L * √(frob (M - N) * H))) hpt
  simpa using this

/-- `Ψ ∘ T` is Lipschitz for the Euclidean norm of the standardized entries. -/
lemma PsiG_eulip (hL0 : 0 ≤ L) (hL : EuLip ψ L) (hl : Measurable lamf) (hr : Measurable r)
    {Λ H : ℝ} (hΛ : ∀ ξ, lamf ξ ^ 2 ≤ Λ) (hH : ∀ ξ, normSq (r ξ) ≤ H) (c : Fin n → ℝ)
    {v : ℝ} (hv : 0 ≤ v) :
    EuLip (fun x : Fin n × Fin m → ℝ => PsiG μ ψ lamf r c (Tv v x)) (L * √(v * H)) := by
  intro x y
  refine (PsiG_lip μ hL0 hL hl hr hΛ hH c (Tv v x) (Tv v y)).trans (le_of_eq ?_)
  rw [frob_Tv_sub hv]
  have hS : 0 ≤ ∑ p, (x p - y p) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [show v * (∑ p, (x p - y p) ^ 2) * H = v * H * ∑ p, (x p - y p) ^ 2 by ring,
    Real.sqrt_mul' _ hS, mul_assoc]

/-- **For almost every `M`, for almost every `ξ`: `r ξ = 0` or `y_ξ(M)` is in the set `S` of
full Lebesgue measure.** -/
lemma ae_good (hl : Measurable lamf) (hr : Measurable r) (c : Fin n → ℝ) {v : ℝ} (hv : 0 < v)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (hS0 : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), y ∈ S) :
    ∀ᵐ M ∂gaussMat n m v, ∀ᵐ ξ ∂μ, r ξ = 0 ∨ yG lamf r c M ξ ∈ S := by
  have hB : MeasurableSet {q : Ξ × Matrix (Fin n) (Fin m) ℝ |
      r q.1 = 0 ∨ yG lamf r c q.2 q.1 ∈ S} := by
    have h1 : MeasurableSet {q : Ξ × Matrix (Fin n) (Fin m) ℝ | r q.1 = 0} :=
      (hr.comp measurable_fst) (measurableSet_singleton 0)
    have h2 : MeasurableSet {q : Ξ × Matrix (Fin n) (Fin m) ℝ | yG lamf r c q.2 q.1 ∈ S} :=
      ((measurable_yG hl hr c).comp measurable_swap) hS
    exact h1.union h2
  have h1 : ∀ ξ, ∀ᵐ M ∂gaussMat n m v, r ξ = 0 ∨ yG lamf r c M ξ ∈ S := by
    intro ξ
    by_cases h0 : r ξ = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inl h0
    · set σ : ℝ := √v * √(normSq (r ξ)) with hσ
      have hσ0 : σ ≠ 0 := by
        have h1 : 0 < √v := Real.sqrt_pos.mpr hv
        have h2 : 0 < normSq (r ξ) :=
          lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero h0))
        have h3 : 0 < √(normSq (r ξ)) := Real.sqrt_pos.mpr h2
        exact (mul_pos h1 h3).ne'
      have hSm : MeasurableSet {y' : Fin n → ℝ | lamf ξ • c + y' ∈ S} :=
        (measurable_const.add measurable_id) hS
      have hnull : ∀ᵐ γ ∂stdGauss (Fin n), lamf ξ • c + σ • γ ∈ S := by
        rw [ae_iff] at hS0
        refine stdGauss_ac (ae_iff.mpr ?_)
        have e : {γ : Fin n → ℝ | ¬(lamf ξ • c + σ • γ ∈ S)} =
            (fun γ : Fin n → ℝ => σ • γ) ⁻¹' ((fun x : Fin n → ℝ => lamf ξ • c + x) ⁻¹'
              {y | ¬(y ∈ S)}) := rfl
        rw [e, Measure.addHaar_preimage_smul _ hσ0, measure_preimage_add, hS0, mul_zero]
      have h2 : ∀ᵐ y' ∂(stdGauss (Fin n)).map (fun γ => σ • γ), lamf ξ • c + y' ∈ S :=
        (ae_map_iff (measurable_const_smul σ).aemeasurable hSm).mpr hnull
      rw [hσ, ← gaussMat_mulVec (m := n) (k := m) v (r ξ)] at h2
      have h3 := (ae_map_iff (measurable_mulVec_right (r ξ)).aemeasurable hSm).mp h2
      exact h3.mono fun M hM => Or.inr hM
  have h2 : ∀ᵐ ξ ∂μ, ∀ᵐ M ∂gaussMat n m v, r ξ = 0 ∨ yG lamf r c M ξ ∈ S :=
    Filter.Eventually.of_forall h1
  exact (Measure.ae_ae_comm hB).mp h2

/-- **The gradient bound.** At a point `x` (standardized entries, `M = T x`) where, for almost
every `ξ`, `r ξ = 0` or `y_ξ(M) ∈ S`: `|∇(Ψ ∘ T)(x)|² ≤ Mr·E_ξ Σ_i a(y_ξ(M))_i²`. -/
lemma grad_bound (hL0 : 0 ≤ L) (hL : EuLip ψ L) (hl : Measurable lamf) (hr : Measurable r)
    {Λ H : ℝ} (hΛ : ∀ ξ, lamf ξ ^ 2 ≤ Λ) (hH : ∀ ξ, normSq (r ξ) ≤ H) (c : Fin n → ℝ)
    {v : ℝ} (hv : 0 < v) {Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hMr : ∀ w : Fin m → ℝ, v * ∫ ξ, (∑ j, r ξ j * w j) ^ 2 ∂μ ≤ Mr * ∑ j, w j ^ 2)
    {S : Set (Fin n → ℝ)} {a : (Fin n → ℝ) → Fin n → ℝ} (ha : Measurable a) {Ca : ℝ}
    (hCa : ∀ y, ∑ i, a y i ^ 2 ≤ Ca)
    (hSa : ∀ y ∈ S, DifferentiableAt ℝ ψ y ∧ ∀ i, fderiv ℝ ψ y (Pi.single i 1) = a y i)
    (x : Fin n × Fin m → ℝ)
    (hx : ∀ᵐ ξ ∂μ, r ξ = 0 ∨ yG lamf r c (Tv v x) ξ ∈ S) :
    gradSq (fun x' : Fin n × Fin m → ℝ => PsiG μ ψ lamf r c (Tv v x')) x ≤
      Mr * AG μ a lamf r c (Tv v x) := by
  set G : (Fin n × Fin m → ℝ) → ℝ := fun x' => PsiG μ ψ lamf r c (Tv v x') with hG
  have hGL := PsiG_eulip μ hL0 hL hl hr hΛ hH c hv.le
  have hK0 : 0 ≤ L * √(v * H) := mul_nonneg hL0 (Real.sqrt_nonneg _)
  have hA0 : 0 ≤ AG μ a lamf r c (Tv v x) :=
    integral_nonneg fun ξ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hH0 : 0 ≤ H := by
    obtain ⟨ξ0⟩ := μ.nonempty_of_neZero
    exact (normSq_nonneg _).trans (hH ξ0)
  by_cases hd : DifferentiableAt ℝ G x
  swap
  · have : gradSq G x = 0 := by
      unfold gradSq
      rw [fderiv_zero_of_not_differentiableAt hd]
      simp
    rw [this]
    positivity
  obtain ⟨g, hlin, -⟩ := hGL.grad hK0 hd
  set D : ℝ := ∑ p, g p ^ 2 with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hgrad : gradSq G x = D := by
    unfold gradSq
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hlin]
    simp [dotProduct, Pi.single_apply]
  have hDg : fderiv ℝ G x g = D := by
    rw [hlin]
    simp only [dotProduct, hD]
    exact Finset.sum_congr rfl fun p _ => (sq _).symm
  -- the line `t ↦ x + t g`
  set N : Matrix (Fin n) (Fin m) ℝ := Tv v g with hN
  set y : Ξ → Fin n → ℝ := yG lamf r c (Tv v x) with hy
  set d : Ξ → Fin n → ℝ := fun ξ => N *ᵥ r ξ with hdd
  have hym : Measurable y := measurable_yG_right hl hr c (Tv v x)
  have hdm : Measurable d :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp hr
  have hdn : ∀ ξ, normSq (d ξ) ≤ frob N * H := fun ξ =>
    (normSq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hH ξ) (frob_nonneg _))
  set F : ℝ → Ξ → ℝ := fun t ξ => ψ (y ξ + t • d ξ) with hF
  set F' : Ξ → ℝ := fun ξ => ∑ i, a (y ξ) i * d ξ i with hF'
  have key : ∀ t : ℝ, G (x + t • g) = ∫ ξ, F t ξ ∂μ := by
    intro t
    simp only [hG, PsiG, hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show ψ (yG lamf r c (Tv v (x + t • g)) ξ) = ψ (y ξ + t • d ξ)
    rw [Tv_add_smul, yG_add_smul]
  have hderiv1 : HasDerivAt (fun t : ℝ => G (x + t • g)) (fderiv ℝ G x g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • g) g 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add x
      simpa using this
    have h2 : HasFDerivAt G (fderiv ℝ G x) (x + (0 : ℝ) • g) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hψm : Measurable ψ := (hL.continuous hL0).measurable
  have hFm : ∀ t : ℝ, Measurable (F t) := fun t =>
    hψm.comp (hym.add (hdm.const_smul t))
  have hF0 : Integrable (F 0) μ := by
    have e : F 0 = fun ξ => ψ (y ξ) := by
      funext ξ; simp [hF]
    rw [e]
    exact int_psi_yG μ hL0 hL hl hr hΛ hH c (Tv v x)
  have hF'm : Measurable F' := by
    refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
    · exact (measurable_pi_apply i).comp (ha.comp hym)
    · exact (measurable_pi_apply i).comp hdm
  set Kb : ℝ := L * √(frob N * H) with hKb
  have hKb0 : 0 ≤ Kb := mul_nonneg hL0 (Real.sqrt_nonneg _)
  have hlip : ∀ᵐ ξ ∂μ, LipschitzOnWith (Real.nnabs Kb) (fun t => F t ξ) univ := by
    refine Filter.Eventually.of_forall fun ξ => ?_
    refine (LipschitzWith.of_dist_le_mul fun t s => ?_).lipschitzOnWith
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hKb0]
    have h1 := hL (y ξ + t • d ξ) (y ξ + s • d ξ)
    have e : ∑ i, ((y ξ + t • d ξ) i - (y ξ + s • d ξ) i) ^ 2 = (t - s) ^ 2 * normSq (d ξ) := by
      unfold normSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs] at h1
    have h2 : √(normSq (d ξ)) ≤ √(frob N * H) := Real.sqrt_le_sqrt (hdn ξ)
    calc |F t ξ - F s ξ| ≤ L * (|t - s| * √(normSq (d ξ))) := h1
      _ ≤ L * (|t - s| * √(frob N * H)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) hL0
      _ = Kb * |t - s| := by rw [hKb]; ring
  have hdiff : ∀ᵐ ξ ∂μ, HasDerivAt (fun t => F t ξ) (F' ξ) 0 := by
    filter_upwards [hx] with ξ hξ
    rcases hξ with h0 | hS
    · have hd0 : d ξ = 0 := by
        simp only [hdd, h0, Matrix.mulVec_zero]
      have e1 : (fun t => F t ξ) = fun _ => ψ (y ξ) := by
        funext t; simp [hF, hd0]
      have e2 : F' ξ = 0 := by
        simp [hF', hd0]
      rw [e1, e2]
      exact hasDerivAt_const _ _
    · obtain ⟨hdψ, hpart⟩ := hSa _ hS
      have h1 : HasDerivAt (fun t : ℝ => y ξ + t • d ξ) (d ξ) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).smul_const (d ξ)).const_add (y ξ)
        simpa using this
      have h2 : HasFDerivAt ψ (fderiv ℝ ψ (y ξ)) (y ξ + (0 : ℝ) • d ξ) := by
        simpa using hdψ.hasFDerivAt
      have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
      have e : fderiv ℝ ψ (y ξ) (d ξ) = F' ξ := by
        rw [fderiv_eq_sum]
        simp only [hF']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hpart i]; ring
      rw [e] at h3
      exact h3
  obtain ⟨hF'int, hderiv2⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun _ => Kb) (s := univ)
    Filter.univ_mem (Filter.Eventually.of_forall fun t => (hFm t).aestronglyMeasurable) hF0
    hF'm.aestronglyMeasurable hlip (integrable_const _) hdiff
  have efun : (fun t : ℝ => G (x + t • g)) = fun t => ∫ ξ, F t ξ ∂μ := funext key
  rw [efun] at hderiv1
  have hDeq : D = ∫ ξ, F' ξ ∂μ := by
    rw [← hDg]; exact hderiv1.unique hderiv2
  -- Cauchy–Schwarz
  have hAint : Integrable (fun ξ => ∑ i, a (y ξ) i ^ 2) μ := by
    have hm : Measurable (fun ξ => ∑ i, a (y ξ) i ^ 2) :=
      Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp (ha.comp hym)).pow_const 2
    refine Integrable.of_bound hm.aestronglyMeasurable Ca (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact hCa _
  have hdint : Integrable (fun ξ => normSq (d ξ)) μ := by
    refine Integrable.of_bound (measurable_normSq.comp hdm).aestronglyMeasurable (frob N * H)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]
    exact hdn ξ
  have hcs := wcs (P := μ) (f := F') (D := fun ξ => ∑ i, a (y ξ) i ^ 2)
    (g := fun ξ => normSq (d ξ)) hF'int hAint hdint
    (fun ξ => Finset.sum_nonneg fun i _ => sq_nonneg _) (fun ξ => normSq_nonneg _)
    (fun ξ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => a (y ξ) i) (d ξ))
  -- the mean of `|N r|²`
  have hrow : ∀ i : Fin n, Integrable (fun ξ => (∑ j, r ξ j * N i j) ^ 2) μ := by
    intro i
    have hm : Measurable (fun ξ => (∑ j, r ξ j * N i j) ^ 2) :=
      (Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hr).mul_const _).pow_const 2
    refine Integrable.of_bound hm.aestronglyMeasurable (H * ∑ j, N i j ^ 2)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => r ξ j) (fun j => N i j)
    have h2 : (∑ j, r ξ j ^ 2) ≤ H := hH ξ
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hNr : ∫ ξ, normSq (d ξ) ∂μ ≤ Mr * D := by
    have e : ∀ ξ, normSq (d ξ) = ∑ i, (∑ j, r ξ j * N i j) ^ 2 := by
      intro ξ
      unfold normSq
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hdd, Matrix.mulVec, dotProduct]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => hrow i]
    have h1 : ∀ i : Fin n, ∫ ξ, (∑ j, r ξ j * N i j) ^ 2 ∂μ ≤ Mr * (∑ j, N i j ^ 2) / v := by
      intro i
      rw [le_div_iff₀ hv]
      have := hMr (fun j => N i j)
      linarith
    refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have hfr : ∑ i, ∑ j, N i j ^ 2 = v * D := by
      have := frob_Tv (n := n) (m := m) hv.le g
      unfold frob at this
      rw [hN, this]
    rw [hfr]
    field_simp
  have hfin : D ^ 2 ≤ AG μ a lamf r c (Tv v x) * (Mr * D) := by
    rw [hDeq]
    refine hcs.trans (mul_le_mul_of_nonneg_left ?_ hA0)
    rw [← hDeq]; exact hNr
  rw [hgrad]
  rcases hD0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : D * D ≤ (Mr * AG μ a lamf r c (Tv v x)) * D := by nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma measurable_AG (hl : Measurable lamf) (hr : Measurable r) (c : Fin n → ℝ)
    {a : (Fin n → ℝ) → Fin n → ℝ} (ha : Measurable a) :
    Measurable (AG μ a lamf r c) := by
  unfold AG
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : Matrix (Fin n) (Fin m) ℝ × Ξ => ∑ i, a (yG lamf r c q.1 q.2) i ^ 2) ?_
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp (ha.comp (measurable_yG hl hr c))).pow_const 2).stronglyMeasurable

lemma AG_le {a : (Fin n → ℝ) → Fin n → ℝ} {Ca : ℝ} (hCa : ∀ y, ∑ i, a y i ^ 2 ≤ Ca)
    (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) : AG μ a lamf r c M ≤ Ca := by
  unfold AG
  by_cases hi : Integrable (fun ξ => ∑ i, a (yG lamf r c M ξ) i ^ 2) μ
  · have := integral_mono hi (integrable_const Ca) fun ξ => hCa _
    simpa using this
  · rw [integral_undef hi]
    obtain ⟨ξ0⟩ := μ.nonempty_of_neZero
    exact (Finset.sum_nonneg fun i _ => sq_nonneg _).trans (hCa (yG lamf r c M ξ0))

lemma AG_nonneg (a : (Fin n → ℝ) → Fin n → ℝ) (c : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ AG μ a lamf r c M :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma integrable_AG (hl : Measurable lamf) (hr : Measurable r) (c : Fin n → ℝ)
    {a : (Fin n → ℝ) → Fin n → ℝ} (ha : Measurable a) {Ca : ℝ}
    (hCa : ∀ y, ∑ i, a y i ^ 2 ≤ Ca) (v : ℝ) :
    Integrable (AG μ a lamf r c) (gaussMat n m v) := by
  refine Integrable.of_bound (measurable_AG μ hl hr c ha).aestronglyMeasurable Ca
    (Filter.Eventually.of_forall fun M => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (AG_nonneg μ a c M)]
  exact AG_le μ hCa c M

/-- **The Poincaré step of Lemma U (i), general form.** `M` an `n × m` Gaussian matrix with
entry variance `v > 0`; `Ψ(M) = E_ξ ψ(lamf ξ • c + M·r ξ)` with `ψ` Lipschitz, with partial
derivatives `a` on a measurable set `S` of full Lebesgue measure; `v·E_ξ⟨r, w⟩² ≤ Mr·|w|²`. Then
`Var_M Ψ ≤ Mr·E_M E_ξ Σ_i a(y_ξ(M))_i²`. -/
theorem poincU (hL0 : 0 ≤ L) (hL : EuLip ψ L) (hl : Measurable lamf) (hr : Measurable r)
    {Λ H : ℝ} (hΛ : ∀ ξ, lamf ξ ^ 2 ≤ Λ) (hH : ∀ ξ, normSq (r ξ) ≤ H) (c : Fin n → ℝ)
    {v : ℝ} (hv : 0 < v) {Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hMr : ∀ w : Fin m → ℝ, v * ∫ ξ, (∑ j, r ξ j * w j) ^ 2 ∂μ ≤ Mr * ∑ j, w j ^ 2)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (hS0 : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), y ∈ S)
    {a : (Fin n → ℝ) → Fin n → ℝ} (ha : Measurable a) {Ca : ℝ}
    (hCa : ∀ y, ∑ i, a y i ^ 2 ≤ Ca)
    (hSa : ∀ y ∈ S, DifferentiableAt ℝ ψ y ∧ ∀ i, fderiv ℝ ψ y (Pi.single i 1) = a y i) :
    ∫ M, (PsiG μ ψ lamf r c M - ∫ M', PsiG μ ψ lamf r c M' ∂gaussMat n m v) ^ 2
        ∂gaussMat n m v ≤
      Mr * ∫ M, AG μ a lamf r c M ∂gaussMat n m v := by
  set G : (Fin n × Fin m → ℝ) → ℝ := fun x' => PsiG μ ψ lamf r c (Tv v x') with hG
  have hGL := PsiG_eulip μ hL0 hL hl hr hΛ hH c hv.le
  have hK0 : 0 ≤ L * √(v * H) := mul_nonneg hL0 (Real.sqrt_nonneg _)
  have hgood := ae_good μ hl hr c hv hS hS0
  rw [gaussMat_eq_Tv] at hgood
  have hgood' := ae_of_ae_map (measurable_Tv v).aemeasurable hgood
  have hAm := measurable_AG μ hl hr c ha
  have hΓ : Integrable (fun x : Fin n × Fin m → ℝ => Mr * AG μ a lamf r c (Tv v x))
      (stdGauss (Fin n × Fin m)) := by
    have h := integrable_AG μ hl hr c ha hCa v
    rw [gaussMat_eq_Tv] at h
    exact ((integrable_map_measure hAm.aestronglyMeasurable
      (measurable_Tv v).aemeasurable).mp h).const_mul Mr
  have hP := poincare_lip_le hK0 hGL hΓ (hgood'.mono fun x hx =>
    grad_bound μ hL0 hL hl hr hΛ hH c hv hMr0 hMr ha hCa hSa x hx)
  -- back to the Gaussian matrix
  have hΨm : Measurable (PsiG μ ψ lamf r c) := by
    have hc : Continuous (PsiG μ ψ lamf r c) := by
      refine continuous_iff_continuousAt.mpr fun M => ?_
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      have hcont : Continuous (fun N : Matrix (Fin n) (Fin m) ℝ => L * √(frob (N - M) * H)) := by
        have h1 : Continuous (fun N : Matrix (Fin n) (Fin m) ℝ => frob (N - M)) :=
          continuous_frob.comp (continuous_id.sub continuous_const)
        exact continuous_const.mul (Real.continuous_sqrt.comp (h1.mul continuous_const))
      have h0 : L * √(frob (M - M) * H) = 0 := by
        simp [frob]
      have ht := hcont.tendsto M
      rw [h0] at ht
      filter_upwards [ht.eventually (gt_mem_nhds hε)] with N hN
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (PsiG_lip μ hL0 hL hl hr hΛ hH c N M) hN
    exact hc.measurable
  have e1 : ∫ M', PsiG μ ψ lamf r c M' ∂gaussMat n m v = ∫ y, G y ∂stdGauss (Fin n × Fin m) := by
    rw [gaussMat_eq_Tv, integral_map (measurable_Tv v).aemeasurable hΨm.aestronglyMeasurable]
  have e2 : ∫ M, (PsiG μ ψ lamf r c M - ∫ M', PsiG μ ψ lamf r c M' ∂gaussMat n m v) ^ 2
      ∂gaussMat n m v =
      ∫ x, (G x - ∫ y, G y ∂stdGauss (Fin n × Fin m)) ^ 2 ∂stdGauss (Fin n × Fin m) := by
    rw [e1, gaussMat_eq_Tv]
    exact integral_map (μ := stdGauss (Fin n × Fin m)) (measurable_Tv v).aemeasurable
      (f := fun M => (PsiG μ ψ lamf r c M - ∫ y, G y ∂stdGauss (Fin n × Fin m)) ^ 2)
      ((hΨm.sub measurable_const).pow_const 2).aestronglyMeasurable
  have e3 : ∫ M, AG μ a lamf r c M ∂gaussMat n m v =
      ∫ x, AG μ a lamf r c (Tv v x) ∂stdGauss (Fin n × Fin m) := by
    rw [gaussMat_eq_Tv, integral_map (measurable_Tv v).aemeasurable hAm.aestronglyMeasurable]
  rw [e2, e3, ← integral_const_mul]
  exact hP

end main

end gen

end BstLean.Part151
