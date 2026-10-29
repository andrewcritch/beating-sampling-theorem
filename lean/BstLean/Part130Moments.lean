import BstLean.Part130Layer
import BstLean.Part29GaussProd

/-!
# Part 130, moments of one layer

* `int_relu_sq`, `int_relu_four`: `E ReLU(g)² = 1/2`, `E ReLU(g)⁴ = 3/2`, `g` standard Gaussian.
* `pi_sum`, `pi_sum_sq`: the first two moments of a sum of independent copies.
* `layer_relu_sq`, `layer_relu_four`: for a Gaussian matrix `M` (`m` rows, variance `v`) and a fixed
  vector `h`: `E|ReLU(M h)|² = (m/2)·v|h|²`, `E|ReLU(M h)|⁴ = (m²/4 + 5m/4)·(v|h|²)²`.
* `layer_lin_sq`, `layer_lin_four`: `E|M h|² = m·v|h|²`, `E|M h|⁴ = (m² + 2m)·(v|h|²)²`.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)

/-! ## `relu` -/

lemma relu_nonneg (t : ℝ) : 0 ≤ relu t := le_max_left _ _

lemma relu_of_nonneg {t : ℝ} (h : 0 ≤ t) : relu t = t := max_eq_right h

lemma relu_of_nonpos {t : ℝ} (h : t ≤ 0) : relu t = 0 := max_eq_left h

lemma abs_relu_le (t : ℝ) : |relu t| ≤ |t| := by
  rcases le_total 0 t with h | h
  · rw [relu_of_nonneg h]
  · rw [relu_of_nonpos h]; simp

lemma relu_pow_add (t : ℝ) {n : ℕ} (hn : n ≠ 0) : relu t ^ n + relu (-t) ^ n = |t| ^ n := by
  rcases le_total 0 t with h | h
  · rw [relu_of_nonneg h, relu_of_nonpos (by linarith), zero_pow hn, abs_of_nonneg h, add_zero]
  · rw [relu_of_nonpos h, relu_of_nonneg (by linarith), zero_pow hn, abs_of_nonpos h, zero_add]

lemma relu_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : relu (c * t) = c * relu t := by
  unfold relu
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

lemma continuous_relu : Continuous relu := continuous_const.max continuous_id

lemma measurable_relu : Measurable relu := continuous_relu.measurable

lemma continuous_reluV {ι : Type*} : Continuous (reluV : (ι → ℝ) → ι → ℝ) :=
  continuous_pi fun i => continuous_relu.comp (continuous_apply i)

lemma measurable_reluV {ι : Type*} [Countable ι] : Measurable (reluV : (ι → ℝ) → ι → ℝ) :=
  measurable_pi_iff.mpr fun i => measurable_relu.comp (measurable_pi_apply i)

lemma normSq_nonneg {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ normSq y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_normSq {ι : Type*} [Fintype ι] : Continuous (normSq : (ι → ℝ) → ℝ) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2

lemma normSq_smul {ι : Type*} [Fintype ι] (c : ℝ) (y : ι → ℝ) : normSq (c • y) = c ^ 2 * normSq y := by
  simp only [normSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma reluV_smul_of_nonneg {ι : Type*} {c : ℝ} (hc : 0 ≤ c) (y : ι → ℝ) :
    reluV (c • y) = c • reluV y := by
  funext i
  simp only [reluV, Pi.smul_apply, smul_eq_mul, relu_mul_of_nonneg hc]

/-! ## One standard Gaussian -/

lemma integrable_pow_gauss (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) n

lemma integrable_relu_pow (n : ℕ) : Integrable (fun x : ℝ => relu x ^ n) (gaussianReal 0 1) := by
  refine (integrable_pow_gauss n).mono (measurable_relu.pow_const n).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_relu_le x) n

lemma int_relu_pow_even {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    ∫ x, relu x ^ n ∂gaussianReal 0 1 = gaussMom n / 2 := by
  have h1 : ∫ x, relu (-x) ^ n ∂gaussianReal 0 1 = ∫ x, relu x ^ n ∂gaussianReal 0 1 := by
    have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
      rw [gaussianReal_map_neg]; simp
    conv_rhs => rw [← hneg]
    rw [integral_map (by fun_prop) (measurable_relu.pow_const n).aestronglyMeasurable]
  have hint2 : Integrable (fun x : ℝ => relu (-x) ^ n) (gaussianReal 0 1) := by
    refine (integrable_pow_gauss n).mono
      ((measurable_relu.comp measurable_neg).pow_const n).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using abs_relu_le (-x)) n
  have h2 : ∫ x, relu x ^ n ∂gaussianReal 0 1 + ∫ x, relu (-x) ^ n ∂gaussianReal 0 1 =
      gaussMom n := by
    rw [← integral_add (integrable_relu_pow n) hint2, ← gaussMom_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [relu_pow_add x hn, Even.pow_abs he]
  linarith

lemma int_relu_sq : ∫ x, relu x ^ 2 ∂gaussianReal 0 1 = 1 / 2 := by
  rw [int_relu_pow_even (by norm_num) (by decide)]
  norm_num [gaussMom]

lemma int_relu_four : ∫ x, relu x ^ 4 ∂gaussianReal 0 1 = 3 / 2 := by
  rw [int_relu_pow_even (by norm_num) (by decide)]
  have : Even 4 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]

/-! ## Sums of independent copies -/

section pi

variable {ι : Type*} [Fintype ι] {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma pi_sum_integrable {f : ℝ → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω : ι → ℝ => ∑ i, f (ω i)) (Measure.pi fun _ : ι => μ) :=
  integrable_finsetSum _ fun i _ => integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hf

/-- `E Σ_i f(ω_i) = m·E f`. -/
lemma pi_sum {f : ℝ → ℝ} (hf : Integrable f μ) :
    ∫ ω : ι → ℝ, ∑ i, f (ω i) ∂(Measure.pi fun _ : ι => μ) = Fintype.card ι * ∫ x, f x ∂μ := by
  rw [integral_finsetSum _ fun i _ => integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hf]
  simp_rw [integral_comp_eval (μ := fun _ : ι => μ) hf.aestronglyMeasurable]
  simp

lemma pi_mul_integrable {f : ℝ → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (i j : ι) :
    Integrable (fun ω : ι → ℝ => f (ω i) * f (ω j)) (Measure.pi fun _ : ι => μ) := by
  by_cases hij : i = j
  · subst hij
    have := integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hf2
    simpa [sq] using this
  · have hind := (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => f)
      (fun _ => hf.aestronglyMeasurable.aemeasurable)).indepFun hij
    exact hind.integrable_mul (integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hf)
      (integrable_comp_eval (μ := fun _ : ι => μ) (i := j) hf)

lemma pi_sum_sq_integrable {f : ℝ → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    Integrable (fun ω : ι → ℝ => (∑ i, f (ω i)) ^ 2) (Measure.pi fun _ : ι => μ) := by
  have : (fun ω : ι → ℝ => (∑ i, f (ω i)) ^ 2) = fun ω => ∑ i, ∑ j, f (ω i) * f (ω j) := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  rw [this]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    pi_mul_integrable hf hf2 i j

/-- `E (Σ_i f(ω_i))² = m·E f² + m(m − 1)·(E f)²`. -/
lemma pi_sum_sq {f : ℝ → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ ω : ι → ℝ, (∑ i, f (ω i)) ^ 2 ∂(Measure.pi fun _ : ι => μ) =
      Fintype.card ι * ∫ x, f x ^ 2 ∂μ +
        Fintype.card ι * ((Fintype.card ι : ℝ) - 1) * (∫ x, f x ∂μ) ^ 2 := by
  classical
  have : (fun ω : ι → ℝ => (∑ i, f (ω i)) ^ 2) = fun ω => ∑ i, ∑ j, f (ω i) * f (ω j) := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    pi_mul_integrable hf hf2 i j]
  simp_rw [integral_finsetSum _ fun j _ => pi_mul_integrable hf hf2 _ j]
  have key : ∀ i j : ι, ∫ ω : ι → ℝ, f (ω i) * f (ω j) ∂(Measure.pi fun _ : ι => μ) =
      if i = j then ∫ x, f x ^ 2 ∂μ else (∫ x, f x ∂μ) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have := integral_comp_eval (μ := fun _ : ι => μ) (i := i) hf2.aestronglyMeasurable
      simpa [sq] using this
    · simp only [hij, ↓reduceIte]
      have hind := (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => f)
        (fun _ => hf.aestronglyMeasurable.aemeasurable)).indepFun hij
      have h := hind.integral_mul_eq_mul_integral
        (integrable_comp_eval (μ := fun _ : ι => μ) (i := i) hf).aestronglyMeasurable
        (integrable_comp_eval (μ := fun _ : ι => μ) (i := j) hf).aestronglyMeasurable
      rw [integral_comp_eval (μ := fun _ : ι => μ) hf.aestronglyMeasurable,
        integral_comp_eval (μ := fun _ : ι => μ) hf.aestronglyMeasurable] at h
      rw [sq, ← h]
      rfl
  simp_rw [key]
  have e : ∀ i : ι, ∑ j, (if i = j then ∫ x, f x ^ 2 ∂μ else (∫ x, f x ∂μ) ^ 2) =
      ∫ x, f x ^ 2 ∂μ + ((Fintype.card ι : ℝ) - 1) * (∫ x, f x ∂μ) ^ 2 := by
    intro i
    have : ∀ j : ι, (if i = j then ∫ x, f x ^ 2 ∂μ else (∫ x, f x ∂μ) ^ 2) =
        (∫ x, f x ∂μ) ^ 2 + if i = j then (∫ x, f x ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2) else 0 := by
      intro j; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mem_univ, ite_true]
    ring
  simp_rw [e]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end pi

/-! ## One layer -/

variable {m k : ℕ}

lemma measurable_mulVec_right (h : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h) :=
  (Continuous.matrix_mulVec continuous_id continuous_const).measurable

/-- A function of `M h` has the same mean as the same function of `√v·|h|·ξ`. -/
lemma layer_transfer (v : ℝ) (h : Fin k → ℝ) {g : (Fin m → ℝ) → ℝ} (hg : Measurable g) :
    ∫ M, g (M.mulVec h) ∂gaussMat m k v =
      ∫ ξ, g ((Real.sqrt v * Real.sqrt (normSq h)) • ξ) ∂stdGauss (Fin m) := by
  have h1 := integral_map (μ := gaussMat m k v) (measurable_mulVec_right h).aemeasurable
    (f := g) hg.aestronglyMeasurable
  rw [← h1, gaussMat_mulVec, integral_map (measurable_const_smul _).aemeasurable
    hg.aestronglyMeasurable]

lemma layer_transfer_integrable (v : ℝ) (h : Fin k → ℝ) {g : (Fin m → ℝ) → ℝ} (hg : Measurable g)
    (hi : Integrable (fun ξ => g ((Real.sqrt v * Real.sqrt (normSq h)) • ξ)) (stdGauss (Fin m))) :
    Integrable (fun M => g (M.mulVec h)) (gaussMat m k v) := by
  have h1 := integrable_map_measure (μ := gaussMat m k v) (f := fun M => M.mulVec h) (g := g)
    hg.aestronglyMeasurable (measurable_mulVec_right h).aemeasurable
  refine h1.mp ?_
  rw [gaussMat_mulVec]
  exact (integrable_map_measure hg.aestronglyMeasurable (measurable_const_smul _).aemeasurable).mpr hi

lemma sq_scale {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    (Real.sqrt v * Real.sqrt (normSq h)) ^ 2 = v * normSq h := by
  rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg h)]

lemma scale_nonneg (v : ℝ) (h : Fin k → ℝ) : 0 ≤ Real.sqrt v * Real.sqrt (normSq h) :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma measurable_normSq {ι : Type*} [Fintype ι] : Measurable (normSq : (ι → ℝ) → ℝ) :=
  continuous_normSq.measurable

lemma sq_sq (x : ℝ) : (x ^ 2) ^ 2 = x ^ 4 := by ring

/-- `E|ReLU(M h)|² = (m/2)·v|h|²`. -/
theorem layer_relu_sq {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M => normSq (reluV (M.mulVec h))) (gaussMat m k v) ∧
    ∫ M, normSq (reluV (M.mulVec h)) ∂gaussMat m k v = (m : ℝ) / 2 * (v * normSq h) := by
  have hg : Measurable (fun y : Fin m → ℝ => normSq (reluV y)) :=
    measurable_normSq.comp measurable_reluV
  have e : ∀ ξ : Fin m → ℝ, normSq (reluV ((Real.sqrt v * Real.sqrt (normSq h)) • ξ)) =
      (v * normSq h) * ∑ i, relu (ξ i) ^ 2 := by
    intro ξ
    rw [reluV_smul_of_nonneg (scale_nonneg v h), normSq_smul, sq_scale hv]
    rfl
  refine ⟨layer_transfer_integrable v h hg ?_, ?_⟩
  · simp_rw [e]
    exact (pi_sum_integrable (integrable_relu_pow 2)).const_mul _
  · rw [layer_transfer v h hg]
    simp_rw [e]
    rw [integral_const_mul]
    unfold stdGauss
    rw [pi_sum (integrable_relu_pow 2), int_relu_sq, Fintype.card_fin]
    ring

/-- `E|ReLU(M h)|⁴ = (m²/4 + 5m/4)·(v|h|²)²`. -/
theorem layer_relu_four {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M => normSq (reluV (M.mulVec h)) ^ 2) (gaussMat m k v) ∧
    ∫ M, normSq (reluV (M.mulVec h)) ^ 2 ∂gaussMat m k v =
      ((m : ℝ) ^ 2 / 4 + 5 * m / 4) * (v * normSq h) ^ 2 := by
  have hg : Measurable (fun y : Fin m → ℝ => normSq (reluV y) ^ 2) :=
    (measurable_normSq.comp measurable_reluV).pow_const 2
  have e : ∀ ξ : Fin m → ℝ, normSq (reluV ((Real.sqrt v * Real.sqrt (normSq h)) • ξ)) ^ 2 =
      (v * normSq h) ^ 2 * (∑ i, relu (ξ i) ^ 2) ^ 2 := by
    intro ξ
    rw [reluV_smul_of_nonneg (scale_nonneg v h), normSq_smul, sq_scale hv, mul_pow]
    rfl
  have i4 : Integrable (fun x : ℝ => (relu x ^ 2) ^ 2) (gaussianReal 0 1) := by
    simp_rw [sq_sq]; exact integrable_relu_pow 4
  refine ⟨layer_transfer_integrable v h hg ?_, ?_⟩
  · simp_rw [e]
    exact (pi_sum_sq_integrable (integrable_relu_pow 2) i4).const_mul _
  · rw [layer_transfer v h hg]
    simp_rw [e]
    rw [integral_const_mul]
    unfold stdGauss
    rw [pi_sum_sq (integrable_relu_pow 2) i4, int_relu_sq]
    simp_rw [sq_sq]
    rw [int_relu_four, Fintype.card_fin]
    ring

/-- `E|M h|² = m·v|h|²`. -/
theorem layer_lin_sq {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M => normSq (M.mulVec h)) (gaussMat m k v) ∧
    ∫ M, normSq (M.mulVec h) ∂gaussMat m k v = (m : ℝ) * (v * normSq h) := by
  have e : ∀ ξ : Fin m → ℝ, normSq ((Real.sqrt v * Real.sqrt (normSq h)) • ξ) =
      (v * normSq h) * ∑ i, ξ i ^ 2 := by
    intro ξ
    rw [normSq_smul, sq_scale hv]
    rfl
  refine ⟨layer_transfer_integrable v h measurable_normSq ?_, ?_⟩
  · simp_rw [e]
    exact (pi_sum_integrable (integrable_pow_gauss 2)).const_mul _
  · rw [layer_transfer v h measurable_normSq]
    simp_rw [e]
    rw [integral_const_mul]
    unfold stdGauss
    rw [pi_sum (integrable_pow_gauss 2), gaussMom_eq, Fintype.card_fin]
    norm_num [gaussMom]
    ring

/-- `E|M h|⁴ = (m² + 2m)·(v|h|²)²`. -/
theorem layer_lin_four {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M => normSq (M.mulVec h) ^ 2) (gaussMat m k v) ∧
    ∫ M, normSq (M.mulVec h) ^ 2 ∂gaussMat m k v =
      ((m : ℝ) ^ 2 + 2 * m) * (v * normSq h) ^ 2 := by
  have hg : Measurable (fun y : Fin m → ℝ => normSq y ^ 2) := measurable_normSq.pow_const 2
  have e : ∀ ξ : Fin m → ℝ, normSq ((Real.sqrt v * Real.sqrt (normSq h)) • ξ) ^ 2 =
      (v * normSq h) ^ 2 * (∑ i, ξ i ^ 2) ^ 2 := by
    intro ξ
    rw [normSq_smul, sq_scale hv, mul_pow]
    rfl
  have i4 : Integrable (fun x : ℝ => (x ^ 2) ^ 2) (gaussianReal 0 1) := by
    simp_rw [sq_sq]; exact integrable_pow_gauss 4
  refine ⟨layer_transfer_integrable v h hg ?_, ?_⟩
  · simp_rw [e]
    exact (pi_sum_sq_integrable (integrable_pow_gauss 2) i4).const_mul _
  · rw [layer_transfer v h hg]
    simp_rw [e]
    rw [integral_const_mul]
    unfold stdGauss
    rw [pi_sum_sq (integrable_pow_gauss 2) i4]
    simp_rw [sq_sq]
    rw [gaussMom_eq, gaussMom_eq, Fintype.card_fin]
    have : Even 4 := by decide
    simp [gaussMom, this, Nat.doubleFactorial]
    ring

end BstLean.Part130
