import BstLean.Part130Row

/-!
# Part 130: the exact two-point formula of one layer, and of the last two matrices

Paper source: `delegations/answers/onW2c-cx.md` §3, (4) and (5).
* `layer_dot_relu`: `E ⟨ReLU(M h), ReLU(M h′)⟩ = (m/2)·v·|h||h′|·κ(cos(h, h′))`.
* `layer_dot_lin`: `E ⟨M h, M h′⟩ = m·v·⟨h, h′⟩`.
* `mlp2_two_point_inner`: given `M₁`, the mean of `⟨N(z), N(z′)⟩` over `(M₂, M₃)` is
  `q·v₃·(m₂/2)·v₂·|h₁||h₁′|·κ(cos(h₁, h₁′))`, `h₁ = ReLU(M₁ z)`, `h₁′ = ReLU(M₁ z′)`.
  The width `m₂` of the last hidden layer cancels for the variances of the random MLP distribution.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

variable {k m m₁ m₂ q : ℕ}

/-- `⟨y, y′⟩ = Σ_i y_i y′_i`. -/
def dotp {ι : Type*} [Fintype ι] (y y' : ι → ℝ) : ℝ := ∑ i, y i * y' i

/-- The two-point kernel of one ReLU layer: `Φ(h, h′) = |h||h′|·κ(⟨h, h′⟩/(|h||h′|))`
(`0` if `h = 0` or `h′ = 0`). -/
noncomputable def kernelPhi {ι : Type*} [Fintype ι] (h h' : ι → ℝ) : ℝ :=
  Real.sqrt (normSq h) * Real.sqrt (normSq h') *
    kappa (dotp h h' / (Real.sqrt (normSq h) * Real.sqrt (normSq h')))

lemma abs_mul_le_normSq {ι : Type*} [Fintype ι] (y y' : ι → ℝ) (i : ι) :
    |y i * y' i| ≤ normSq y + normSq y' := by
  have h1 : y i ^ 2 ≤ normSq y :=
    Finset.single_le_sum (f := fun i => y i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : y' i ^ 2 ≤ normSq y' :=
    Finset.single_le_sum (f := fun i => y' i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y i - y' i), sq_nonneg (y i + y' i)]

lemma abs_dotp_le {ι : Type*} [Fintype ι] (y y' : ι → ℝ) :
    |dotp y y'| ≤ normSq y + normSq y' := by
  have h : ∀ i, |y i * y' i| ≤ (y i ^ 2 + y' i ^ 2) / 2 := by
    intro i
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y i - y' i), sq_nonneg (y i + y' i)]
  calc |dotp y y'| ≤ ∑ i, |y i * y' i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (y i ^ 2 + y' i ^ 2) / 2 := Finset.sum_le_sum fun i _ => h i
    _ = (normSq y + normSq y') / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]; rfl
    _ ≤ normSq y + normSq y' := by
      linarith [normSq_nonneg y, normSq_nonneg y']

lemma continuous_dotp {ι : Type*} [Fintype ι] :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => dotp p.1 p.2) :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

lemma layer_mul_relu_integrable {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) (i : Fin m) :
    Integrable (fun M => relu ((M.mulVec h) i) * relu ((M.mulVec h') i)) (gaussMat m k v) := by
  refine Integrable.mono' ((layer_lin_sq hv h).1.add (layer_lin_sq hv h').1) ?_ ?_
  · exact ((measurable_relu.comp ((measurable_pi_apply i).comp (measurable_mulVec_right h))).mul
      (measurable_relu.comp ((measurable_pi_apply i).comp
        (measurable_mulVec_right h')))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun M => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |relu ((M.mulVec h) i)| * |relu ((M.mulVec h') i)|
        ≤ |(M.mulVec h) i| * |(M.mulVec h') i| :=
          mul_le_mul (abs_relu_le _) (abs_relu_le _) (abs_nonneg _) (abs_nonneg _)
      _ = |(M.mulVec h) i * (M.mulVec h') i| := (abs_mul _ _).symm
      _ ≤ _ := abs_mul_le_normSq _ _ i

/-- **The exact two-point formula of one ReLU layer**:
`E ⟨ReLU(M h), ReLU(M h′)⟩ = (m/2)·v·Φ(h, h′)`. -/
theorem layer_dot_relu {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M => dotp (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) ∧
    ∫ M, dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) ∂gaussMat m k v =
      (m : ℝ) / 2 * (v * kernelPhi h h') := by
  refine ⟨integrable_finsetSum _ fun i _ => layer_mul_relu_integrable hv h h' i, ?_⟩
  unfold dotp reluV
  rw [integral_finsetSum _ fun i _ => layer_mul_relu_integrable hv h h' i]
  have hrow : ∀ i : Fin m, ∫ M, relu ((M.mulVec h) i) * relu ((M.mulVec h') i) ∂gaussMat m k v =
      v * kernelPhi h h' / 2 := by
    intro i
    have := row_formula (m := m) hv h h' i
    unfold kernelPhi dotp
    linarith
  simp_rw [hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma layer_mul_lin_integrable {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) (i : Fin m) :
    Integrable (fun M => (M.mulVec h) i * (M.mulVec h') i) (gaussMat m k v) := by
  refine Integrable.mono' ((layer_lin_sq hv h).1.add (layer_lin_sq hv h').1) ?_ ?_
  · exact (((measurable_pi_apply i).comp (measurable_mulVec_right h)).mul
      ((measurable_pi_apply i).comp (measurable_mulVec_right h'))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun M => abs_mul_le_normSq _ _ i

/-- `E ⟨M h, M h′⟩ = m·v·⟨h, h′⟩`. -/
theorem layer_dot_lin {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M => dotp (M.mulVec h) (M.mulVec h')) (gaussMat m k v) ∧
    ∫ M, dotp (M.mulVec h) (M.mulVec h') ∂gaussMat m k v = (m : ℝ) * (v * dotp h h') := by
  refine ⟨integrable_finsetSum _ fun i _ => layer_mul_lin_integrable hv h h' i, ?_⟩
  unfold dotp
  rw [integral_finsetSum _ fun i _ => layer_mul_lin_integrable hv h h' i]
  simp_rw [gaussMat_cov hv h h']
  simp

/-- **The exact two-point formula given `M₁`** (paper: onW2c (5)): the mean of `⟨N(z), N(z′)⟩`
over `(M₂, M₃)` is `q·v₃·(m₂/2)·v₂·Φ(h₁, h₁′)`, `h₁ = ReLU(M₁ z)`, `h₁′ = ReLU(M₁ z′)`. -/
theorem mlp2_two_point_inner {v₂ v₃ : ℝ} (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (z z' : Fin k → ℝ) :
    ∫ θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ,
        dotp (mlp2 M₁ θ.1 θ.2 z) (mlp2 M₁ θ.1 θ.2 z')
      ∂((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) =
      (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
        kernelPhi (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) := by
  set μ := (gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃) with hμ
  -- integrability of the two squared norms on the product
  have hsq : ∀ z : Fin k → ℝ, Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ ×
      Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 M₁ θ.1 θ.2 z)) μ := by
    intro z
    have step := prod_step (μ := gaussMat m₂ m₁ v₂) (ν := gaussMat q m₂ v₃)
      (continuous_normSq_mlp2_inner z M₁).measurable (fun p => normSq_nonneg _)
      (fun M₂ => (q : ℝ) * (v₃ * normSq (reluV (M₂.mulVec (reluV (M₁.mulVec z))))))
      (fun M₂ => layer_lin_sq (m := q) h₃ (reluV (M₂.mulVec (reluV (M₁.mulVec z)))))
      (((layer_relu_sq (m := m₂) h₂ (reluV (M₁.mulVec z))).1.const_mul v₃).const_mul (q : ℝ))
    exact step.1
  have hcont : Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      dotp (mlp2 M₁ θ.1 θ.2 z) (mlp2 M₁ θ.1 θ.2 z')) := by
    have c1 := continuous_mlp2 (m₁ := m₁) (m₂ := m₂) (q := q) z
    have c2 := continuous_mlp2 (m₁ := m₁) (m₂ := m₂) (q := q) z'
    have c0 : Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (M₁, θ)) := by fun_prop
    exact continuous_dotp.comp ((c1.comp c0).prodMk (c2.comp c0))
  have hint : Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      dotp (mlp2 M₁ θ.1 θ.2 z) (mlp2 M₁ θ.1 θ.2 z')) μ := by
    refine Integrable.mono' ((hsq z).add (hsq z')) hcont.measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun θ => abs_dotp_le _ _
  rw [hμ, integral_prod _ hint]
  have hin : ∀ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ,
      ∫ M₃, dotp (mlp2 M₁ M₂ M₃ z) (mlp2 M₁ M₂ M₃ z') ∂gaussMat q m₂ v₃ =
        (q : ℝ) * (v₃ * dotp (reluV (M₂.mulVec (reluV (M₁.mulVec z))))
          (reluV (M₂.mulVec (reluV (M₁.mulVec z'))))) := by
    intro M₂
    exact (layer_dot_lin (m := q) h₃ (reluV (M₂.mulVec (reluV (M₁.mulVec z))))
      (reluV (M₂.mulVec (reluV (M₁.mulVec z'))))).2
  simp_rw [hin]
  rw [integral_const_mul, integral_const_mul,
    (layer_dot_relu (m := m₂) h₂ (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z'))).2]
  ring

/-- The same at the variances of the random MLP distribution (`v₂ = v₃ = 2/m`, `m ≥ 1`):
`E[⟨N(z), N(z′)⟩ | M₁] = q·(2/m)·Φ(h₁, h₁′)`. The width of the last hidden layer cancels. -/
theorem mlp_two_point_inner (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin k) ℝ) (z z' : Fin k → ℝ) :
    ∫ θ : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin q) (Fin m) ℝ,
        dotp (mlp2 M₁ θ.1 θ.2 z) (mlp2 M₁ θ.1 θ.2 z')
      ∂((gaussMat m m (2 / (m : ℝ))).prod (gaussMat q m (2 / (m : ℝ)))) =
      (q : ℝ) * (2 / (m : ℝ) * kernelPhi (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z'))) := by
  rw [mlp2_two_point_inner (two_div_nonneg m) (two_div_nonneg m)]
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp

end BstLean.Part130

open BstLean.Part130 in
#print axioms layer_dot_relu
open BstLean.Part130 in
#print axioms layer_dot_lin
open BstLean.Part130 in
#print axioms mlp_two_point_inner
