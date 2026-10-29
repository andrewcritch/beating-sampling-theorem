import BstLean.Part130Second
import BstLean.Part105Thm1

/-!
# Part 130, item 4: symmetries, the conditional Gaussian structure, and zero mean

Paper source: `delegations/answers/onW2c-cx.md` §2 and §4.
* `mlpGauss_input_orth`, `mlpGauss_output_orth`: the weight distribution is invariant under
  `M₁ ↦ M₁ R` and `M₃ ↦ Q M₃`, `R`, `Q` orthogonal; `mlpEval_input_orth`, `mlpEval_output_orth`:
  the consequences for the distribution of `N(z)`.
* `mlp2_last_gauss`, `mlp2_last_family`: given `(M₁, M₂)`, the output `M₃ h` is Gaussian with
  covariance `v|h|²·I`; the joint distribution of the outputs at several inputs depends on the Gram
  matrix of the last hidden vectors only.
* `muWn_normSq`: `x` is a unit vector, `μ_W`-almost surely.
* `Bn_integrable`, `Bn_mean_zero`: `E_F B(W, A, F) = 0` for every fixed `(W, A)`.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere gaussMom gaussMom_eq)
open BstLean.Part105 (sphProj measurable_sphProj)
open BstLean.Part73 (IsOrth)

variable {k m q : ℕ}

/-! ## Invariance of the weight distribution -/

/-- **Invariance under an orthogonal change of the input**: `(M₁ R, M₂, M₃)` has the
distribution of `(M₁, M₂, M₃)`. -/
theorem mlpGauss_input_orth (R : Matrix (Fin k) (Fin k) ℝ) (hR : IsOrth R) :
    (mlpGauss k m q).map (fun θ => (θ.1 * R, θ.2.1, θ.2.2)) = mlpGauss k m q := by
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => M * R) :=
    (Continuous.matrix_mul continuous_id continuous_const).measurable
  have h := Measure.map_prod_map (gaussMat m k (2 / (k : ℝ)))
    ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat q m (2 / (m : ℝ)))) hmeas measurable_id
  rw [gaussMat_mul_orth _ R hR, Measure.map_id] at h
  unfold mlpGauss
  conv_rhs => rw [h]
  rfl

/-- **Invariance under an orthogonal change of the output**: `(M₁, M₂, Q M₃)` has the
distribution of `(M₁, M₂, M₃)`. -/
theorem mlpGauss_output_orth (Q : Matrix (Fin q) (Fin q) ℝ) (hQ : IsOrth Q) :
    (mlpGauss k m q).map (fun θ => (θ.1, θ.2.1, Q * θ.2.2)) = mlpGauss k m q := by
  have hmeas : Measurable (fun M : Matrix (Fin q) (Fin m) ℝ => Q * M) :=
    (Continuous.matrix_mul continuous_const continuous_id).measurable
  have h1 := Measure.map_prod_map (gaussMat m m (2 / (m : ℝ))) (gaussMat q m (2 / (m : ℝ)))
    measurable_id hmeas
  rw [gaussMat_orth_mul _ Q hQ, Measure.map_id] at h1
  have h := Measure.map_prod_map (gaussMat m k (2 / (k : ℝ)))
    ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat q m (2 / (m : ℝ)))) measurable_id
    (measurable_id.prodMap hmeas)
  rw [Measure.map_id, ← h1] at h
  unfold mlpGauss
  conv_rhs => rw [h]
  rfl

/-- The sign change of the last matrix keeps the weight distribution. -/
theorem mlpGauss_neg_last :
    (mlpGauss k m q).map (fun θ => (θ.1, θ.2.1, -θ.2.2)) = mlpGauss k m q := by
  have hmeas : Measurable (fun M : Matrix (Fin q) (Fin m) ℝ => -M) := measurable_neg
  have h1 := Measure.map_prod_map (gaussMat m m (2 / (m : ℝ))) (gaussMat q m (2 / (m : ℝ)))
    measurable_id hmeas
  rw [gaussMat_neg, Measure.map_id] at h1
  have h := Measure.map_prod_map (gaussMat m k (2 / (k : ℝ)))
    ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat q m (2 / (m : ℝ)))) measurable_id
    (measurable_id.prodMap hmeas)
  rw [Measure.map_id, ← h1] at h
  unfold mlpGauss
  conv_rhs => rw [h]
  rfl

/-! ## Consequences for the distribution of the output -/

lemma continuous_mlpEval_joint :
    Continuous (fun p : MlpParam k m q × (Fin k → ℝ) => mlpEval p.1 p.2) := by
  unfold mlpEval mlp2
  refine Continuous.matrix_mulVec (by fun_prop) ?_
  refine continuous_reluV.comp ?_
  refine Continuous.matrix_mulVec (by fun_prop) ?_
  refine continuous_reluV.comp ?_
  exact Continuous.matrix_mulVec (by fun_prop) (by fun_prop)

lemma continuous_mlpEval_param (z : Fin k → ℝ) :
    Continuous (fun θ : MlpParam k m q => mlpEval θ z) :=
  continuous_mlpEval_joint.comp (continuous_id.prodMk continuous_const)

lemma continuous_mlpEval (θ : MlpParam k m q) : Continuous (mlpEval θ) :=
  continuous_mlpEval_joint.comp (continuous_const.prodMk continuous_id)

lemma measurable_mlpEval_param (z : Fin k → ℝ) :
    Measurable (fun θ : MlpParam k m q => mlpEval θ z) :=
  (continuous_mlpEval_param z).measurable

/-- **Rotation invariance in the input**: `N(R z)` has the distribution of `N(z)`. -/
theorem mlpEval_input_orth (R : Matrix (Fin k) (Fin k) ℝ) (hR : IsOrth R) (z : Fin k → ℝ) :
    (mlpGauss k m q).map (fun θ => mlpEval θ (R.mulVec z)) =
      (mlpGauss k m q).map (fun θ => mlpEval θ z) := by
  have hmeas : Measurable (fun θ : MlpParam k m q => (θ.1 * R, θ.2.1, θ.2.2)) :=
    (Continuous.prodMk (Continuous.matrix_mul continuous_fst continuous_const)
      continuous_snd).measurable
  conv_rhs => rw [← mlpGauss_input_orth (m := m) (q := q) R hR]
  rw [Measure.map_map (measurable_mlpEval_param z) hmeas]
  congr 1
  funext θ
  simp only [Function.comp, mlpEval, mlp2, Matrix.mulVec_mulVec]

/-- **Rotation invariance in the output**: `Q N(z)` has the distribution of `N(z)`. -/
theorem mlpEval_output_orth (Q : Matrix (Fin q) (Fin q) ℝ) (hQ : IsOrth Q) (z : Fin k → ℝ) :
    (mlpGauss k m q).map (fun θ => Q.mulVec (mlpEval θ z)) =
      (mlpGauss k m q).map (fun θ => mlpEval θ z) := by
  have hmeas : Measurable (fun θ : MlpParam k m q => (θ.1, θ.2.1, Q * θ.2.2)) :=
    (Continuous.prodMk continuous_fst (Continuous.prodMk (continuous_fst.comp continuous_snd)
      (Continuous.matrix_mul continuous_const (continuous_snd.comp continuous_snd)))).measurable
  conv_rhs => rw [← mlpGauss_output_orth (k := k) (m := m) Q hQ]
  rw [Measure.map_map (measurable_mlpEval_param z) hmeas]
  congr 1
  funext θ
  simp only [Function.comp, mlpEval, mlp2, Matrix.mulVec_mulVec]

/-! ## The conditional Gaussian structure of the last matrix -/

variable {m₁ m₂ : ℕ}

/-- The last hidden vector `h₂(z) = ReLU(M₂ ReLU(M₁ z))`. -/
noncomputable def hid2 (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (z : Fin k → ℝ) : Fin m₂ → ℝ :=
  reluV (M₂.mulVec (reluV (M₁.mulVec z)))

lemma mlp2_eq_hid2 (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (M₃ : Matrix (Fin q) (Fin m₂) ℝ) (z : Fin k → ℝ) :
    mlp2 M₁ M₂ M₃ z = M₃.mulVec (hid2 M₁ M₂ z) := rfl

/-- **Given `(M₁, M₂)`, the output `M₃ h₂(z)` is a Gaussian vector with covariance
`v·|h₂(z)|²·I_q`**: it has the distribution of `√v·|h₂(z)|·ξ`, `ξ` standard Gaussian in `ℝ^q`.
(`v = 2/m` in the random MLP distribution.) -/
theorem mlp2_last_gauss (v : ℝ) (M₁ : Matrix (Fin m₁) (Fin k) ℝ)
    (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (z : Fin k → ℝ) :
    (gaussMat q m₂ v).map (fun M₃ => mlp2 M₁ M₂ M₃ z) =
      (stdGauss (Fin q)).map
        (fun ξ => (Real.sqrt v * Real.sqrt (normSq (hid2 M₁ M₂ z))) • ξ) :=
  gaussMat_mulVec v (hid2 M₁ M₂ z)

/-- **Given the hidden matrices, the outputs at several inputs form a Gaussian family whose
distribution depends on the Gram matrix of the last hidden vectors only.** Two networks (hidden
matrices `(M₁, M₂)` and `(M₁', M₂')`, inputs `z a` and `z' a`, last hidden widths `m₂`, `m₂'`)
with `⟨h₂(z a), h₂(z b)⟩ = ⟨h₂'(z' a), h₂'(z' b)⟩` for all `a, b` have the same distribution of
`(M₃ h₂(z a))_a`. -/
theorem mlp2_last_family {p k' m₁' m₂' : ℕ} (v : ℝ)
    (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (M₁' : Matrix (Fin m₁') (Fin k') ℝ) (M₂' : Matrix (Fin m₂') (Fin m₁') ℝ)
    (z : Fin p → Fin k → ℝ) (z' : Fin p → Fin k' → ℝ)
    (hG : ∀ a b, ∑ j, hid2 M₁ M₂ (z a) j * hid2 M₁ M₂ (z b) j =
      ∑ j, hid2 M₁' M₂' (z' a) j * hid2 M₁' M₂' (z' b) j) :
    (gaussMat q m₂ v).map (fun M₃ a => mlp2 M₁ M₂ M₃ (z a)) =
      (gaussMat q m₂' v).map (fun M₃ a => mlp2 M₁' M₂' M₃ (z' a)) :=
  gaussMat_family v (fun a => hid2 M₁ M₂ (z a)) (fun a => hid2 M₁' M₂' (z' a)) hG

lemma stdGauss_mul_integrable {ι : Type*} [Fintype ι] (a b : ι) :
    Integrable (fun ξ : ι → ℝ => ξ a * ξ b) (stdGauss ι) := by
  unfold stdGauss
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
    simpa using integrable_pow_gauss 1
  exact pi_mul_integrable (f := fun x => x) h1 (integrable_pow_gauss 2) a b

lemma stdGauss_cov {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    ∫ ξ, ξ a * ξ b ∂stdGauss ι = if a = b then 1 else 0 := by
  unfold stdGauss
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
    simpa using integrable_pow_gauss 1
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    have := integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := a)
      (integrable_pow_gauss 2).aestronglyMeasurable
    simp only [sq] at this
    rw [this]
    have h2 := gaussMom_eq 2
    simp only [sq] at h2
    rw [h2]
    norm_num [gaussMom]
  · simp only [hab, ↓reduceIte]
    have hind := (iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun _ => fun x : ℝ => x)
      (fun _ => measurable_id.aemeasurable)).indepFun hab
    have h := hind.integral_mul_eq_mul_integral
      (measurable_pi_apply a).aestronglyMeasurable (measurable_pi_apply b).aestronglyMeasurable
    have h3 : ∫ ω : ι → ℝ, ω a ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = 0 := by
      rw [integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := a) (f := fun x => x)
        measurable_id.aestronglyMeasurable]
      exact integral_id_gaussianReal
    have h' : ∫ ω : ι → ℝ, ω a * ω b ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
        (∫ ω : ι → ℝ, ω a ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) *
          ∫ ω : ι → ℝ, ω b ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := h
    rw [h', h3, zero_mul]

/-- The covariance of two outputs of a Gaussian matrix:
`E[(M h)_i (M h′)_j] = v·⟨h, h′⟩·δ_ij`. -/
theorem gaussMat_cov {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) (i j : Fin m) :
    ∫ M, (M.mulVec h) i * (M.mulVec h') j ∂gaussMat m k v =
      if i = j then v * ∑ l, h l * h' l else 0 := by
  classical
  unfold gaussMat
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => (M.mulVec h) i * (M.mulVec h') j) :=
    ((measurable_pi_apply i).comp (measurable_mulVec_right h)).mul
      ((measurable_pi_apply j).comp (measurable_mulVec_right h'))
  rw [integral_map (measurable_ofFlat _).aemeasurable hmeas.aestronglyMeasurable]
  have e : ∀ ξ : Fin m × Fin k → ℝ,
      ((Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin m) (Fin k) ℝ).mulVec h) i *
        ((Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin m) (Fin k) ℝ).mulVec h') j =
      ∑ l, ∑ l', (v * (h l * h' l')) * (ξ (i, l) * ξ (j, l')) := by
    intro ξ
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    have := Real.mul_self_sqrt hv
    calc Real.sqrt v * ξ (i, l) * h l * (Real.sqrt v * ξ (j, l') * h' l')
        = (Real.sqrt v * Real.sqrt v) * (h l * h' l') * (ξ (i, l) * ξ (j, l')) := by ring
      _ = _ := by rw [this]
  simp_rw [e]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun l' _ =>
    (stdGauss_mul_integrable _ _).const_mul _]
  simp_rw [integral_finsetSum _ fun l' _ =>
    (stdGauss_mul_integrable (ι := Fin m × Fin k) _ _).const_mul _, integral_const_mul,
    stdGauss_cov, Prod.mk.injEq]
  by_cases hij : i = j
  · simp only [hij, true_and, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, Finset.mul_sum]
  · simp [hij]

end BstLean.Part130

open BstLean.Part130 in
#print axioms mlpGauss_input_orth
open BstLean.Part130 in
#print axioms mlpGauss_output_orth
open BstLean.Part130 in
#print axioms mlpEval_input_orth
open BstLean.Part130 in
#print axioms mlpEval_output_orth
open BstLean.Part130 in
#print axioms mlp2_last_gauss
open BstLean.Part130 in
#print axioms mlp2_last_family
open BstLean.Part130 in
#print axioms gaussMat_cov
