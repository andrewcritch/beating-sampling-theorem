import BstLean.Part130All
import BstLean.Part131Block
import BstLean.Part131Cantelli
import BstLean.Part131Estimator
import BstLean.Part131Fubini

/-!
# Part 131, items 3 to 6: the probability step of Theorem C for the networks

Role: `delegations/statements/p131-spec.md`. Paper source: round onW4c ("Confirmed probability
argument", §7); round onW2c (the conditional Gaussian structure).

Notation of Part 130: `W : MlpParam N mW n` (the World network; `N = r·n`), `A : MlpParam n mA n`
(the Agent network), `F = (F₁, F₂, F₃) : MlpParam n mF 1`; `Bn W A F` the target, `sdn W A F` the
realized spread.

* `hidF F₁ F₂ A x`: the last hidden vector of `F` at `A(x)`.
* `aVec W A F₁ F₂`: its mean over `u` (`a_A`); `covMat W A F₁ F₂`: its covariance over `u` (`Σ_A`).
* `Dn = (2/m_F)|a_A − a_{A′}|²`, `Tn = (2/m_F)·tr((Σ_A + Σ_{A′})/2)`, `Jn = Dn − Tn`.
* `Bn_last`, `sdn_last`: `B_A = w·a_A`, `s_A = √(wᵀΣ_A w)`, `w` the one row of `F₃`.
* `sep_cond` (item 3): if `Tn < Dn`, the separation has probability above `3/25` over `F₃`.
* `thmC_of_meanVar` (item 4), `noReadA_of_separation` (item 5), `thmC_conditional` (item 6).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130

universe w

variable {N mW n mA mF : ℕ}

/-! ## Definitions -/

/-- The last hidden vector of `F` at `A(x)`: `ReLU(F₂ ReLU(F₁ A(x)))`. -/
noncomputable def hidF (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) (x : Fin n → ℝ) : Fin mF → ℝ :=
  hid2 F₁ F₂ (mlpEval A x)

/-- `a_A`: the mean over `u` of the last hidden vector of `F` at `A(x(u))`. -/
noncomputable def aVec (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) : Fin mF → ℝ :=
  fun i => ∫ x, hidF F₁ F₂ A x i ∂muWn W

/-- `Σ_A`: the covariance matrix over `u` of the last hidden vector of `F` at `A(x(u))`. -/
noncomputable def covMat (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    Matrix (Fin mF) (Fin mF) ℝ :=
  Matrix.of fun i j => ∫ x, (hidF F₁ F₂ A x i - aVec W A F₁ F₂ i) *
    (hidF F₁ F₂ A x j - aVec W A F₁ F₂ j) ∂muWn W

/-- `D = (2/m_F)·|a_A − a_{A′}|²`: the variance of `B_A − B_{A′}` over the last matrix of `F`. -/
noncomputable def Dn (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) : ℝ :=
  2 / (mF : ℝ) * normSq (aVec W A F₁ F₂ - aVec W A' F₁ F₂)

/-- `T̄ = (2/m_F)·tr((Σ_A + Σ_{A′})/2)`: the mean of `(s_A² + s_{A′}²)/2` over the last matrix
of `F`. -/
noncomputable def Tn (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) : ℝ :=
  2 / (mF : ℝ) * (((1 : ℝ) / 2) • (covMat W A F₁ F₂ + covMat W A' F₁ F₂)).trace

/-- `J = D − T̄`, a function of `(W, A, A′, F₁, F₂)`. -/
noncomputable def Jn (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) : ℝ :=
  Dn W A A' F₁ F₂ - Tn W A A' F₁ F₂

/-! ## The linear and the quadratic form in the last row of `F` -/

lemma hidF_eq (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) (x : Fin n → ℝ) :
    hidF F₁ F₂ A x = mlpEval ((F₁, F₂, (1 : Matrix (Fin mF) (Fin mF) ℝ)) : MlpParam n mF mF)
      (mlpEval A x) := by
  simp [hidF, hid2, mlpEval, mlp2]

lemma continuous_hidF (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) (i : Fin mF) : Continuous fun x => hidF F₁ F₂ A x i := by
  simp_rw [hidF_eq]
  exact (continuous_apply i).comp ((continuous_mlpEval _).comp (continuous_mlpEval A))

lemma phiN_last (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
    (F₂ : Matrix (Fin mF) (Fin mF) ℝ) (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (x : Fin n → ℝ) :
    phiN A (F₁, F₂, F₃) x = ∑ j, F₃ 0 j * hidF F₁ F₂ A x j := rfl

section fixed

variable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
  (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)

include hn hN

lemma hidF_integrable (i : Fin mF) : Integrable (fun x => hidF F₁ F₂ A x i) (muWn W) :=
  muWn_integrable_of_continuous hn hN W (continuous_hidF F₁ F₂ A i)

lemma hidF_cov_integrable (i j : Fin mF) :
    Integrable (fun x => (hidF F₁ F₂ A x i - aVec W A F₁ F₂ i) *
      (hidF F₁ F₂ A x j - aVec W A F₁ F₂ j)) (muWn W) :=
  muWn_integrable_of_continuous hn hN W
    (((continuous_hidF F₁ F₂ A i).sub continuous_const).mul
      ((continuous_hidF F₁ F₂ A j).sub continuous_const))

/-- **`B_A = w·a_A`**, `w` the row of the last matrix of `F`. -/
theorem Bn_last (F₃ : Matrix (Fin 1) (Fin mF) ℝ) :
    Bn W A (F₁, F₂, F₃) = rowOf 0 F₃ ⬝ᵥ aVec W A F₁ F₂ := by
  unfold Bn
  simp_rw [phiN_last]
  rw [integral_finsetSum _ fun j _ => (hidF_integrable hn hN W A F₁ F₂ j).const_mul _]
  simp_rw [integral_const_mul]
  rfl

/-- `yᵀΣ_A y = E_u (y·(H − a_A))²`. -/
lemma covMat_qform (y : Fin mF → ℝ) :
    y ⬝ᵥ covMat W A F₁ F₂ *ᵥ y =
      ∫ x, (∑ j, y j * (hidF F₁ F₂ A x j - aVec W A F₁ F₂ j)) ^ 2 ∂muWn W := by
  rw [qform_expand]
  have e : ∀ x, (∑ j, y j * (hidF F₁ F₂ A x j - aVec W A F₁ F₂ j)) ^ 2 =
      ∑ i, ∑ j, (y i * y j) * ((hidF F₁ F₂ A x i - aVec W A F₁ F₂ i) *
        (hidF F₁ F₂ A x j - aVec W A F₁ F₂ j)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hidF_cov_integrable hn hN W A F₁ F₂ i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hidF_cov_integrable hn hN W A F₁ F₂ i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  simp only [covMat, of_apply]
  ring

/-- `Σ_A` has a nonnegative quadratic form. -/
lemma covMat_nonneg (y : Fin mF → ℝ) : 0 ≤ y ⬝ᵥ covMat W A F₁ F₂ *ᵥ y := by
  rw [covMat_qform hn hN]
  exact integral_nonneg fun x => sq_nonneg _

/-- **`s_A² = wᵀΣ_A w`**, in the form `s_A = √(wᵀΣ_A w)`. -/
theorem sdn_last (F₃ : Matrix (Fin 1) (Fin mF) ℝ) :
    sdn W A (F₁, F₂, F₃) = √(rowOf 0 F₃ ⬝ᵥ covMat W A F₁ F₂ *ᵥ rowOf 0 F₃) := by
  unfold sdn
  congr 1
  rw [variance_eq_integral (continuous_phiN A (F₁, F₂, F₃)).measurable.aemeasurable,
    covMat_qform hn hN]
  have hB := Bn_last hn hN W A F₁ F₂ F₃
  unfold Bn at hB
  rw [hB]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [phiN_last, dotProduct, rowOf]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end fixed

/-! ## Item 3: the conditional separation statement -/

/-- `((s + s′)/2)² ≤ (s² + s′²)/2`, in the form that the separation needs. -/
lemma sep_arith {p p' y : ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p') (h : (p + p') / 2 < y ^ 2) :
    (√p + √p') / 2 < |y| := by
  have h1 : √p ^ 2 = p := Real.sq_sqrt hp
  have h2 : √p' ^ 2 = p' := Real.sq_sqrt hp'
  have h3 : 0 ≤ √p := Real.sqrt_nonneg _
  have h4 : 0 ≤ √p' := Real.sqrt_nonneg _
  have h5 : ((√p + √p') / 2) ^ 2 < y ^ 2 := by nlinarith [sq_nonneg (√p - √p')]
  have h6 := sq_lt_sq.mp h5
  rwa [abs_of_nonneg (by positivity)] at h6

/-- **Item 3 (the conditional separation).** Fix `W`, `A`, `A′` and the first two matrices
`F₁, F₂` of `F`. If `T̄ < D`, then over the last matrix `F₃` of `F` (one row, independent
`N(0, 2/m_F)` entries) the separation `|B_A − B_{A′}| > (s_A + s_{A′})/2` has probability above
`3/25`. -/
theorem sep_cond (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (hJ : Tn W A A' F₁ F₂ < Dn W A A' F₁ F₂) :
    3 / 25 < (gaussMat 1 mF (2 / (mF : ℝ))).real
      {F₃ | (sdn W A (F₁, F₂, F₃) + sdn W A' (F₁, F₂, F₃)) / 2 <
        |Bn W A (F₁, F₂, F₃) - Bn W A' (F₁, F₂, F₃)|} := by
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 ≤ α := by positivity
  set r : ℝ := √α with hr
  have hrr : r * r = α := Real.mul_self_sqrt hα0
  set a := aVec W A F₁ F₂ with ha
  set a' := aVec W A' F₁ F₂ with ha'
  set C := covMat W A F₁ F₂ with hC
  set C' := covMat W A' F₁ F₂ with hC'
  let v : Fin mF → ℝ := r • (a - a')
  let M : Matrix (Fin mF) (Fin mF) ℝ := α • (((1 : ℝ) / 2) • (C + C'))
  have hMq : ∀ y : Fin mF → ℝ, y ⬝ᵥ M *ᵥ y = α * ((y ⬝ᵥ C *ᵥ y + y ⬝ᵥ C' *ᵥ y) / 2) := by
    intro y
    simp only [M, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, smul_eq_mul]
    ring
  have hM : ∀ y : Fin mF → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y := by
    intro y
    rw [hMq]
    have h1 := covMat_nonneg hn hN W A F₁ F₂ y
    have h2 := covMat_nonneg hn hN W A' F₁ F₂ y
    positivity
  have hv : M.trace < v ⬝ᵥ v := by
    have e1 : M.trace = Tn W A A' F₁ F₂ := by
      simp only [M, Tn, trace_smul, smul_eq_mul, hα, hC, hC']
    have e2 : v ⬝ᵥ v = Dn W A A' F₁ F₂ := by
      simp only [v, Dn, normSq, dotProduct, ← hα, ← ha, ← ha']
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hrr]; ring
    rw [e1, e2]; exact hJ
  have hblock := gauss_block v M hM hv
  -- the separation event in terms of the row `w`
  let S' : Set (Fin mF → ℝ) :=
    {w | (√(w ⬝ᵥ C *ᵥ w) + √(w ⬝ᵥ C' *ᵥ w)) / 2 < |w ⬝ᵥ a - w ⬝ᵥ a'|}
  have hS' : MeasurableSet S' := by
    have h1 : Continuous fun w : Fin mF → ℝ => (√(w ⬝ᵥ C *ᵥ w) + √(w ⬝ᵥ C' *ᵥ w)) / 2 := by
      fun_prop
    have h2 : Continuous fun w : Fin mF → ℝ => |w ⬝ᵥ a - w ⬝ᵥ a'| := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hset : {F₃ : Matrix (Fin 1) (Fin mF) ℝ |
      (sdn W A (F₁, F₂, F₃) + sdn W A' (F₁, F₂, F₃)) / 2 <
        |Bn W A (F₁, F₂, F₃) - Bn W A' (F₁, F₂, F₃)|} = rowOf 0 ⁻¹' S' := by
    ext F₃
    simp only [S', mem_preimage, mem_ofPred_eq, sdn_last hn hN, Bn_last hn hN, ← ha, ← ha', ← hC,
      ← hC']
  rw [hset, ← map_measureReal_apply (measurable_rowOf 0) hS', gaussMat_row,
    map_measureReal_apply (measurable_const_smul _) hS']
  refine lt_of_lt_of_le hblock (measureReal_mono ?_)
  intro ξ hξ
  have hξ' : ξ ⬝ᵥ M *ᵥ ξ < (ξ ⬝ᵥ v) ^ 2 := hξ
  rw [hMq] at hξ'
  change (√((r • ξ) ⬝ᵥ C *ᵥ (r • ξ)) + √((r • ξ) ⬝ᵥ C' *ᵥ (r • ξ))) / 2 <
    |(r • ξ) ⬝ᵥ a - (r • ξ) ⬝ᵥ a'|
  have q1 : (r • ξ) ⬝ᵥ C *ᵥ (r • ξ) = α * (ξ ⬝ᵥ C *ᵥ ξ) := by
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, hrr]
  have q2 : (r • ξ) ⬝ᵥ C' *ᵥ (r • ξ) = α * (ξ ⬝ᵥ C' *ᵥ ξ) := by
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, hrr]
  have q3 : (r • ξ) ⬝ᵥ a - (r • ξ) ⬝ᵥ a' = ξ ⬝ᵥ v := by
    simp only [v, smul_dotProduct, dotProduct_smul, dotProduct_sub, smul_eq_mul]
    ring
  rw [q1, q2, q3]
  have n1 : 0 ≤ α * (ξ ⬝ᵥ C *ᵥ ξ) := mul_nonneg hα0 (covMat_nonneg hn hN W A F₁ F₂ ξ)
  have n2 : 0 ≤ α * (ξ ⬝ᵥ C' *ᵥ ξ) := mul_nonneg hα0 (covMat_nonneg hn hN W A' F₁ F₂ ξ)
  exact sep_arith n1 n2 (by linarith)

/-! ## What `D` and `T̄` are: the conditional distribution over the last matrix of `F` -/

lemma smul_sub_dot {α : ℝ} (hα : 0 ≤ α) (a a' : Fin mF → ℝ) :
    (√α • (a - a')) ⬝ᵥ (√α • (a - a')) = α * normSq (a - a') := by
  simp only [normSq, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := Real.sq_sqrt hα
  calc √α * (a - a') i * (√α * (a - a') i) = √α ^ 2 * (a - a') i ^ 2 := by ring
    _ = α * (a - a') i ^ 2 := by rw [h]

/-- **Given `W`, `A`, `A′`, `F₁`, `F₂`: over the last matrix of `F`, `B_A − B_{A′}` is a centred
Gaussian with variance `D`.** -/
theorem Bn_diff_gaussian (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    (gaussMat 1 mF (2 / (mF : ℝ))).map
        (fun F₃ => Bn W A (F₁, F₂, F₃) - Bn W A' (F₁, F₂, F₃)) =
      gaussianReal 0 (Dn W A A' F₁ F₂).toNNReal := by
  have hα0 : (0 : ℝ) ≤ 2 / (mF : ℝ) := by positivity
  have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => Bn W A (F₁, F₂, F₃) - Bn W A' (F₁, F₂, F₃)) =
      (fun w : Fin mF → ℝ => w ⬝ᵥ (aVec W A F₁ F₂ - aVec W A' F₁ F₂)) ∘ rowOf 0 := by
    funext F₃
    simp only [Function.comp, Bn_last hn hN, dotProduct_sub]
  have hm : Measurable (fun w : Fin mF → ℝ => w ⬝ᵥ (aVec W A F₁ F₂ - aVec W A' F₁ F₂)) := by
    fun_prop
  rw [e, ← Measure.map_map hm (measurable_rowOf 0), gaussMat_row,
    Measure.map_map hm (measurable_const_smul _)]
  have e2 : ((fun w : Fin mF → ℝ => w ⬝ᵥ (aVec W A F₁ F₂ - aVec W A' F₁ F₂)) ∘
      fun ξ : Fin mF → ℝ => √(2 / (mF : ℝ)) • ξ) =
      fun ξ => ξ ⬝ᵥ (√(2 / (mF : ℝ)) • (aVec W A F₁ F₂ - aVec W A' F₁ F₂)) := by
    funext ξ
    simp only [Function.comp, smul_dotProduct, dotProduct_smul]
  rw [e2, stdGauss_dot, smul_sub_dot hα0]
  rfl

/-- The mean of a quadratic form in the row of a Gaussian matrix with one row. -/
lemma gaussMat_row_qform (α : ℝ) (hα : 0 ≤ α) (C : Matrix (Fin mF) (Fin mF) ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => rowOf 0 F₃ ⬝ᵥ C *ᵥ rowOf 0 F₃)
      (gaussMat 1 mF α) ∧
    ∫ F₃, rowOf 0 F₃ ⬝ᵥ C *ᵥ rowOf 0 F₃ ∂gaussMat 1 mF α = α * C.trace := by
  have hc : Continuous fun w : Fin mF → ℝ => w ⬝ᵥ C *ᵥ w := by fun_prop
  have hq : ∀ ξ : Fin mF → ℝ, (√α • ξ) ⬝ᵥ C *ᵥ (√α • ξ) = α * (ξ ⬝ᵥ C *ᵥ ξ) := by
    intro ξ
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, Real.mul_self_sqrt hα]
  constructor
  · have h1 : Integrable (fun w : Fin mF → ℝ => w ⬝ᵥ C *ᵥ w)
        ((gaussMat 1 mF α).map (rowOf 0)) := by
      rw [gaussMat_row, integrable_map_measure hc.measurable.aestronglyMeasurable
        (measurable_const_smul _).aemeasurable]
      simp only [Function.comp_def, hq]
      exact (qform_integrable C).const_mul α
    exact (integrable_map_measure hc.measurable.aestronglyMeasurable
      (measurable_rowOf 0).aemeasurable).mp h1
  · rw [← integral_map (measurable_rowOf 0).aemeasurable hc.measurable.aestronglyMeasurable
        (f := fun w : Fin mF → ℝ => w ⬝ᵥ C *ᵥ w),
      gaussMat_row, integral_map (measurable_const_smul _).aemeasurable
        hc.measurable.aestronglyMeasurable]
    simp only [hq]
    rw [integral_const_mul, qform_integral]

/-- **Given `W`, `A`, `F₁`, `F₂`: the mean of `s_A²` over the last matrix of `F` is
`(2/m_F)·tr Σ_A`.** -/
theorem sdn_sq_mean_last (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => sdn W A (F₁, F₂, F₃) ^ 2)
      (gaussMat 1 mF (2 / (mF : ℝ))) ∧
    ∫ F₃, sdn W A (F₁, F₂, F₃) ^ 2 ∂gaussMat 1 mF (2 / (mF : ℝ)) =
      2 / (mF : ℝ) * (covMat W A F₁ F₂).trace := by
  have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => sdn W A (F₁, F₂, F₃) ^ 2) =
      fun F₃ => rowOf 0 F₃ ⬝ᵥ covMat W A F₁ F₂ *ᵥ rowOf 0 F₃ := by
    funext F₃
    rw [sdn_last hn hN, Real.sq_sqrt (covMat_nonneg hn hN W A F₁ F₂ _)]
  rw [e]
  exact gaussMat_row_qform _ (by positivity) _

/-- **`T̄` is the mean of `(s_A² + s_{A′}²)/2` over the last matrix of `F`.** -/
theorem Tn_eq_mean (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    ∫ F₃, (sdn W A (F₁, F₂, F₃) ^ 2 + sdn W A' (F₁, F₂, F₃) ^ 2) / 2
      ∂gaussMat 1 mF (2 / (mF : ℝ)) = Tn W A A' F₁ F₂ := by
  obtain ⟨i1, e1⟩ := sdn_sq_mean_last hn hN W A F₁ F₂
  obtain ⟨i2, e2⟩ := sdn_sq_mean_last hn hN W A' F₁ F₂
  rw [integral_div, integral_add i1 i2, e1, e2]
  simp only [Tn, trace_smul, trace_add, smul_eq_mul]
  ring

end BstLean.Part131


open BstLean.Part131 in
#print axioms Bn_last
open BstLean.Part131 in
#print axioms sdn_last
open BstLean.Part131 in
#print axioms sep_cond
open BstLean.Part131 in
#print axioms Bn_diff_gaussian
open BstLean.Part131 in
#print axioms Tn_eq_mean
