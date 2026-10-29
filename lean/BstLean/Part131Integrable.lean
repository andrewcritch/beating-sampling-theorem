import BstLean.Part131Space

/-!
# Part 131: `J = D − T̄` has a finite second moment

Role: `delegations/statements/p131-spec.md`, item 4 ("state its integrability as a hypothesis or
prove it"). `memLp_Jall`: `J` is in `L²` of the distribution of the four networks. So the mean and
the variance of `J` in `thmC_of_meanVar` are those of a square-integrable variable.

Proof: for a unit vector `x`, `|H(x)|² ≤ K`, with `K` the product of the squared Frobenius norms
of the five matrices `F₂, F₁, A₃, A₂, A₁` (Cauchy–Schwarz, and `ReLU(t)² ≤ t²`). So
`|J| ≤ (2/m_F)·m_F·2·(K_A + K_{A′})`, and `K²` is a product of integrable functions of independent
matrices.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130

variable {N mW n mA mF : ℕ}

/-- The squared Frobenius norm of a matrix. -/
def frob {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

lemma frob_nonneg {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : 0 ≤ frob M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_frob {a b : ℕ} : Continuous (frob : Matrix (Fin a) (Fin b) ℝ → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).pow 2

lemma normSq_mulVec_le {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (h : Fin b → ℝ) :
    normSq (M *ᵥ h) ≤ frob M * normSq h := by
  unfold normSq frob
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) h

lemma normSq_reluV_le {a : ℕ} (v : Fin a → ℝ) : normSq (reluV v) ≤ normSq v := by
  unfold normSq reluV
  refine Finset.sum_le_sum fun i _ => ?_
  have := abs_relu_le (v i)
  exact sq_le_sq.mpr this

lemma normSq_hid2_le {k m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ)
    (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (z : Fin k → ℝ) :
    normSq (hid2 M₁ M₂ z) ≤ frob M₂ * (frob M₁ * normSq z) := by
  unfold hid2
  calc normSq (reluV (M₂ *ᵥ reluV (M₁ *ᵥ z))) ≤ normSq (M₂ *ᵥ reluV (M₁ *ᵥ z)) :=
        normSq_reluV_le _
    _ ≤ frob M₂ * normSq (reluV (M₁ *ᵥ z)) := normSq_mulVec_le _ _
    _ ≤ frob M₂ * (frob M₁ * normSq z) :=
        mul_le_mul_of_nonneg_left ((normSq_reluV_le _).trans (normSq_mulVec_le _ _))
          (frob_nonneg _)

lemma normSq_mlpEval_le {k m q : ℕ} (θ : MlpParam k m q) (z : Fin k → ℝ) :
    normSq (mlpEval θ z) ≤ frob θ.2.2 * (frob θ.2.1 * (frob θ.1 * normSq z)) := by
  unfold mlpEval
  rw [mlp2_eq_hid2]
  exact (normSq_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_left (normSq_hid2_le _ _ _) (frob_nonneg _))

/-- `(‖A₃‖²‖A₂‖²‖A₁‖²)²`. -/
def frobA (A : MlpParam n mA n) : ℝ := frob A.1 ^ 2 * (frob A.2.1 ^ 2 * frob A.2.2 ^ 2)

/-- `K`: the product of the squared Frobenius norms of `F₂, F₁, A₃, A₂, A₁`. -/
def Kb (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) : ℝ :=
  frob F₂ * (frob F₁ * (frob A.2.2 * (frob A.2.1 * frob A.1)))

lemma Kb_nonneg (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) : 0 ≤ Kb F₁ F₂ A := by
  unfold Kb
  have := frob_nonneg F₁; have := frob_nonneg F₂; have := frob_nonneg A.1
  have := frob_nonneg A.2.1; have := frob_nonneg A.2.2
  positivity

lemma Kb_sq (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) : Kb F₁ F₂ A ^ 2 = frob F₁ ^ 2 * frob F₂ ^ 2 * frobA A := by
  unfold Kb frobA; ring

lemma hidF_sq_le (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (A : MlpParam n mA n) {x : Fin n → ℝ} (hx : normSq x = 1) (i : Fin mF) :
    hidF F₁ F₂ A x i ^ 2 ≤ Kb F₁ F₂ A := by
  have h1 : hidF F₁ F₂ A x i ^ 2 ≤ normSq (hidF F₁ F₂ A x) :=
    Finset.single_le_sum (f := fun i => hidF F₁ F₂ A x i ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 := normSq_hid2_le F₁ F₂ (mlpEval A x)
  have h3 := normSq_mlpEval_le A x
  rw [hx, mul_one] at h3
  have h4 : frob F₂ * (frob F₁ * normSq (mlpEval A x)) ≤ Kb F₁ F₂ A := by
    unfold Kb
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (frob_nonneg _)) (frob_nonneg _)
  exact h1.trans (h2.trans h4)

section bounds

variable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
  (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)

include hn hN

lemma aVec_sq_le (i : Fin mF) : aVec W A F₁ F₂ i ^ 2 ≤ Kb F₁ F₂ A := by
  have := muWn_isProbability hN W
  have hK := Kb_nonneg F₁ F₂ A
  have h1 : ‖∫ x, hidF F₁ F₂ A x i ∂muWn W‖ ≤ √(Kb F₁ F₂ A) * (muWn W).real univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [muWn_normSq hn W] with x hx
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (hidF_sq_le F₁ F₂ A hx i)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h1
  have h2 : aVec W A F₁ F₂ i ^ 2 ≤ √(Kb F₁ F₂ A) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [Real.sq_sqrt hK] at h2

omit hn hN in
lemma covDiag_nonneg (i : Fin mF) : 0 ≤ covMat W A F₁ F₂ i i := by
  simp only [covMat, of_apply]
  exact integral_nonneg fun x => mul_self_nonneg _

lemma covDiag_le (i : Fin mF) : covMat W A F₁ F₂ i i ≤ 4 * Kb F₁ F₂ A := by
  have := muWn_isProbability hN W
  have ha := aVec_sq_le hn hN W A F₁ F₂ i
  simp only [covMat, of_apply]
  have h1 : ∫ x, (hidF F₁ F₂ A x i - aVec W A F₁ F₂ i) * (hidF F₁ F₂ A x i - aVec W A F₁ F₂ i)
      ∂muWn W ≤ ∫ _ : Fin n → ℝ, 4 * Kb F₁ F₂ A ∂muWn W := by
    refine integral_mono_ae (hidF_cov_integrable hn hN W A F₁ F₂ i i) (integrable_const _) ?_
    filter_upwards [muWn_normSq hn W] with x hx
    have hh := hidF_sq_le F₁ F₂ A hx i
    nlinarith [sq_nonneg (hidF F₁ F₂ A x i + aVec W A F₁ F₂ i)]
  simpa using h1

end bounds

/-- `|J| ≤ 4·(K_A + K_{A′})` (the factor `(2/m_F)·m_F` is at most `2`). -/
lemma abs_Jn_le (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    |Jn W A A' F₁ F₂| ≤ 4 * (Kb F₁ F₂ A + Kb F₁ F₂ A') := by
  have hK := Kb_nonneg F₁ F₂ A
  have hK' := Kb_nonneg F₁ F₂ A'
  have hα0 : (0 : ℝ) ≤ 2 / (mF : ℝ) := by positivity
  have hαm : 2 / (mF : ℝ) * (mF : ℝ) ≤ 2 := by
    rcases Nat.eq_zero_or_pos mF with h | h
    · simp [h]
    · have : (0 : ℝ) < mF := by exact_mod_cast h
      rw [div_mul_cancel₀ _ this.ne']
  -- `0 ≤ S_D ≤ m_F·2(K + K′)` and the same for `S_T`
  have hD1 : normSq (aVec W A F₁ F₂ - aVec W A' F₁ F₂) ≤
      (mF : ℝ) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) := by
    unfold normSq
    calc ∑ i, (aVec W A F₁ F₂ - aVec W A' F₁ F₂) i ^ 2
        ≤ ∑ _i : Fin mF, 2 * (Kb F₁ F₂ A + Kb F₁ F₂ A') := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := aVec_sq_le hn hN W A F₁ F₂ i
          have h2 := aVec_sq_le hn hN W A' F₁ F₂ i
          simp only [Pi.sub_apply]
          nlinarith [sq_nonneg (aVec W A F₁ F₂ i + aVec W A' F₁ F₂ i)]
      _ = (mF : ℝ) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) := by simp
  have hD0 : 0 ≤ normSq (aVec W A F₁ F₂ - aVec W A' F₁ F₂) := normSq_nonneg _
  have hTe : (((1 : ℝ) / 2) • (covMat W A F₁ F₂ + covMat W A' F₁ F₂)).trace =
      ∑ i, (1 / 2) * (covMat W A F₁ F₂ i i + covMat W A' F₁ F₂ i i) := by
    simp [Matrix.trace, Matrix.diag]
  have hT1 : (((1 : ℝ) / 2) • (covMat W A F₁ F₂ + covMat W A' F₁ F₂)).trace ≤
      (mF : ℝ) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) := by
    rw [hTe]
    calc ∑ i, (1 / 2) * (covMat W A F₁ F₂ i i + covMat W A' F₁ F₂ i i)
        ≤ ∑ _i : Fin mF, 2 * (Kb F₁ F₂ A + Kb F₁ F₂ A') := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := covDiag_le hn hN W A F₁ F₂ i
          have h2 := covDiag_le hn hN W A' F₁ F₂ i
          linarith
      _ = (mF : ℝ) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) := by simp
  have hT0 : 0 ≤ (((1 : ℝ) / 2) • (covMat W A F₁ F₂ + covMat W A' F₁ F₂)).trace := by
    rw [hTe]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 := covDiag_nonneg W A F₁ F₂ i
    have h2 := covDiag_nonneg W A' F₁ F₂ i
    positivity
  have hb : ∀ s : ℝ, 0 ≤ s → s ≤ (mF : ℝ) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) →
      2 / (mF : ℝ) * s ≤ 4 * (Kb F₁ F₂ A + Kb F₁ F₂ A') := by
    intro s _ hs
    calc 2 / (mF : ℝ) * s ≤ 2 / (mF : ℝ) * ((mF : ℝ) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A'))) :=
          mul_le_mul_of_nonneg_left hs hα0
      _ = (2 / (mF : ℝ) * (mF : ℝ)) * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) := by ring
      _ ≤ 2 * (2 * (Kb F₁ F₂ A + Kb F₁ F₂ A')) :=
          mul_le_mul_of_nonneg_right hαm (by positivity)
      _ = 4 * (Kb F₁ F₂ A + Kb F₁ F₂ A') := by ring
  unfold Jn Dn Tn
  have h1 := hb _ hD0 hD1
  have h2 := hb _ hT0 hT1
  have h3 : 0 ≤ 2 / (mF : ℝ) * normSq (aVec W A F₁ F₂ - aVec W A' F₁ F₂) :=
    mul_nonneg hα0 hD0
  have h4 : 0 ≤ 2 / (mF : ℝ) * (((1 : ℝ) / 2) • (covMat W A F₁ F₂ + covMat W A' F₁ F₂)).trace :=
    mul_nonneg hα0 hT0
  rw [abs_le]
  constructor <;> linarith

/-! ## Integrability of the bound -/

lemma frob_sq_integrable (a b : ℕ) (v : ℝ) :
    Integrable (fun M : Matrix (Fin a) (Fin b) ℝ => frob M ^ 2) (gaussMat a b v) := by
  unfold gaussMat
  have hc : Continuous (fun M : Matrix (Fin a) (Fin b) ℝ => frob M ^ 2) := continuous_frob.pow 2
  rw [integrable_map_measure hc.measurable.aestronglyMeasurable
    (measurable_ofFlat _).aemeasurable]
  have e : ((fun M : Matrix (Fin a) (Fin b) ℝ => frob M ^ 2) ∘
      fun ξ : Fin a × Fin b → ℝ => Matrix.of fun i j => √v * ξ (i, j)) =
      fun ξ => (√v ^ 2) ^ 2 * (∑ p, ξ p ^ 2) ^ 2 := by
    funext ξ
    simp only [Function.comp, frob, of_apply, mul_pow]
    rw [← mul_pow, Fintype.sum_prod_type, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [e]
  have h4 : Integrable (fun x : ℝ => (x ^ 2) ^ 2) (gaussianReal 0 1) := by
    simpa [← pow_mul] using integrable_pow_gauss 4
  exact (pi_sum_sq_integrable (f := fun x : ℝ => x ^ 2) (integrable_pow_gauss 2) h4).const_mul _

lemma frobA_integrable : Integrable (frobA (n := n) (mA := mA)) (mlpGauss n mA n) := by
  unfold mlpGauss
  exact (frob_sq_integrable _ _ _).mul_prod
    ((frob_sq_integrable _ _ _).mul_prod (frob_sq_integrable _ _ _))

/-- `J` has a finite second moment under the distribution of the four networks. -/
theorem memLp_Jall (hn : 1 ≤ n) (hN : 1 ≤ N) :
    MemLp (Jall (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) 2 (lawAll N mW n mA mF) := by
  rw [memLp_two_iff_integrable_sq (measurable_Jall hN).aestronglyMeasurable]
  -- the bound `32·(K_A² + K_{A′}²)`
  have hF : Integrable (fun F : MlpParam n mF 1 => frob F.1 ^ 2 * frob F.2.1 ^ 2)
      (mlpGauss n mF 1) := by
    unfold mlpGauss
    exact (frob_sq_integrable _ _ _).mul_prod ((frob_sq_integrable _ _ _).comp_fst _)
  have hWF : Integrable (fun x : MlpParam N mW n × MlpParam n mF 1 =>
      frob x.2.1 ^ 2 * frob x.2.2.1 ^ 2) (lawWF N mW n mF) := by
    unfold lawWF
    exact hF.comp_snd _
  have hA1 : Integrable (fun q : MlpParam n mA n × MlpParam n mA n => frobA q.1)
      ((mlpGauss n mA n).prod (mlpGauss n mA n)) := frobA_integrable.comp_fst _
  have hA2 : Integrable (fun q : MlpParam n mA n × MlpParam n mA n => frobA q.2)
      ((mlpGauss n mA n).prod (mlpGauss n mA n)) := frobA_integrable.comp_snd _
  have hb1 : Integrable (fun t : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n ×
      MlpParam n mA n => frob t.1.2.1 ^ 2 * frob t.1.2.2.1 ^ 2 * frobA t.2.1)
      (lawAll N mW n mA mF) := by
    unfold lawAll
    exact hWF.mul_prod hA1
  have hb2 : Integrable (fun t : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n ×
      MlpParam n mA n => frob t.1.2.1 ^ 2 * frob t.1.2.2.1 ^ 2 * frobA t.2.2)
      (lawAll N mW n mA mF) := by
    unfold lawAll
    exact hWF.mul_prod hA2
  refine Integrable.mono' ((hb1.add hb2).const_mul 32)
    ((measurable_Jall hN).pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have h := abs_Jn_le hn hN t.1.1 t.2.1 t.2.2 t.1.2.1 t.1.2.2.1
  have hK := Kb_nonneg t.1.2.1 t.1.2.2.1 t.2.1
  have hK' := Kb_nonneg t.1.2.1 t.1.2.2.1 t.2.2
  have e1 := Kb_sq t.1.2.1 t.1.2.2.1 t.2.1
  have e2 := Kb_sq t.1.2.1 t.1.2.2.1 t.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  rw [← e1, ← e2]
  have h5 : Jall t ^ 2 ≤ (4 * (Kb t.1.2.1 t.1.2.2.1 t.2.1 + Kb t.1.2.1 t.1.2.2.1 t.2.2)) ^ 2 := by
    rw [← sq_abs (Jall t)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (Kb t.1.2.1 t.1.2.2.1 t.2.1 - Kb t.1.2.1 t.1.2.2.1 t.2.2)]

end BstLean.Part131

open BstLean.Part131 in
#print axioms memLp_Jall
