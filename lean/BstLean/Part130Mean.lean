import BstLean.Part130Sym

/-!
# Part 130, item 4: the input distribution `μ_W`, the mean of `B` over `F`, and the mean of the
second moment

* `normSq_sphPt`: `sphPt y` is a unit vector (for `n ≥ 1`); `muWn_normSq`: `x` is a unit vector,
  `μ_W`-almost surely; `muWn_isProbability`.
* `phiN_integrable`: `x ↦ F(A(x))` and its square are integrable under `μ_W`.
* `Bn_integrable`, `Bn_mean_zero`: `E_F B(W, A, F) = 0` for every fixed `(W, A)`.
* `phiN_second_moment`: `E_A E_F E_u F(A(x))² = 4/n` for every fixed `W`.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (sphProj measurable_sphProj)

variable {n N m mA' mF' : ℕ}

/-! ## The point `x` -/

lemma normSq_e0 (hn : 1 ≤ n) : normSq (e0 n) = 1 := by
  unfold normSq e0
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp
  · intro b _ hb
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [this]
  · simp

lemma normSq_sphProj (y : Fin n → ℝ) (hy : normSq y ≠ 0) : normSq (sphProj y) = 1 := by
  have hpos : 0 < normSq y := lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy)
  unfold sphProj
  rw [normSq_smul]
  change (1 / Real.sqrt (normSq y)) ^ 2 * normSq y = 1
  rw [div_pow, Real.sq_sqrt hpos.le]
  field_simp

/-- `sphPt y` is on the unit sphere, for every `y` (also `y = 0`). -/
theorem normSq_sphPt (hn : 1 ≤ n) (y : Fin n → ℝ) : normSq (sphPt y) = 1 := by
  unfold sphPt
  split_ifs with h
  · exact normSq_e0 hn
  · exact normSq_sphProj y h

/-- `sphPt y = y/|y|` for `y ≠ 0`. -/
theorem sphPt_of_ne (y : Fin n → ℝ) (hy : normSq y ≠ 0) : sphPt y = sphProj y := by
  unfold sphPt; simp only [hy, ↓reduceIte]

lemma measurable_sphPt : Measurable (sphPt (n := n)) := by
  unfold sphPt
  exact Measurable.ite (measurable_normSq (measurableSet_singleton 0)) measurable_const
    measurable_sphProj

lemma measurable_sphPt_mlpEval (W : MlpParam N m n) :
    Measurable (fun u => sphPt (mlpEval W u)) :=
  measurable_sphPt.comp (continuous_mlpEval W).measurable

/-- `μ_W` is a probability measure (for `N ≥ 1`). -/
theorem muWn_isProbability (hN : 1 ≤ N) (W : MlpParam N m n) : IsProbabilityMeasure (muWn W) := by
  have := uniformSphere_isProbability N hN
  exact (Measure.isProbabilityMeasure_map_iff (measurable_sphPt_mlpEval W).aemeasurable).2 this

/-- `x` is a unit vector, `μ_W`-almost surely. -/
theorem muWn_normSq (hn : 1 ≤ n) (W : MlpParam N m n) : ∀ᵐ x ∂muWn W, normSq x = 1 := by
  unfold muWn
  have hs : MeasurableSet {x : Fin n → ℝ | normSq x = 1} :=
    measurable_normSq (measurableSet_singleton 1)
  exact (ae_map_iff (measurable_sphPt_mlpEval W).aemeasurable hs).mpr
    (Filter.Eventually.of_forall fun u => normSq_sphPt hn _)

lemma isCompact_unit : IsCompact {x : Fin n → ℝ | normSq x = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq continuous_normSq continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : x i ^ 2 ≤ normSq x :=
      Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hx : normSq x = 1 := hx
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

/-- A continuous function is integrable under `μ_W`. -/
lemma muWn_integrable_of_continuous (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N m n)
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) : Integrable g (muWn W) := by
  have := muWn_isProbability hN W
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hg.measurable.aestronglyMeasurable C ?_
  filter_upwards [muWn_normSq hn W] with x hx using hC x hx

/-! ## `F(A(x))` -/

lemma continuous_phiN_joint (A : MlpParam n mA' n) :
    Continuous (fun p : (Fin n → ℝ) × MlpParam n mF' 1 => phiN A p.2 p.1) := by
  unfold phiN
  exact (continuous_apply 0).comp (continuous_mlpEval_joint.comp
    (continuous_snd.prodMk ((continuous_mlpEval A).comp continuous_fst)))

lemma continuous_phiN (A : MlpParam n mA' n) (F : MlpParam n mF' 1) : Continuous (phiN A F) :=
  (continuous_phiN_joint A).comp (continuous_id.prodMk continuous_const)

/-- `x ↦ F(A(x))` is integrable under `μ_W`. -/
theorem phiN_integrable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N m n) (A : MlpParam n mA' n)
    (F : MlpParam n mF' 1) : Integrable (phiN A F) (muWn W) :=
  muWn_integrable_of_continuous hn hN W (continuous_phiN A F)

/-- `x ↦ F(A(x))²` is integrable under `μ_W`. -/
theorem phiN_sq_integrable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N m n) (A : MlpParam n mA' n)
    (F : MlpParam n mF' 1) : Integrable (fun x => phiN A F x ^ 2) (muWn W) :=
  muWn_integrable_of_continuous hn hN W ((continuous_phiN A F).pow 2)

lemma F_sq_integrable (y : Fin n → ℝ) :
    Integrable (fun F : MlpParam n mF' 1 => (mlpEval F y 0) ^ 2) (mlpGauss n mF' 1) := by
  have h := mlp_normSq_integrable (m := mF') (q := 1) y
  simpa [normSq] using h

/-- `(x, F) ↦ F(A(x))²` is integrable under `μ_W ⊗ (distribution of F)`, with the inner mean. -/
lemma phiN_sq_prod (hn : 1 ≤ n) (hN : 1 ≤ N) (hF : 1 ≤ mF') (W : MlpParam N m n)
    (A : MlpParam n mA' n) :
    Integrable (fun p : (Fin n → ℝ) × MlpParam n mF' 1 => phiN A p.2 p.1 ^ 2)
      ((muWn W).prod (mlpGauss n mF' 1)) ∧
    ∫ p, phiN A p.2 p.1 ^ 2 ∂((muWn W).prod (mlpGauss n mF' 1)) =
      ∫ x, 2 * normSq (mlpEval A x) / n ∂muWn W := by
  have := muWn_isProbability hN W
  have h1 : ∀ x : Fin n → ℝ,
      Integrable (fun F : MlpParam n mF' 1 => phiN A F x ^ 2) (mlpGauss n mF' 1) ∧
      ∫ F, phiN A F x ^ 2 ∂mlpGauss n mF' 1 = 2 * normSq (mlpEval A x) / n := by
    intro x
    exact ⟨F_sq_integrable (mlpEval A x), F_second_moment hF (mlpEval A x)⟩
  refine prod_step ((continuous_phiN_joint A).pow 2).measurable (fun p => sq_nonneg _)
    (fun x => 2 * normSq (mlpEval A x) / n) h1 ?_
  exact muWn_integrable_of_continuous hn hN W
    ((continuous_const.mul (continuous_normSq.comp (continuous_mlpEval A))).div_const _)

/-- `(x, F) ↦ F(A(x))` is integrable under `μ_W ⊗ (distribution of F)`. -/
lemma phiN_prod_integrable (hn : 1 ≤ n) (hN : 1 ≤ N) (hF : 1 ≤ mF') (W : MlpParam N m n)
    (A : MlpParam n mA' n) :
    Integrable (fun p : (Fin n → ℝ) × MlpParam n mF' 1 => phiN A p.2 p.1)
      ((muWn W).prod (mlpGauss n mF' 1)) := by
  have := muWn_isProbability hN W
  have h2 := (phiN_sq_prod hn hN hF W A).1
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h2)
    (continuous_phiN_joint A).measurable.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (phiN A p.2 p.1 - 1), sq_nonneg (phiN A p.2 p.1 + 1)]

/-! ## The mean of `B` over `F` -/

/-- `F ↦ B(W, A, F)` is integrable under the random MLP distribution of `F`. -/
theorem Bn_integrable (hn : 1 ≤ n) (hN : 1 ≤ N) (hF : 1 ≤ mF') (W : MlpParam N m n)
    (A : MlpParam n mA' n) :
    Integrable (fun F : MlpParam n mF' 1 => Bn W A F) (mlpGauss n mF' 1) := by
  have := muWn_isProbability hN W
  exact (phiN_prod_integrable hn hN hF W A).integral_prod_right

lemma phiN_neg_last (A : MlpParam n mA' n) (F : MlpParam n mF' 1) (x : Fin n → ℝ) :
    phiN A (F.1, F.2.1, -F.2.2) x = -phiN A F x := by
  simp only [phiN, mlpEval, mlp2, Matrix.neg_mulVec, Pi.neg_apply]

/-- **Zero mean**: `E_F B(W, A, F) = 0` for every fixed `(W, A)` (the last matrix of `F` is
centred). -/
theorem Bn_mean_zero (hn : 1 ≤ n) (hN : 1 ≤ N) (hF : 1 ≤ mF') (W : MlpParam N m n)
    (A : MlpParam n mA' n) :
    ∫ F, Bn W A F ∂mlpGauss n mF' 1 = 0 := by
  have hint := Bn_integrable hn hN hF W A
  have hneg : ∀ F : MlpParam n mF' 1, Bn W A (F.1, F.2.1, -F.2.2) = -Bn W A F := by
    intro F
    unfold Bn
    simp_rw [phiN_neg_last]
    rw [integral_neg]
  have hmeas : Measurable (fun θ : MlpParam n mF' 1 => (θ.1, θ.2.1, -θ.2.2)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd).neg)
  have h1 : ∫ F, Bn W A F ∂mlpGauss n mF' 1 =
      ∫ F, Bn W A (F.1, F.2.1, -F.2.2) ∂mlpGauss n mF' 1 := by
    conv_lhs => rw [← mlpGauss_neg_last (k := n) (m := mF') (q := 1)]
    rw [integral_map hmeas.aemeasurable]
    rw [mlpGauss_neg_last]
    exact hint.aestronglyMeasurable
  simp_rw [hneg] at h1
  rw [integral_neg] at h1
  linarith

/-! ## The mean of the second moment -/

/-- For a fixed `A`: `E_F E_u F(A(x))² = (2/n)·E_u |A(x)|²`. -/
theorem phiN_sq_mean_F (hn : 1 ≤ n) (hN : 1 ≤ N) (hF : 1 ≤ mF') (W : MlpParam N m n)
    (A : MlpParam n mA' n) :
    ∫ F, ∫ x, phiN A F x ^ 2 ∂muWn W ∂mlpGauss n mF' 1 =
      ∫ x, 2 * normSq (mlpEval A x) / n ∂muWn W := by
  have := muWn_isProbability hN W
  have h := phiN_sq_prod hn hN hF W A
  rw [← h.2, integral_prod _ h.1]
  exact (integral_integral_swap (f := fun x (F : MlpParam n mF' 1) => phiN A F x ^ 2) h.1).symm

/-- **The mean of the second moment**: `E_A E_F E_u F(A(x))² = 4/n`, for every fixed `W`
(the scale `S = 4/n` of the paper). -/
theorem phiN_second_moment (hn : 1 ≤ n) (hN : 1 ≤ N) (hA : 1 ≤ mA') (hF : 1 ≤ mF')
    (W : MlpParam N m n) :
    ∫ A, ∫ F, ∫ x, phiN A F x ^ 2 ∂muWn W ∂mlpGauss n mF' 1 ∂mlpGauss n mA' n = 4 / n := by
  have := muWn_isProbability hN W
  simp_rw [phiN_sq_mean_F hn hN hF W]
  have hcont : Continuous (fun p : (Fin n → ℝ) × MlpParam n mA' n =>
      2 * normSq (mlpEval p.2 p.1) / n) :=
    (continuous_const.mul (continuous_normSq.comp
      (continuous_mlpEval_joint.comp (continuous_snd.prodMk continuous_fst)))).div_const _
  have h1 : ∀ x : Fin n → ℝ,
      Integrable (fun A : MlpParam n mA' n => 2 * normSq (mlpEval A x) / n) (mlpGauss n mA' n) ∧
      ∫ A, 2 * normSq (mlpEval A x) / n ∂mlpGauss n mA' n = 4 * normSq x / n := by
    intro x
    refine ⟨((mlp_normSq_integrable x).const_mul 2).div_const _, ?_⟩
    rw [integral_div, integral_const_mul, agent_second_moment hn hA]
    ring
  have hstep := prod_step (μ := muWn W) (ν := mlpGauss n mA' n) hcont.measurable
    (fun p => div_nonneg (mul_nonneg zero_le_two (normSq_nonneg _)) (Nat.cast_nonneg n)) (fun x => 4 * normSq x / n) h1
    (muWn_integrable_of_continuous hn hN W ((continuous_const.mul continuous_normSq).div_const _))
  rw [← integral_integral_swap (f := fun x (A : MlpParam n mA' n) =>
    2 * normSq (mlpEval A x) / n) hstep.1]
  have h2 : ∀ᵐ x ∂muWn W, ∫ A, 2 * normSq (mlpEval A x) / n ∂mlpGauss n mA' n = 4 / n := by
    filter_upwards [muWn_normSq hn W] with x hx
    rw [(h1 x).2, hx, mul_one]
  rw [integral_congr_ae h2, integral_const]
  simp

end BstLean.Part130

open BstLean.Part130 in
#print axioms phiN_second_moment

open BstLean.Part130 in
#print axioms muWn_normSq
open BstLean.Part130 in
#print axioms Bn_integrable
open BstLean.Part130 in
#print axioms Bn_mean_zero
