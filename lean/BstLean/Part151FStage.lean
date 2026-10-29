import BstLean.Part151Struct
import BstLean.Part149LemmaC

/-!
# Part 151, item 4 (c): Lemma TR in its mean form, and the bridge to the last row

Role: `delegations/statements/p151-spec.md`, item 4 (c). Paper source:
`proofs/option-n/theorem5-08-F-rows.tex`, Lemma TR.

`θ = (F₁, F₂)` are the hidden matrices of `F` (`HidParam n m`), `z_F(y) = hid2 F₁ F₂ y`,
`t_F = 2/m`.

* `gauss_sq_lintegral`, `row_sq_lintegral`: `E_{f₃}(f₃·Δ)² = t_F·|Δ|²` (the bridge: a second
  moment of `F(·)` over the whole of `F` is the mean over `(F₁, F₂)` of `t_F·|feature vector|²`).
* `hid2_lip`: `|z_F(y) − z_F(y′)|² ≤ ‖F₂‖²_F·‖F₁‖²_F·|y − y′|²` (Frobenius norms).
* `dPair P X Y θ`: the vector `Δ_{y,y′} = E[z_F(X) − z_F(Y)]` for a coupling `(X, Y)` on a
  probability space `(Ω', P)` that does not depend on `F`.
* `pair_struct`: `E[F(X) − F(Y)] = f₃·Δ_{y,y′}`.
* **`lemmaTR_mean`**: `E_{F₁,F₂} t_F·|Δ_{y,y′}|² ≤ (2/n)·E|X − Y|²`. It is `lemmaC149`
  (Part 149) with the last row integrated out by the bridge.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part149 (lemmaC149 reluV_lip_sq)

/-! ## The bridge -/

/-- `∫ x² dN(0, V) = V`, as a lower integral. -/
lemma gauss_sq_lintegral (V : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂gaussianReal 0 V = ENNReal.ofReal V := by
  have hv : Var[id; gaussianReal 0 V] = V := variance_id_gaussianReal
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  simp only [id, integral_id_gaussianReal, sub_zero] at hv
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 V) :=
    (memLp_id_gaussianReal (μ := 0) (v := V) 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => sq_nonneg x),
    hv]

/-- **The bridge**: for a one-row matrix `M` with independent `N(0, v)` entries,
`E (M·Δ)² = v·|Δ|²`. -/
theorem row_sq_lintegral {m : ℕ} {v : ℝ} (hv : 0 ≤ v) (Δ : Fin m → ℝ) :
    ∫⁻ M, ENNReal.ofReal ((rowOf 0 M ⬝ᵥ Δ) ^ 2) ∂gaussMat 1 m v =
      ENNReal.ofReal (v * normSq Δ) := by
  have hm : Measurable (fun M : Matrix (Fin 1) (Fin m) ℝ => rowOf 0 M ⬝ᵥ Δ) := by
    simp only [dotProduct, rowOf]
    fun_prop
  have h := lintegral_map (μ := gaussMat 1 m v) (f := fun x : ℝ => ENNReal.ofReal (x ^ 2))
    (g := fun M : Matrix (Fin 1) (Fin m) ℝ => rowOf 0 M ⬝ᵥ Δ) (by fun_prop) hm
  rw [← h, row_gauss hv, gauss_sq_lintegral]
  have hns : 0 ≤ normSq Δ := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.coe_toNNReal _ (mul_nonneg hv hns)]

/-! ## The feature map is Lipschitz -/

lemma normSq_reluV_sub_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (reluV a - reluV b) ≤ normSq (a - b) := by
  have h := reluV_lip_sq a b
  have h0 : 0 ≤ normSq (reluV (-a) - reluV (-b)) := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- `|z_F(y) − z_F(y′)|² ≤ ‖F₂‖²_F·(‖F₁‖²_F·|y − y′|²)` (squared Frobenius norms `frob`). -/
theorem hid2_lip {k m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y y' : Fin k → ℝ) :
    normSq (hid2 M₁ M₂ y - hid2 M₁ M₂ y') ≤ frob M₂ * (frob M₁ * normSq (y - y')) := by
  unfold hid2
  calc normSq (reluV (M₂ *ᵥ reluV (M₁ *ᵥ y)) - reluV (M₂ *ᵥ reluV (M₁ *ᵥ y')))
      ≤ normSq (M₂ *ᵥ reluV (M₁ *ᵥ y) - M₂ *ᵥ reluV (M₁ *ᵥ y')) := normSq_reluV_sub_le _ _
    _ = normSq (M₂ *ᵥ (reluV (M₁ *ᵥ y) - reluV (M₁ *ᵥ y'))) := by rw [Matrix.mulVec_sub]
    _ ≤ frob M₂ * normSq (reluV (M₁ *ᵥ y) - reluV (M₁ *ᵥ y')) := normSq_mulVec_le _ _
    _ ≤ frob M₂ * (frob M₁ * normSq (y - y')) := by
        refine mul_le_mul_of_nonneg_left ?_ (frob_nonneg _)
        calc normSq (reluV (M₁ *ᵥ y) - reluV (M₁ *ᵥ y'))
            ≤ normSq (M₁ *ᵥ y - M₁ *ᵥ y') := normSq_reluV_sub_le _ _
          _ = normSq (M₁ *ᵥ (y - y')) := by rw [Matrix.mulVec_sub]
          _ ≤ frob M₁ * normSq (y - y') := normSq_mulVec_le _ _

/-! ## Lemma TR, mean form -/

section TR

variable {Ω' : Type*} [MeasurableSpace Ω'] {n m : ℕ}

/-- `Δ_{y,y′} = E[z_F(X) − z_F(Y)]`: the difference of the feature means for a coupling
`(X, Y)` of two input distributions, on a probability space `(Ω', P)`. -/
noncomputable def dPair (P : Measure Ω') (X Y : Ω' → Fin n → ℝ) (θ : HidParam n m) :
    Fin m → ℝ :=
  fun i => ∫ ω, (hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i) ∂P

lemma hid2_pair_integrable (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) (θ : HidParam n m) (i : Fin m) :
    Integrable (fun ω => hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i) P := by
  have hc : Continuous (fun y : Fin n → ℝ => hid2 θ.1 θ.2 y i) :=
    (continuous_apply i).comp (continuous_hid2_joint.comp (continuous_const.prodMk continuous_id))
  have hmeas : Measurable (fun ω => hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i) :=
    (hc.measurable.comp hX).sub (hc.measurable.comp hY)
  set C : ℝ := frob θ.2 * frob θ.1 with hC
  have hC0 : 0 ≤ C := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  have hdom : Integrable (fun ω => (1 + C * normSq (X ω - Y ω)) / 2) P :=
    ((integrable_const 1).add (hXY.const_mul C)).div_const 2
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hid2_lip θ.1 θ.2 (X ω) (Y ω)
  have h2 : (hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i) ^ 2 ≤
      normSq (hid2 θ.1 θ.2 (X ω) - hid2 θ.1 θ.2 (Y ω)) := by
    unfold normSq
    exact Finset.single_le_sum (f := fun j => (hid2 θ.1 θ.2 (X ω) - hid2 θ.1 θ.2 (Y ω)) j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : (hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i) ^ 2 ≤ C * normSq (X ω - Y ω) := by
    rw [hC, mul_assoc]; exact h2.trans h1
  have h4 : |hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i| ^ 2 =
      (hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|hid2 θ.1 θ.2 (X ω) i - hid2 θ.1 θ.2 (Y ω) i| - 1)]

/-- `E[F(X) − F(Y)] = f₃·Δ_{y,y′}`. -/
theorem pair_struct (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) (F : MlpParam n m 1) :
    ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P =
      rowOf 0 F.2.2 ⬝ᵥ dPair P X Y (F.1, F.2.1) := by
  obtain ⟨F₁, F₂, F₃⟩ := F
  have e : ∀ ω, mlpEval (F₁, F₂, F₃) (X ω) 0 - mlpEval (F₁, F₂, F₃) (Y ω) 0 =
      ∑ l, F₃ 0 l * (hid2 F₁ F₂ (X ω) l - hid2 F₁ F₂ (Y ω) l) := by
    intro ω
    have e1 : ∀ y : Fin n → ℝ, mlpEval (F₁, F₂, F₃) y 0 = ∑ l, F₃ 0 l * hid2 F₁ F₂ y l :=
      fun y => rfl
    rw [e1, e1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun l _ =>
    (hid2_pair_integrable P hX hY hXY (F₁, F₂) l).const_mul _]
  simp_rw [integral_const_mul]
  rfl

lemma measurable_dPair (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (i : Fin m) :
    Measurable (fun θ : HidParam n m => dPair P X Y θ i) := by
  unfold dPair
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : HidParam n m × Ω' => hid2 q.1.1 q.1.2 (X q.2) i - hid2 q.1.1 q.1.2 (Y q.2) i) ?_
  refine Measurable.stronglyMeasurable ?_
  have hj := ((continuous_apply i).comp (continuous_hid2_joint (N := n) (m := m))).measurable
  exact (hj.comp (measurable_fst.prodMk (hX.comp measurable_snd))).sub
    (hj.comp (measurable_fst.prodMk (hY.comp measurable_snd)))

/-- **Lemma TR, mean form** (the bias against the coupling cost). For a coupling `(X, Y)` that
does not depend on `F`, with `E|X − Y|² < ∞`, and `n, m ≥ 1`:
`E_{F₁,F₂} t_F·|E[z_F(X) − z_F(Y)]|² ≤ (2/n)·E|X − Y|²`, `t_F = 2/m`. -/
theorem lemmaTR_mean (P : Measure Ω') [IsProbabilityMeasure P] (hn : 1 ≤ n) (hm : 1 ≤ m)
    {X Y : Ω' → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) :
    ∫⁻ θ, ENNReal.ofReal (2 / (m : ℝ) * normSq (dPair P X Y θ)) ∂hidGauss n m ≤
      ENNReal.ofReal (2 / (n : ℝ) * ∫ ω, normSq (X ω - Y ω) ∂P) := by
  obtain ⟨hint, hle⟩ := lemmaC149 P hn hm hX hY hXY
  have hv : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  -- the last row is integrated first
  have e1 : ∀ θ : HidParam n m, ENNReal.ofReal (2 / (m : ℝ) * normSq (dPair P X Y θ)) =
      ∫⁻ w, ENNReal.ofReal ((rowOf 0 w ⬝ᵥ dPair P X Y θ) ^ 2) ∂gaussMat 1 m (2 / (m : ℝ)) :=
    fun θ => (row_sq_lintegral hv _).symm
  simp_rw [e1]
  have hmeas : Measurable (fun q : HidParam n m × Matrix (Fin 1) (Fin m) ℝ =>
      ENNReal.ofReal ((rowOf 0 q.2 ⬝ᵥ dPair P X Y q.1) ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ 2)
    simp only [dotProduct, rowOf]
    refine Finset.measurable_sum _ fun i _ => Measurable.mul (by fun_prop) ?_
    exact (measurable_dPair P hX hY i).comp measurable_fst
  rw [← lintegral_prod _ hmeas.aemeasurable]
  -- back to the distribution of `F`
  have hmap : (mlpGauss n m 1).map
      (fun F : MlpParam n m 1 => (((F.1, F.2.1) : HidParam n m), F.2.2)) =
      (hidGauss n m).prod (gaussMat 1 m (2 / (m : ℝ))) := by
    unfold mlpGauss hidGauss
    exact assoc_symm_map _ _ _
  rw [← hmap, lintegral_map hmeas (by fun_prop)]
  have e2 : ∀ F : MlpParam n m 1,
      ENNReal.ofReal ((rowOf 0 F.2.2 ⬝ᵥ dPair P X Y (F.1, F.2.1)) ^ 2) =
        ENNReal.ofReal ((∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) ^ 2) := by
    intro F
    rw [pair_struct P hX hY hXY F]
  simp_rw [e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun F => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

end TR

end BstLean.Part151
