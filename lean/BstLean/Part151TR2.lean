import BstLean.Part151TR
import BstLean.Part151FStage

/-!
# Part 151, Lemma TR with its charges

Role: `delegations/statements/p151-spec.md`, item 4 (c). Paper source:
`proofs/option-n/theorem5-08-F-rows.tex`, Lemma TR.

Setting: a probability space `(Ω', P)`, a coupling `X, Y : Ω' → ℝⁿ` (measurable, with
`E|X − Y|² < ∞`) that does not depend on `F`; `D = E|X − Y|²`; `F₁ ∼ gaussMat m n (2/n)`,
`F₂ ∼ gaussMat m m (2/m)` independent (`hidGauss n m`); `t_F = 2/m`.

* `hidA F₁ X ω = ReLU(F₁·X(ω))`; `Tfun P X Y F₁ = E|ReLU(F₁X) − ReLU(F₁Y)|²` (the `T` of the
  paper); `Yf P X Y w = E(ReLU(w·X) − ReLU(w·Y))²` (the `Y_i` of the paper at the row `w`).
* `dPair_sq`: `|Δ_{y,y′}|² = Σ_j X_j`, `X_j = XR P h h′ (row j of F₂)`.
* **`lemmaTR_T2`** (the event `E_{T2}`): for fixed `F₁`,
  `Pr_{F₂}(t_F|Δ|² > (1 + δ)·t_F·T) ≤ (432/m²)(1 + 63/m)/δ⁴`.
* **`lemmaTR_T1`** (the event `E_{T1}`):
  `Pr_{F₁}(t_F·T > (1 + δ′)(2/n)·D) ≤ (432/m²)(1 + 63/m)/δ′⁴`.
* **`lemmaTR`**: `Pr_{F₁,F₂}(t_F|Δ|² > (1 + δ)(1 + δ′)(2/n)·D)
  ≤ (432/m²)(1 + 63/m)(1/δ⁴ + 1/δ′⁴)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)

section TRc

variable {Ω' : Type*} [MeasurableSpace Ω'] {n m : ℕ}

/-- The first hidden vector of `F` at the input `X(ω)`: `ReLU(F₁·X(ω))`. -/
noncomputable def hidA (F₁ : Matrix (Fin m) (Fin n) ℝ) (X : Ω' → Fin n → ℝ) (ω : Ω') :
    Fin m → ℝ :=
  reluV (F₁ *ᵥ X ω)

lemma measurable_hidA (F₁ : Matrix (Fin m) (Fin n) ℝ) {X : Ω' → Fin n → ℝ} (hX : Measurable X) :
    Measurable (hidA F₁ X) :=
  (continuous_reluV.comp
    (Continuous.matrix_mulVec continuous_const continuous_id)).measurable.comp hX

omit [MeasurableSpace Ω'] in
lemma hidA_sub_le (F₁ : Matrix (Fin m) (Fin n) ℝ) (X Y : Ω' → Fin n → ℝ) (ω : Ω') :
    normSq (hidA F₁ X ω - hidA F₁ Y ω) ≤ frob F₁ * normSq (X ω - Y ω) := by
  unfold hidA
  calc normSq (reluV (F₁ *ᵥ X ω) - reluV (F₁ *ᵥ Y ω))
      ≤ normSq (F₁ *ᵥ X ω - F₁ *ᵥ Y ω) := normSq_reluV_sub_le _ _
    _ = normSq (F₁ *ᵥ (X ω - Y ω)) := by rw [Matrix.mulVec_sub]
    _ ≤ frob F₁ * normSq (X ω - Y ω) := normSq_mulVec_le _ _

lemma hidA_int (P : Measure Ω') (F₁ : Matrix (Fin m) (Fin n) ℝ) {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) :
    Integrable (fun ω => normSq (hidA F₁ X ω - hidA F₁ Y ω)) P := by
  have hm : Measurable (fun ω => normSq (hidA F₁ X ω - hidA F₁ Y ω)) :=
    continuous_normSq.measurable.comp ((measurable_hidA F₁ hX).sub (measurable_hidA F₁ hY))
  refine (hXY.const_mul (frob F₁)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]
  exact hidA_sub_le F₁ X Y ω

/-- `T(F₁) = E|ReLU(F₁X) − ReLU(F₁Y)|²`. -/
noncomputable def Tfun (P : Measure Ω') (X Y : Ω' → Fin n → ℝ)
    (F₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  TR P (hidA F₁ X) (hidA F₁ Y)

lemma Tfun_nonneg (P : Measure Ω') (X Y : Ω' → Fin n → ℝ) (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ Tfun P X Y F₁ := TR_nonneg _ _ _

lemma Tfun_le (P : Measure Ω') (F₁ : Matrix (Fin m) (Fin n) ℝ) {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) :
    Tfun P X Y F₁ ≤ frob F₁ * ∫ ω, normSq (X ω - Y ω) ∂P := by
  unfold Tfun TR
  rw [← integral_const_mul]
  exact integral_mono (hidA_int P F₁ hX hY hXY) (hXY.const_mul _) (hidA_sub_le F₁ X Y)

/-- `|Δ_{y,y′}|² = Σ_j X_j`, with `X_j = XR P h h′ (row j of F₂)`. -/
lemma dPair_sq (P : Measure Ω') (X Y : Ω' → Fin n → ℝ) (F₁ : Matrix (Fin m) (Fin n) ℝ)
    (F₂ : Matrix (Fin m) (Fin m) ℝ) :
    normSq (dPair P X Y (F₁, F₂)) = ∑ j, XR P (hidA F₁ X) (hidA F₁ Y) (rowOf j F₂) := rfl

/-- `X(w) ≤ |w|²·T`. -/
lemma XR_le_T {d : ℕ} {P : Measure Ω'} [IsProbabilityMeasure P] {h h' : Ω' → Fin d → ℝ}
    (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) (w : Fin d → ℝ) :
    XR P h h' w ≤ normSq w * TR P h h' := by
  refine (lemmaR_iii_le hh hh' hT w).trans ?_
  unfold QR TR
  rw [← integral_const_mul]
  exact integral_mono (qint hh hh' hT w) (hT.const_mul _) fun ω => dot_sq_le _ _

/-- **Lemma TR, the event `E_{T2}`.** Fix `F₁`; integrate `F₂`. For `δ > 0`, `m ≥ 1`:
`Pr_{F₂}(t_F·|Δ_{y,y′}|² > (1 + δ)·t_F·T(F₁)) ≤ (432/m²)(1 + 63/m)/δ⁴`. -/
theorem lemmaTR_T2 (P : Measure Ω') [IsProbabilityMeasure P] (hm : 1 ≤ m)
    {X Y : Ω' → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) (F₁ : Matrix (Fin m) (Fin n) ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (gaussMat m m (2 / (m : ℝ))).real
        {F₂ | (1 + δ) * (2 / (m : ℝ) * Tfun P X Y F₁) <
          2 / (m : ℝ) * normSq (dPair P X Y (F₁, F₂))} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ ^ 4 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set h := hidA F₁ X with hh_def
  set h' := hidA F₁ Y with hh'_def
  have hh : Measurable h := measurable_hidA F₁ hX
  have hh' : Measurable h' := measurable_hidA F₁ hY
  have hT : Integrable (fun ω => normSq (h ω - h' ω)) P := hidA_int P F₁ hX hY hXY
  have hTdef : Tfun P X Y F₁ = TR P h h' := rfl
  set T := TR P h h' with hTT
  have hT0 : 0 ≤ T := TR_nonneg _ _ _
  have hrhs : 0 ≤ 432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ ^ 4 := by positivity
  rw [hTdef]
  rcases hT0.eq_or_lt with hz | hpos
  · -- `T = 0`: the event is empty
    have hempty : {F₂ : Matrix (Fin m) (Fin m) ℝ | (1 + δ) * (2 / (m : ℝ) * T) <
        2 / (m : ℝ) * normSq (dPair P X Y (F₁, F₂))} = ∅ := by
      ext F₂
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [dPair_sq, ← hz]
      have : ∑ j, XR P (hidA F₁ X) (hidA F₁ Y) (rowOf j F₂) ≤ 0 := by
        refine Finset.sum_nonpos fun j _ => ?_
        have := XR_le_T hh hh' hT (rowOf j F₂)
        rw [← hTT, ← hz, mul_zero] at this
        exact this
      nlinarith
    rw [hempty]
    simpa using hrhs
  set U : ℝ := T / m with hU
  have hU0 : 0 < U := by positivity
  have hv : (0 : ℝ) ≤ 2 / (m : ℝ) := ht.le
  have h1 := lemmaR_iii_mean hh hh' hT hv
  have h2 := lemmaR_iii_sq hh hh' hT hv
  have h4 := lemmaR_iii_four hh hh' hT hv
  rw [show 2 / (m : ℝ) / 2 * TR P h h' = U by rw [hU, hTT]; field_simp] at h1
  rw [show 3 * (2 / (m : ℝ)) ^ 2 * TR P h h' ^ 2 = 12 * U ^ 2 by rw [hU, hTT]; ring] at h2
  rw [show 105 * (2 / (m : ℝ)) ^ 4 * TR P h h' ^ 4 = 1680 * U ^ 4 by rw [hU, hTT]; ring] at h4
  have hrows := tail_rows (m := m) (XR_meas hh hh') (fun w => XR_nonneg P h h' w) hU0 h1 h2 h4
    hm hδ
  refine le_trans (measureReal_mono ?_) hrows
  intro F₂ hF₂
  simp only [mem_ofPred_eq] at hF₂ ⊢
  rw [dPair_sq] at hF₂
  have e : (m : ℝ) * U = T := by rw [hU]; field_simp
  rw [e]
  have h5 : 2 / (m : ℝ) * ((1 + δ) * T) <
      2 / (m : ℝ) * ∑ j, XR P (hidA F₁ X) (hidA F₁ Y) (rowOf j F₂) := by
    calc 2 / (m : ℝ) * ((1 + δ) * T) = (1 + δ) * (2 / (m : ℝ) * T) := by ring
      _ < _ := hF₂
  exact lt_of_mul_lt_mul_left h5 ht.le

/-! ## The event `E_{T1}` -/

/-- `Y(w) = E(ReLU(w·X) − ReLU(w·Y))²`: the term of `T` for a row `w` of `F₁`. -/
noncomputable def Yf (P : Measure Ω') (X Y : Ω' → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  ∫ ω, (relu (w ⬝ᵥ X ω) - relu (w ⬝ᵥ Y ω)) ^ 2 ∂P

lemma Yf_nonneg (P : Measure Ω') (X Y : Ω' → Fin n → ℝ) (w : Fin n → ℝ) : 0 ≤ Yf P X Y w :=
  integral_nonneg fun ω => sq_nonneg _

lemma Yf_meas (P : Measure Ω') [SFinite P] {X Y : Ω' → Fin n → ℝ} (hX : Measurable X)
    (hY : Measurable Y) : Measurable (Yf P X Y) := by
  unfold Yf
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : (Fin n → ℝ) × Ω' => (relu (q.1 ⬝ᵥ X q.2) - relu (q.1 ⬝ᵥ Y q.2)) ^ 2) ?_
  exact (((measurable_relu.comp (measurable_dot_joint hX)).sub
    (measurable_relu.comp (measurable_dot_joint hY))).pow_const 2).stronglyMeasurable

lemma Yf_le_QR (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) (w : Fin n → ℝ) :
    Yf P X Y w ≤ QR P X Y w :=
  integral_mono (rdiff_int hX hY hXY w) (qint hX hY hXY w) fun _ => relu_diff_sq_le _ _ _

/-- `T(F₁) = Σ_i Y(row i of F₁)`. -/
lemma Tfun_eq_sum (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    Tfun P X Y F₁ = ∑ i, Yf P X Y (rowOf i F₁) := by
  have e : ∀ ω, normSq (hidA F₁ X ω - hidA F₁ Y ω) =
      ∑ i, (relu (rowOf i F₁ ⬝ᵥ X ω) - relu (rowOf i F₁ ⬝ᵥ Y ω)) ^ 2 := fun _ => rfl
  unfold Tfun TR Yf
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => rdiff_int hX hY hXY (rowOf i F₁)]

/-- The mean of `Y` over a Gaussian row: `E Y(√v • ξ) ≤ (v/2)·D`. -/
lemma Yf_mean (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (Yf P X Y (√v • ξ)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (v / 2 * ∫ ω, normSq (X ω - Y ω) ∂P) := by
  have h1 : ∀ ξ : Fin n → ℝ, ENNReal.ofReal (Yf P X Y (√v • ξ)) =
      ∫⁻ ω, ENNReal.ofReal ((relu ((√v • ξ) ⬝ᵥ X ω) - relu ((√v • ξ) ⬝ᵥ Y ω)) ^ 2) ∂P := by
    intro ξ
    unfold Yf
    rw [← ofReal_integral_eq_lintegral_ofReal (rdiff_int hX hY hXY _)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  simp_rw [h1]
  have hmeas : Measurable (fun q : (Fin n → ℝ) × Ω' =>
      ENNReal.ofReal ((relu ((√v • q.1) ⬝ᵥ X q.2) - relu ((√v • q.1) ⬝ᵥ Y q.2)) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_relu.comp (measurable_sdot hX v)).sub
      (measurable_relu.comp (measurable_sdot hY v))).pow_const 2)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine (lintegral_mono fun ω => lemmaR_ii hv (X ω) (Y ω)).trans (le_of_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (hXY.const_mul _)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (by positivity) (normSq_nonneg _)),
    integral_const_mul]

/-- **Lemma TR, the event `E_{T1}`.** Integrate `F₁`. For `δ′ > 0`, `n, m ≥ 1`:
`Pr_{F₁}(t_F·T(F₁) > (1 + δ′)·(2/n)·D) ≤ (432/m²)(1 + 63/m)/δ′⁴`. -/
theorem lemmaTR_T1 (P : Measure Ω') [IsProbabilityMeasure P] (hn : 1 ≤ n) (hm : 1 ≤ m)
    {X Y : Ω' → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) {δ' : ℝ} (hδ' : 0 < δ') :
    (gaussMat m n (2 / (n : ℝ))).real
        {F₁ | (1 + δ') * (2 / (n : ℝ) * ∫ ω, normSq (X ω - Y ω) ∂P) <
          2 / (m : ℝ) * Tfun P X Y F₁} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ' ^ 4 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set D : ℝ := ∫ ω, normSq (X ω - Y ω) ∂P with hD
  have hD0 : 0 ≤ D := integral_nonneg fun ω => normSq_nonneg _
  have hrhs : 0 ≤ 432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ' ^ 4 := by positivity
  rcases hD0.eq_or_lt with hz | hpos
  · have hempty : {F₁ : Matrix (Fin m) (Fin n) ℝ | (1 + δ') * (2 / (n : ℝ) * D) <
        2 / (m : ℝ) * Tfun P X Y F₁} = ∅ := by
      ext F₁
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      have h1 := Tfun_le P F₁ hX hY hXY
      rw [← hD, ← hz, mul_zero] at h1
      rw [← hz]
      have : 2 / (m : ℝ) * Tfun P X Y F₁ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht.le h1
      simpa using this
    rw [hempty]
    simpa using hrhs
  set U : ℝ := D / n with hU
  have hU0 : 0 < U := by positivity
  have hv : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have hTXY : TR P X Y = D := rfl
  have mY : Measurable (Yf P X Y) := Yf_meas P hX hY
  have h1 : ∫⁻ ξ, ENNReal.ofReal (Yf P X Y (√(2 / (n : ℝ)) • ξ)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal U := by
    have h := Yf_mean P hX hY hXY hv
    rwa [show 2 / (n : ℝ) / 2 * ∫ ω, normSq (X ω - Y ω) ∂P = U by rw [hU, hD]; field_simp] at h
  have h2 : ∫⁻ ξ, ENNReal.ofReal (Yf P X Y (√(2 / (n : ℝ)) • ξ) ^ 2) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (12 * U ^ 2) := by
    have h := QR_sq hX hY hXY hv
    rw [hTXY, show 3 * (2 / (n : ℝ)) ^ 2 * D ^ 2 = 12 * U ^ 2 by rw [hU]; ring] at h
    refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_).trans h
    exact pow_le_pow_left₀ (Yf_nonneg _ _ _ _) (Yf_le_QR P hX hY hXY _) 2
  have h4 : ∫⁻ ξ, ENNReal.ofReal (Yf P X Y (√(2 / (n : ℝ)) • ξ) ^ 4) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (1680 * U ^ 4) := by
    have h := QR_four hX hY hXY hv
    rw [hTXY, show 105 * (2 / (n : ℝ)) ^ 4 * D ^ 4 = 1680 * U ^ 4 by rw [hU]; ring] at h
    refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_).trans h
    exact pow_le_pow_left₀ (Yf_nonneg _ _ _ _) (Yf_le_QR P hX hY hXY _) 4
  have hrows := tail_rows (m := m) mY (fun w => Yf_nonneg P X Y w) hU0 h1 h2 h4 hm hδ'
  refine le_trans (measureReal_mono ?_) hrows
  intro F₁ hF₁
  simp only [mem_ofPred_eq] at hF₁ ⊢
  rw [Tfun_eq_sum P hX hY hXY] at hF₁
  have e : (1 + δ') * (2 / (n : ℝ) * D) = 2 / (m : ℝ) * ((1 + δ') * ((m : ℝ) * U)) := by
    rw [hU]; field_simp
  rw [e] at hF₁
  exact lt_of_mul_lt_mul_left hF₁ ht.le

/-! ## The two events together -/

lemma Tfun_meas (P : Measure Ω') [IsProbabilityMeasure P] {X Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) :
    Measurable (fun F₁ : Matrix (Fin m) (Fin n) ℝ => Tfun P X Y F₁) := by
  have e : (fun F₁ : Matrix (Fin m) (Fin n) ℝ => Tfun P X Y F₁) =
      fun F₁ => ∑ i, Yf P X Y (rowOf i F₁) := funext fun F₁ => Tfun_eq_sum P hX hY hXY F₁
  rw [e]
  exact Finset.measurable_sum _ fun i _ => (Yf_meas P hX hY).comp (measurable_rowOf i)

/-- **Lemma TR** (the bias against the coupling cost, with its charge). For a coupling `(X, Y)`
that does not depend on `F`, with `D = E|X − Y|² < ∞`, `n, m ≥ 1`, `δ, δ′ > 0`:
`Pr_{F₁,F₂}(t_F·|Δ_{y,y′}|² > (1 + δ)(1 + δ′)·(2/n)·D) ≤ (432/m²)(1 + 63/m)(1/δ⁴ + 1/δ′⁴)`. -/
theorem lemmaTR (P : Measure Ω') [IsProbabilityMeasure P] (hn : 1 ≤ n) (hm : 1 ≤ m)
    {X Y : Ω' → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') :
    (hidGauss n m).real
        {θ | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * ∫ ω, normSq (X ω - Y ω) ∂P) <
          2 / (m : ℝ) * normSq (dPair P X Y θ)} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) * (1 / δ ^ 4 + 1 / δ' ^ 4) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set D : ℝ := ∫ ω, normSq (X ω - Y ω) ∂P with hD
  set c : ℝ := 432 / (m : ℝ) ^ 2 * (1 + 63 / m) with hc
  have hc0 : 0 ≤ c := by positivity
  set B₁ : Set (Matrix (Fin m) (Fin n) ℝ) :=
    {F₁ | (1 + δ') * (2 / (n : ℝ) * D) < 2 / (m : ℝ) * Tfun P X Y F₁} with hB₁
  set A : Set (HidParam n m) :=
    {θ | (1 + δ) * (2 / (m : ℝ) * Tfun P X Y θ.1) < 2 / (m : ℝ) * normSq (dPair P X Y θ)}
    with hA
  have mA : MeasurableSet A := by
    refine measurableSet_lt ?_ ?_
    · exact measurable_const.mul (measurable_const.mul
        ((Tfun_meas P hX hY hXY).comp measurable_fst))
    · unfold normSq
      exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        (measurable_dPair P hX hY i).pow_const 2)
  have hsub : {θ : HidParam n m | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * D) <
      2 / (m : ℝ) * normSq (dPair P X Y θ)} ⊆ (B₁ ×ˢ univ) ∪ A := by
    intro θ hθ
    simp only [mem_ofPred_eq] at hθ
    by_cases h1 : θ.1 ∈ B₁
    · exact Or.inl ⟨h1, mem_univ _⟩
    · refine Or.inr ?_
      have h1' : 2 / (m : ℝ) * Tfun P X Y θ.1 ≤ (1 + δ') * (2 / (n : ℝ) * D) := not_lt.mp h1
      show (1 + δ) * (2 / (m : ℝ) * Tfun P X Y θ.1) < 2 / (m : ℝ) * normSq (dPair P X Y θ)
      have h2 : (1 + δ) * (2 / (m : ℝ) * Tfun P X Y θ.1) ≤
          (1 + δ) * ((1 + δ') * (2 / (n : ℝ) * D)) :=
        mul_le_mul_of_nonneg_left h1' (by linarith)
      calc (1 + δ) * (2 / (m : ℝ) * Tfun P X Y θ.1)
          ≤ (1 + δ) * (1 + δ') * (2 / (n : ℝ) * D) := by rw [mul_assoc]; exact h2
        _ < _ := hθ
  have hT1 := lemmaTR_T1 P hn hm hX hY hXY hδ'
  rw [← hD, ← hc] at hT1
  have hB : (hidGauss n m).real (B₁ ×ˢ (univ : Set (Matrix (Fin m) (Fin m) ℝ))) ≤
      c / δ' ^ 4 := by
    unfold hidGauss
    rw [measureReal_prod_prod]
    simpa using hT1
  have hAle : (hidGauss n m).real A ≤ c / δ ^ 4 := by
    have hc1 : 0 ≤ c / δ ^ 4 := by positivity
    have hle : (hidGauss n m) A ≤ ENNReal.ofReal (c / δ ^ 4) := by
      unfold hidGauss
      rw [Measure.prod_apply mA]
      calc ∫⁻ F₁, (gaussMat m m (2 / (m : ℝ))) (Prod.mk F₁ ⁻¹' A) ∂gaussMat m n (2 / (n : ℝ))
          ≤ ∫⁻ _, ENNReal.ofReal (c / δ ^ 4) ∂gaussMat m n (2 / (n : ℝ)) := by
            refine lintegral_mono fun F₁ => ?_
            have h := lemmaTR_T2 P hm hX hY hXY F₁ hδ
            rw [measureReal_def] at h
            exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc1).mpr h
        _ = ENNReal.ofReal (c / δ ^ 4) := by simp
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hc1 hle
  calc (hidGauss n m).real {θ | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * D) <
        2 / (m : ℝ) * normSq (dPair P X Y θ)}
      ≤ (hidGauss n m).real ((B₁ ×ˢ univ) ∪ A) := measureReal_mono hsub
    _ ≤ (hidGauss n m).real (B₁ ×ˢ univ) + (hidGauss n m).real A := measureReal_union_le _ _
    _ ≤ c / δ' ^ 4 + c / δ ^ 4 := add_le_add hB hAle
    _ = c * (1 / δ ^ 4 + 1 / δ' ^ 4) := by ring

end TRc

end BstLean.Part151
