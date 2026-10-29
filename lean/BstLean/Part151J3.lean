import BstLean.Part151J2
import BstLean.Part151TR

/-!
# Part 151: Lemma JF with a charge (the Frobenius norm of the Jacobian of the features, averaged
over a distribution of inputs)

Role: `proofs/option-n/theorem5-08-F-rows.tex`, Lemma JF, second claim, in a two-step form
(first `F₁`, then `F₂` given `F₁`, as Lemma TR), with fourth-moment Markov charges.

* `unifFin n`: the uniform distribution on `Fin n`.
* `sumQ`, `sumT`, `sumQ_sq`, `sumQ_four`: moments of a positive semidefinite Gaussian quadratic
  form `q(w) = E_ω Σ_l (w·b_l(ω))²` with trace `T`: `E q² ≤ 3v²T²`, `E q⁴ ≤ 105v⁴T⁴`
  (from `QR_sq`, `QR_four` of `Part151R` on the product with the uniform index `l`).
* `phiJ`, `fX`, `Wb`, `fY`, `PhiJ`: the row functions and `Φ = E_y t_F‖J_F(y)‖²_F`.
* `lemmaJF_T2`: given `F₁`: `Pr_{F₂}(Φ > (1 + δ)·t_F·E_y‖D₁F₁‖²_F) ≤ (432/m²)(1 + 63/m)/δ⁴`.
* `lemmaJF_T1`: `Pr_{F₁}(E_y‖D₁F₁‖²_F > (1 + δ′)m) ≤ (432/m²)(1 + 63/m)/δ′⁴`.
* **`lemmaJF`**: `Pr(Φ > 2(1 + δ)(1 + δ′)) ≤ (432/m²)(1 + 63/m)(1/δ⁴ + 1/δ′⁴)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)

/-! ## The uniform distribution on `Fin n` -/

/-- The uniform distribution on `Fin n`. -/
noncomputable def unifFin (n : ℕ) : Measure (Fin n) := (n : ℝ≥0∞)⁻¹ • Measure.count

lemma unifFin_prob {n : ℕ} (hn : 1 ≤ n) : IsProbabilityMeasure (unifFin n) := by
  constructor
  unfold unifFin
  rw [Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
    smul_eq_mul]
  have h0 : (n : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this.ne'
  simpa using ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top n)

lemma integral_unifFin {n : ℕ} (f : Fin n → ℝ) :
    ∫ l, f l ∂unifFin n = (n : ℝ)⁻¹ * ∑ l, f l := by
  unfold unifFin
  rw [integral_smul_measure, integral_fintype (Integrable.of_finite)]
  simp

/-! ## A positive semidefinite Gaussian quadratic form -/

section sumQ

variable {Ω' : Type*} [MeasurableSpace Ω'] {n d : ℕ}

/-- `q(w) = E_ω Σ_l (w·b_l(ω))²`: a positive semidefinite quadratic form in `w`. -/
noncomputable def sumQ (P : Measure Ω') (b : Fin n → Ω' → Fin d → ℝ) (w : Fin d → ℝ) : ℝ :=
  ∫ ω, ∑ l, (w ⬝ᵥ b l ω) ^ 2 ∂P

/-- `T = E_ω Σ_l |b_l(ω)|²`: the trace of the quadratic form `sumQ`. -/
noncomputable def sumT (P : Measure Ω') (b : Fin n → Ω' → Fin d → ℝ) : ℝ :=
  ∫ ω, ∑ l, normSq (b l ω) ∂P

lemma sumQ_nonneg (P : Measure Ω') (b : Fin n → Ω' → Fin d → ℝ) (w : Fin d → ℝ) :
    0 ≤ sumQ P b w :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sumT_nonneg (P : Measure Ω') (b : Fin n → Ω' → Fin d → ℝ) : 0 ≤ sumT P b :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _

variable (P : Measure Ω') [IsProbabilityMeasure P] {b : Fin n → Ω' → Fin d → ℝ}

/-- The quadratic form and its trace, written on the product with the uniform index. -/
lemma sumQ_prod (hn : 1 ≤ n) (hb : ∀ l, Measurable (b l)) {K : ℝ}
    (hK : ∀ l ω, normSq (b l ω) ≤ K) :
    haveI := unifFin_prob hn
    Measurable (fun p : Ω' × Fin n => b p.2 p.1) ∧
    Integrable (fun p : Ω' × Fin n => normSq (b p.2 p.1 - (fun _ : Ω' × Fin n => (0 : Fin d → ℝ)) p))
      (P.prod (unifFin n)) ∧
    (∀ w : Fin d → ℝ, sumQ P b w = n * QR (P.prod (unifFin n)) (fun p => b p.2 p.1)
      (fun _ => 0) w) ∧
    sumT P b = n * TR (P.prod (unifFin n)) (fun p => b p.2 p.1) (fun _ => 0) := by
  have := unifFin_prob hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have hmeas : Measurable (fun p : Ω' × Fin n => b p.2 p.1) :=
    measurable_from_prod_countable_left fun l => hb l
  have hns : Measurable (fun p : Ω' × Fin n => normSq (b p.2 p.1)) :=
    measurable_normSq.comp hmeas
  have hK0 : 0 ≤ K := by
    obtain ⟨ω⟩ := P.nonempty_of_neZero
    have l : Fin n := ⟨0, by omega⟩
    exact (normSq_nonneg _).trans (hK l ω)
  have hint : Integrable (fun p : Ω' × Fin n => normSq (b p.2 p.1)) (P.prod (unifFin n)) :=
    Integrable.of_bound hns.aestronglyMeasurable K (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]; exact hK p.2 p.1)
  refine ⟨hmeas, ?_, ?_, ?_⟩
  · simpa using hint
  · intro w
    unfold sumQ QR
    have hg : Measurable (fun p : Ω' × Fin n => (w ⬝ᵥ b p.2 p.1) ^ 2) := by
      refine Measurable.pow_const ?_ 2
      have : Measurable (fun u : Fin d → ℝ => w ⬝ᵥ u) := by
        simp only [dotProduct]; fun_prop
      exact this.comp hmeas
    have hgi : Integrable (fun p : Ω' × Fin n => (w ⬝ᵥ b p.2 p.1) ^ 2) (P.prod (unifFin n)) :=
      Integrable.of_bound hg.aestronglyMeasurable (normSq w * K)
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact (dot_sq_le _ _).trans
            (mul_le_mul_of_nonneg_left (hK p.2 p.1) (normSq_nonneg _)))
    have e : (fun p : Ω' × Fin n => (w ⬝ᵥ (b p.2 p.1 -
        (fun _ : Ω' × Fin n => (0 : Fin d → ℝ)) p)) ^ 2) =
        fun p => (w ⬝ᵥ b p.2 p.1) ^ 2 := by
      funext p; simp
    rw [e, integral_prod _ hgi]
    simp_rw [integral_unifFin]
    rw [integral_const_mul]
    field_simp
  · unfold sumT TR
    have e : (fun p : Ω' × Fin n => normSq (b p.2 p.1 -
        (fun _ : Ω' × Fin n => (0 : Fin d → ℝ)) p)) = fun p => normSq (b p.2 p.1) := by
      funext p; simp
    rw [e, integral_prod _ hint]
    simp_rw [integral_unifFin]
    rw [integral_const_mul]
    field_simp

/-- **Second moment of the quadratic form**: `E q(√v·ξ)² ≤ 3v²T²`. -/
theorem sumQ_sq (hn : 1 ≤ n) (hb : ∀ l, Measurable (b l)) {K : ℝ}
    (hK : ∀ l ω, normSq (b l ω) ≤ K) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (sumQ P b (√v • ξ) ^ 2) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (3 * v ^ 2 * sumT P b ^ 2) := by
  have := unifFin_prob hn
  obtain ⟨hm, hT, hq, ht⟩ := sumQ_prod P hn hb hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := QR_sq (P := P.prod (unifFin n)) hm measurable_const hT hv
  simp_rw [hq]
  have e : ∀ ξ : Fin d → ℝ, ENNReal.ofReal ((n * QR (P.prod (unifFin n))
      (fun p => b p.2 p.1) (fun _ => 0) (√v • ξ)) ^ 2) =
      ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (QR (P.prod (unifFin n))
        (fun p => b p.2 p.1) (fun _ => 0) (√v • ξ) ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_pow]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ht]
  congr 1
  ring

/-- **Fourth moment of the quadratic form**: `E q(√v·ξ)⁴ ≤ 105v⁴T⁴`. -/
theorem sumQ_four (hn : 1 ≤ n) (hb : ∀ l, Measurable (b l)) {K : ℝ}
    (hK : ∀ l ω, normSq (b l ω) ≤ K) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (sumQ P b (√v • ξ) ^ 4) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (105 * v ^ 4 * sumT P b ^ 4) := by
  have := unifFin_prob hn
  obtain ⟨hm, hT, hq, ht⟩ := sumQ_prod P hn hb hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := QR_four (P := P.prod (unifFin n)) hm measurable_const hT hv
  simp_rw [hq]
  have e : ∀ ξ : Fin d → ℝ, ENNReal.ofReal ((n * QR (P.prod (unifFin n))
      (fun p => b p.2 p.1) (fun _ => 0) (√v • ξ)) ^ 4) =
      ENNReal.ofReal ((n : ℝ) ^ 4) * ENNReal.ofReal (QR (P.prod (unifFin n))
        (fun p => b p.2 p.1) (fun _ => 0) (√v • ξ) ^ 4) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ht]
  congr 1
  ring

end sumQ

/-! ## Lemma JF with a charge -/

section JFc

variable {Ω' : Type*} [MeasurableSpace Ω'] {n m : ℕ}

lemma measurable_pre1 (F₁ : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Measurable (fun y : Fin n → ℝ => (F₁ *ᵥ y) i) := by
  simp only [mulVec, dotProduct]
  fun_prop

lemma measurable_maskedF (F₁ : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (l : Fin n) :
    Measurable (fun y : Fin n → ℝ => maskedF F₁ y i l) := by
  simp only [maskedF, Matrix.of_apply]
  exact (measurable_mask.comp (measurable_pre1 F₁ i)).mul measurable_const

lemma maskedF_sq_le (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin m) (l : Fin n) :
    maskedF F₁ y i l ^ 2 ≤ F₁ i l ^ 2 := by
  simp only [maskedF, Matrix.of_apply, mul_pow, mask_sq]
  have h0 := mask_nonneg ((F₁ *ᵥ y) i)
  have h1 : mask ((F₁ *ᵥ y) i) ≤ 1 := by unfold mask; split_ifs <;> norm_num
  nlinarith [sq_nonneg (F₁ i l)]

lemma maskedF_fro_le (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    ∑ i, ∑ l, maskedF F₁ y i l ^ 2 ≤ frob F₁ :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => maskedF_sq_le F₁ y i l

/-- One row term of `‖J_F(y)‖²_F`: `1[w·h(y) > 0]·|w·D₁F₁|²`. -/
noncomputable def phiJ (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  if 0 < w ⬝ᵥ reluV (F₁ *ᵥ y) then ∑ l, (∑ i, w i * maskedF F₁ y i l) ^ 2 else 0

lemma phiJ_nonneg (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ phiJ F₁ w y := by
  unfold phiJ
  split_ifs
  · exact Finset.sum_nonneg fun l _ => sq_nonneg _
  · exact le_rfl

lemma phiJ_le_quad (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) (y : Fin n → ℝ) :
    phiJ F₁ w y ≤ ∑ l, (w ⬝ᵥ fun i => maskedF F₁ y i l) ^ 2 := by
  unfold phiJ
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun l _ => sq_nonneg _

lemma quad_le (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) (y : Fin n → ℝ) :
    ∑ l, (w ⬝ᵥ fun i => maskedF F₁ y i l) ^ 2 ≤ normSq w * frob F₁ := by
  calc ∑ l, (w ⬝ᵥ fun i => maskedF F₁ y i l) ^ 2
      ≤ ∑ l, normSq w * normSq (fun i => maskedF F₁ y i l) :=
        Finset.sum_le_sum fun l _ => dot_sq_le _ _
    _ = normSq w * ∑ i, ∑ l, maskedF F₁ y i l ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]; rfl
    _ ≤ normSq w * frob F₁ :=
        mul_le_mul_of_nonneg_left (maskedF_fro_le F₁ y) (normSq_nonneg _)

lemma measurable_phiJ (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (fun q : (Fin m → ℝ) × (Fin n → ℝ) => phiJ F₁ q.1 q.2) := by
  unfold phiJ
  refine Measurable.ite (measurableSet_lt measurable_const ?_) ?_ measurable_const
  · have e : (fun q : (Fin m → ℝ) × (Fin n → ℝ) => q.1 ⬝ᵥ reluV (F₁ *ᵥ q.2)) =
        fun q => ∑ i, q.1 i * relu ((F₁ *ᵥ q.2) i) := by
      funext q; simp [dotProduct, reluV]
    rw [e]
    refine Finset.measurable_sum _ fun i _ => Measurable.mul (by fun_prop) ?_
    exact measurable_relu.comp ((measurable_pre1 F₁ i).comp measurable_snd)
  · refine Finset.measurable_sum _ fun l _ => Measurable.pow_const
      (Finset.measurable_sum _ fun i _ => Measurable.mul (by fun_prop) ?_) 2
    exact (measurable_maskedF F₁ i l).comp measurable_snd

variable (P : Measure Ω') [IsProbabilityMeasure P] (Yv : Ω' → Fin n → ℝ)

/-- `E_y 1[w·h(y) > 0]·|w·D₁(y)F₁|²`: the row function of the step over `F₂`. -/
noncomputable def fX (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) : ℝ :=
  ∫ ω, phiJ F₁ w (Yv ω) ∂P

/-- `E_y ‖D₁(y)F₁‖²_F`. -/
noncomputable def Wb (F₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∫ ω, ∑ i, ∑ l, maskedF F₁ (Yv ω) i l ^ 2 ∂P

/-- `E_y 1[f·y > 0]·|f|²`: the row function of the step over `F₁`. -/
noncomputable def fY (f : Fin n → ℝ) : ℝ :=
  ∫ ω, (if 0 < f ⬝ᵥ Yv ω then normSq f else 0) ∂P

/-- `Φ = E_y t_F·‖J_F(y)‖²_F`, `t_F = 2/m`. -/
noncomputable def PhiJ (θ : HidParam n m) : ℝ :=
  ∫ ω, 2 / (m : ℝ) * jacFro θ.1 θ.2 (Yv ω) ∂P

variable {Yv}

omit [IsProbabilityMeasure P] in
lemma fX_nonneg (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) : 0 ≤ fX P Yv F₁ w :=
  integral_nonneg fun _ => phiJ_nonneg _ _ _

lemma phiJ_integrable (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) :
    Integrable (fun ω => phiJ F₁ w (Yv ω)) P := by
  have hm : Measurable (fun ω => phiJ F₁ w (Yv ω)) :=
    (measurable_phiJ F₁).comp (measurable_const.prodMk hY)
  refine Integrable.of_bound hm.aestronglyMeasurable (normSq w * frob F₁)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (phiJ_nonneg _ _ _)]
  exact (phiJ_le_quad _ _ _).trans (quad_le _ _ _)

lemma fX_meas (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (fX P Yv F₁) := by
  unfold fX
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : (Fin m → ℝ) × Ω' => phiJ F₁ q.1 (Yv q.2)) ?_
  exact ((measurable_phiJ F₁).comp
    (measurable_fst.prodMk (hY.comp measurable_snd))).stronglyMeasurable

lemma masked_integrable (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun ω => ∑ i, ∑ l, maskedF F₁ (Yv ω) i l ^ 2) P := by
  have hm : Measurable (fun ω => ∑ i, ∑ l, maskedF F₁ (Yv ω) i l ^ 2) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun l _ =>
      ((measurable_maskedF F₁ i l).comp hY).pow_const 2
  refine Integrable.of_bound hm.aestronglyMeasurable (frob F₁)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _)]
  exact maskedF_fro_le F₁ _

omit [IsProbabilityMeasure P] in
lemma Wb_nonneg (F₁ : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ Wb P Yv F₁ :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `E_y ‖J_F(y)‖²_F = Σ_j fX(row_j F₂)`. -/
lemma int_jacFro (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ)
    (F₂ : Matrix (Fin m) (Fin m) ℝ) :
    ∫ ω, jacFro F₁ F₂ (Yv ω) ∂P = ∑ j, fX P Yv F₁ (rowOf j F₂) := by
  simp_rw [jacFro_rows]
  unfold fX
  rw [← integral_finsetSum _ fun j _ => phiJ_integrable P hY F₁ (rowOf j F₂)]
  rfl

/-- The mean of the row function: `E fX(√v·ξ) = (v/2)·E_y‖D₁F₁‖²_F`. -/
lemma fX_mean (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ) {v : ℝ} (hv : 0 < v) :
    ∫⁻ ξ, ENNReal.ofReal (fX P Yv F₁ (√v • ξ)) ∂stdGauss (Fin m) =
      ENNReal.ofReal (v / 2 * Wb P Yv F₁) := by
  have hc : √v ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have e1 : ∀ ξ : Fin m → ℝ, ENNReal.ofReal (fX P Yv F₁ (√v • ξ)) =
      ∫⁻ ω, ENNReal.ofReal (phiJ F₁ (√v • ξ) (Yv ω)) ∂P := fun ξ =>
    ofReal_integral_eq_lintegral_ofReal (phiJ_integrable P hY F₁ _)
      (Filter.Eventually.of_forall fun ω => phiJ_nonneg _ _ _)
  simp_rw [e1]
  have hjoint : Measurable (fun q : (Fin m → ℝ) × Ω' =>
      ENNReal.ofReal (phiJ F₁ (√v • q.1) (Yv q.2))) :=
    ENNReal.measurable_ofReal.comp ((measurable_phiJ F₁).comp
      (((measurable_const_smul (√v)).comp measurable_fst).prodMk (hY.comp measurable_snd)))
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have e2 : ∀ ω, ∫⁻ ξ, ENNReal.ofReal (phiJ F₁ (√v • ξ) (Yv ω)) ∂stdGauss (Fin m) =
      ENNReal.ofReal (v / 2 * ∑ i, ∑ l, maskedF F₁ (Yv ω) i l ^ 2) := by
    intro ω
    have h2 := half_second (maskedF F₁ (Yv ω)) (reluV (F₁ *ᵥ Yv ω)) hc
      (fun h0 => maskedF_zero_of F₁ (Yv ω) h0)
    rw [Real.sq_sqrt hv.le] at h2
    rw [← h2]
    refine lintegral_congr fun ξ => ?_
    unfold phiJ
    split_ifs <;> simp
  simp_rw [e2]
  rw [← ofReal_integral_eq_lintegral_ofReal ((masked_integrable P hY F₁).const_mul _)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _)),
    integral_const_mul]
  rfl

/-- The row function is below a quadratic form with trace `E_y‖D₁F₁‖²_F`. -/
lemma fX_le_sumQ (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) :
    fX P Yv F₁ w ≤ sumQ P (fun l ω i => maskedF F₁ (Yv ω) i l) w := by
  unfold fX sumQ
  have hq : Integrable (fun ω => ∑ l, (w ⬝ᵥ fun i => maskedF F₁ (Yv ω) i l) ^ 2) P := by
    have hm : Measurable (fun ω => ∑ l, (w ⬝ᵥ fun i => maskedF F₁ (Yv ω) i l) ^ 2) := by
      refine Finset.measurable_sum _ fun l _ => Measurable.pow_const ?_ 2
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ =>
        measurable_const.mul ((measurable_maskedF F₁ i l).comp hY)
    refine Integrable.of_bound hm.aestronglyMeasurable (normSq w * frob F₁)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _)]
    exact quad_le _ _ _
  exact integral_mono (phiJ_integrable P hY F₁ w) hq fun ω => phiJ_le_quad _ _ _

omit [IsProbabilityMeasure P] in
lemma sumT_masked (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    sumT P (fun l ω i => maskedF F₁ (Yv ω) i l) = Wb P Yv F₁ := by
  unfold sumT Wb
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ∑ l, normSq (fun i => maskedF F₁ (Yv ω) i l) = ∑ i, ∑ l, maskedF F₁ (Yv ω) i l ^ 2
  rw [Finset.sum_comm]; rfl

/-- **Lemma JF, the step over `F₂`** (fixed `F₁`): for `n, m ≥ 1`, `δ > 0`:
`Pr_{F₂}(E_y t_F‖J_F(y)‖²_F > (1 + δ)·t_F·E_y‖D₁F₁‖²_F) ≤ (432/m²)(1 + 63/m)/δ⁴`. -/
theorem lemmaJF_T2 (hn : 1 ≤ n) (hm : 1 ≤ m) (hY : Measurable Yv)
    (F₁ : Matrix (Fin m) (Fin n) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMat m m (2 / (m : ℝ))).real
        {F₂ | (1 + δ) * (2 / (m : ℝ) * Wb P Yv F₁) < PhiJ P Yv (F₁, F₂)} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ ^ 4 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hPhi : ∀ F₂ : Matrix (Fin m) (Fin m) ℝ,
      PhiJ P Yv (F₁, F₂) = 2 / (m : ℝ) * ∑ j, fX P Yv F₁ (rowOf j F₂) := by
    intro F₂
    unfold PhiJ
    rw [integral_const_mul, int_jacFro P hY]
  have hW0 := Wb_nonneg P (Yv := Yv) F₁
  rcases hW0.eq_or_lt with h0 | hpos
  · -- `Wb = 0`: the event is empty
    have hfx : ∀ w : Fin m → ℝ, fX P Yv F₁ w = 0 := by
      intro w
      have h1 := fX_le_sumQ P hY F₁ w
      have h2 : sumQ P (fun l ω i => maskedF F₁ (Yv ω) i l) w ≤ normSq w * Wb P Yv F₁ := by
        unfold sumQ Wb
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun l _ => sq_nonneg _)
          ((masked_integrable P hY F₁).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
        calc ∑ l, (w ⬝ᵥ fun i => maskedF F₁ (Yv ω) i l) ^ 2
            ≤ ∑ l, normSq w * normSq (fun i => maskedF F₁ (Yv ω) i l) :=
              Finset.sum_le_sum fun l _ => dot_sq_le _ _
          _ = normSq w * ∑ i, ∑ l, maskedF F₁ (Yv ω) i l ^ 2 := by
              rw [← Finset.mul_sum, Finset.sum_comm]; rfl
      rw [← h0, mul_zero] at h2
      exact le_antisymm (h1.trans h2) (fX_nonneg P F₁ w)
    have hempty : {F₂ : Matrix (Fin m) (Fin m) ℝ |
        (1 + δ) * (2 / (m : ℝ) * Wb P Yv F₁) < PhiJ P Yv (F₁, F₂)} = ∅ := by
      ext F₂
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [hPhi, ← h0]
      simp [hfx]
    rw [hempty]
    simp only [measureReal_empty]
    positivity
  · set U : ℝ := Wb P Yv F₁ / m with hU
    have hU0 : 0 < U := by rw [hU]; positivity
    have hK : ∀ (l : Fin n) (ω : Ω'), normSq (fun i => maskedF F₁ (Yv ω) i l) ≤ frob F₁ := by
      intro l ω
      calc normSq (fun i => maskedF F₁ (Yv ω) i l)
          ≤ ∑ l', normSq (fun i => maskedF F₁ (Yv ω) i l') :=
            Finset.single_le_sum (f := fun l' => normSq (fun i => maskedF F₁ (Yv ω) i l'))
              (fun _ _ => normSq_nonneg _) (Finset.mem_univ l)
        _ = ∑ i, ∑ l', maskedF F₁ (Yv ω) i l' ^ 2 := by rw [Finset.sum_comm]; rfl
        _ ≤ frob F₁ := maskedF_fro_le F₁ _
    have hbm : ∀ l : Fin n, Measurable (fun ω => fun i => maskedF F₁ (Yv ω) i l) := fun l =>
      measurable_pi_iff.mpr fun i => (measurable_maskedF F₁ i l).comp hY
    have h1 : ∫⁻ ξ, ENNReal.ofReal (fX P Yv F₁ (√(2 / (m : ℝ)) • ξ)) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal U := by
      rw [fX_mean P hY F₁ hv]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hU]; field_simp
    have h2 : ∫⁻ ξ, ENNReal.ofReal (fX P Yv F₁ (√(2 / (m : ℝ)) • ξ) ^ 2) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal (12 * U ^ 2) := by
      have hs := sumQ_sq P hn hbm hK hv.le
      rw [sumT_masked] at hs
      refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (fX_nonneg P F₁ _) (fX_le_sumQ P hY F₁ _) 2)).trans (hs.trans ?_)
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hU]; field_simp; ring
    have h4 : ∫⁻ ξ, ENNReal.ofReal (fX P Yv F₁ (√(2 / (m : ℝ)) • ξ) ^ 4) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal (1680 * U ^ 4) := by
      have hs := sumQ_four P hn hbm hK hv.le
      rw [sumT_masked] at hs
      refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (fX_nonneg P F₁ _) (fX_le_sumQ P hY F₁ _) 4)).trans (hs.trans ?_)
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hU]; field_simp; ring
    have ht := tail_rows (m := m) (fX_meas P hY F₁) (fX_nonneg P F₁) hU0 h1 h2 h4 hm hδ
    refine le_trans (measureReal_mono ?_) ht
    intro F₂ hF
    simp only [mem_ofPred_eq] at hF ⊢
    rw [hPhi] at hF
    have e : (m : ℝ) * U = Wb P Yv F₁ := by rw [hU]; field_simp
    rw [e]
    have h3 : (1 + δ) * Wb P Yv F₁ * (2 / (m : ℝ)) <
        (∑ j, fX P Yv F₁ (rowOf j F₂)) * (2 / (m : ℝ)) := by linarith
    exact lt_of_mul_lt_mul_right h3 hv.le

end JFc

/-! ### The step over `F₁` -/

section T1

variable {Ω' : Type*} [MeasurableSpace Ω'] {n m : ℕ}
variable (P : Measure Ω') [IsProbabilityMeasure P] {Yv : Ω' → Fin n → ℝ}

omit [IsProbabilityMeasure P] in
lemma fY_nonneg (f : Fin n → ℝ) : 0 ≤ fY P Yv f :=
  integral_nonneg fun _ => by split_ifs <;> [exact normSq_nonneg _; exact le_rfl]

lemma measurable_fYint (hY : Measurable Yv) :
    Measurable (fun q : (Fin n → ℝ) × Ω' =>
      if 0 < q.1 ⬝ᵥ Yv q.2 then normSq q.1 else 0) := by
  refine Measurable.ite (measurableSet_lt measurable_const ?_)
    (measurable_normSq.comp measurable_fst) measurable_const
  simp only [dotProduct]
  refine Finset.measurable_sum _ fun l _ => Measurable.mul (by fun_prop) ?_
  exact (measurable_pi_apply l).comp (hY.comp measurable_snd)

lemma fYint_integrable (hY : Measurable Yv) (f : Fin n → ℝ) :
    Integrable (fun ω => if 0 < f ⬝ᵥ Yv ω then normSq f else 0) P := by
  have hm : Measurable (fun ω => if 0 < f ⬝ᵥ Yv ω then normSq f else 0) :=
    (measurable_fYint hY).comp (measurable_const.prodMk measurable_id)
  refine Integrable.of_bound hm.aestronglyMeasurable (normSq f)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_nonneg (normSq_nonneg _)]
  · simpa using normSq_nonneg f

lemma fY_meas (hY : Measurable Yv) : Measurable (fY P Yv) := by
  unfold fY
  refine StronglyMeasurable.measurable ?_
  exact StronglyMeasurable.integral_prod_right'
    (f := fun q : (Fin n → ℝ) × Ω' => if 0 < q.1 ⬝ᵥ Yv q.2 then normSq q.1 else 0)
    (measurable_fYint hY).stronglyMeasurable

lemma fY_le (hY : Measurable Yv) (f : Fin n → ℝ) : fY P Yv f ≤ normSq f := by
  unfold fY
  have h := integral_mono (fYint_integrable P hY f) (integrable_const (normSq f))
    (fun ω => by
      show (if 0 < f ⬝ᵥ Yv ω then normSq f else 0) ≤ normSq f
      split_ifs
      · exact le_rfl
      · exact normSq_nonneg _)
  simpa using h

/-- `E_y‖D₁(y)F₁‖²_F = Σ_i fY(row_i F₁)`. -/
lemma Wb_rows (hY : Measurable Yv) (F₁ : Matrix (Fin m) (Fin n) ℝ) :
    Wb P Yv F₁ = ∑ i, fY P Yv (rowOf i F₁) := by
  unfold Wb fY
  simp_rw [maskedF_fro]
  rw [integral_finsetSum _ fun i _ => fYint_integrable P hY (rowOf i F₁)]

/-- `|f|²` as a quadratic form `sumQ` with trace `n`. -/
lemma normSq_eq_sumQ (f : Fin n → ℝ) :
    normSq f = sumQ P (fun (l : Fin n) (_ : Ω') => (Pi.single l 1 : Fin n → ℝ)) f := by
  unfold sumQ
  simp [normSq, dotProduct, Pi.single_apply]

lemma sumT_single :
    sumT P (fun (l : Fin n) (_ : Ω') => (Pi.single l 1 : Fin n → ℝ)) = n := by
  unfold sumT
  simp [normSq, Pi.single_apply]

/-- `E 1[(cξ)·y > 0]·|cξ|² ≤ 1` for `c = √(2/n)`. -/
lemma half_normSq (hn : 1 ≤ n) (y : Fin n → ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ y then
      normSq (√(2 / (n : ℝ)) • ξ) else 0) ∂stdGauss (Fin n) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv' : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  by_cases hy : y = 0
  · subst hy
    simp
  · have hc : √(2 / (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hv').ne'
    set N : (Fin n → ℝ) → ℝ≥0∞ := fun w => ENNReal.ofReal (normSq w) with hNd
    have hN : Measurable N := ENNReal.measurable_ofReal.comp measurable_normSq
    have hev : ∀ w, N (-w) = N w := fun w => by
      simp only [hNd]; rw [BstLean.Part135.normSq_neg]
    have h2 := half_lint hy hc hN hev
    have h3 : ∫⁻ ξ, N (√(2 / (n : ℝ)) • ξ) ∂stdGauss (Fin n) = 2 := by
      obtain ⟨hi, hval⟩ := BstLean.Part149.stdGauss_normSq n
      have e3 : ∀ ξ : Fin n → ℝ, N (√(2 / (n : ℝ)) • ξ) =
          ENNReal.ofReal (2 / (n : ℝ) * normSq ξ) := by
        intro ξ
        simp only [hNd]
        rw [normSq_smul, Real.sq_sqrt hv'.le]
      simp_rw [e3]
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
        (Filter.Eventually.of_forall fun ξ => mul_nonneg hv'.le (normSq_nonneg _)),
        integral_const_mul, hval]
      have : 2 / (n : ℝ) * n = 2 := by field_simp
      rw [this]; simp
    rw [h3] at h2
    have e : ∀ ξ : Fin n → ℝ, ENNReal.ofReal (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ y then
        normSq (√(2 / (n : ℝ)) • ξ) else 0) =
        (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ y then N (√(2 / (n : ℝ)) • ξ) else 0) := by
      intro ξ
      split_ifs <;> simp [hNd]
    simp_rw [e]
    have h5 : (2 : ℝ≥0∞) * ∫⁻ ξ, (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ y then
        N (√(2 / (n : ℝ)) • ξ) else 0) ∂stdGauss (Fin n) = 2 * 1 := by
      rw [mul_one]; exact h2
    exact le_of_eq ((ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h5)

/-- **Lemma JF, the step over `F₁`**: for `n, m ≥ 1`, `δ′ > 0`:
`Pr_{F₁}(E_y‖D₁(y)F₁‖²_F > (1 + δ′)·m) ≤ (432/m²)(1 + 63/m)/δ′⁴`. -/
theorem lemmaJF_T1 (hn : 1 ≤ n) (hm : 1 ≤ m) (hY : Measurable Yv) {δ' : ℝ} (hδ' : 0 < δ') :
    (gaussMat m n (2 / (n : ℝ))).real {F₁ | (1 + δ') * m < Wb P Yv F₁} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) / δ' ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv' : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hbm : ∀ l : Fin n, Measurable (fun _ : Ω' => (Pi.single l 1 : Fin n → ℝ)) :=
    fun _ => measurable_const
  have hK : ∀ (l : Fin n) (_ : Ω'), normSq (Pi.single l 1 : Fin n → ℝ) ≤ 1 := by
    intro l _
    simp [normSq, Pi.single_apply]
  have h1 : ∫⁻ ξ, ENNReal.ofReal (fY P Yv (√(2 / (n : ℝ)) • ξ)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal 1 := by
    have e1 : ∀ ξ : Fin n → ℝ, ENNReal.ofReal (fY P Yv (√(2 / (n : ℝ)) • ξ)) =
        ∫⁻ ω, ENNReal.ofReal (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ Yv ω then
          normSq (√(2 / (n : ℝ)) • ξ) else 0) ∂P := fun ξ =>
      ofReal_integral_eq_lintegral_ofReal (fYint_integrable P hY _)
        (Filter.Eventually.of_forall fun ω => by
          show 0 ≤ (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ Yv ω then
            normSq (√(2 / (n : ℝ)) • ξ) else 0)
          split_ifs
          · exact normSq_nonneg _
          · exact le_rfl)
    simp_rw [e1]
    have hjoint : Measurable (fun q : (Fin n → ℝ) × Ω' =>
        ENNReal.ofReal (if 0 < (√(2 / (n : ℝ)) • q.1) ⬝ᵥ Yv q.2 then
          normSq (√(2 / (n : ℝ)) • q.1) else 0)) :=
      ENNReal.measurable_ofReal.comp ((measurable_fYint hY).comp
        (((measurable_const_smul (√(2 / (n : ℝ)))).comp measurable_fst).prodMk measurable_snd))
    rw [lintegral_lintegral_swap hjoint.aemeasurable]
    calc ∫⁻ ω, ∫⁻ ξ, ENNReal.ofReal (if 0 < (√(2 / (n : ℝ)) • ξ) ⬝ᵥ Yv ω then
          normSq (√(2 / (n : ℝ)) • ξ) else 0) ∂stdGauss (Fin n) ∂P
        ≤ ∫⁻ _, 1 ∂P := lintegral_mono fun ω => half_normSq hn (Yv ω)
      _ = ENNReal.ofReal 1 := by simp
  have h2 : ∫⁻ ξ, ENNReal.ofReal (fY P Yv (√(2 / (n : ℝ)) • ξ) ^ 2) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (12 * (1 : ℝ) ^ 2) := by
    have hs := sumQ_sq P hn hbm hK hv'.le
    rw [sumT_single] at hs
    refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_).trans (hs.trans ?_)
    · rw [← normSq_eq_sumQ]
      exact pow_le_pow_left₀ (fY_nonneg P _) (fY_le P hY _) 2
    · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      field_simp; ring
  have h4 : ∫⁻ ξ, ENNReal.ofReal (fY P Yv (√(2 / (n : ℝ)) • ξ) ^ 4) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (1680 * (1 : ℝ) ^ 4) := by
    have hs := sumQ_four P hn hbm hK hv'.le
    rw [sumT_single] at hs
    refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_).trans (hs.trans ?_)
    · rw [← normSq_eq_sumQ]
      exact pow_le_pow_left₀ (fY_nonneg P _) (fY_le P hY _) 4
    · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      field_simp; ring
  have ht := tail_rows (m := m) (fY_meas P hY) (fY_nonneg P) one_pos h1 h2 h4 hm hδ'
  refine le_trans (measureReal_mono ?_) ht
  intro F₁ hF
  simp only [mem_ofPred_eq] at hF ⊢
  rw [Wb_rows P hY] at hF
  rw [mul_one]
  exact hF

lemma measurable_jacFro_joint :
    Measurable (fun q : HidParam n m × (Fin n → ℝ) => jacFro q.1.1 q.1.2 q.2) := by
  have hpre1 : ∀ i, Measurable (fun q : HidParam n m × (Fin n → ℝ) => (q.1.1 *ᵥ q.2) i) := by
    intro i
    simp only [mulVec, dotProduct]
    fun_prop
  have hpre2 : ∀ j, Measurable (fun q : HidParam n m × (Fin n → ℝ) =>
      (q.1.2 *ᵥ reluV (q.1.1 *ᵥ q.2)) j) := by
    intro j
    have e : (fun q : HidParam n m × (Fin n → ℝ) => (q.1.2 *ᵥ reluV (q.1.1 *ᵥ q.2)) j) =
        fun q => ∑ i, q.1.2 j i * relu ((q.1.1 *ᵥ q.2) i) := by
      funext q
      simp [mulVec, dotProduct, reluV]
    rw [e]
    refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (measurable_relu.comp (hpre1 i))
    fun_prop
  unfold jacFro jac
  simp only [Matrix.of_apply]
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
    Measurable.pow_const ((measurable_mask.comp (hpre2 j)).mul
      (Finset.measurable_sum _ fun i _ => Measurable.mul (Measurable.mul ?_
        (measurable_mask.comp (hpre1 i))) ?_)) 2
  · fun_prop
  · fun_prop

lemma PhiJ_meas (hY : Measurable Yv) : Measurable (PhiJ (m := m) P Yv) := by
  unfold PhiJ
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : HidParam n m × Ω' => 2 / (m : ℝ) * jacFro q.1.1 q.1.2 (Yv q.2)) ?_
  exact ((measurable_jacFro_joint.comp
    (measurable_fst.prodMk (hY.comp measurable_snd))).const_mul _).stronglyMeasurable

/-- **Lemma JF with its charge (two-step form).** `P` is a distribution of inputs `y = Yv ω`
that does not depend on `F`; `Φ = E_y t_F·‖J_F(y)‖²_F`. For `n, m ≥ 1`, `δ, δ′ > 0`:
`Pr_{F₁,F₂}(Φ > 2(1 + δ)(1 + δ′)) ≤ (432/m²)(1 + 63/m)(1/δ⁴ + 1/δ′⁴)`. -/
theorem lemmaJF (hn : 1 ≤ n) (hm : 1 ≤ m) (hY : Measurable Yv) {δ δ' : ℝ} (hδ : 0 < δ)
    (hδ' : 0 < δ') :
    (hidGauss n m).real {θ | 2 * (1 + δ) * (1 + δ') < PhiJ P Yv θ} ≤
      432 / (m : ℝ) ^ 2 * (1 + 63 / m) * (1 / δ ^ 4 + 1 / δ' ^ 4) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℝ := 432 / (m : ℝ) ^ 2 * (1 + 63 / m) with hc
  have hc0 : 0 ≤ c := by positivity
  set B₁ : Set (Matrix (Fin m) (Fin n) ℝ) := {F₁ | (1 + δ') * m < Wb P Yv F₁} with hB₁
  set A : Set (HidParam n m) :=
    {θ | (1 + δ) * (2 / (m : ℝ) * Wb P Yv θ.1) < PhiJ P Yv θ} with hA
  have hWm : Measurable (fun F₁ : Matrix (Fin m) (Fin n) ℝ => Wb P Yv F₁) := by
    have e : (fun F₁ : Matrix (Fin m) (Fin n) ℝ => Wb P Yv F₁) =
        fun F₁ => ∑ i, fY P Yv (rowOf i F₁) := funext fun F₁ => Wb_rows P hY F₁
    rw [e]
    exact Finset.measurable_sum _ fun i _ => (fY_meas P hY).comp (measurable_rowOf i)
  have mA : MeasurableSet A :=
    measurableSet_lt (measurable_const.mul (measurable_const.mul (hWm.comp measurable_fst)))
      (PhiJ_meas P hY)
  have hsub : {θ : HidParam n m | 2 * (1 + δ) * (1 + δ') < PhiJ P Yv θ} ⊆
      (B₁ ×ˢ univ) ∪ A := by
    intro θ hθ
    simp only [mem_ofPred_eq] at hθ
    by_cases h1 : θ.1 ∈ B₁
    · exact Or.inl ⟨h1, mem_univ _⟩
    · refine Or.inr ?_
      have h1' : Wb P Yv θ.1 ≤ (1 + δ') * m := not_lt.mp h1
      show (1 + δ) * (2 / (m : ℝ) * Wb P Yv θ.1) < PhiJ P Yv θ
      have h2 : 2 / (m : ℝ) * Wb P Yv θ.1 ≤ 2 * (1 + δ') := by
        have := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ 2 / (m : ℝ))
        have e : 2 / (m : ℝ) * ((1 + δ') * m) = 2 * (1 + δ') := by field_simp
        linarith
      have h3 : (1 + δ) * (2 / (m : ℝ) * Wb P Yv θ.1) ≤ (1 + δ) * (2 * (1 + δ')) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      calc (1 + δ) * (2 / (m : ℝ) * Wb P Yv θ.1) ≤ 2 * (1 + δ) * (1 + δ') := by
            linarith
        _ < _ := hθ
  have hT1 := lemmaJF_T1 P hn hm hY hδ'
  rw [← hc] at hT1
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
            have h := lemmaJF_T2 P hn hm hY F₁ hδ
            rw [measureReal_def] at h
            exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc1).mpr h
        _ = ENNReal.ofReal (c / δ ^ 4) := by simp
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hc1 hle
  calc (hidGauss n m).real {θ | 2 * (1 + δ) * (1 + δ') < PhiJ P Yv θ}
      ≤ (hidGauss n m).real ((B₁ ×ˢ univ) ∪ A) := measureReal_mono hsub
    _ ≤ (hidGauss n m).real (B₁ ×ˢ univ) + (hidGauss n m).real A := measureReal_union_le _ _
    _ ≤ c / δ' ^ 4 + c / δ ^ 4 := add_le_add hB hAle
    _ = c * (1 / δ ^ 4 + 1 / δ' ^ 4) := by ring

end T1

end BstLean.Part151
