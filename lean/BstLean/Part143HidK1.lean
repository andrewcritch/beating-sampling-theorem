import BstLean.Part136Final
import BstLean.Part133Four

/-!
# Part 143, helper `hidK`, file 1: sharper second moments of one ReLU layer

* `row_lin_four`: one Gaussian row `r`: `E (⟨r, h⟩⟨r, h′⟩)² = v²(|h|²|h′|² + 2⟨h, h′⟩²)`.
* `row_relu_four_le`: `E ReLU(⟨r, h⟩)²ReLU(⟨r, h′⟩)² ≤ (1/2)·v²(|h|²|h′|² + 2⟨h, h′⟩²)`
  (the symmetry `r → −r`).
* `layer_dot_relu_var143`: `Var ⟨ReLU(M h), ReLU(M h′)⟩ ≤
  m·(v²(|h|²|h′|² + 2⟨h, h′⟩²)/2 − (v·Φ(h, h′)/2)²)`.
* `layer_relu_sq_var`: `Var |ReLU(M h)|² = (5m/4)(v|h|²)²` (exact).
* `relu_nrm_unit_L2`: for unit `h, h′`: `‖|ReLU(M h)||ReLU(M h′)| − (m/2)v‖₂ ≤ √10/√m·(m/2)v`.
* `relu_layer_unit_L2`: for unit `h, h′`, `t = ⟨h, h′⟩`:
  `‖Ψ_κ(ReLU(M h), ReLU(M h′)) − (m/2)v·κ(κ(t))‖₂ ≤ (√10·κ(0) + √(2 + 4t²))/√m·(m/2)v`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133

variable {m k : ℕ}

/-- One Gaussian row: `E (⟨r, h⟩⟨r, h′⟩)² = v²(|h|²|h′|² + 2⟨h, h′⟩²)`. -/
lemma row_lin_four {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ => dotp (M.mulVec h) (M.mulVec h') ^ 2)
      (gaussMat 1 k v) ∧
    ∫ M : Matrix (Fin 1) (Fin k) ℝ, dotp (M.mulVec h) (M.mulVec h') ^ 2 ∂gaussMat 1 k v =
      v ^ 2 * (normSq h * normSq h' + 2 * dotp h h' ^ 2) := by
  obtain ⟨i0, -⟩ := lin_dot_var0 (m := 1) hv h h'
  have e0 := lin_dot_var (m := 1) hv h h'
  obtain ⟨i1, e1⟩ := layer_dot_lin (m := 1) hv h h'
  simp only [Nat.cast_one, one_mul] at i0 e0 e1
  have hexp : (fun M : Matrix (Fin 1) (Fin k) ℝ => dotp (M.mulVec h) (M.mulVec h') ^ 2) =
      fun M => (dotp (M.mulVec h) (M.mulVec h') - v * dotp h h') ^ 2 +
        (2 * (v * dotp h h') * dotp (M.mulVec h) (M.mulVec h') - (v * dotp h h') ^ 2) := by
    funext M; ring
  have i2 : Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ =>
      2 * (v * dotp h h') * dotp (M.mulVec h) (M.mulVec h') - (v * dotp h h') ^ 2)
      (gaussMat 1 k v) := (i1.const_mul _).sub (integrable_const _)
  rw [hexp]
  refine ⟨i0.add i2, ?_⟩
  rw [integral_add i0 i2, integral_sub (i1.const_mul _) (integrable_const _),
    integral_const_mul, e0, e1, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

lemma relu_sq_pair (a b : ℝ) :
    relu a ^ 2 * relu b ^ 2 + relu (-a) ^ 2 * relu (-b) ^ 2 ≤ (a * b) ^ 2 := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [relu_of_nonneg ha, relu_of_nonneg hb, relu_of_nonpos (by linarith : -a ≤ 0)]
    nlinarith
  · rw [relu_of_nonpos hb, relu_of_nonpos (by linarith : -a ≤ 0)]
    nlinarith [sq_nonneg (a * b)]
  · rw [relu_of_nonpos ha, relu_of_nonpos (by linarith : -b ≤ 0)]
    nlinarith [sq_nonneg (a * b)]
  · rw [relu_of_nonpos ha, relu_of_nonneg (by linarith : 0 ≤ -a),
      relu_of_nonneg (by linarith : 0 ≤ -b)]
    nlinarith

lemma normSq_reluV_one (y : Fin 1 → ℝ) : normSq (reluV y) = relu (y 0) ^ 2 := by
  change ∑ i : Fin 1, relu (y i) ^ 2 = _
  rw [Fin.sum_univ_one]

lemma dotp_one (y y' : Fin 1 → ℝ) : dotp y y' = y 0 * y' 0 := by
  unfold dotp
  rw [Fin.sum_univ_one]

/-- One Gaussian row: `E ReLU(⟨r, h⟩)²·ReLU(⟨r, h′⟩)² ≤ (1/2)·v²(|h|²|h′|² + 2⟨h, h′⟩²)`. -/
lemma row_relu_four_le {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ =>
      normSq (reluV (M.mulVec h)) * normSq (reluV (M.mulVec h'))) (gaussMat 1 k v) ∧
    ∫ M : Matrix (Fin 1) (Fin k) ℝ, normSq (reluV (M.mulVec h)) * normSq (reluV (M.mulVec h'))
      ∂gaussMat 1 k v ≤ v ^ 2 * (normSq h * normSq h' + 2 * dotp h h' ^ 2) / 2 := by
  obtain ⟨iq, eq⟩ := row_lin_four hv h h'
  set F : Matrix (Fin 1) (Fin k) ℝ → ℝ := fun M =>
    normSq (reluV (M.mulVec h)) * normSq (reluV (M.mulVec h')) with hF
  have mF : Measurable F :=
    (measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right h))).mul
      (measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right h')))
  have hF0 : ∀ M, 0 ≤ F M := fun M => mul_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hpt : ∀ M : Matrix (Fin 1) (Fin k) ℝ,
      F M + F (-M) ≤ dotp (M.mulVec h) (M.mulVec h') ^ 2 := by
    intro M
    simp only [hF, normSq_reluV_one, dotp_one, Matrix.neg_mulVec, Pi.neg_apply]
    exact relu_sq_pair _ _
  have iF : Integrable F (gaussMat 1 k v) := by
    refine Integrable.mono' iq mF.aestronglyMeasurable (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 M)]
    have := hpt M
    have := hF0 (-M)
    linarith
  have mneg : Measurable (fun M : Matrix (Fin 1) (Fin k) ℝ => -M) := measurable_neg
  have iFn : Integrable (fun M => F (-M)) (gaussMat 1 k v) := by
    have h1 : Integrable F ((gaussMat 1 k v).map (fun M => -M)) := by rw [gaussMat_neg]; exact iF
    exact (integrable_map_measure mF.aestronglyMeasurable mneg.aemeasurable).mp h1
  have eFn : ∫ M, F (-M) ∂gaussMat 1 k v = ∫ M, F M ∂gaussMat 1 k v := by
    have h1 := integral_map (μ := gaussMat 1 k v) mneg.aemeasurable mF.aestronglyMeasurable
    rw [gaussMat_neg] at h1
    exact h1.symm
  refine ⟨iF, ?_⟩
  have h2 : ∫ M, (F M + F (-M)) ∂gaussMat 1 k v ≤
      ∫ M : Matrix (Fin 1) (Fin k) ℝ, dotp (M.mulVec h) (M.mulVec h') ^ 2 ∂gaussMat 1 k v :=
    integral_mono (iF.add iFn) iq hpt
  rw [integral_add iF iFn, eFn, eq] at h2
  linarith

/-- **The variance of the layer inner product, sharper**:
`Var ⟨ReLU(M h), ReLU(M h′)⟩ ≤ m·(v²(|h|²|h′|² + 2⟨h, h′⟩²)/2 − (v·Φ(h, h′)/2)²)`. -/
theorem layer_dot_relu_var143 {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * (v * kernelPhi h h')) ^ 2)
      (gaussMat m k v) ∧
    ∫ M, (dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * (v * kernelPhi h h')) ^ 2
      ∂gaussMat m k v ≤ (m : ℝ) * (v ^ 2 * (normSq h * normSq h' + 2 * dotp h h' ^ 2) / 2 -
        (v * kernelPhi h h' / 2) ^ 2) := by
  let f : (Fin k → ℝ) → ℝ := fun w => relu (∑ j, w j * h j) * relu (∑ j, w j * h' j)
  have hf : Measurable f :=
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).mul_const _)).mul
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _))
  let R : (Fin k → ℝ) → Matrix (Fin 1) (Fin k) ℝ → ℝ := fun g M => normSq (reluV (M.mulVec g))
  have hR : ∀ (g : Fin k → ℝ) (M : Matrix (Fin 1) (Fin k) ℝ),
      R g M = relu (∑ j, M 0 j * g j) ^ 2 := by
    intro g M
    change ∑ i : Fin 1, relu ((M.mulVec g) i) ^ 2 = _
    rw [Fin.sum_univ_one]
    rfl
  have key : (fun M : Matrix (Fin 1) (Fin k) ℝ => f (rowOf 0 M) ^ 2) =
      fun M => R h M * R h' M := by
    funext M
    rw [hR, hR]
    simp only [f, rowOf]
    ring
  obtain ⟨hRR, hbound⟩ := row_relu_four_le hv h h'
  change Integrable (fun M => R h M * R h' M) (gaussMat 1 k v) at hRR
  change ∫ M, R h M * R h' M ∂gaussMat 1 k v ≤ _ at hbound
  have hf2 : Integrable (fun ξ => f (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)) := by
    refine (row_integrable_iff (m := 1) v (0 : Fin 1) (hf.pow_const 2)).mp ?_
    have := hRR
    rw [← key] at this
    exact this
  have hE2 : ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      v ^ 2 * (normSq h * normSq h' + 2 * dotp h h' ^ 2) / 2 := by
    have e : ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) =
        ∫ M, R h M * R h' M ∂gaussMat 1 k v := by
      rw [← key]
      exact (row_integral (m := 1) v (0 : Fin 1) (hf.pow_const 2)).symm
    rw [e]
    exact hbound
  have ha : ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) = v * kernelPhi h h' / 2 := by
    have e := row_integral (m := 1) v (0 : Fin 1) hf
    have r := row_formula (m := 1) hv h h' 0
    change 2 * ∫ M, f (rowOf 0 M) ∂gaussMat 1 k v = _ at r
    rw [e] at r
    unfold kernelPhi dotp
    linarith
  have S := rows_sum_sq (m := m) v f hf hf2
  have L := layer_dot_relu (m := m) hv h h'
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) = ∑ i, f (rowOf i M) := fun M => rfl
  rw [← ha]
  set c := (m : ℝ) / 2 * (v * kernelPhi h h') with hc
  set a := ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) with haa
  set E2 := ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) with hE2d
  have hca : c = (m : ℝ) * a := by rw [hc, ha]; ring
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - c) ^ 2) =
      fun M => (∑ i, f (rowOf i M)) ^ 2 -
        2 * c * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) + c ^ 2 := by
    funext M
    rw [← hsum M]
    ring
  rw [hexp]
  have i2 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * c * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) :=
    L.1.const_mul (2 * c)
  have i1 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M)) ^ 2 -
      2 * c * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) := S.1.sub i2
  refine ⟨i1.add (integrable_const _), ?_⟩
  rw [integral_add i1 (integrable_const _), integral_sub S.1 i2,
    integral_const_mul, L.2, S.2, integral_const]
  have hu : (gaussMat m k v).real Set.univ = 1 := by simp
  rw [hu, one_smul]
  rw [hca]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : (m : ℝ) * E2 ≤ (m : ℝ) * (v ^ 2 * (normSq h * normSq h' + 2 * dotp h h' ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hE2 hm0
  nlinarith [h1]

/-- **The variance of the squared norm after a ReLU layer** (exact):
`Var |ReLU(M h)|² = (5m/4)·(v|h|²)²`. -/
theorem layer_relu_sq_var {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * (v * normSq h)) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ,
      (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * (v * normSq h)) ^ 2 ∂gaussMat m k v =
      5 * (m : ℝ) / 4 * (v * normSq h) ^ 2 := by
  obtain ⟨i1, e1⟩ := layer_relu_sq (m := m) hv h
  obtain ⟨i2, e2⟩ := layer_relu_four (m := m) hv h
  set c := (m : ℝ) / 2 * (v * normSq h) with hc
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ => (normSq (reluV (M.mulVec h)) - c) ^ 2) =
      fun M => normSq (reluV (M.mulVec h)) ^ 2 - (2 * c * normSq (reluV (M.mulVec h)) - c ^ 2) := by
    funext M; ring
  have i3 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * c * normSq (reluV (M.mulVec h)) - c ^ 2) (gaussMat m k v) :=
    (i1.const_mul _).sub (integrable_const _)
  rw [hexp]
  refine ⟨i2.sub i3, ?_⟩
  rw [integral_sub i2 i3, integral_sub (i1.const_mul _) (integrable_const _),
    integral_const_mul, e1, e2, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hc]
  ring

lemma mul_sub_sq_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b - c) ^ 2 ≤ (a ^ 2 - c) ^ 2 + (b ^ 2 - c) ^ 2 := by
  rcases le_total a b with hab | hab
  · have h1 : a ^ 2 ≤ a * b := by nlinarith
    have h2 : a * b ≤ b ^ 2 := by nlinarith
    rcases le_total 0 (a * b - c) with h0 | h0
    · nlinarith [sq_nonneg (a ^ 2 - c)]
    · nlinarith [sq_nonneg (b ^ 2 - c)]
  · have h1 : b ^ 2 ≤ a * b := by nlinarith
    have h2 : a * b ≤ a ^ 2 := by nlinarith
    rcases le_total 0 (a * b - c) with h0 | h0
    · nlinarith [sq_nonneg (b ^ 2 - c)]
    · nlinarith [sq_nonneg (a ^ 2 - c)]

/-- For unit `h, h′`: `‖|ReLU(M h)||ReLU(M h′)| − (m/2)v‖₂ ≤ √10/√m·(m/2)v`. -/
theorem relu_nrm_unit_L2 {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - (m : ℝ) / 2 * v)
      (√10 / √(m : ℝ) * ((m : ℝ) / 2 * v)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨i1, e1⟩ := layer_relu_sq_var (m := m) hv h
  obtain ⟨i2, e2⟩ := layer_relu_sq_var (m := m) hv h'
  rw [hh, mul_one] at i1 e1
  rw [hh', mul_one] at i2 e2
  have mP : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - (m : ℝ) / 2 * v) :=
    (((continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h))).mul
      (continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h')))).sub
      measurable_const)
  refine L2le.of_sq_le mP.aestronglyMeasurable (i1.add i2) (fun M => ?_) ?_
  · have := mul_sub_sq_le (c := (m : ℝ) / 2 * v) (nrm_nonneg (reluV (M.mulVec h)))
      (nrm_nonneg (reluV (M.mulVec h')))
    rw [nrm_sq, nrm_sq] at this
    exact this
  · rw [integral_add' i1 i2, e1, e2, mul_pow, div_pow, Real.sq_sqrt hm'.le,
      Real.sq_sqrt (by norm_num)]
    refine le_of_eq ?_
    field_simp
    ring

/-- For unit `h, h′`, `t = ⟨h, h′⟩`:
`‖⟨ReLU(M h), ReLU(M h′)⟩ − (m/2)v·κ(t)‖₂ ≤ √(2 + 4t²)/√m·(m/2)v`. -/
theorem relu_dot_unit_L2 {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * v * kappa (dotp h h'))
      (√(2 + 4 * dotp h h' ^ 2) / √(m : ℝ) * ((m : ℝ) / 2 * v)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨iC, uC⟩ := layer_dot_relu_var143 (m := m) hv h h'
  rw [kernelPhi_eq_psi, psi_unit _ hh hh'] at iC uC
  rw [hh, hh'] at uC
  have mC : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * v * kappa (dotp h h')) :=
    (measurable_dotp_comp (measurable_reluV.comp (measurable_mulVec_right h))
      (measurable_reluV.comp (measurable_mulVec_right h'))).sub measurable_const
  have e : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * (v * kappa (dotp h h')) =
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * v * kappa (dotp h h') :=
    fun M => by ring
  simp only [e] at iC uC
  refine L2le.mk' mC.aestronglyMeasurable iC (uC.trans ?_)
  have eR : (√(2 + 4 * dotp h h' ^ 2) / √(m : ℝ) * ((m : ℝ) / 2 * v)) ^ 2 =
      (2 + 4 * dotp h h' ^ 2) / (m : ℝ) * ((m : ℝ) / 2 * v) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hm'.le, Real.sq_sqrt (by positivity)]
  rw [eR]
  have h0 : 0 ≤ (m : ℝ) * (v * kappa (dotp h h') / 2) ^ 2 := by positivity
  have e2 : (2 + 4 * dotp h h' ^ 2) / (m : ℝ) * ((m : ℝ) / 2 * v) ^ 2 =
      (m : ℝ) * (v ^ 2 * (1 * 1 + 2 * dotp h h' ^ 2) / 2) := by
    field_simp
    ring
  rw [e2]
  linarith

/-- **One ReLU layer in `L²`, unit inputs, sharper constants.** `t = ⟨h, h′⟩`:
`‖Ψ_κ(ReLU(M h), ReLU(M h′)) − (m/2)v·κ(κ(t))‖₂ ≤ (√10·κ(0) + √(2 + 4t²))/√m·(m/2)v`. -/
theorem relu_layer_unit_L2 {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => psi kappa (reluV (M.mulVec h)) (reluV (M.mulVec h')) -
        (m : ℝ) / 2 * v * kappa (kappa (dotp h h')))
      ((√10 * kappa 0 + √(2 + 4 * dotp h h' ^ 2)) / √(m : ℝ) * ((m : ℝ) / 2 * v)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpb0 : 0 ≤ (m : ℝ) / 2 * v := by positivity
  have htm := BstLean.Part133.unit_dot_mem hh hh'
  have ht01 := kappa_mem htm.1 htm.2
  have htabs : |kappa (dotp h h')| ≤ 1 := by rw [abs_of_nonneg ht01.1]; exact ht01.2
  have key := psi_L2_core (μ := gaussMat m k v) kGood_kappa
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h))
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h'))
    (measurable_psi_relu continuous_kappa h h').aestronglyMeasurable hpb0 htabs
    (relu_nrm_unit_L2 hv hm hh hh') (relu_dot_unit_L2 hv hm hh hh')
    (by positivity) (by positivity)
  refine key.congr_bound ?_
  ring

end BstLean.Part143

open BstLean.Part143 in
#print axioms layer_dot_relu_var143
open BstLean.Part143 in
#print axioms layer_relu_sq_var
open BstLean.Part143 in
#print axioms relu_layer_unit_L2
