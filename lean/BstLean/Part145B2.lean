import BstLean.Part145B1
import BstLean.Part143FC
import BstLean.Part143HidC2

/-!
# Part 145, bias of one ReLU layer, file `B2`: the mean of the remainder `rF0`

`rF0 F₁ y y′ = (2/m_F)·Φ_κ(h₁, h₁′) − (2/n)·Φ_{κ∘κ}(y, y′)`, `h₁ = ReLU(F₁ y)` (Part 143). Part 143
has the `L²` bound `rF0_L2` (order `1/√m_F`). This file has the MEAN over `F₁` (order
`m_F^{−3/4}`).

Notation of the proof: `A = |h₁|²`, `B = |h₁′|²`, `C = ⟨h₁, h₁′⟩`, `ℓ = |y′|/|y|`,
`S = (m/2)·v·|y||y′|` (`v = 2/n`), `ρ₀ = κ(cos(y, y′))`. Then `E(ℓA) = E(B/ℓ) = S` and
`E C = ρ₀·S` exactly, and `Ψ_κ(h₁, h₁′) = L_κ(√A·√B, C)`.

* `rowF`, `rowF_moments`, `layer_D_var`: the linear statistic `D = C − ρ₀(ℓA + B/ℓ)/2` has mean
  `0` and `E D² ≤ m·(3/2)·v²(|y||y′|)² = (6/m)·S²`.
* `psi_sandwich_lower`, `psi_sandwich_upper`: the pointwise bounds of `Ψ_κ(h, h′)`.
* `psi_layer_mean`: `|E Ψ_κ(h₁, h₁′) − S·κ(κ(cos(y, y′)))| ≤ S·biasK m`.
* `biasK m = (6/m)^{3/4} + 11/m`, written as `√(√(6/m))³ + 11/m`; `biasK_eq`, `biasK_le`.
* `rF0_bias`: `|E rF0| ≤ (2/n)·biasK(m_F)·(|y|² + |y′|²)/2`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part142 BstLean.Part143

/-! ## The bias constant -/

/-- The bias constant of one ReLU layer of width `m`: `(6/m)^{3/4} + 11/m`. -/
noncomputable def biasK (m : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (6 / (m : ℝ))) ^ 3 + 11 / (m : ℝ)

lemma biasK_nonneg (m : ℕ) : 0 ≤ biasK m := by unfold biasK; positivity

/-- `biasK m = √6·√(√6)/(√m·√(√m)) + 11/m`. -/
theorem biasK_eq (m : ℕ) :
    biasK m = Real.sqrt 6 * Real.sqrt (Real.sqrt 6) /
      (Real.sqrt (m : ℝ) * Real.sqrt (Real.sqrt (m : ℝ))) + 11 / (m : ℝ) := by
  unfold biasK
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  have e1 : ∀ z : ℝ, 0 ≤ z →
      Real.sqrt (Real.sqrt z) ^ 3 = Real.sqrt z * Real.sqrt (Real.sqrt z) := by
    intro z _
    have := Real.sq_sqrt (Real.sqrt_nonneg z)
    calc Real.sqrt (Real.sqrt z) ^ 3 = Real.sqrt (Real.sqrt z) ^ 2 * Real.sqrt (Real.sqrt z) := by
          ring
      _ = Real.sqrt z * Real.sqrt (Real.sqrt z) := by rw [this]
  rw [Real.sqrt_div h6, Real.sqrt_div (Real.sqrt_nonneg 6), div_pow, e1 6 h6,
    e1 (m : ℝ) (Nat.cast_nonneg m)]

/-- **The bias constant in numbers**: `biasK m ≤ 3.84/(√m·√(√m)) + 11/m`, for every `m`. -/
theorem biasK_le (m : ℕ) :
    biasK m ≤ 3.84 / (Real.sqrt (m : ℝ) * Real.sqrt (Real.sqrt (m : ℝ))) + 11 / (m : ℝ) := by
  rw [biasK_eq]
  have h1 : Real.sqrt 6 ≤ 2.4495 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h2 : Real.sqrt (Real.sqrt 6) ≤ 1.5651 := by
    rw [Real.sqrt_le_left (by norm_num)]
    refine h1.trans ?_
    norm_num
  have h3 : Real.sqrt 6 * Real.sqrt (Real.sqrt 6) ≤ 3.84 := by
    calc Real.sqrt 6 * Real.sqrt (Real.sqrt 6) ≤ 2.4495 * 1.5651 :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ 3.84 := by norm_num
  have h4 : 0 ≤ Real.sqrt (m : ℝ) * Real.sqrt (Real.sqrt (m : ℝ)) := by positivity
  have := div_le_div_of_nonneg_right h3 h4
  linarith

/-- The scale `r = (6/m)^{1/4}` of the Young inequalities. -/
lemma biasR_spec {m : ℕ} (hm : 1 ≤ m) :
    0 < Real.sqrt (Real.sqrt (6 / (m : ℝ))) ∧
      Real.sqrt (Real.sqrt (6 / (m : ℝ))) ^ 4 = 6 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h6 : (0 : ℝ) < 6 / (m : ℝ) := by positivity
  refine ⟨Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h6), ?_⟩
  calc Real.sqrt (Real.sqrt (6 / (m : ℝ))) ^ 4
      = (Real.sqrt (Real.sqrt (6 / (m : ℝ))) ^ 2) ^ 2 := by ring
    _ = 6 / (m : ℝ) := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h6.le]

/-! ## A linear combination of six integrable functions -/

lemma int_lin6 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f1 f2 f3 f4 f5 f6 : Ω → ℝ} (i1 : Integrable f1 μ) (i2 : Integrable f2 μ)
    (i3 : Integrable f3 μ) (i4 : Integrable f4 μ) (i5 : Integrable f5 μ) (i6 : Integrable f6 μ)
    (k1 k2 k3 k4 k5 k6 k0 : ℝ) :
    Integrable (fun ω => k1 * f1 ω + k2 * f2 ω + k3 * f3 ω + k4 * f4 ω + k5 * f5 ω + k6 * f6 ω
      + k0) μ ∧
    ∫ ω, (k1 * f1 ω + k2 * f2 ω + k3 * f3 ω + k4 * f4 ω + k5 * f5 ω + k6 * f6 ω + k0) ∂μ =
      k1 * ∫ ω, f1 ω ∂μ + k2 * ∫ ω, f2 ω ∂μ + k3 * ∫ ω, f3 ω ∂μ + k4 * ∫ ω, f4 ω ∂μ +
        k5 * ∫ ω, f5 ω ∂μ + k6 * ∫ ω, f6 ω ∂μ + k0 := by
  have j2 : Integrable (fun ω => k1 * f1 ω + k2 * f2 ω) μ :=
    (i1.const_mul k1).add (i2.const_mul k2)
  have j3 : Integrable (fun ω => k1 * f1 ω + k2 * f2 ω + k3 * f3 ω) μ :=
    j2.add (i3.const_mul k3)
  have j4 : Integrable (fun ω => k1 * f1 ω + k2 * f2 ω + k3 * f3 ω + k4 * f4 ω) μ :=
    j3.add (i4.const_mul k4)
  have j5 : Integrable (fun ω => k1 * f1 ω + k2 * f2 ω + k3 * f3 ω + k4 * f4 ω + k5 * f5 ω) μ :=
    j4.add (i5.const_mul k5)
  have j6 : Integrable (fun ω => k1 * f1 ω + k2 * f2 ω + k3 * f3 ω + k4 * f4 ω + k5 * f5 ω +
      k6 * f6 ω) μ := j5.add (i6.const_mul k6)
  refine ⟨j6.add (integrable_const k0), ?_⟩
  rw [integral_add j6 (integrable_const k0), integral_add j5 (i6.const_mul k6),
    integral_add j4 (i5.const_mul k5), integral_add j3 (i4.const_mul k4),
    integral_add j2 (i3.const_mul k3), integral_add (i1.const_mul k1) (i2.const_mul k2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const]
  simp

/-! ## One row -/

variable {m k : ℕ}

/-- The function of one row `w` whose sum over the rows is `D = C − ρ(ℓA + B/ℓ)/2`. -/
noncomputable def rowF (y y' : Fin k → ℝ) (l ρ : ℝ) : (Fin k → ℝ) → ℝ := fun w =>
  relu (∑ j, w j * y j) * relu (∑ j, w j * y' j) -
    ρ * ((l * relu (∑ j, w j * y j) ^ 2 + relu (∑ j, w j * y' j) ^ 2 / l) / 2)

lemma measurable_rowF (y y' : Fin k → ℝ) (l ρ : ℝ) : Measurable (rowF y y' l ρ) := by
  have h1 : ∀ z : Fin k → ℝ, Measurable (fun w : Fin k → ℝ => relu (∑ j, w j * z j)) := fun z =>
    measurable_relu.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _)
  unfold rowF
  have h2 : Measurable (fun w : Fin k → ℝ =>
      (l * relu (∑ j, w j * y j) ^ 2 + relu (∑ j, w j * y' j) ^ 2 / l) / 2) :=
    ((((h1 y).pow_const 2).const_mul l).add (((h1 y').pow_const 2).div_const l)).div_const 2
  exact ((h1 y).mul (h1 y')).sub (h2.const_mul ρ)

lemma rowF_sum (y y' : Fin k → ℝ) (l ρ : ℝ) (M : Matrix (Fin m) (Fin k) ℝ) :
    ∑ i, rowF y y' l ρ (rowOf i M) =
      dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) -
        ρ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2) := by
  have e1 : dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) =
      ∑ i, relu (∑ j, rowOf i M j * y j) * relu (∑ j, rowOf i M j * y' j) := rfl
  have e2 : ∀ z : Fin k → ℝ, normSq (reluV (M.mulVec z)) =
      ∑ i, relu (∑ j, rowOf i M j * z j) ^ 2 := fun z => rfl
  rw [e1, e2 y, e2 y']
  unfold rowF
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_div]

lemma rowF_sq_le {l ρ r r' : ℝ} (hl : 0 < l) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : 0 ≤ r)
    (hr' : 0 ≤ r') :
    (r * r' - ρ * ((l * r ^ 2 + r' ^ 2 / l) / 2)) ^ 2 ≤
      (l ^ 2 * (r ^ 2) ^ 2 + (r' ^ 2) ^ 2 / l ^ 2) / 2 := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = l * r ^ 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = r' ^ 2 / l := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have ht0 : 0 ≤ r * r' := mul_nonneg hr hr'
  have ht1 : r * r' ≤ (u + w) / 2 := by
    have h1 : 0 ≤ (l * r - r') ^ 2 / (2 * l) := by positivity
    have e : (u + w) / 2 - r * r' = (l * r - r') ^ 2 / (2 * l) := by
      rw [hu, hw]
      field_simp
      ring
    linarith
  have hh : 0 ≤ (u + w) / 2 := by positivity
  have hρh0 : 0 ≤ ρ * ((u + w) / 2) := mul_nonneg hρ0 hh
  have hρh1 : ρ * ((u + w) / 2) ≤ (u + w) / 2 := by nlinarith
  have hmid : (r * r' - ρ * ((u + w) / 2)) ^ 2 ≤ ((u + w) / 2) ^ 2 := by
    apply sq_le_sq'
    · linarith
    · linarith
  have hfin : ((u + w) / 2) ^ 2 ≤ (u ^ 2 + w ^ 2) / 2 := by nlinarith [sq_nonneg (u - w)]
  have eu : l ^ 2 * (r ^ 2) ^ 2 = u ^ 2 := by rw [hu]; ring
  have ew : (r' ^ 2) ^ 2 / l ^ 2 = w ^ 2 := by rw [hw, div_pow]
  rw [← hu, ← hw, eu, ew]
  exact hmid.trans hfin

/-- **The moments of one row.** `ℓ > 0`, `|y′|² = ℓ²|y|²`, `ρ ∈ [0, 1]` and
`Φ(y, y′) = ρ·ℓ|y|²` (then `ℓ|y|² = |y||y′|`). The row function has mean `0`, and its second
moment is at most `(3/2)·v²·(ℓ|y|²)²`. -/
lemma rowF_moments {v : ℝ} (hv : 0 ≤ v) (y y' : Fin k → ℝ) {l ρ : ℝ} (hl : 0 < l)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hN' : normSq y' = l ^ 2 * normSq y)
    (hker : kernelPhi y y' = ρ * (l * normSq y)) :
    Integrable (fun ξ => rowF y y' l ρ (Real.sqrt v • ξ)) (stdGauss (Fin k)) ∧
    ∫ ξ, rowF y y' l ρ (Real.sqrt v • ξ) ∂stdGauss (Fin k) = 0 ∧
    Integrable (fun ξ => rowF y y' l ρ (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)) ∧
    ∫ ξ, rowF y y' l ρ (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      3 / 2 * v ^ 2 * (l * normSq y) ^ 2 := by
  have hf := measurable_rowF y y' l ρ
  have hrow1 : ∀ M : Matrix (Fin 1) (Fin k) ℝ, rowF y y' l ρ (rowOf 0 M) =
      dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) -
        ρ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2) := by
    intro M
    rw [← rowF_sum, Fin.sum_univ_one]
  obtain ⟨iA, eA⟩ := layer_relu_sq (m := 1) hv y
  obtain ⟨iB, eB⟩ := layer_relu_sq (m := 1) hv y'
  obtain ⟨iC, eC⟩ := layer_dot_relu (m := 1) hv y y'
  obtain ⟨iA4, eA4⟩ := layer_relu_four (m := 1) hv y
  obtain ⟨iB4, eB4⟩ := layer_relu_four (m := 1) hv y'
  have hl0 : l ≠ 0 := hl.ne'
  -- the first moment
  have iP : Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ =>
      ρ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2))
      (gaussMat 1 k v) :=
    (((iA.const_mul l).add (iB.div_const l)).div_const 2).const_mul ρ
  have iF1 : Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ => rowF y y' l ρ (rowOf 0 M))
      (gaussMat 1 k v) := by
    simp_rw [hrow1]
    exact iC.sub iP
  have i1 := (row_integrable_iff (m := 1) v (0 : Fin 1) hf).mp iF1
  have e1 : ∫ ξ, rowF y y' l ρ (Real.sqrt v • ξ) ∂stdGauss (Fin k) = 0 := by
    rw [← row_integral (m := 1) v (0 : Fin 1) hf]
    simp_rw [hrow1]
    rw [integral_sub iC iP, integral_const_mul, integral_div,
      integral_add (iA.const_mul l) (iB.div_const l), integral_const_mul, integral_div, eA, eB,
      eC, hN', hker]
    push_cast
    field_simp
    ring
  -- the second moment
  have iG : Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ =>
      (l ^ 2 * normSq (reluV (M.mulVec y)) ^ 2 + normSq (reluV (M.mulVec y')) ^ 2 / l ^ 2) / 2)
      (gaussMat 1 k v) :=
    ((iA4.const_mul (l ^ 2)).add (iB4.div_const (l ^ 2))).div_const 2
  have hpt : ∀ M : Matrix (Fin 1) (Fin k) ℝ, rowF y y' l ρ (rowOf 0 M) ^ 2 ≤
      (l ^ 2 * normSq (reluV (M.mulVec y)) ^ 2 + normSq (reluV (M.mulVec y')) ^ 2 / l ^ 2) / 2 := by
    intro M
    have h := rowF_sq_le hl hρ0 hρ1 (relu_nonneg (∑ j, M 0 j * y j))
      (relu_nonneg (∑ j, M 0 j * y' j))
    rw [normSq_reluV_one, normSq_reluV_one]
    exact h
  have iF2 : Integrable (fun M : Matrix (Fin 1) (Fin k) ℝ => rowF y y' l ρ (rowOf 0 M) ^ 2)
      (gaussMat 1 k v) := by
    refine Integrable.mono' iG
      ((hf.pow_const 2).comp (measurable_rowOf (0 : Fin 1))).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun M => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt M
  have i2 : Integrable (fun ξ => rowF y y' l ρ (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)) :=
    (row_integrable_iff (m := 1) v (0 : Fin 1) (hf.pow_const 2)).mp iF2
  have e2 : ∫ ξ, rowF y y' l ρ (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) =
      ∫ M : Matrix (Fin 1) (Fin k) ℝ, rowF y y' l ρ (rowOf 0 M) ^ 2 ∂gaussMat 1 k v :=
    (row_integral (m := 1) v (0 : Fin 1) (hf.pow_const 2)).symm
  refine ⟨i1, e1, i2, ?_⟩
  rw [e2]
  refine (integral_mono iF2 iG hpt).trans (le_of_eq ?_)
  rw [integral_div, integral_add (iA4.const_mul _) (iB4.div_const _), integral_const_mul,
    integral_div, eA4, eB4, hN']
  push_cast
  field_simp
  ring

/-- **The second moment of the linear statistic `D = C − ρ(ℓA + B/ℓ)/2`** of a Gaussian layer:
`E D² ≤ m·(3/2)·v²·(ℓ|y|²)²`. -/
lemma layer_D_var {v : ℝ} (hv : 0 ≤ v) (y y' : Fin k → ℝ) {l ρ : ℝ} (hl : 0 < l)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hN' : normSq y' = l ^ 2 * normSq y)
    (hker : kernelPhi y y' = ρ * (l * normSq y)) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) -
        ρ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2)) ^ 2)
      (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ,
      (dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) -
        ρ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2)) ^ 2
      ∂gaussMat m k v ≤ (m : ℝ) * (3 / 2 * v ^ 2 * (l * normSq y) ^ 2) := by
  obtain ⟨i1, e1, i2, u2⟩ := rowF_moments hv y y' hl hρ0 hρ1 hN' hker
  have h := rows_var_le (m := m) v (rowF y y' l ρ) (measurable_rowF y y' l ρ) i1 e1 i2 u2
  simp only [mul_zero, sub_zero, rowF_sum] at h
  exact h

/-! ## The pointwise bounds of `Ψ_κ(h, h′)` -/

/-- `Ψ_κ(h, h′) = S·L_κ(√x·√y, C/S)` with `x = ℓ|h|²/S`, `y = (|h′|²/ℓ)/S`. -/
lemma psi_scaled (h h' : Fin m → ℝ) {S l : ℝ} (hS : 0 < S) (hl : 0 < l) :
    0 ≤ l * normSq h / S ∧ 0 ≤ normSq h' / l / S ∧
    |dotp h h' / S| ≤ Real.sqrt (l * normSq h / S) * Real.sqrt (normSq h' / l / S) ∧
    psi kappa h h' = S * persp kappa
      (Real.sqrt (l * normSq h / S) * Real.sqrt (normSq h' / l / S)) (dotp h h' / S) := by
  have hA := normSq_nonneg h
  have hB := normSq_nonneg h'
  have hx : 0 ≤ l * normSq h / S := by positivity
  have hy : 0 ≤ normSq h' / l / S := by positivity
  have hsq : Real.sqrt (l * normSq h / S) * Real.sqrt (normSq h' / l / S) =
      nrm h * nrm h' / S := by
    rw [← Real.sqrt_mul hx]
    have e : l * normSq h / S * (normSq h' / l / S) = normSq h * normSq h' / S ^ 2 := by
      field_simp
    rw [e, Real.sqrt_div (mul_nonneg hA hB), Real.sqrt_sq hS.le, Real.sqrt_mul hA]
    rfl
  refine ⟨hx, hy, ?_, ?_⟩
  · rw [hsq, abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right (abs_dotp_le_nrm h h') hS.le
  · rw [hsq, psi_eq_persp]
    unfold persp
    rw [div_div_div_cancel_right₀ hS.ne']
    field_simp

/-- **The lower bound.** `s ↦ a + b·s` is a supporting line of `κ` with `a ≥ 0`. -/
lemma psi_sandwich_lower (h h' : Fin m → ℝ) {S l a b : ℝ} (hS : 0 < S) (hl : 0 < l)
    (ha0 : 0 ≤ a) (hab : ∀ s ∈ Icc (-1 : ℝ) 1, a + b * s ≤ kappa s) :
    a * l / 2 * normSq h + a / (2 * l) * normSq h' + b * dotp h h' +
      -(a * l ^ 2 / S) * (normSq h - S / l) ^ 2 +
      -(a / (l ^ 2 * S)) * (normSq h' - S * l) ^ 2 ≤ psi kappa h h' := by
  obtain ⟨hx, hy, hc, hpsi⟩ := psi_scaled h h' hS hl
  have h1 := mul_le_mul_of_nonneg_left (persp_sqrt_lower ha0 hab hx hy hc) hS.le
  rw [← hpsi] at h1
  refine le_trans (le_of_eq ?_) h1
  field_simp
  ring

/-- **The upper bound.** The reference cosine is `ρ₀ ∈ [0, 1]`; `r > 0` is a free scale. -/
lemma psi_sandwich_upper (h h' : Fin m → ℝ) {S l ρ₀ r : ℝ} (hS : 0 < S) (hl : 0 < l)
    (h0 : 0 ≤ ρ₀) (h1 : ρ₀ ≤ 1) (hr : 0 < r) :
    psi kappa h h' ≤
      (kappa ρ₀ - kg ρ₀ * ρ₀) * l / 2 * normSq h +
      (kappa ρ₀ - kg ρ₀ * ρ₀) / (2 * l) * normSq h' + kg ρ₀ * dotp h h' +
      l ^ 2 / (2 * S) * (normSq h - S / l) ^ 2 +
      1 / (2 * l ^ 2 * S) * (normSq h' - S * l) ^ 2 +
      (3 / (4 * r) + 1) / S *
        (dotp h h' - ρ₀ * ((l * normSq h + normSq h' / l) / 2)) ^ 2 +
      S * (r ^ 3 / 4) := by
  obtain ⟨hx, hy, hc, hpsi⟩ := psi_scaled h h' hS hl
  have h2 := mul_le_mul_of_nonneg_left (persp_sqrt_upper h0 h1 hr hx hy hc) hS.le
  rw [← hpsi] at h2
  refine le_trans h2 (le_of_eq ?_)
  field_simp
  ring

/-! ## The mean of `Ψ_κ` of one ReLU layer -/

/-- `Ψ_κ(ReLU(M y), ReLU(M y′))` is integrable. -/
lemma psi_layer_integrable {v : ℝ} (hv : 0 ≤ v) (y y' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi kappa (reluV (M.mulVec y)) (reluV (M.mulVec y'))) (gaussMat m k v) := by
  obtain ⟨iA, -⟩ := layer_relu_sq (m := m) hv y
  obtain ⟨iB, -⟩ := layer_relu_sq (m := m) hv y'
  have c1 : Continuous (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (reluV (M.mulVec y), reluV (M.mulVec y'))) :=
    (continuous_reluV.comp (Continuous.matrix_mulVec continuous_id continuous_const)).prodMk
      (continuous_reluV.comp (Continuous.matrix_mulVec continuous_id continuous_const))
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi kappa (reluV (M.mulVec y)) (reluV (M.mulVec y'))) :=
    (measurable_psi continuous_kappa).comp c1.measurable
  refine Integrable.mono' (iA.add iB) hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun M => ?_
  have h0 := psi_nonneg kGood_kappa (reluV (M.mulVec y)) (reluV (M.mulVec y'))
  have h1 := psi_le_nrm kGood_kappa (reluV (M.mulVec y)) (reluV (M.mulVec y'))
  have h2 := nrm_mul_le (reluV (M.mulVec y)) (reluV (M.mulVec y'))
  have h3 := normSq_nonneg (reluV (M.mulVec y))
  have h4 := normSq_nonneg (reluV (M.mulVec y'))
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  simp only [Pi.add_apply]
  linarith

/-- The core of `psi_layer_mean`, with the scales as variables: `|y| = a`, `|y′| = ℓ·a`,
`S = (m/2)·v·a·(ℓa)`, `ρ₀ = κ(cos(y, y′))`, `r⁴ = 6/m`. -/
lemma psi_layer_mean_core {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) (y y' : Fin k → ℝ) {a l S ρ₀ r : ℝ}
    (ha : 0 < a) (hl : 0 < l) (hN : normSq y = a * a) (hN' : normSq y' = (l * a) * (l * a))
    (hS : S = (m : ℝ) / 2 * (v * (a * (l * a)))) (hρ : ρ₀ = kappa (cosv y y')) (hr : 0 < r)
    (hr4 : r ^ 4 = 6 / (m : ℝ)) :
    |∫ M : Matrix (Fin m) (Fin k) ℝ, psi kappa (reluV (M.mulVec y)) (reluV (M.mulVec y'))
      ∂gaussMat m k v - S * kappa ρ₀| ≤ S * (r ^ 3 + 11 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hS0 : 0 < S := by rw [hS]; positivity
  have hna : nrm y = a := by unfold nrm; rw [hN, Real.sqrt_mul_self ha.le]
  have hna' : nrm y' = l * a := by
    unfold nrm; rw [hN', Real.sqrt_mul_self (by positivity)]
  obtain ⟨hρ0, hρ1⟩ : 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 := by
    rw [hρ]; exact kappa_mem (cosv_mem y y').1 (cosv_mem y y').2
  have hker : kernelPhi y y' = ρ₀ * (l * normSq y) := by
    rw [kernelPhi_eq_psi, hN, hρ]
    unfold psi
    rw [hna, hna']
    ring
  have hN'' : normSq y' = l ^ 2 * normSq y := by rw [hN, hN']; ring
  have hAb : (m : ℝ) / 2 * (v * normSq y) = S / l := by rw [hS, hN]; field_simp
  have hBb : (m : ℝ) / 2 * (v * normSq y') = S * l := by rw [hS, hN']; ring
  -- the moments of the linear statistics
  obtain ⟨iA, eA⟩ := layer_relu_sq (m := m) hv.le y
  obtain ⟨iB, eB⟩ := layer_relu_sq (m := m) hv.le y'
  obtain ⟨iC, eC⟩ := layer_dot_relu (m := m) hv.le y y'
  obtain ⟨iVA, eVA⟩ := layer_relu_sq_var (m := m) hv.le y
  obtain ⟨iVB, eVB⟩ := layer_relu_sq_var (m := m) hv.le y'
  obtain ⟨iD, eD⟩ := layer_D_var (m := m) hv.le y y' hl hρ0 hρ1 hN'' hker
  have ipsi := psi_layer_integrable (m := m) hv.le y y'
  have eVA' : 5 * (m : ℝ) / 4 * (v * normSq y) ^ 2 = 5 / (m : ℝ) * S ^ 2 / l ^ 2 := by
    rw [hS, hN]; field_simp; ring
  have eVB' : 5 * (m : ℝ) / 4 * (v * normSq y') ^ 2 = 5 / (m : ℝ) * S ^ 2 * l ^ 2 := by
    rw [hS, hN']; field_simp; ring
  have eD' : (m : ℝ) * (3 / 2 * v ^ 2 * (l * normSq y) ^ 2) = 6 / (m : ℝ) * S ^ 2 := by
    rw [hS, hN]; field_simp; ring
  have eC' : (m : ℝ) / 2 * (v * kernelPhi y y') = S * ρ₀ := by
    rw [hker, hS, hN]; ring
  rw [hAb] at eA iVA eVA
  rw [hBb] at eB iVB eVB
  rw [eVA'] at eVA
  rw [eVB'] at eVB
  rw [eD'] at eD
  rw [eC'] at eC
  have hD0 : 0 ≤ ∫ M : Matrix (Fin m) (Fin k) ℝ,
      (dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) -
        ρ₀ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2)) ^ 2
      ∂gaussMat m k v := integral_nonneg fun M => sq_nonneg _
  have hSm : 0 ≤ S / (m : ℝ) := by positivity
  rw [abs_le]
  constructor
  · -- the lower side
    obtain ⟨a_, b, ha0, ha1, hb0, hb1, heq, hab⟩ :=
      kGood_kappa.support (t := ρ₀) ⟨by linarith, hρ1⟩
    have ha1' : a_ ≤ 1 := ha1.trans (kGood_kappa.le_one KGood.zero_mem)
    obtain ⟨iL, eL⟩ := int_lin6 iA iB iC iVA iVB iD (a_ * l / 2) (a_ / (2 * l)) b
      (-(a_ * l ^ 2 / S)) (-(a_ / (l ^ 2 * S))) 0 0
    have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ,
        a_ * l / 2 * normSq (reluV (M.mulVec y)) + a_ / (2 * l) * normSq (reluV (M.mulVec y'))
          + b * dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) +
          -(a_ * l ^ 2 / S) * (normSq (reluV (M.mulVec y)) - S / l) ^ 2 +
          -(a_ / (l ^ 2 * S)) * (normSq (reluV (M.mulVec y')) - S * l) ^ 2 +
          0 * (dotp (reluV (M.mulVec y)) (reluV (M.mulVec y')) -
            ρ₀ * ((l * normSq (reluV (M.mulVec y)) + normSq (reluV (M.mulVec y')) / l) / 2)) ^ 2
          + 0 ≤ psi kappa (reluV (M.mulVec y)) (reluV (M.mulVec y')) := fun M => by
      have h := psi_sandwich_lower (reluV (M.mulVec y)) (reluV (M.mulVec y')) hS0 hl ha0 hab
      linarith
    have hmono := integral_mono iL ipsi hpt
    rw [eL, eA, eB, eC, eVA, eVB] at hmono
    have e : a_ * l / 2 * (S / l) + a_ / (2 * l) * (S * l) + b * (S * ρ₀) +
        -(a_ * l ^ 2 / S) * (5 / (m : ℝ) * S ^ 2 / l ^ 2) +
        -(a_ / (l ^ 2 * S)) * (5 / (m : ℝ) * S ^ 2 * l ^ 2) =
        S * (a_ + b * ρ₀) - a_ * (10 * (S / (m : ℝ))) := by
      field_simp
      ring
    have h10 := mul_le_mul_of_nonneg_right ha1' (by positivity : 0 ≤ 10 * (S / (m : ℝ)))
    have hr3 : 0 ≤ S * r ^ 3 := by positivity
    have e11 : S * (r ^ 3 + 11 / (m : ℝ)) = S * r ^ 3 + 11 * (S / (m : ℝ)) := by ring
    rw [heq] at e
    linarith
  · -- the upper side
    obtain ⟨iL, eL⟩ := int_lin6 iA iB iC iVA iVB iD ((kappa ρ₀ - kg ρ₀ * ρ₀) * l / 2)
      ((kappa ρ₀ - kg ρ₀ * ρ₀) / (2 * l)) (kg ρ₀) (l ^ 2 / (2 * S)) (1 / (2 * l ^ 2 * S))
      ((3 / (4 * r) + 1) / S) (S * (r ^ 3 / 4))
    have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ,
        psi kappa (reluV (M.mulVec y)) (reluV (M.mulVec y')) ≤ _ := fun M =>
      psi_sandwich_upper (reluV (M.mulVec y)) (reluV (M.mulVec y')) hS0 hl hρ0 hρ1 hr
    have hmono := integral_mono ipsi iL hpt
    rw [eL, eA, eB, eC, eVA, eVB] at hmono
    have hk6 : 0 ≤ (3 / (4 * r) + 1) / S := by positivity
    have hDm := mul_le_mul_of_nonneg_left eD hk6
    have e6a : (3 / (4 * r) + 1) / S * (6 / (m : ℝ) * S ^ 2) =
        3 / (4 * r) * (6 / (m : ℝ)) * S + 6 * (S / (m : ℝ)) := by
      field_simp
    have e6b : 3 / (4 * r) * (6 / (m : ℝ)) * S = 3 / 4 * (S * r ^ 3) := by
      rw [← hr4]
      field_simp
    have e6 : (3 / (4 * r) + 1) / S * (6 / (m : ℝ) * S ^ 2) =
        3 / 4 * (S * r ^ 3) + 6 * (S / (m : ℝ)) := by
      rw [e6a, e6b]
    rw [e6] at hDm
    have e : (kappa ρ₀ - kg ρ₀ * ρ₀) * l / 2 * (S / l) +
        (kappa ρ₀ - kg ρ₀ * ρ₀) / (2 * l) * (S * l) + kg ρ₀ * (S * ρ₀) +
        l ^ 2 / (2 * S) * (5 / (m : ℝ) * S ^ 2 / l ^ 2) +
        1 / (2 * l ^ 2 * S) * (5 / (m : ℝ) * S ^ 2 * l ^ 2) =
        S * kappa ρ₀ + 5 * (S / (m : ℝ)) := by
      field_simp
      ring
    have e11 : S * (r ^ 3 + 11 / (m : ℝ)) = S * r ^ 3 + 11 * (S / (m : ℝ)) := by ring
    have e4 : S * (r ^ 3 / 4) = 1 / 4 * (S * r ^ 3) := by ring
    linarith

/-- **The mean of `Ψ_κ` after one ReLU layer.** `M` is a Gaussian `m × k` matrix with entry
variance `v > 0`; `y, y′ ≠ 0`; `S = (m/2)·v·|y||y′|`. Then
`|E Ψ_κ(ReLU(M y), ReLU(M y′)) − S·κ(κ(cos(y, y′)))| ≤ S·biasK m`. -/
theorem psi_layer_mean {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) (y y' : Fin k → ℝ)
    (ha : 0 < nrm y) (ha' : 0 < nrm y') :
    |∫ M : Matrix (Fin m) (Fin k) ℝ, psi kappa (reluV (M.mulVec y)) (reluV (M.mulVec y'))
      ∂gaussMat m k v - (m : ℝ) / 2 * (v * (nrm y * nrm y')) * kappa (kappa (cosv y y'))| ≤
      (m : ℝ) / 2 * (v * (nrm y * nrm y')) * biasK m := by
  obtain ⟨hr, hr4⟩ := biasR_spec hm
  have hl : 0 < nrm y' / nrm y := div_pos ha' ha
  have hla : nrm y' / nrm y * nrm y = nrm y' := by field_simp
  have h := psi_layer_mean_core (m := m) hv hm y y' (a := nrm y) (l := nrm y' / nrm y)
    (S := (m : ℝ) / 2 * (v * (nrm y * nrm y'))) (ρ₀ := kappa (cosv y y')) ha hl
    (nrm_mul_self y).symm (by rw [hla]; exact (nrm_mul_self y').symm) (by rw [hla]) rfl hr hr4
  unfold biasK
  exact h

/-! ## The mean of `rF0` -/

variable {n mF : ℕ}

/-- The mean of `rF0` through the mean of `Ψ_κ`: the norm part of `Φ_κ` has an exact mean. -/
lemma rF0_integral (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ => rF0 F₁ y y') (gaussMat mF n (2 / (n : ℝ))) ∧
    ∫ F₁, rF0 F₁ y y' ∂gaussMat mF n (2 / (n : ℝ)) =
      2 / (n : ℝ) * (nrm y * nrm y' * kappa (kappa (cosv y y'))) -
        2 / (mF : ℝ) * ∫ F₁ : Matrix (Fin mF) (Fin n) ℝ,
          psi kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y')) ∂gaussMat mF n (2 / (n : ℝ)) := by
  have hm0 : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  obtain ⟨iA, eA⟩ := layer_relu_sq (m := mF) hv y
  obtain ⟨iB, eB⟩ := layer_relu_sq (m := mF) hv y'
  have ipsi := psi_layer_integrable (m := mF) hv y y'
  have efun : (fun F₁ : Matrix (Fin mF) (Fin n) ℝ => rF0 F₁ y y') = fun F₁ =>
      2 / (mF : ℝ) * ((normSq (reluV (F₁.mulVec y)) + normSq (reluV (F₁.mulVec y'))) / 2 -
        psi kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y'))) -
        2 / (n : ℝ) * phiD (kappa ∘ kappa) y y' := by
    funext F₁
    rfl
  rw [efun]
  have i1 : Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ =>
      (normSq (reluV (F₁.mulVec y)) + normSq (reluV (F₁.mulVec y'))) / 2)
      (gaussMat mF n (2 / (n : ℝ))) := (iA.add iB).div_const 2
  have i3 : Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ =>
      (normSq (reluV (F₁.mulVec y)) + normSq (reluV (F₁.mulVec y'))) / 2 -
        psi kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y'))) (gaussMat mF n (2 / (n : ℝ))) :=
    i1.sub ipsi
  have i2 : Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ =>
      2 / (mF : ℝ) * ((normSq (reluV (F₁.mulVec y)) + normSq (reluV (F₁.mulVec y'))) / 2 -
        psi kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y')))) (gaussMat mF n (2 / (n : ℝ))) :=
    i3.const_mul (2 / (mF : ℝ))
  refine ⟨i2.sub (integrable_const _), ?_⟩
  rw [integral_sub i2 (integrable_const _), integral_const_mul, integral_sub i1 ipsi,
    integral_div, integral_add iA iB, eA, eB, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have e : phiD (kappa ∘ kappa) y y' =
      (normSq y + normSq y') / 2 - nrm y * nrm y' * kappa (kappa (cosv y y')) := rfl
  rw [e]
  field_simp
  ring

lemma psi_zero_left {G : ℝ → ℝ} {ι : Type*} [Fintype ι] (h h' : ι → ℝ) (hz : nrm h = 0) :
    psi G h h' = 0 := by
  unfold psi
  rw [hz]
  ring

lemma psi_zero_right {G : ℝ → ℝ} {ι : Type*} [Fintype ι] (h h' : ι → ℝ) (hz : nrm h' = 0) :
    psi G h h' = 0 := by
  unfold psi
  rw [hz]
  ring

lemma nrm_relu_layer_zero (M : Matrix (Fin m) (Fin k) ℝ) {y : Fin k → ℝ} (hz : nrm y = 0) :
    nrm (reluV (M.mulVec y)) = 0 := by
  have h0 : normSq y = 0 := by
    have := nrm_mul_self y
    rw [hz] at this
    linarith
  rw [normSq_eq_zero h0]
  have e : reluV (M.mulVec (0 : Fin k → ℝ)) = 0 := by
    funext i
    simp [reluV, relu, Matrix.mulVec_zero]
  rw [e]
  simp [nrm, normSq]

/-- **The bias of one ReLU layer.** The mean over `F₁` of the remainder `rF0` of the link of `F`
is of order `m_F^{−3/4}`: `|E rF0| ≤ (2/n)·biasK(m_F)·(|y|² + |y′|²)/2`. -/
theorem rF0_bias (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ => rF0 F₁ y y') (gaussMat mF n (2 / (n : ℝ))) ∧
    |∫ F₁, rF0 F₁ y y' ∂gaussMat mF n (2 / (n : ℝ))| ≤
      2 / (n : ℝ) * (biasK mF * ((normSq y + normSq y') / 2)) := by
  have hm0 : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  obtain ⟨iR, eR⟩ := rF0_integral hn hmF y y'
  refine ⟨iR, ?_⟩
  have hK := biasK_nonneg mF
  have hq := nrm_mul_le y y'
  have hq0 := nrm_mul_nonneg y y'
  have hrhs : 0 ≤ 2 / (n : ℝ) * (biasK mF * ((normSq y + normSq y') / 2)) := by
    have : 0 ≤ (normSq y + normSq y') / 2 := hq0.trans hq
    positivity
  rw [eR]
  by_cases hz : nrm y = 0 ∨ nrm y' = 0
  · have hzero : ∀ F₁ : Matrix (Fin mF) (Fin n) ℝ,
        psi kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y')) = 0 := by
      intro F₁
      rcases hz with h | h
      · exact psi_zero_left _ _ (nrm_relu_layer_zero F₁ h)
      · exact psi_zero_right _ _ (nrm_relu_layer_zero F₁ h)
    simp_rw [hzero]
    have hq00 : nrm y * nrm y' = 0 := by
      rcases hz with h | h <;> rw [h] <;> ring
    rw [hq00]
    simpa using hrhs
  · have hz1 : nrm y ≠ 0 := fun h => hz (Or.inl h)
    have hz2 : nrm y' ≠ 0 := fun h => hz (Or.inr h)
    have ha : 0 < nrm y := lt_of_le_of_ne (nrm_nonneg y) (Ne.symm hz1)
    have ha' : 0 < nrm y' := lt_of_le_of_ne (nrm_nonneg y') (Ne.symm hz2)
    have hM := psi_layer_mean (m := mF) hv hmF y y' ha ha'
    obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ F₁ : Matrix (Fin mF) (Fin n) ℝ,
        psi kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y')) ∂gaussMat mF n (2 / (n : ℝ)) :=
      ⟨_, rfl⟩
    rw [← hI] at hM ⊢
    have e : 2 / (n : ℝ) * (nrm y * nrm y' * kappa (kappa (cosv y y'))) - 2 / (mF : ℝ) * I =
        -(2 / (mF : ℝ)) * (I - (mF : ℝ) / 2 * (2 / (n : ℝ) * (nrm y * nrm y')) *
          kappa (kappa (cosv y y'))) := by
      field_simp
      ring
    rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 / (mF : ℝ))]
    have h1 := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ 2 / (mF : ℝ))
    have e2 : 2 / (mF : ℝ) * ((mF : ℝ) / 2 * (2 / (n : ℝ) * (nrm y * nrm y')) * biasK mF) =
        2 / (n : ℝ) * (biasK mF * (nrm y * nrm y')) := by
      field_simp
    rw [e2] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hK) hv.le

end BstLean.Part145

open BstLean.Part145 in
#print axioms kappa_tangent_ge
open BstLean.Part145 in
#print axioms kappa_tangent_le
open BstLean.Part145 in
#print axioms psi_layer_mean
open BstLean.Part145 in
#print axioms biasK_le
open BstLean.Part145 in
#print axioms rF0_bias
