import BstLean.Part167Plane

/-!
# Part 167 (file `Lam`): the 2×2 matrix `Λ` of the plane coordinates (sub-lemma 4)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: proof of Lemma `t7:p07:LJ`, second paragraph. `ξ₁, ξ₂` are independent standard Gaussian
vectors of `ℝ^m` (the standardized plane coordinates of the rows of `A₂`), `D_j = 1{ξ₁_j > 0}`,
`Λ = Σ_j D_j ξ_j ξ_jᵀ` with entries `Λ₁₁ = Σ D_j ξ₁_j²`, `Λ₂₂ = Σ D_j ξ₂_j²`,
`Λ₁₂ = Σ D_j ξ₁_j ξ₂_j`, and `λ⁺ = max(Λ₁₁, Λ₂₂) + |Λ₁₂|` (`λ_max(Λ) ≤ λ⁺`).

* **`lam_det`**: `(Σ D_j y_j ξ₁_j)² + (Σ D_j y_j ξ₂_j)² ≤ |y|²·λ⁺` (Cauchy–Schwarz).
* **`mgf_L11`, `mgf_L22`**: `E Λ₁₁^k ≤ (m/2 + 4k)^k` and `E Λ₂₂^k ≤ (m/2 + 4k)^k` for
  `m ≥ 200k` (moment generating function at `t = k/(m/2 + 4k)`, the symmetry `z ↦ −z`, and
  `(1 − 2t)^{−1/2} ≤ 1 + t + 2t²`). This replaces the paper's Hoeffding count moment `b^{bin}`.
* **`mom_L12`**: `E Λ₁₂^{64} ≤ 64^{32}·(m/2 + 128)^{32}` (Gaussian given `ξ₁`).
* **`mom_lamP`**: `E (λ⁺)^{64} ≤ (2^{1/64}(m/2 + 256) + 8√(m/2 + 128))^{64}` in the form
  `E(λ⁺)^{64} ≤ BL m ^ 64` (`m ≥ 12 800`).
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask mask_of_pos mask_of_nonpos mask_sq mask_nonneg measurable_mask)

variable {m : ℕ}

/-- `Λ₁₁ = Σ_j D_j ξ₁_j²`. -/
noncomputable def L11 (ξ₁ : Fin m → ℝ) : ℝ := ∑ j, mask (ξ₁ j) * ξ₁ j ^ 2
/-- `Λ₂₂ = Σ_j D_j ξ₂_j²`. -/
noncomputable def L22 (ξ₁ ξ₂ : Fin m → ℝ) : ℝ := ∑ j, mask (ξ₁ j) * ξ₂ j ^ 2
/-- `Λ₁₂ = Σ_j D_j ξ₁_j ξ₂_j`. -/
noncomputable def L12 (ξ₁ ξ₂ : Fin m → ℝ) : ℝ := ∑ j, mask (ξ₁ j) * ξ₁ j * ξ₂ j
/-- `λ⁺ = max(Λ₁₁, Λ₂₂) + |Λ₁₂|`. -/
noncomputable def lamP (ξ₁ ξ₂ : Fin m → ℝ) : ℝ := max (L11 ξ₁) (L22 ξ₁ ξ₂) + |L12 ξ₁ ξ₂|

lemma L11_nonneg (ξ₁ : Fin m → ℝ) : 0 ≤ L11 ξ₁ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mask_nonneg _) (sq_nonneg _)
lemma L22_nonneg (ξ₁ ξ₂ : Fin m → ℝ) : 0 ≤ L22 ξ₁ ξ₂ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mask_nonneg _) (sq_nonneg _)
lemma lamP_nonneg (ξ₁ ξ₂ : Fin m → ℝ) : 0 ≤ lamP ξ₁ ξ₂ :=
  add_nonneg ((L11_nonneg ξ₁).trans (le_max_left _ _)) (abs_nonneg _)

/-! ## §1 The deterministic bound -/

/-- **`|Σ_j D_j y_j ξ_j|² ≤ |y|²·λ⁺`.** -/
theorem lam_det (y ξ₁ ξ₂ : Fin m → ℝ) :
    (∑ j, mask (ξ₁ j) * y j * ξ₁ j) ^ 2 + (∑ j, mask (ξ₁ j) * y j * ξ₂ j) ^ 2 ≤
      normSq y * lamP ξ₁ ξ₂ := by
  set P1 := ∑ j, mask (ξ₁ j) * y j * ξ₁ j
  set P2 := ∑ j, mask (ξ₁ j) * y j * ξ₂ j
  set S := P1 ^ 2 + P2 ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have eS : S = ∑ j, (mask (ξ₁ j) * y j) * (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) := by
    have : ∀ j, (mask (ξ₁ j) * y j) * (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) =
        P1 * (mask (ξ₁ j) * y j * ξ₁ j) + P2 * (mask (ξ₁ j) * y j * ξ₂ j) := by
      intro j
      have h2 : mask (ξ₁ j) * mask (ξ₁ j) = mask (ξ₁ j) := by rw [← sq, mask_sq]
      linear_combination (y j * (P1 * ξ₁ j + P2 * ξ₂ j)) * h2
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS]; ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => mask (ξ₁ j) * y j)
    (fun j => mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j))
  rw [← eS] at hCS
  have hA : ∑ j, (mask (ξ₁ j) * y j) ^ 2 ≤ normSq y := by
    unfold normSq
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, mask_sq]
    have : mask (ξ₁ j) ≤ 1 := by unfold mask; split_ifs <;> norm_num
    nlinarith [sq_nonneg (y j), mask_nonneg (ξ₁ j)]
  have hB : ∑ j, (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) ^ 2 =
      P1 ^ 2 * L11 ξ₁ + 2 * (P1 * P2) * L12 ξ₁ ξ₂ + P2 ^ 2 * L22 ξ₁ ξ₂ := by
    have e : ∀ j, (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) ^ 2 =
        P1 ^ 2 * (mask (ξ₁ j) * ξ₁ j ^ 2) + 2 * (P1 * P2) * (mask (ξ₁ j) * ξ₁ j * ξ₂ j) +
          P2 ^ 2 * (mask (ξ₁ j) * ξ₂ j ^ 2) := fun j => by rw [mul_pow, mask_sq]; ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  have hB2 : P1 ^ 2 * L11 ξ₁ + 2 * (P1 * P2) * L12 ξ₁ ξ₂ + P2 ^ 2 * L22 ξ₁ ξ₂ ≤
      S * lamP ξ₁ ξ₂ := by
    unfold lamP
    have h1 : P1 ^ 2 * L11 ξ₁ + P2 ^ 2 * L22 ξ₁ ξ₂ ≤ S * max (L11 ξ₁) (L22 ξ₁ ξ₂) := by
      have := le_max_left (L11 ξ₁) (L22 ξ₁ ξ₂)
      have := le_max_right (L11 ξ₁) (L22 ξ₁ ξ₂)
      nlinarith [sq_nonneg P1, sq_nonneg P2]
    have h2 : 2 * (P1 * P2) * L12 ξ₁ ξ₂ ≤ S * |L12 ξ₁ ξ₂| := by
      have h3 : 2 * (P1 * P2) ≤ S := by nlinarith [sq_nonneg (P1 - P2)]
      have h4 : -(2 * (P1 * P2)) ≤ S := by nlinarith [sq_nonneg (P1 + P2)]
      rcases le_or_gt 0 (L12 ξ₁ ξ₂) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]; nlinarith
    nlinarith
  rw [hB] at hCS
  have hlam := lamP_nonneg ξ₁ ξ₂
  have hS2 : S ^ 2 ≤ normSq y * (S * lamP ξ₁ ξ₂) :=
    hCS.trans (mul_le_mul hA hB2 (by
      rw [← hB]; exact Finset.sum_nonneg fun j _ => sq_nonneg _) (normSq_nonneg y))
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (normSq_nonneg y) hlam
  · have : S * S ≤ S * (normSq y * lamP ξ₁ ξ₂) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-! ## §2 One coordinate: the symmetry `z ↦ −z` -/

lemma gauss_int_neg (f : ℝ → ℝ) :
    ∫ z, f (-z) ∂gaussianReal 0 1 = ∫ z, f z ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (MeasurableEquiv.neg ℝ) = gaussianReal 0 1 := by
    have := gaussianReal_map_neg (μ := 0) (v := 1)
    rw [neg_zero] at this
    exact this
  have h := integral_map_equiv (MeasurableEquiv.neg ℝ) (μ := gaussianReal 0 1) f
  rw [hmap] at h
  exact h.symm

/-- `φ₁(t) = (1 − 2t)^{−1/2}`. -/
noncomputable def phi1 (t : ℝ) : ℝ := (√(1 - 2 * t))⁻¹

lemma phi1_ge_one {t : ℝ} (ht : 0 ≤ t) (ht2 : t < 1 / 2) : 1 ≤ phi1 t := by
  unfold phi1
  have h0 : 0 < 1 - 2 * t := by linarith
  rw [one_le_inv₀ (Real.sqrt_pos.mpr h0)]
  calc √(1 - 2 * t) ≤ √1 := Real.sqrt_le_sqrt (by linarith)
    _ = 1 := Real.sqrt_one

lemma mask_add_neg {z : ℝ} (hz : z ≠ 0) : mask z + mask (-z) = 1 := by
  rcases lt_or_gt_of_ne hz with h | h
  · rw [mask_of_nonpos h.le, mask_of_pos (by linarith)]; ring
  · rw [mask_of_pos h, mask_of_nonpos (by linarith)]; ring

lemma measurable_exp_mask (t : ℝ) :
    Measurable (fun z : ℝ => exp (t * mask z * z ^ 2)) :=
  continuous_exp.measurable.comp ((measurable_const.mul measurable_mask).mul
    (measurable_id.pow_const 2))

/-- `E exp(t·D·z²) = (1 + φ₁(t))/2` for one coordinate (`D = 1{z > 0}`). -/
lemma int_exp_mask {t : ℝ} (ht : 0 ≤ t) (ht2 : t < 1 / 2) :
    Integrable (fun z : ℝ => exp (t * mask z * z ^ 2)) (gaussianReal 0 1) ∧
    ∫ z, exp (t * mask z * z ^ 2) ∂gaussianReal 0 1 = (1 + phi1 t) / 2 := by
  obtain ⟨hI, hE⟩ := BstLean.Part152.gauss_mgf_sq ht2
  have hle : ∀ z : ℝ, exp (t * mask z * z ^ 2) ≤ exp (t * z ^ 2) := by
    intro z
    apply exp_le_exp.mpr
    have h1 : mask z ≤ 1 := by unfold mask; split_ifs <;> norm_num
    have := mask_nonneg z
    nlinarith [sq_nonneg z, mul_nonneg ht (sq_nonneg z)]
  have hInt : Integrable (fun z : ℝ => exp (t * mask z * z ^ 2)) (gaussianReal 0 1) :=
    hI.mono' (measurable_exp_mask t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hle z)
  refine ⟨hInt, ?_⟩
  have hsum : ∀ z : ℝ, exp (t * mask z * z ^ 2) + exp (t * mask (-z) * (-z) ^ 2) =
      1 + exp (t * z ^ 2) := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [mask_of_nonpos]
    · rcases lt_or_gt_of_ne hz with h | h
      · rw [mask_of_nonpos h.le, mask_of_pos (by linarith)]; simp
      · rw [mask_of_pos h, mask_of_nonpos (by linarith)]; simp
        ring
  have hneg := gauss_int_neg (fun z => exp (t * mask z * z ^ 2))
  have hInt' : Integrable (fun z : ℝ => exp (t * mask (-z) * (-z) ^ 2)) (gaussianReal 0 1) := by
    have : (fun z : ℝ => exp (t * mask (-z) * (-z) ^ 2)) =
        (fun z => exp (t * mask z * z ^ 2)) ∘ (MeasurableEquiv.neg ℝ) := rfl
    rw [this]
    have hmap : (gaussianReal 0 1).map (MeasurableEquiv.neg ℝ) = gaussianReal 0 1 := by
      have := gaussianReal_map_neg (μ := 0) (v := 1)
      rw [neg_zero] at this; exact this
    rw [← (MeasurableEquiv.neg ℝ).measurableEmbedding.integrable_map_iff, hmap]
    exact hInt
  have h2 : ∫ z, exp (t * mask z * z ^ 2) ∂gaussianReal 0 1 +
      ∫ z, exp (t * mask (-z) * (-z) ^ 2) ∂gaussianReal 0 1 = 1 + phi1 t := by
    rw [← integral_add hInt hInt']
    simp_rw [hsum]
    rw [integral_add (integrable_const _) hI, hE]
    simp [phi1]
  rw [hneg] at h2
  linarith

lemma mask_le_one (z : ℝ) : mask z ≤ 1 := by unfold mask; split_ifs <;> norm_num

lemma integrable_mask : Integrable mask (gaussianReal 0 1) :=
  (integrable_const (1 : ℝ)).mono' measurable_mask.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mask_nonneg z)]; exact mask_le_one z)

lemma int_mask_le : ∫ z, mask z ∂gaussianReal 0 1 ≤ 1 / 2 := by
  have hneg := gauss_int_neg mask
  have hInt' : Integrable (fun z : ℝ => mask (-z)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' (measurable_mask.comp measurable_neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mask_nonneg _)]; exact mask_le_one _)
  have hle : ∫ z, (mask z + mask (-z)) ∂gaussianReal 0 1 ≤ ∫ _z, (1 : ℝ) ∂gaussianReal 0 1 := by
    refine integral_mono (integrable_mask.add hInt') (integrable_const _) fun z => ?_
    by_cases hz : z = 0
    · subst hz; simp [mask_of_nonpos]
    · exact le_of_eq (mask_add_neg hz)
  rw [integral_add integrable_mask hInt', hneg] at hle
  simp at hle
  linarith

/-- `ψ(z) = (1 − 2t·D(z))^{−1/2}`; `E ψ ≤ (1 + φ₁(t))/2`. -/
lemma int_psi_mask {t : ℝ} (ht : 0 ≤ t) (ht2 : t < 1 / 2) :
    Integrable (fun z : ℝ => (√(1 - 2 * (t * mask z)))⁻¹) (gaussianReal 0 1) ∧
    ∫ z, (√(1 - 2 * (t * mask z)))⁻¹ ∂gaussianReal 0 1 ≤ (1 + phi1 t) / 2 := by
  have hval : ∀ z : ℝ, (√(1 - 2 * (t * mask z)))⁻¹ = 1 + mask z * (phi1 t - 1) := by
    intro z
    unfold phi1
    by_cases h : 0 < z
    · rw [mask_of_pos h]; ring_nf
    · rw [mask_of_nonpos (not_lt.mp h)]; simp
  simp_rw [hval]
  have hI : Integrable (fun z : ℝ => 1 + mask z * (phi1 t - 1)) (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_mask.mul_const _)
  refine ⟨hI, ?_⟩
  rw [integral_add (integrable_const _) (integrable_mask.mul_const _), integral_mul_const]
  have h1 := phi1_ge_one ht ht2
  have h2 := int_mask_le
  simp
  nlinarith

/-! ## §3 The moment generating functions of `Λ₁₁` and `Λ₂₂` -/

/-- `(M/e)^k·((1 + φ₁(k/M))/2)^m ≤ M^k` for `M = m/2 + 4k`, `m ≥ 200k`. -/
lemma mgf_num {k : ℕ} (hk : 1 ≤ k) (hm : (200 * k : ℝ) ≤ m) :
    ((m / 2 + 4 * k : ℝ) / exp 1) ^ k * ((1 + phi1 (k / (m / 2 + 4 * k))) / 2) ^ m ≤
      (m / 2 + 4 * k : ℝ) ^ k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set M : ℝ := m / 2 + 4 * k with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := k / M with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 100 := by
    rw [ht, div_le_iff₀ hM0]; nlinarith
  -- `φ₁(t) ≤ 1 + t + 2t²`
  have hphi : phi1 t ≤ 1 + t + 2 * t ^ 2 := by
    unfold phi1
    have h0 : 0 < 1 - 2 * t := by linarith
    have hs : 0 < √(1 - 2 * t) := Real.sqrt_pos.mpr h0
    rw [inv_le_iff_one_le_mul₀ hs]
    have hsq : 1 ≤ ((1 + t + 2 * t ^ 2) * √(1 - 2 * t)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h0.le]
      nlinarith [mul_nonneg ht0 ht0, mul_nonneg (mul_nonneg ht0 ht0) ht0,
        mul_nonneg (mul_nonneg (mul_nonneg ht0 ht0) ht0) ht0]
    have hpos : 0 ≤ (1 + t + 2 * t ^ 2) * √(1 - 2 * t) := by positivity
    nlinarith [hsq, hpos]
  have hbase : (1 + phi1 t) / 2 ≤ exp (t / 2 + t ^ 2) := by
    have := Real.add_one_le_exp (t / 2 + t ^ 2)
    linarith
  have hpow : ((1 + phi1 t) / 2) ^ m ≤ exp (k) := by
    have h1 : ((1 + phi1 t) / 2) ^ m ≤ exp (t / 2 + t ^ 2) ^ m :=
      pow_le_pow_left₀ (by have := phi1_ge_one ht0 (by linarith); positivity) hbase m
    refine h1.trans ?_
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    -- `m(t/2 + t²) ≤ k`
    have e : (m : ℝ) * (t / 2 + t ^ 2) = k * ((m : ℝ) * (M + 2 * k) / (2 * M ^ 2)) := by
      rw [ht]; field_simp
    rw [e]
    have h2 : (m : ℝ) * (M + 2 * k) / (2 * M ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity), hM]; nlinarith
    nlinarith
  calc (M / exp 1) ^ k * ((1 + phi1 t) / 2) ^ m ≤ (M / exp 1) ^ k * exp k :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = M ^ k := by rw [div_pow, ← Real.exp_nat_mul, mul_one]; field_simp

/-- The product formula `E exp(t Σ_j a_j ξ_j²) = Π_j (1 − 2t a_j)^{−1/2}`. -/
lemma int_exp_quad (a : Fin m → ℝ) {t : ℝ} (hta : ∀ j, t * a j < 1 / 2) :
    Integrable (fun ξ : Fin m → ℝ => exp (t * ∑ j, a j * ξ j ^ 2)) (stdGauss (Fin m)) ∧
    ∫ ξ, exp (t * ∑ j, a j * ξ j ^ 2) ∂stdGauss (Fin m) = ∏ j, (√(1 - 2 * (t * a j)))⁻¹ := by
  have hprod : ∀ ξ : Fin m → ℝ, exp (t * ∑ j, a j * ξ j ^ 2) = ∏ j, exp ((t * a j) * ξ j ^ 2) := by
    intro ξ
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by ring_nf
  simp_rw [hprod]
  unfold stdGauss
  refine ⟨Integrable.fintype_prod (f := fun j z => exp ((t * a j) * z ^ 2))
    (fun j => (BstLean.Part152.gauss_mgf_sq (hta j)).1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun j z => exp ((t * a j) * z ^ 2))]
  exact Finset.prod_congr rfl fun j _ => (BstLean.Part152.gauss_mgf_sq (hta j)).2

lemma measurable_L11 : Measurable (L11 (m := m)) := by
  unfold L11
  exact Finset.measurable_sum _ fun j _ => (measurable_mask.comp (measurable_pi_apply j)).mul
    ((measurable_pi_apply j).pow_const 2)

lemma measurable_L22 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => L22 p.1 p.2) := by
  unfold L22
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_mask.comp ((measurable_pi_apply j).comp measurable_fst)).mul
    (((measurable_pi_apply j).comp measurable_snd).pow_const 2)

lemma measurable_L12 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => L12 p.1 p.2) := by
  unfold L12
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_mask.comp ((measurable_pi_apply j).comp measurable_fst)).mul
    ((measurable_pi_apply j).comp measurable_fst)).mul ((measurable_pi_apply j).comp measurable_snd)

/-- **`E Λ₁₁^k ≤ (m/2 + 4k)^k`** (`m ≥ 200k`). -/
theorem mgf_L11 {k : ℕ} (hk : 1 ≤ k) (hm : (200 * k : ℝ) ≤ m) :
    ∫⁻ ξ, ENNReal.ofReal (L11 ξ ^ k) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((m / 2 + 4 * k : ℝ) ^ k) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set M : ℝ := m / 2 + 4 * k with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := k / M with ht
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t < 1 / 2 := by rw [ht, div_lt_iff₀ hM0]; nlinarith
  obtain ⟨hI1, hE1⟩ := int_exp_mask ht0 ht2
  have hprod : ∀ ξ : Fin m → ℝ, exp (t * L11 ξ) = ∏ j, exp (t * mask (ξ j) * ξ j ^ 2) := by
    intro ξ; unfold L11
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by ring_nf
  have hInt : Integrable (fun ξ : Fin m → ℝ => (M / exp 1) ^ k * exp (t * L11 ξ))
      (stdGauss (Fin m)) := by
    refine Integrable.const_mul ?_ _
    simp_rw [hprod]
    unfold stdGauss
    exact Integrable.fintype_prod (f := fun _ z => exp (t * mask z * z ^ 2)) (fun _ => hI1)
  have hval : ∫ ξ, (M / exp 1) ^ k * exp (t * L11 ξ) ∂stdGauss (Fin m) =
      (M / exp 1) ^ k * ((1 + phi1 t) / 2) ^ m := by
    rw [integral_const_mul]
    congr 1
    simp_rw [hprod]
    unfold stdGauss
    rw [integral_fintype_prod_eq_pow (fun z => exp (t * mask z * z ^ 2)), hE1, Fintype.card_fin]
  have hpt : ∀ ξ : Fin m → ℝ, ENNReal.ofReal (L11 ξ ^ k) ≤
      ENNReal.ofReal ((M / exp 1) ^ k * exp (t * L11 ξ)) := fun ξ =>
    ENNReal.ofReal_le_ofReal (BstLean.Part166.pow_le_exp_bound (L11_nonneg ξ) hM0 k)
  refine (lintegral_mono hpt).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun ξ => by positivity), hval]
  exact ENNReal.ofReal_le_ofReal (mgf_num hk hm)

/-- **`E Λ₂₂^k ≤ (m/2 + 4k)^k`** (`m ≥ 200k`; `ξ₂` given `ξ₁`, then the binomial gates). -/
theorem mgf_L22 {k : ℕ} (hk : 1 ≤ k) (hm : (200 * k : ℝ) ≤ m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ k) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((m / 2 + 4 * k : ℝ) ^ k) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set M : ℝ := m / 2 + 4 * k with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := k / M with ht
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t < 1 / 2 := by rw [ht, div_lt_iff₀ hM0]; nlinarith
  have hta : ∀ (ξ₁ : Fin m → ℝ) j, t * mask (ξ₁ j) < 1 / 2 := fun ξ₁ j =>
    lt_of_le_of_lt (mul_le_of_le_one_right ht0 (mask_le_one _)) ht2
  -- inner integral
  have hin : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ k) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((M / exp 1) ^ k * ∏ j, (√(1 - 2 * (t * mask (ξ₁ j))))⁻¹) := by
    intro ξ₁
    obtain ⟨hI, hE⟩ := int_exp_quad (fun j => mask (ξ₁ j)) (hta ξ₁)
    have hpt : ∀ ξ₂ : Fin m → ℝ, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ k) ≤
        ENNReal.ofReal ((M / exp 1) ^ k * exp (t * ∑ j, mask (ξ₁ j) * ξ₂ j ^ 2)) := fun ξ₂ =>
      ENNReal.ofReal_le_ofReal (BstLean.Part166.pow_le_exp_bound (L22_nonneg ξ₁ ξ₂) hM0 k)
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)
      (ae_of_all _ fun ξ => by positivity), integral_const_mul, hE]
  refine (lintegral_mono hin).trans ?_
  obtain ⟨hIψ, hEψ⟩ := int_psi_mask ht0 ht2
  have hInt : Integrable (fun ξ₁ : Fin m → ℝ =>
      (M / exp 1) ^ k * ∏ j, (√(1 - 2 * (t * mask (ξ₁ j))))⁻¹) (stdGauss (Fin m)) := by
    refine Integrable.const_mul ?_ _
    unfold stdGauss
    exact Integrable.fintype_prod (f := fun _ z => (√(1 - 2 * (t * mask z)))⁻¹) (fun _ => hIψ)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun ξ => by positivity),
    integral_const_mul]
  unfold stdGauss
  rw [integral_fintype_prod_eq_pow (fun z => (√(1 - 2 * (t * mask z)))⁻¹), Fintype.card_fin]
  refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left ?_ (by positivity)).trans
    (mgf_num hk hm))
  exact pow_le_pow_left₀ (integral_nonneg fun z => by positivity) hEψ m

/-! ## §4 `Λ₁₂` and `λ⁺` -/

/-- **`E Λ₁₂^{64} ≤ 64^{32}(m/2 + 128)^{32}`** (`m ≥ 6400`): given `ξ₁`, `Λ₁₂ = ⟨ξ₂, D ξ₁⟩` is
Gaussian with variance `Λ₁₁`. -/
theorem mom_L12 (hm : (6400 : ℝ) ≤ m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((64 : ℝ) ^ 32 * (m / 2 + 128) ^ 32) := by
  have hm1 : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  have : Nonempty (Fin m) := ⟨⟨0, hm1⟩⟩
  have hin : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64) ∂stdGauss (Fin m) =
      ENNReal.ofReal (BstLean.Part162.gmom 64 * L11 ξ₁ ^ 32) := by
    intro ξ₁
    set v : Fin m → ℝ := fun j => mask (ξ₁ j) * ξ₁ j with hv
    have hL : ∀ ξ₂, L12 ξ₁ ξ₂ = ξ₂ ⬝ᵥ v := by
      intro ξ₂; unfold L12; simp only [dotProduct, hv]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hvv : v ⬝ᵥ v = L11 ξ₁ := by
      unfold L11; simp only [dotProduct, hv]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := mask_sq (ξ₁ j); rw [sq] at this
      calc mask (ξ₁ j) * ξ₁ j * (mask (ξ₁ j) * ξ₁ j) = (mask (ξ₁ j) * mask (ξ₁ j)) * ξ₁ j ^ 2 := by
            ring
        _ = mask (ξ₁ j) * ξ₁ j ^ 2 := by rw [this]
    simp_rw [hL]
    have hInt : Integrable (fun y : Fin m → ℝ => |y ⬝ᵥ v| ^ 64) (stdGauss (Fin m)) := by
      refine ((BstLean.Part162.integrable_radF_pow (d := m) 64).const_mul
        (BstLean.Part153.nrm v ^ 64)).mono'
        ((((continuous_id.dotProduct continuous_const).abs).pow 64).measurable.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := BstLean.Part153.abs_dot_le_nrm y v
      have h2 : BstLean.Part153.nrm y = BstLean.Part53.radF53 y := rfl
      rw [h2] at h1
      calc |y ⬝ᵥ v| ^ 64 ≤ (BstLean.Part53.radF53 y * BstLean.Part153.nrm v) ^ 64 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 64
        _ = BstLean.Part153.nrm v ^ 64 * BstLean.Part53.radF53 y ^ 64 := by ring
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun y => by positivity),
      BstLean.Part162.gauss_dot_mom v 64, hvv]
    congr 2
    rw [show (64 : ℕ) = 2 * 32 by norm_num, pow_mul, Real.sq_sqrt (L11_nonneg ξ₁)]
  simp_rw [hin]
  have hg : BstLean.Part162.gmom 64 ≤ (64 : ℝ) ^ 32 := by
    have := BstLean.Part162.gmom_even_le 32; norm_num at this ⊢; exact this
  have hg0 := BstLean.Part162.gmom_nonneg 64
  calc ∫⁻ ξ₁, ENNReal.ofReal (BstLean.Part162.gmom 64 * L11 ξ₁ ^ 32) ∂stdGauss (Fin m)
      = ENNReal.ofReal (BstLean.Part162.gmom 64) *
          ∫⁻ ξ₁, ENNReal.ofReal (L11 ξ₁ ^ 32) ∂stdGauss (Fin m) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun ξ₁ => ENNReal.ofReal_mul hg0
    _ ≤ ENNReal.ofReal ((64 : ℝ) ^ 32) * ENNReal.ofReal ((m / 2 + 4 * (32 : ℕ) : ℝ) ^ 32) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hg)
          (mgf_L11 (k := 32) (by norm_num) (by push_cast; linarith))
    _ = ENNReal.ofReal ((64 : ℝ) ^ 32 * (m / 2 + 128) ^ 32) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; norm_num

/-- `(a + b)^p ≤ (A + B)^{p−1}(a^p/A^{p−1} + b^p/B^{p−1})` (convexity of `x^p`). -/
lemma pow_add_split {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) (hB : 0 < B) (p : ℕ) :
    (a + b) ^ (p + 1) ≤ (A + B) ^ p * (a ^ (p + 1) / A ^ p + b ^ (p + 1) / B ^ p) := by
  have hAB : 0 < A + B := by positivity
  set l := A / (A + B)
  set u := B / (A + B)
  have hl : 0 ≤ l := by positivity
  have hu : 0 ≤ u := by positivity
  have hlu : l + u = 1 := by simp only [l, u]; field_simp
  have hx : 0 ≤ a * (A + B) / A := by positivity
  have hy : 0 ≤ b * (A + B) / B := by positivity
  have hc := (convexOn_pow (p + 1)).2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hl hu hlu
  simp only [smul_eq_mul] at hc
  have e1 : l * (a * (A + B) / A) + u * (b * (A + B) / B) = a + b := by
    simp only [l, u]; field_simp
  rw [e1] at hc
  refine hc.trans (le_of_eq ?_)
  simp only [l, u]
  rw [div_pow, div_pow, mul_pow, mul_pow, pow_succ (A + B) p, pow_succ A p, pow_succ B p]
  field_simp

/-- The bound of `‖λ⁺‖_{64}`: `2^{1/64}(m/2 + 256) + 8√(m/2 + 128)`. -/
noncomputable def BL (m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 : ℝ) / 64) * ((m : ℝ) / 2 + 256) + 8 * √((m : ℝ) / 2 + 128)

/-- **`E (λ⁺)^{64} ≤ BL(m)^{64}`** (`m ≥ 12 800`). -/
theorem mom_lamP (hm : (12800 : ℝ) ≤ m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 64) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (BL m ^ 64) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (m : ℝ) / 2 + 256 := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = (m : ℝ) / 2 + 128 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 : ℝ) ^ ((1 : ℝ) / 64) * M := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 8 * √M' := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  have hM'0 : 0 < M' := by rw [hM']; positivity
  have hA0 : 0 < A := by rw [hA]; positivity
  have hB0 : 0 < B := by rw [hB]; positivity
  have hA64 : A ^ 64 = 2 * M ^ 64 := by
    rw [hA, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 64)), ← Real.rpow_mul (by norm_num)]
    norm_num
  have hB64 : B ^ 64 = (64 : ℝ) ^ 32 * M' ^ 32 := by
    rw [hB, mul_pow, show (64 : ℕ) = 2 * 32 by norm_num, pow_mul (√M'), Real.sq_sqrt hM'0.le]
    norm_num
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = A + B := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  have hBL : BL m = T := by rw [hT, hA, hB, hM, hM']; rfl
  obtain ⟨c₁, hc1⟩ : ∃ c : ℝ, c = T ^ 63 / A ^ 63 := ⟨_, rfl⟩
  obtain ⟨c₂, hc2⟩ : ∃ c : ℝ, c = T ^ 63 / B ^ 63 := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := by rw [hc1]; positivity
  have hc₂ : 0 ≤ c₂ := by rw [hc2]; positivity
  have hpt : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 64) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (L11 ξ₁ ^ 64) +
        ENNReal.ofReal c₁ * ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 64) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64) := by
    intro ξ₁ ξ₂
    have p1 : 0 ≤ c₁ * L11 ξ₁ ^ 64 := mul_nonneg hc₁ (pow_nonneg (L11_nonneg ξ₁) 64)
    have p2 : 0 ≤ c₁ * L22 ξ₁ ξ₂ ^ 64 := mul_nonneg hc₁ (pow_nonneg (L22_nonneg ξ₁ ξ₂) 64)
    have p3 : 0 ≤ c₂ * |L12 ξ₁ ξ₂| ^ 64 := mul_nonneg hc₂ (pow_nonneg (abs_nonneg _) 64)
    rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
      ← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ max (L11 ξ₁) (L22 ξ₁ ξ₂) := (L11_nonneg ξ₁).trans (le_max_left _ _)
    have h1 := pow_add_split h0 (abs_nonneg (L12 ξ₁ ξ₂)) hA0 hB0 63
    rw [← hT] at h1
    have h2 : max (L11 ξ₁) (L22 ξ₁ ξ₂) ^ 64 ≤ L11 ξ₁ ^ 64 + L22 ξ₁ ξ₂ ^ 64 := by
      rcases le_total (L11 ξ₁) (L22 ξ₁ ξ₂) with h | h
      · rw [max_eq_right h]; have := pow_nonneg (L11_nonneg ξ₁) 64; linarith
      · rw [max_eq_left h]; have := pow_nonneg (L22_nonneg ξ₁ ξ₂) 64; linarith
    unfold lamP
    refine h1.trans ?_
    have e : T ^ 63 * (max (L11 ξ₁) (L22 ξ₁ ξ₂) ^ 64 / A ^ 63 + |L12 ξ₁ ξ₂| ^ 64 / B ^ 63) =
        c₁ * max (L11 ξ₁) (L22 ξ₁ ξ₂) ^ 64 + c₂ * |L12 ξ₁ ξ₂| ^ 64 := by
      rw [hc1, hc2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h2 hc₁
    linarith
  have hm11 : ∀ ξ₁ : Fin m → ℝ, Measurable (fun ξ₂ : Fin m → ℝ => ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 64)) :=
    fun ξ₁ => ENNReal.measurable_ofReal.comp ((measurable_L22.comp
      (measurable_const.prodMk measurable_id)).pow_const 64)
  have hm12 : ∀ ξ₁ : Fin m → ℝ, Measurable (fun ξ₂ : Fin m → ℝ =>
      ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64)) :=
    fun ξ₁ => ENNReal.measurable_ofReal.comp ((measurable_L12.comp
      (measurable_const.prodMk measurable_id)).abs.pow_const 64)
  have hinner : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 64) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (L11 ξ₁ ^ 64) +
        ENNReal.ofReal c₁ * ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 64) ∂stdGauss (Fin m) +
        ENNReal.ofReal c₂ * ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64) ∂stdGauss (Fin m) := by
    intro ξ₁
    refine (lintegral_mono (hpt ξ₁)).trans (le_of_eq ?_)
    rw [lintegral_add_right _ ((hm12 ξ₁).const_mul _),
      lintegral_add_right _ ((hm11 ξ₁).const_mul _), lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (hm11 ξ₁), lintegral_const_mul _ (hm12 ξ₁)]
  have hmo1 : Measurable (fun ξ₁ : Fin m → ℝ => ENNReal.ofReal (L11 ξ₁ ^ 64)) :=
    ENNReal.measurable_ofReal.comp (measurable_L11.pow_const 64)
  have hmo2 : Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 64) ∂stdGauss (Fin m)) :=
    (ENNReal.measurable_ofReal.comp (measurable_L22.pow_const 64)).lintegral_prod_right'
  have hmo3 : Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64) ∂stdGauss (Fin m)) :=
    (ENNReal.measurable_ofReal.comp (measurable_L12.abs.pow_const 64)).lintegral_prod_right'
  refine (lintegral_mono hinner).trans ?_
  rw [lintegral_add_right _ (hmo3.const_mul _), lintegral_add_right _ (hmo2.const_mul _),
    lintegral_const_mul _ hmo1, lintegral_const_mul _ hmo2, lintegral_const_mul _ hmo3]
  have b1 := mgf_L11 (m := m) (k := 64) (by norm_num) (by push_cast; linarith)
  have b2 := mgf_L22 (m := m) (k := 64) (by norm_num) (by push_cast; linarith)
  have b3 := mom_L12 (m := m) (by linarith)
  have e4 : ((m : ℝ) / 2 + 4 * (64 : ℕ)) = M := by rw [hM]; norm_num
  rw [e4] at b1 b2
  rw [← hM'] at b3
  have q1 : 0 ≤ c₁ * (M ^ 64) := mul_nonneg hc₁ (pow_nonneg hM0.le 64)
  have q3 : 0 ≤ c₂ * ((64 : ℝ) ^ 32 * M' ^ 32) :=
    mul_nonneg hc₂ (mul_nonneg (by norm_num) (pow_nonneg hM'0.le 32))
  calc ENNReal.ofReal c₁ * ∫⁻ ξ₁, ENNReal.ofReal (L11 ξ₁ ^ 64) ∂stdGauss (Fin m) +
        ENNReal.ofReal c₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (L22 ξ₁ ξ₂ ^ 64) ∂stdGauss (Fin m)
          ∂stdGauss (Fin m) +
        ENNReal.ofReal c₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (|L12 ξ₁ ξ₂| ^ 64) ∂stdGauss (Fin m)
          ∂stdGauss (Fin m)
      ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (M ^ 64) + ENNReal.ofReal c₁ * ENNReal.ofReal (M ^ 64) +
          ENNReal.ofReal c₂ * ENNReal.ofReal ((64 : ℝ) ^ 32 * M' ^ 32) := by
        gcongr
    _ = ENNReal.ofReal (c₁ * M ^ 64 + c₁ * M ^ 64 + c₂ * ((64 : ℝ) ^ 32 * M' ^ 32)) := by
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
          ← ENNReal.ofReal_add q1 q1, ← ENNReal.ofReal_add (add_nonneg q1 q1) q3]
    _ = ENNReal.ofReal (BL m ^ 64) := by
        congr 1
        have k1 : c₁ * M ^ 64 + c₁ * M ^ 64 = c₁ * A ^ 64 := by rw [hA64]; ring
        rw [k1, ← hB64, hBL, hc1, hc2, pow_succ A 63, pow_succ B 63, ← mul_assoc, ← mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero _ hA0.ne'), div_mul_cancel₀ _ (pow_ne_zero _ hB0.ne'),
          ← mul_add, ← hT, ← pow_succ]

end BstLean.Part167
