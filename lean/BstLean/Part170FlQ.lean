import BstLean.Part170Sq

/-!
# Part 170 (file `FlQ`): the energy fluctuation (paper `t7:p08:energy`), abstract form

No proof is left open; no `native_decide` or `axiom` is used.

Setting of file `Fl`. The energy of the transverse matrix `N` is
`Q(N) = Σ_j E_v ReLU((M₀a(v))_j + (N w(v))_j)²`.

* `int_cs`: Cauchy–Schwarz for integrals.
* **`sqrtQ_euLip`**: `√Q` is Euclidean Lipschitz in the standard coordinates of `N`, constant
  `√(tΛ)` (the paper's "`√Q_en` is `√Γ_max`-Lipschitz", with Lean's covariance bound).
* **`flQ_mean_le`**: `E_N Q ≤ K_α + m t K²` if `|M₀a(v)|² ≤ K_α` and `|a(v)|² ≤ K²`.
* **`flQ_conc`**: `E_N |Q − E_N Q|⁸ ≤ (c₁₆²tΛ + 2(√(E_N Q) + 1)c₈√(tΛ) + c₂²tΛ)⁸`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part134 (res lam projPerp)
open BstLean.Part167 (perp normSq_perp_le perp_res)
open BstLean.Part162 (gmom gmom_nonneg poincare_p_lint)
open BstLean.Part148 (EuLip)

variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- Cauchy–Schwarz for integrals. -/
lemma int_cs {f g : V → ℝ} (hf : Integrable (fun v => f v ^ 2) μ)
    (hg : Integrable (fun v => g v ^ 2) μ) (hfg : Integrable (fun v => f v * g v) μ) :
    ∫ v, f v * g v ∂μ ≤ √(∫ v, f v ^ 2 ∂μ) * √(∫ v, g v ^ 2 ∂μ) := by
  set A := ∫ v, f v ^ 2 ∂μ
  set B := ∫ v, g v ^ 2 ∂μ
  set X := ∫ v, f v * g v ∂μ
  have hA : 0 ≤ A := integral_nonneg fun v => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun v => sq_nonneg _
  have key : ∀ l : ℝ, 0 < l → 2 * X ≤ l * A + B / l := by
    intro l hl
    have hpt : ∀ v, 2 * (f v * g v) ≤ l * f v ^ 2 + g v ^ 2 / l := fun v => by
      have : 0 ≤ (l * f v - g v) ^ 2 / l := div_nonneg (sq_nonneg _) hl.le
      have e : (l * f v - g v) ^ 2 / l = l * f v ^ 2 - 2 * (f v * g v) + g v ^ 2 / l := by
        field_simp; ring
      linarith
    have e : ∫ v, (l * f v ^ 2 + g v ^ 2 / l) ∂μ = l * A + B / l := by
      rw [integral_add (hf.const_mul l) (hg.div_const l), integral_const_mul, integral_div]
    have := integral_mono (f := fun v => 2 * (f v * g v)) (g := fun v => l * f v ^ 2 + g v ^ 2 / l)
      (hfg.const_mul 2) ((hf.const_mul l).add (hg.div_const l)) hpt
    rw [integral_const_mul, e] at this
    exact this
  by_cases hA0 : A = 0
  · rw [hA0, Real.sqrt_zero, zero_mul]
    by_contra hX; push Not at hX
    have := key (B / X + 1) (by positivity)
    rw [hA0, mul_zero, zero_add] at this
    have h2 : B / (B / X + 1) < X := by
      rw [div_lt_iff₀ (by positivity)]
      have : B / X * X = B := div_mul_cancel₀ B hX.ne'
      nlinarith
    linarith
  by_cases hB0 : B = 0
  · rw [hB0, Real.sqrt_zero, mul_zero]
    by_contra hX; push Not at hX
    have := key (X / (A + 1)) (by positivity)
    rw [hB0, zero_div, add_zero] at this
    have h2 : X / (A + 1) * A < X := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  · have hA' : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hB' : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hsA : 0 < √A := Real.sqrt_pos.mpr hA'
    have hsB : 0 < √B := Real.sqrt_pos.mpr hB'
    have := key (√B / √A) (div_pos hsB hsA)
    have e1 : √B / √A * A = √A * √B := by
      rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt, mul_comm]
    have e2 : B / (√B / √A) = √A * √B := by
      rw [div_div_eq_mul_div, mul_div_right_comm, Real.div_sqrt, mul_comm]
    rw [e1, e2] at this
    linarith

/-- **The energy of the transverse matrix**: `Q(N) = Σ_j E_v ReLU((M₀a(v))_j + (N w(v))_j)²`. -/
noncomputable def flQ (μ : Measure V) (a : V → Fin m → ℝ) (h : Fin m → ℝ)
    (M₀ : Matrix (Fin m) (Fin m) ℝ) (N : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ j, ∫ v, relu ((M₀ *ᵥ a v) j + (N *ᵥ perp (res h (vmean μ a)) (perp h (a v))) j) ^ 2 ∂μ

lemma flQ_nonneg (a : V → Fin m → ℝ) (h : Fin m → ℝ) (M₀ N : Matrix (Fin m) (Fin m) ℝ) :
    0 ≤ flQ μ a h M₀ N :=
  Finset.sum_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _

lemma relu_lip (x y : ℝ) : |relu x - relu y| ≤ |x - y| := by
  unfold relu
  rw [max_comm 0 x, max_comm 0 y]; exact abs_max_sub_max_le_abs x y 0

/-- **`√Q` is Euclidean Lipschitz** with constant `√(tΛ)`. -/
lemma sqrtQ_euLip {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t) :
    EuLip (fun ξ : Fin m × Fin m → ℝ => √(flQ μ a h M₀ (matOf t ξ))) (√(t * Λ)) := by
  intro ξ ξ'
  set r := res h (vmean μ a)
  set R : Fin m → V → ℝ := fun j v => relu ((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ perp r (perp h (a v))) j)
  set R' : Fin m → V → ℝ := fun j v =>
    relu ((M₀ *ᵥ a v) j + (matOf t ξ' *ᵥ perp r (perp h (a v))) j)
  have cR : ∀ N₁ : Matrix (Fin m) (Fin m) ℝ, ∀ j, Continuous (fun y : Fin m → ℝ =>
      relu ((M₀ *ᵥ y) j + (N₁ *ᵥ perp r (perp h y)) j)) := fun N₁ j =>
    continuous_relu.comp (((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      ((continuous_perp r).comp (continuous_perp h)))))
  have iRR : ∀ j, Integrable (fun v => R j v * R' j v) μ := fun j =>
    int_comp_bdd (f := fun y => relu ((M₀ *ᵥ y) j + (matOf t ξ *ᵥ perp r (perp h y)) j) *
      relu ((M₀ *ᵥ y) j + (matOf t ξ' *ᵥ perp r (perp h y)) j)) ha hK ((cR _ j).mul (cR _ j))
  have iR2 : ∀ j, Integrable (fun v => R j v ^ 2) μ := fun j =>
    int_comp_bdd (f := fun y => relu ((M₀ *ᵥ y) j + (matOf t ξ *ᵥ perp r (perp h y)) j) ^ 2)
      ha hK ((cR _ j).pow 2)
  have iR2' : ∀ j, Integrable (fun v => R' j v ^ 2) μ := fun j =>
    int_comp_bdd (f := fun y => relu ((M₀ *ᵥ y) j + (matOf t ξ' *ᵥ perp r (perp h y)) j) ^ 2)
      ha hK ((cR _ j).pow 2)
  set Q := ∑ j, ∫ v, R j v ^ 2 ∂μ
  set Q' := ∑ j, ∫ v, R' j v ^ 2 ∂μ
  set X := ∑ j, ∫ v, R j v * R' j v ∂μ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _
  have hQ0' : 0 ≤ Q' := Finset.sum_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _
  -- Cauchy–Schwarz
  have hX : X ≤ √Q * √Q' := by
    have h1 : X ≤ ∑ j, √(∫ v, R j v ^ 2 ∂μ) * √(∫ v, R' j v ^ 2 ∂μ) :=
      Finset.sum_le_sum fun j _ => int_cs (iR2 j) (iR2' j) (iRR j)
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => √(∫ v, R j v ^ 2 ∂μ))
      (fun j => √(∫ v, R' j v ^ 2 ∂μ))
    have e1 : ∑ j, √(∫ v, R j v ^ 2 ∂μ) ^ 2 = Q :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (integral_nonneg fun v => sq_nonneg _)
    have e2 : ∑ j, √(∫ v, R' j v ^ 2 ∂μ) ^ 2 = Q' :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (integral_nonneg fun v => sq_nonneg _)
    rw [e1, e2] at h2
    exact h1.trans h2
  -- the difference
  set D := ∑ j, ∫ v, (R j v - R' j v) ^ 2 ∂μ
  have hD : D = Q + Q' - 2 * X := by
    simp only [D, Q, Q', X]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_add (iR2 j) (iR2' j), ← integral_const_mul,
      ← integral_sub (f := fun v => R j v ^ 2 + R' j v ^ 2) (g := fun v => 2 * (R j v * R' j v))
      ((iR2 j).add (iR2' j)) ((iRR j).const_mul 2)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => by simp only [Pi.add_apply]; ring)
  have hDb : D ≤ t * Λ * ∑ i, (ξ i - ξ' i) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    set δ : Fin m → ℝ := fun k => ξ (j, k) - ξ' (j, k)
    set e := perp h (perp r δ)
    have hd : ∀ v, (matOf t ξ *ᵥ perp r (perp h (a v))) j -
        (matOf t ξ' *ᵥ perp r (perp h (a v))) j = √t * (e ⬝ᵥ (a v - vmean μ a)) := by
      intro v
      have e1 : (matOf t ξ *ᵥ perp r (perp h (a v))) j - (matOf t ξ' *ᵥ perp r (perp h (a v))) j =
          √t * (δ ⬝ᵥ perp r (perp h (a v))) := by
        simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, δ, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e2 : δ ⬝ᵥ perp r (perp h (a v)) = e ⬝ᵥ a v := by rw [← perp_dot, ← perp_dot]
      have e3 : e ⬝ᵥ vmean μ a = 0 := by
        show perp h (perp r δ) ⬝ᵥ vmean μ a = 0
        rw [perp_dot, perp_dot, perp_perp_res]; simp
      rw [e1, e2, dotProduct_sub, e3, sub_zero]
    have hpt : ∀ v, (R j v - R' j v) ^ 2 ≤ t * (e ⬝ᵥ (a v - vmean μ a)) ^ 2 := by
      intro v
      have := relu_lip ((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ perp r (perp h (a v))) j)
        ((M₀ *ᵥ a v) j + (matOf t ξ' *ᵥ perp r (perp h (a v))) j)
      rw [add_sub_add_left_eq_sub, hd v] at this
      calc (R j v - R' j v) ^ 2 = |R j v - R' j v| ^ 2 := (sq_abs _).symm
        _ ≤ |√t * (e ⬝ᵥ (a v - vmean μ a))| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = t * (e ⬝ᵥ (a v - vmean μ a)) ^ 2 := by
          rw [sq_abs, mul_pow, Real.sq_sqrt ht]
    have cE : Continuous (fun y : Fin m → ℝ => e ⬝ᵥ (y - vmean μ a)) :=
      continuous_const.dotProduct (continuous_id.sub continuous_const)
    have iE2 : Integrable (fun v => (e ⬝ᵥ (a v - vmean μ a)) ^ 2) μ :=
      int_comp_bdd (f := fun y : Fin m → ℝ => (e ⬝ᵥ (y - vmean μ a)) ^ 2) ha hK (cE.pow 2)
    have iD : Integrable (fun v => (R j v - R' j v) ^ 2) μ := by
      have : (fun v => (R j v - R' j v) ^ 2) = fun v => R j v ^ 2 - 2 * (R j v * R' j v) +
          R' j v ^ 2 := by funext v; ring
      rw [this]; exact ((iR2 j).sub ((iRR j).const_mul 2)).add (iR2' j)
    calc ∫ v, (R j v - R' j v) ^ 2 ∂μ ≤ ∫ v, t * (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ :=
          integral_mono iD (iE2.const_mul t) hpt
      _ = t * ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ t * (Λ * normSq δ) := by
          refine mul_le_mul_of_nonneg_left ((hΛ e).trans ?_) ht
          exact mul_le_mul_of_nonneg_left ((normSq_perp_le h _).trans (normSq_perp_le r δ)) hΛ0
      _ = t * Λ * ∑ k, (ξ (j, k) - ξ' (j, k)) ^ 2 := by unfold normSq; ring
  -- conclude
  have hsq : (√Q - √Q') ^ 2 ≤ D := by
    rw [hD]
    have e1 : (√Q - √Q') ^ 2 = Q + Q' - 2 * (√Q * √Q') := by
      rw [sub_sq, Real.sq_sqrt hQ0, Real.sq_sqrt hQ0']; ring
    rw [e1]; linarith
  have hfin : |√Q - √Q'| ≤ √(t * Λ) * √(∑ i, (ξ i - ξ' i) ^ 2) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hsq.trans hDb)
  exact hfin

lemma integrable_shift_sq {ι : Type} [Fintype ι] (α : ℝ) (u : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => (α + ξ ⬝ᵥ u) ^ 2) (stdGauss ι) := by
  have hm : MemLp (fun ξ : ι → ℝ => ξ ⬝ᵥ u) 2 (stdGauss ι) := by
    have : (fun ξ : ι → ℝ => ξ ⬝ᵥ u) = fun ξ => ∑ i, u i * ξ i := by
      funext ξ; unfold dotProduct; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    exact memLp_finset_sum _ fun i _ => (BstLean.Part112.memLp_coord i).const_mul (u i)
  have hm2 : MemLp (fun ξ : ι → ℝ => α + ξ ⬝ᵥ u) 2 (stdGauss ι) := (memLp_const α).add hm
  exact hm2.integrable_sq

/-- The Gaussian mean of `(α + ⟨ξ, u⟩)²` is `α² + |u|²`. -/
lemma gauss_sq_shift {ι : Type} [Fintype ι] (α : ℝ) (u : ι → ℝ) :
    ∫ ξ, (α + ξ ⬝ᵥ u) ^ 2 ∂stdGauss ι = α ^ 2 + u ⬝ᵥ u := by
  have hm : MemLp (fun ξ : ι → ℝ => ξ ⬝ᵥ u) 2 (stdGauss ι) := by
    have : (fun ξ : ι → ℝ => ξ ⬝ᵥ u) = fun ξ => ∑ i, u i * ξ i := by
      funext ξ; unfold dotProduct; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    exact memLp_finset_sum _ fun i _ => (BstLean.Part112.memLp_coord i).const_mul (u i)
  have i1 : Integrable (fun ξ : ι → ℝ => ξ ⬝ᵥ u) (stdGauss ι) := hm.integrable one_le_two
  have i2 : Integrable (fun ξ : ι → ℝ => (ξ ⬝ᵥ u) ^ 2) (stdGauss ι) := hm.integrable_sq
  have hmean : ∫ ξ, ξ ⬝ᵥ u ∂stdGauss ι = 0 := by
    have : (fun ξ : ι → ℝ => ξ ⬝ᵥ u) = fun ξ => ∑ i, u i * ξ i := by
      funext ξ; unfold dotProduct; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this, integral_finsetSum _ fun i _ => (BstLean.Part112.int_coord i).const_mul (u i)]
    simp [integral_const_mul, BstLean.Part112.integral_coord]
  have hsq : ∫ ξ, (ξ ⬝ᵥ u) ^ 2 ∂stdGauss ι = u ⬝ᵥ u := by
    have h := BstLean.Part162.gauss_dot_mom u 2
    simp only [sq_abs] at h
    rw [h, gmom2_eq, one_mul, Real.sq_sqrt]
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have e : (fun ξ : ι → ℝ => (α + ξ ⬝ᵥ u) ^ 2) =
      fun ξ => (α ^ 2 + 2 * α * (ξ ⬝ᵥ u)) + (ξ ⬝ᵥ u) ^ 2 := by funext ξ; ring
  rw [e, integral_add (f := fun ξ => α ^ 2 + 2 * α * (ξ ⬝ᵥ u)) (g := fun ξ => (ξ ⬝ᵥ u) ^ 2)
    ((integrable_const _).add (i1.const_mul _)) i2,
    integral_add (f := fun _ => α ^ 2) (g := fun ξ => 2 * α * (ξ ⬝ᵥ u)) (integrable_const _)
      (i1.const_mul _), integral_const_mul, hmean, hsq]
  simp

/-- **The mean energy**: `E_N Q ≤ K_α + m t K²` if `|M₀a(v)|² ≤ K_α` and `|a(v)|² ≤ K²`. -/
lemma flQ_mean_le {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t) {Kα K2 : ℝ}
    (hKα : 0 ≤ Kα) (hK2' : 0 ≤ K2)
    (hα : ∀ v, normSq (M₀ *ᵥ a v) ≤ Kα) (hK2 : ∀ v, normSq (a v) ≤ K2) :
    ∫ ξ, flQ μ a h M₀ (matOf t ξ) ∂stdGauss (Fin m × Fin m) ≤ Kα + m * t * K2 := by
  set r := res h (vmean μ a)
  set w : V → Fin m → ℝ := fun v => perp r (perp h (a v))
  have hS := sqrtQ_euLip ha hK hΛ0 hΛ h M₀ ht
  have iF : Integrable (fun ξ => flQ μ a h M₀ (matOf t ξ)) (stdGauss (Fin m × Fin m)) := by
    have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
  set u : Fin m → V → (Fin m × Fin m → ℝ) := fun j v p => if p.1 = j then √t * w v p.2 else 0
  have hu : ∀ j v (ξ : Fin m × Fin m → ℝ), (matOf t ξ *ᵥ w v) j = ξ ⬝ᵥ u j v := by
    intro j v ξ
    simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, u, Fintype.sum_prod_type]
    rw [eq_comm, Finset.sum_eq_single j]
    · exact Finset.sum_congr rfl fun k _ => by simp; ring
    · intro b _ hb; exact Finset.sum_eq_zero fun k _ => by simp [hb]
    · simp
  have huu : ∀ j v, u j v ⬝ᵥ u j v = t * normSq (w v) := by
    intro j v
    simp only [dotProduct, u, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · unfold normSq; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp; rw [mul_mul_mul_comm, Real.mul_self_sqrt ht]; ring
    · intro b _ hb; exact Finset.sum_eq_zero fun k _ => by simp [hb]
    · simp
  have cw : Continuous (fun y : Fin m → ℝ => perp r (perp h y)) :=
    (continuous_perp r).comp (continuous_perp h)
  have mT : ∀ j, Measurable (fun p : (Fin m × Fin m → ℝ) × V =>
      ENNReal.ofReal (((M₀ *ᵥ a p.2) j + (matOf t p.1 *ᵥ w p.2) j) ^ 2)) := by
    intro j
    have hc : Continuous (fun q : (Fin m × Fin m → ℝ) × (Fin m → ℝ) =>
        ((M₀ *ᵥ q.2) j + (matOf t q.1 *ᵥ perp r (perp h q.2)) j) ^ 2) := by
      refine ((((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        continuous_snd))).add ((continuous_apply j).comp (Continuous.matrix_mulVec ?_
        (cw.comp continuous_snd)))).pow 2
      unfold matOf
      exact continuous_pi fun i => continuous_pi fun k =>
        continuous_const.mul ((continuous_apply (i, k)).comp continuous_fst)
    exact ENNReal.measurable_ofReal.comp (hc.measurable.comp (measurable_fst.prodMk
      (ha.comp measurable_snd)))
  -- pointwise in `ξ`
  have hpt : ∀ ξ, ENNReal.ofReal (flQ μ a h M₀ (matOf t ξ)) ≤
      ∑ j, ∫⁻ v, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2) ∂μ := by
    intro ξ
    unfold flQ
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _]
    refine Finset.sum_le_sum fun j _ => ?_
    have cR : Continuous (fun y : Fin m → ℝ =>
        relu ((M₀ *ᵥ y) j + (matOf t ξ *ᵥ perp r (perp h y)) j) ^ 2) :=
      (continuous_relu.comp (((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        cw)))).pow 2
    rw [ofReal_integral_eq_lintegral_ofReal (int_comp_bdd ha hK cR)
      (Filter.Eventually.of_forall fun v => sq_nonneg _)]
    refine lintegral_mono fun v => ENNReal.ofReal_le_ofReal ?_
    have hr : ∀ x : ℝ, relu x ^ 2 ≤ x ^ 2 := fun x => by
      unfold relu
      rcases le_total 0 x with hx | hx
      · rw [max_eq_right hx]
      · rw [max_eq_left hx]; nlinarith [sq_nonneg x]
    exact hr _
  have hinner : ∀ j v, ∫⁻ ξ, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2)
      ∂stdGauss (Fin m × Fin m) = ENNReal.ofReal ((M₀ *ᵥ a v) j ^ 2 + t * normSq (w v)) := by
    intro j v
    simp_rw [hu j v]
    have iT := integrable_shift_sq (ι := Fin m × Fin m) ((M₀ *ᵥ a v) j) (u j v)
    rw [← ofReal_integral_eq_lintegral_ofReal iT (Filter.Eventually.of_forall fun ξ => sq_nonneg _),
      gauss_sq_shift, huu]
  have hsum : ∀ v, ∑ j, ((M₀ *ᵥ a v) j ^ 2 + t * normSq (w v)) ≤ Kα + m * t * K2 := by
    intro v
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ j, (M₀ *ᵥ a v) j ^ 2 ≤ Kα := hα v
    have h2 : normSq (w v) ≤ K2 :=
      ((normSq_perp_le r _).trans (normSq_perp_le h _)).trans (hK2 v)
    have : (m : ℝ) * (t * normSq (w v)) ≤ m * t * K2 := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have key : ENNReal.ofReal (∫ ξ, flQ μ a h M₀ (matOf t ξ) ∂stdGauss (Fin m × Fin m)) ≤
      ENNReal.ofReal (Kα + m * t * K2) := by
    rw [ofReal_integral_eq_lintegral_ofReal iF (Filter.Eventually.of_forall fun ξ =>
      flQ_nonneg _ _ _ _)]
    calc ∫⁻ ξ, ENNReal.ofReal (flQ μ a h M₀ (matOf t ξ)) ∂stdGauss (Fin m × Fin m)
        ≤ ∫⁻ ξ, ∑ j, ∫⁻ v, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2) ∂μ
            ∂stdGauss (Fin m × Fin m) := lintegral_mono hpt
      _ = ∑ j, ∫⁻ v, ∫⁻ ξ, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2)
            ∂stdGauss (Fin m × Fin m) ∂μ := by
          rw [lintegral_finset_sum _ fun j _ => (mT j).lintegral_prod_right']
          exact Finset.sum_congr rfl fun j _ => lintegral_lintegral_swap (mT j).aemeasurable
      _ = ∫⁻ v, ENNReal.ofReal (∑ j, ((M₀ *ᵥ a v) j ^ 2 + t * normSq (w v))) ∂μ := by
          simp_rw [hinner]
          rw [← lintegral_finset_sum]
          · refine lintegral_congr fun v => ?_
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => add_nonneg (sq_nonneg _)
              (mul_nonneg ht (normSq_nonneg _))]
          · intro j _
            refine ENNReal.measurable_ofReal.comp ?_
            exact (((measurable_pi_apply j).comp ((Continuous.matrix_mulVec continuous_const
              continuous_id).measurable.comp ha)).pow_const 2).add
              ((continuous_normSq.measurable.comp (cw.measurable.comp ha)).const_mul t)
      _ ≤ ∫⁻ _v, ENNReal.ofReal (Kα + m * t * K2) ∂μ :=
          lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hsum v)
      _ = ENNReal.ofReal (Kα + m * t * K2) := by simp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key

/-- **The energy fluctuation** (paper `t7:p08:energy`, order 8, abstract form). -/
theorem flQ_conc {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ξ, ENNReal.ofReal (|flQ μ a h M₀ (matOf t ξ) -
        ∫ ξ', flQ μ a h M₀ (matOf t ξ') ∂stdGauss (Fin m × Fin m)| ^ 8) ∂stdGauss (Fin m × Fin m) ≤
      ENNReal.ofReal (((π / 2 * (25 / 10) * √(t * Λ)) ^ 2 +
        2 * (√(∫ ξ', flQ μ a h M₀ (matOf t ξ') ∂stdGauss (Fin m × Fin m)) + 1) *
          (π / 2 * (18 / 10) * √(t * Λ)) + (π / 2 * √(t * Λ)) ^ 2) ^ 8) := by
  have hS := sqrtQ_euLip ha hK hΛ0.le hΛ h M₀ ht.le
  have hsq : ∀ ξ, √(flQ μ a h M₀ (matOf t ξ)) ^ 2 = flQ μ a h M₀ (matOf t ξ) := fun ξ =>
    Real.sq_sqrt (flQ_nonneg _ _ _ _)
  have h := sq_conc (Real.sqrt_pos.mpr (mul_pos ht hΛ0)) hS (fun ξ => Real.sqrt_nonneg _)
  simp only [hsq] at h
  exact h

end BstLean.Part170
