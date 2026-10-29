import BstLean.Part170End

/-!
# Part 170 (file `Fl`): the centred location fluctuation (paper Lemma `t7:p08:fl`), abstract form

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, Lemma `t7:p08:fl`: conditional on `A₁` and the plane coordinates,
`‖nΔ_f^fl‖_{L^q(A₂)} ≤ k_q√n ℓ_s/2`.

Abstract setting. `μ` is a probability measure on `V` (the latitude sphere), `a : V → ℝ^m` is
bounded and measurable (the first-layer field `a₁(x_v)`), `ā = E_v a` (componentwise), `h ∈ ℝ^m`
(the direction that the centre `b` reads), `r = res h ā`, and `w(v) = perp r (perp h (a v))`
(the part of `a(v)` orthogonal to the plane `U = span(h, ā)`). The second-layer matrix is
`M₀ + N` on `U^⊥` (Part 167's `plane_split`): `N` is a Gaussian `m × m` matrix (entry variance
`t`). The only property of the field used is the covariance bound
`E_v ⟨e, a − ā⟩² ≤ Λ|e|²` (the paper's `‖H_s‖_op ≤ ℓ_s²/t_A`).

* `relu_half`: `ReLU x = (x + |x|)/2` (the paper's "subtracting 1/2 from the indicator").
* `perp_dot`, `perp_perp_res`: `perp` is self-adjoint; `perp r (perp h ā) = 0`.
* **`flE_euLip`**: `E(N) = κ Σ_j b_j (E_v ReLU((M₀a(v))_j + (N w(v))_j) − ψ_j)` is Euclidean
  Lipschitz in the standard Gaussian coordinates of `N`, with constant `|κ||b|√(tΛ)/2`.
* **`fl_mom`**: `E_N |E − E_N E|⁸ ≤ (π/2)⁸·E|g|⁸·(|κ||b|√(tΛ)/2)⁸` (Pisier's rotation form of the
  Gaussian Poincaré inequality, Part 162's `poincare_p_lint`).
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part134 (res lam projPerp)
open BstLean.Part167 (perp normSq_perp_le perp_res)
open BstLean.Part162 (gmom gmom_nonneg poincare_p_lint)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq gradSq_le gradSq_nonneg)

variable {m : ℕ}

lemma relu_half (x : ℝ) : relu x = (x + |x|) / 2 := by
  unfold relu
  rcases le_total 0 x with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

/-- `perp` is self-adjoint. -/
lemma perp_dot (b x y : Fin m → ℝ) : perp b x ⬝ᵥ y = x ⬝ᵥ perp b y := by
  unfold perp
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have e1 : b ⬝ᵥ y = ∑ j, y j * b j := by
    unfold dotProduct; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : x ⬝ᵥ b = ∑ j, x j * b j := rfl
  rw [e1, e2]; ring

lemma perp_eq_res (h y : Fin m → ℝ) : perp h y = res h y := by
  unfold perp res lam
  rw [div_eq_inv_mul]

lemma normSq_eq_zero_iff' {z : Fin m → ℝ} : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have h0 : ∀ j ∈ Finset.univ, 0 ≤ z j ^ 2 := fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h0).mp hz i (Finset.mem_univ _)
    simpa using this
  · intro hz; subst hz; simp [normSq]

lemma perp_self (r : Fin m → ℝ) : perp r r = 0 := by
  by_cases hr : normSq r = 0
  · rw [normSq_eq_zero_iff'.mp hr]; simp [perp]
  · unfold perp
    have e : ∑ j, r j * r j = normSq r := by
      unfold normSq; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, inv_mul_cancel₀ hr, one_smul, sub_self]

/-- `perp r (perp h ā) = 0` for `r = res h ā`. -/
lemma perp_perp_res (h y : Fin m → ℝ) : perp (res h y) (perp h y) = 0 := by
  have e : perp h y = res h y := perp_eq_res h y
  rw [e]; exact perp_self _

/-! ## Integrals of bounded fields -/

variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

lemma int_comp_bdd {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {f : (Fin m → ℝ) → ℝ} (hf : Continuous f) : Integrable (fun v => f (a v)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin m → ℝ) K).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.mono' (integrable_const C) (hf.measurable.comp ha).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => hC _ ?_)
  rw [Metric.mem_closedBall, dist_zero_right]; exact hK v

/-- The componentwise mean `ā = E_v a`. -/
noncomputable def vmean (μ : Measure V) (a : V → Fin m → ℝ) : Fin m → ℝ := fun i => ∫ v, a v i ∂μ

/-- `E_v ⟨e, F(a v)⟩` for a linear functional: `E_v (e ⬝ᵥ a v) = e ⬝ᵥ ā`. -/
lemma int_dot {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (e : Fin m → ℝ) : ∫ v, e ⬝ᵥ a v ∂μ = e ⬝ᵥ vmean μ a := by
  unfold dotProduct vmean
  rw [integral_finsetSum _ fun i _ => (int_comp_bdd ha hK (continuous_apply i)).const_mul (e i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- The mean of `perp b ∘ a` is `perp b ā`. -/
lemma vmean_perp {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (b : Fin m → ℝ) : vmean μ (fun v => perp b (a v)) = perp b (vmean μ a) := by
  funext k
  unfold vmean perp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have i1 : Integrable (fun v => a v k) μ := int_comp_bdd ha hK (continuous_apply k)
  have i2 : Integrable (fun v => (normSq b)⁻¹ * ∑ j, a v j * b j) μ :=
    int_comp_bdd ha hK (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      (continuous_apply j).mul continuous_const))
  rw [integral_sub i1 (i2.mul_const _), integral_mul_const, integral_const_mul,
    integral_finsetSum _ fun j _ => (int_comp_bdd ha hK (continuous_apply j)).mul_const _]
  congr 3
  exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _

lemma norm_perp_le (b z : Fin m → ℝ) : ‖perp b z‖ ≤ ‖z‖ + |(normSq b)⁻¹ * ∑ j, z j * b j| * ‖b‖ := by
  unfold perp
  exact (norm_sub_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs])

lemma continuous_perp (b : Fin m → ℝ) : Continuous (perp b) := by
  unfold perp; fun_prop

/-- **One row of the fluctuation is Lipschitz** in the transverse row, with constant `√Λ/2`. -/
lemma flY_diff {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ N N' : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    |∫ v, relu ((M₀ *ᵥ a v) j + (N *ᵥ perp (res h (vmean μ a)) (perp h (a v))) j) ∂μ -
      ∫ v, relu ((M₀ *ᵥ a v) j + (N' *ᵥ perp (res h (vmean μ a)) (perp h (a v))) j) ∂μ| ≤
      √(Λ * normSq (fun k => N j k - N' j k)) / 2 := by
  set r := res h (vmean μ a)
  set δ : Fin m → ℝ := fun k => N j k - N' j k
  set e := perp h (perp r δ)
  have cF : ∀ N₁ : Matrix (Fin m) (Fin m) ℝ, Continuous (fun y : Fin m → ℝ =>
      relu ((M₀ *ᵥ y) j + (N₁ *ᵥ perp r (perp h y)) j)) := fun N₁ =>
    continuous_relu.comp (((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      ((continuous_perp r).comp (continuous_perp h)))))
  have i1 := int_comp_bdd (μ := μ) ha hK (cF N)
  have i2 := int_comp_bdd (μ := μ) ha hK (cF N')
  have hd : ∀ v, (N *ᵥ perp r (perp h (a v))) j - (N' *ᵥ perp r (perp h (a v))) j =
      e ⬝ᵥ (a v - vmean μ a) := by
    intro v
    have e1 : (N *ᵥ perp r (perp h (a v))) j - (N' *ᵥ perp r (perp h (a v))) j =
        δ ⬝ᵥ perp r (perp h (a v)) := by
      simp only [Matrix.mulVec, dotProduct, δ, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : δ ⬝ᵥ perp r (perp h (a v)) = e ⬝ᵥ a v := by
      rw [← perp_dot, ← perp_dot]
    have e3 : e ⬝ᵥ vmean μ a = 0 := by
      show perp h (perp r δ) ⬝ᵥ vmean μ a = 0
      rw [perp_dot, perp_dot, perp_perp_res]; simp
    rw [e1, e2, dotProduct_sub, e3, sub_zero]
  have hsplit : ∀ v, relu ((M₀ *ᵥ a v) j + (N *ᵥ perp r (perp h (a v))) j) -
      relu ((M₀ *ᵥ a v) j + (N' *ᵥ perp r (perp h (a v))) j) =
      (e ⬝ᵥ (a v - vmean μ a)) / 2 + (|(M₀ *ᵥ a v) j + (N *ᵥ perp r (perp h (a v))) j| -
        |(M₀ *ᵥ a v) j + (N' *ᵥ perp r (perp h (a v))) j|) / 2 := by
    intro v
    rw [relu_half, relu_half, ← hd v]; ring
  have cE : Continuous (fun y : Fin m → ℝ => e ⬝ᵥ (y - vmean μ a)) :=
    continuous_const.dotProduct (continuous_id.sub continuous_const)
  have iD : Integrable (fun v => e ⬝ᵥ (a v - vmean μ a)) μ :=
    int_comp_bdd (f := fun y : Fin m → ℝ => e ⬝ᵥ (y - vmean μ a)) ha hK cE
  have iD2 : Integrable (fun v => (e ⬝ᵥ (a v - vmean μ a)) ^ 2) μ :=
    int_comp_bdd (f := fun y : Fin m → ℝ => (e ⬝ᵥ (y - vmean μ a)) ^ 2) ha hK (cE.pow 2)
  have iA : Integrable (fun v => (|(M₀ *ᵥ a v) j + (N *ᵥ perp r (perp h (a v))) j| -
        |(M₀ *ᵥ a v) j + (N' *ᵥ perp r (perp h (a v))) j|) / 2) μ := by
    refine int_comp_bdd (f := fun y : Fin m → ℝ => (|(M₀ *ᵥ y) j + (N *ᵥ perp r (perp h y)) j| -
        |(M₀ *ᵥ y) j + (N' *ᵥ perp r (perp h y)) j|) / 2) ha hK
      ((((continuous_abs.comp ?_).sub (continuous_abs.comp ?_))).div_const _)
    · exact ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        ((continuous_perp r).comp (continuous_perp h))))
    · exact ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        ((continuous_perp r).comp (continuous_perp h))))
  have hmean : ∫ v, e ⬝ᵥ (a v - vmean μ a) ∂μ = 0 := by
    have : ∀ v, e ⬝ᵥ (a v - vmean μ a) = e ⬝ᵥ a v - e ⬝ᵥ vmean μ a := fun v => dotProduct_sub _ _ _
    simp_rw [this]
    rw [integral_sub (f := fun v => e ⬝ᵥ a v) (g := fun _ => e ⬝ᵥ vmean μ a)
      (int_comp_bdd (f := fun y : Fin m → ℝ => e ⬝ᵥ y) ha hK
        (continuous_const.dotProduct continuous_id)) (integrable_const _), int_dot ha hK,
      integral_const]
    simp
  rw [← integral_sub i1 i2]
  simp_rw [hsplit]
  rw [integral_add (iD.div_const _) iA, integral_div, hmean, zero_div, zero_add]
  -- `|∫ (|X| − |X'|)/2| ≤ ∫ |e⬝(a − ā)|/2 ≤ √(∫ (e⬝(a − ā))²)/2`
  have hpt : ∀ v, |(|(M₀ *ᵥ a v) j + (N *ᵥ perp r (perp h (a v))) j| -
        |(M₀ *ᵥ a v) j + (N' *ᵥ perp r (perp h (a v))) j|) / 2| ≤
        |e ⬝ᵥ (a v - vmean μ a)| / 2 := by
    intro v
    rw [abs_div, abs_two, ← hd v]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have := abs_abs_sub_abs_le ((M₀ *ᵥ a v) j + (N *ᵥ perp r (perp h (a v))) j)
      ((M₀ *ᵥ a v) j + (N' *ᵥ perp r (perp h (a v))) j)
    rwa [add_sub_add_left_eq_sub] at this
  have h1 : |∫ v, (|(M₀ *ᵥ a v) j + (N *ᵥ perp r (perp h (a v))) j| -
        |(M₀ *ᵥ a v) j + (N' *ᵥ perp r (perp h (a v))) j|) / 2 ∂μ| ≤
      ∫ v, |e ⬝ᵥ (a v - vmean μ a)| / 2 ∂μ :=
    (abs_integral_le_integral_abs).trans (integral_mono iA.abs (iD.abs.div_const _) hpt)
  have h2 : ∫ v, |e ⬝ᵥ (a v - vmean μ a)| ∂μ ≤ √(Λ * normSq δ) := by
    have hJ := BstLean.Part133.sq_integral_le (ρ := μ) (f := fun v => |e ⬝ᵥ (a v - vmean μ a)|)
      (by simpa only [sq_abs] using iD2)
    simp only [sq_abs] at hJ
    have hΛe := hΛ e
    have hee : normSq e ≤ normSq δ :=
      (normSq_perp_le h _).trans (normSq_perp_le r δ)
    have h3 : (∫ v, |e ⬝ᵥ (a v - vmean μ a)| ∂μ) ^ 2 ≤ Λ * normSq δ :=
      hJ.trans (hΛe.trans (mul_le_mul_of_nonneg_left hee hΛ0))
    exact Real.le_sqrt_of_sq_le h3
  have h1' : ∫ v, |e ⬝ᵥ (a v - vmean μ a)| / 2 ∂μ ≤ √(Λ * normSq δ) / 2 := by
    rw [integral_div]; linarith
  exact h1.trans h1'

/-- The `m × m` matrix with standard coordinates `ξ` and entry variance `t` (`gaussMat` is the
image of the standard Gaussian under this map). -/
noncomputable def matOf (t : ℝ) (ξ : Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => √t * ξ (i, j)

lemma gaussMat_eq (t : ℝ) : gaussMat m m t = (stdGauss (Fin m × Fin m)).map (matOf t) := rfl

lemma measurable_matOf (t : ℝ) : Measurable (matOf (m := m) t) := by
  have : Continuous (matOf (m := m) t) := by
    unfold matOf
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_const.mul (continuous_apply (i, j))
  exact this.measurable

/-- **The location error as a function of the transverse matrix `N`**:
`E(N) = κ Σ_j b_j (E_v ReLU((M₀a(v))_j + (N w(v))_j) − ψ_j)`, `w = perp r ∘ perp h ∘ a`. -/
noncomputable def flE (μ : Measure V) (a : V → Fin m → ℝ) (h : Fin m → ℝ)
    (M₀ : Matrix (Fin m) (Fin m) ℝ) (b ψ : Fin m → ℝ) (κ : ℝ) (N : Matrix (Fin m) (Fin m) ℝ) :
    ℝ :=
  κ * ∑ j, b j * (∫ v, relu ((M₀ *ᵥ a v) j +
    (N *ᵥ perp (res h (vmean μ a)) (perp h (a v))) j) ∂μ - ψ j)

/-- **`E` is Euclidean Lipschitz** in the standard coordinates of `N`, constant `|κ||b|√(tΛ)/2`. -/
lemma flE_euLip {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) (b ψ : Fin m → ℝ) (κ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    EuLip (fun ξ : Fin m × Fin m → ℝ => flE μ a h M₀ b ψ κ (matOf t ξ))
      (|κ| * √(normSq b) * √(t * Λ) / 2) := by
  intro ξ ξ'
  unfold flE
  rw [← mul_sub, abs_mul, ← Finset.sum_sub_distrib]
  set u : Fin m → ℝ := fun j => √(Λ * normSq (fun k => matOf t ξ j k - matOf t ξ' j k)) / 2
    with hu
  have hj : ∀ j, |b j * (∫ v, relu ((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ perp (res h (vmean μ a))
      (perp h (a v))) j) ∂μ - ψ j) - b j * (∫ v, relu ((M₀ *ᵥ a v) j + (matOf t ξ' *ᵥ
      perp (res h (vmean μ a)) (perp h (a v))) j) ∂μ - ψ j)| ≤ |b j| * u j := by
    intro j
    rw [← mul_sub, abs_mul, sub_sub_sub_cancel_right]
    exact mul_le_mul_of_nonneg_left (flY_diff ha hK hΛ0 hΛ h M₀ _ _ j) (abs_nonneg _)
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |b j|) u
  simp only [sq_abs] at hCS
  have hu2 : ∑ j, u j ^ 2 = t * Λ / 4 * ∑ i : Fin m × Fin m, (ξ i - ξ' i) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu, div_pow]
    rw [Real.sq_sqrt (mul_nonneg hΛ0 (by unfold normSq; positivity))]
    unfold normSq matOf
    simp only [Matrix.of_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (√t * ξ (j, k) - √t * ξ' (j, k)) ^ 2 = t * (ξ (j, k) - ξ' (j, k)) ^ 2 := by
      rw [← mul_sub, mul_pow, Real.sq_sqrt ht]
    rw [this]; ring
  have hb0 : ∀ j, 0 ≤ |b j| * u j := fun j => mul_nonneg (abs_nonneg _) (by positivity)
  calc |κ| * |∑ j, (b j * (∫ v, relu ((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ perp (res h (vmean μ a))
        (perp h (a v))) j) ∂μ - ψ j) - b j * (∫ v, relu ((M₀ *ᵥ a v) j + (matOf t ξ' *ᵥ
        perp (res h (vmean μ a)) (perp h (a v))) j) ∂μ - ψ j))|
      ≤ |κ| * ∑ j, |b j| * u j := mul_le_mul_of_nonneg_left
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hj j)) (abs_nonneg _)
    _ ≤ |κ| * (√(normSq b) * √(∑ j, u j ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact hCS
    _ = |κ| * √(normSq b) * √(t * Λ) / 2 * √(∑ i, (ξ i - ξ' i) ^ 2) := by
        rw [hu2, Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
          show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        ring

lemma continuous_flE {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) (b ψ : Fin m → ℝ) (κ : ℝ) :
    Continuous (flE μ a h M₀ b ψ κ) := by
  have hL := flE_euLip ha hK hΛ0 hΛ h M₀ b ψ κ (t := 1) zero_le_one
  have hc := hL.continuous (by positivity)
  have e : flE μ a h M₀ b ψ κ = (fun ξ : Fin m × Fin m → ℝ => flE μ a h M₀ b ψ κ (matOf 1 ξ)) ∘
      (fun N : Matrix (Fin m) (Fin m) ℝ => fun p : Fin m × Fin m => N p.1 p.2) := by
    funext N
    simp only [Function.comp, matOf, Real.sqrt_one, one_mul]
    rfl
  rw [e]
  exact hc.comp (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1))

/-- **The centred location fluctuation** (paper Lemma `t7:p08:fl`, order 8, abstract form):
`E_N |E − E_N E|⁸ ≤ (π/2)⁸·E|g|⁸·(|κ||b|√(tΛ)/2)⁸` for `N` Gaussian with entry variance `t`. -/
theorem fl_mom {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) (b ψ : Fin m → ℝ) (κ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ N, ENNReal.ofReal (|flE μ a h M₀ b ψ κ N - ∫ N', flE μ a h M₀ b ψ κ N' ∂gaussMat m m t| ^ 8)
        ∂gaussMat m m t ≤
      ENNReal.ofReal ((π / 2) ^ 8 * (gmom 8 * (|κ| * √(normSq b) * √(t * Λ) / 2) ^ 8)) := by
  set L := |κ| * √(normSq b) * √(t * Λ) / 2 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hL := flE_euLip ha hK hΛ0 hΛ h M₀ b ψ κ ht
  have hc := continuous_flE ha hK hΛ0 hΛ h M₀ b ψ κ
  have mo := measurable_matOf (m := m) t
  have hint : ∫ N', flE μ a h M₀ b ψ κ N' ∂gaussMat m m t =
      ∫ ξ, flE μ a h M₀ b ψ κ (matOf t ξ) ∂stdGauss (Fin m × Fin m) := by
    rw [gaussMat_eq, integral_map mo.aemeasurable hc.aestronglyMeasurable]
  rw [hint, gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (|flE μ a h M₀ b ψ κ N -
    ∫ ξ, flE μ a h M₀ b ψ κ (matOf t ξ) ∂stdGauss (Fin m × Fin m)| ^ 8))
    (ENNReal.measurable_ofReal.comp (((hc.measurable.sub_const _).abs).pow_const 8)) mo]
  refine (poincare_p_lint hL0 hL (p := 8) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hg : ∫ x, √(gradSq (fun ξ : Fin m × Fin m → ℝ => flE μ a h M₀ b ψ κ (matOf t ξ)) x) ^ 8
      ∂stdGauss (Fin m × Fin m) ≤ L ^ 8 := by
    have hpt : ∀ x, √(gradSq (fun ξ : Fin m × Fin m → ℝ => flE μ a h M₀ b ψ κ (matOf t ξ)) x) ^ 8
        ≤ L ^ 8 := fun x => by
      refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 8
      rw [Real.sqrt_le_left hL0]
      exact gradSq_le hL0 hL x
    calc _ ≤ ∫ _x, L ^ 8 ∂stdGauss (Fin m × Fin m) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            (integrable_const _) (Filter.Eventually.of_forall hpt)
      _ = L ^ 8 := by simp
  have := gmom_nonneg 8
  have h8 : (0 : ℝ) ≤ (π / 2) ^ 8 := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg this) h8

end BstLean.Part170
