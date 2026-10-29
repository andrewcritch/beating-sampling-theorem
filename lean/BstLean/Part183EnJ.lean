import BstLean.Part183EnA

/-!
# Part 183 (file `EnJ`): the centred energy fluctuation bound `EnJ_stmt` PROVED

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:energy` (the transverse gradient block of the energy
fluctuation is `2Π E_v[(ReLU(z_j·F_s) − X(z_j))(F_s − F̄)]`, so only the centred energy enters).

* `relu_sq_taylor`: `|ReLU(x+δ)² − ReLU(x)² − 2ReLU(x)δ| ≤ 2δ²`.
* `incr_facts`, `row_cs`, **`flQ_local`**: at fixed plane coordinates,
  `|Q(N') − Q(N)| ≤ 2√(Q_v(N))·√(tΛ)|ξ' − ξ| + 2tΛ|ξ' − ξ|²` (`Q = flQ`, `Q_v = flQv`).
* **`flQ_grad_conc`**: `E|Q − EQ|⁸ ≤ (π/2)⁸E|g|⁸(4tΛ)⁴·E Q_v⁴` (truncation `min(Q, N²)`, Part 162's
  Gaussian `L⁸` Poincaré inequality, `gradSq_le_of_local`, Fatou).
* `measurable_Qvar`, `flQv_Mpl`, `GQ`, `GQ_tot`: the plane split of the centred energy.
* **`exWn_mom_J_of`**: Part 174's `exWn_mom_r` with `WflJ`, given `E_{A₂} Qvar⁴ ≤ Y⁸`.
* **`EnJ_proved : EnJ_stmt`** (with file `EnA`: `Qvar_mom4_gm`, `trCov_lat`).
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real Matrix Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part170
open BstLean.Part134 (res lam projPerp)
open BstLean.Part167 (perp normSq_perp_le perp_res)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part148 (EuLip)

/-- `|ReLU(x + δ)² − ReLU(x)² − 2 ReLU(x) δ| ≤ 2δ²`. -/
lemma relu_sq_taylor (x δ : ℝ) :
    |relu (x + δ) ^ 2 - relu x ^ 2 - 2 * relu x * δ| ≤ 2 * δ ^ 2 := by
  unfold relu
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 (x + δ) with hy | hy
  · rw [max_eq_right hx, max_eq_right hy, abs_le]; constructor <;> nlinarith [sq_nonneg δ]
  · rw [max_eq_right hx, max_eq_left hy, abs_le]; constructor <;> nlinarith
  · rw [max_eq_left hx, max_eq_right hy, abs_le]; constructor <;> nlinarith
  · rw [max_eq_left hx, max_eq_left hy]; simp; positivity

section core
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- The transverse vector `w(y) = perp r (perp h y)`, `r = res h ā`. -/
noncomputable def wT (μ : Measure V) (a : V → Fin m → ℝ) (h y : Fin m → ℝ) : Fin m → ℝ :=
  perp (res h (vmean μ a)) (perp h y)

/-- The row value `ReLU((M₀y)_j + (N w(y))_j)`. -/
noncomputable def Rf (μ : Measure V) (a : V → Fin m → ℝ) (h : Fin m → ℝ)
    (M₀ N : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) (y : Fin m → ℝ) : ℝ :=
  relu ((M₀ *ᵥ y) j + (N *ᵥ wT μ a h y) j)

lemma continuous_wT (a : V → Fin m → ℝ) (h : Fin m → ℝ) : Continuous (wT μ a h) :=
  (continuous_perp _).comp (continuous_perp h)

lemma continuous_Rf (a : V → Fin m → ℝ) (h : Fin m → ℝ) (M₀ N : Matrix (Fin m) (Fin m) ℝ)
    (j : Fin m) : Continuous (Rf μ a h M₀ N j) :=
  continuous_relu.comp (((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
    continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
    (continuous_wT a h))))

lemma flQ_eq_Rf (a : V → Fin m → ℝ) (h : Fin m → ℝ) (M₀ N : Matrix (Fin m) (Fin m) ℝ) :
    flQ μ a h M₀ N = ∑ j, ∫ v, Rf μ a h M₀ N j (a v) ^ 2 ∂μ := rfl

lemma flQv_eq_Rf (a : V → Fin m → ℝ) (h : Fin m → ℝ) (M₀ N : Matrix (Fin m) (Fin m) ℝ) :
    flQv μ a h M₀ N = ∑ j, (∫ v, Rf μ a h M₀ N j (a v) ^ 2 ∂μ -
      (∫ v, Rf μ a h M₀ N j (a v) ∂μ) ^ 2) := rfl

/-- The transverse increment: `(matOf t ξ' w)_j − (matOf t ξ w)_j = √t·⟨e_j, a v − ā⟩`, with
`e_j = perp h (perp r (ξ'_j − ξ_j))`, of mean zero and with `Σ_j E_v(…)² ≤ tΛ|ξ' − ξ|²`. -/
lemma incr_facts {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) (ξ ξ' : Fin m × Fin m → ℝ) :
    (∀ j, Integrable (fun v => ((matOf t ξ' *ᵥ wT μ a h (a v)) j -
        (matOf t ξ *ᵥ wT μ a h (a v)) j)) μ) ∧
    (∀ j, Integrable (fun v => ((matOf t ξ' *ᵥ wT μ a h (a v)) j -
        (matOf t ξ *ᵥ wT μ a h (a v)) j) ^ 2) μ) ∧
    (∀ j, ∫ v, ((matOf t ξ' *ᵥ wT μ a h (a v)) j - (matOf t ξ *ᵥ wT μ a h (a v)) j) ∂μ = 0) ∧
    ∑ j, ∫ v, ((matOf t ξ' *ᵥ wT μ a h (a v)) j - (matOf t ξ *ᵥ wT μ a h (a v)) j) ^ 2 ∂μ ≤
      t * Λ * ∑ i, (ξ' i - ξ i) ^ 2 := by
  set r := res h (vmean μ a)
  have cD : ∀ j, Continuous (fun y : Fin m → ℝ => (matOf t ξ' *ᵥ wT μ a h y) j -
      (matOf t ξ *ᵥ wT μ a h y) j) := fun j =>
    ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const (continuous_wT a h))).sub
      ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const (continuous_wT a h)))
  have iD : ∀ j, Integrable (fun v => ((matOf t ξ' *ᵥ wT μ a h (a v)) j -
      (matOf t ξ *ᵥ wT μ a h (a v)) j)) μ := fun j => int_comp_bdd ha hK (cD j)
  have iD2 : ∀ j, Integrable (fun v => ((matOf t ξ' *ᵥ wT μ a h (a v)) j -
      (matOf t ξ *ᵥ wT μ a h (a v)) j) ^ 2) μ := fun j => int_comp_bdd ha hK ((cD j).pow 2)
  -- the representation
  have hrep : ∀ j v, (matOf t ξ' *ᵥ wT μ a h (a v)) j - (matOf t ξ *ᵥ wT μ a h (a v)) j =
      √t * (perp h (perp r (fun k => ξ' (j, k) - ξ (j, k))) ⬝ᵥ (a v - vmean μ a)) := by
    intro j v
    set δ : Fin m → ℝ := fun k => ξ' (j, k) - ξ (j, k)
    have e1 : (matOf t ξ' *ᵥ wT μ a h (a v)) j - (matOf t ξ *ᵥ wT μ a h (a v)) j =
        √t * (δ ⬝ᵥ perp r (perp h (a v))) := by
      simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, δ, Finset.mul_sum,
        ← Finset.sum_sub_distrib, wT]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : δ ⬝ᵥ perp r (perp h (a v)) = perp h (perp r δ) ⬝ᵥ a v := by
      rw [← perp_dot, ← perp_dot]
    have e3 : perp h (perp r δ) ⬝ᵥ vmean μ a = 0 := by
      rw [perp_dot, perp_dot, perp_perp_res]; simp
    rw [e1, e2, dotProduct_sub, e3, sub_zero]
  refine ⟨iD, iD2, fun j => ?_, ?_⟩
  · simp_rw [hrep j]
    rw [integral_const_mul]
    have cE : Continuous (fun y : Fin m → ℝ =>
        perp h (perp r (fun k => ξ' (j, k) - ξ (j, k))) ⬝ᵥ y) :=
      continuous_const.dotProduct continuous_id
    have : ∫ v, perp h (perp r (fun k => ξ' (j, k) - ξ (j, k))) ⬝ᵥ (a v - vmean μ a) ∂μ = 0 := by
      simp_rw [dotProduct_sub]
      rw [integral_sub (int_comp_bdd ha hK cE) (integrable_const _), int_dot ha hK]
      simp
    rw [this, mul_zero]
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    set δ : Fin m → ℝ := fun k => ξ' (j, k) - ξ (j, k)
    set e := perp h (perp r δ)
    simp_rw [hrep j]
    have cE : Continuous (fun y : Fin m → ℝ => e ⬝ᵥ (y - vmean μ a)) :=
      continuous_const.dotProduct (continuous_id.sub continuous_const)
    calc ∫ v, (√t * (e ⬝ᵥ (a v - vmean μ a))) ^ 2 ∂μ
        = t * ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only; rw [mul_pow, Real.sq_sqrt ht]
      _ ≤ t * (Λ * normSq δ) := by
          refine mul_le_mul_of_nonneg_left ((hΛ e).trans ?_) ht
          exact mul_le_mul_of_nonneg_left ((normSq_perp_le h _).trans (normSq_perp_le r δ)) hΛ0
      _ = t * Λ * ∑ k, (ξ' (j, k) - ξ (j, k)) ^ 2 := by unfold normSq; ring

/-- `E(f − Ef)² = Ef² − (Ef)²`. -/
lemma int_sq_sub_mean {f : V → ℝ} (if1 : Integrable f μ) (if2 : Integrable (fun v => f v ^ 2) μ) :
    ∫ v, (f v - ∫ w, f w ∂μ) ^ 2 ∂μ = ∫ v, f v ^ 2 ∂μ - (∫ v, f v ∂μ) ^ 2 := by
  set c := ∫ w, f w ∂μ
  have h1 : Integrable (fun v => f v ^ 2 - 2 * c * f v) μ := if2.sub (if1.const_mul (2 * c))
  calc ∫ v, (f v - c) ^ 2 ∂μ = ∫ v, ((f v ^ 2 - 2 * c * f v) + c ^ 2) ∂μ := by
        congr 1; funext v; ring
    _ = ∫ v, (f v ^ 2 - 2 * c * f v) ∂μ + ∫ _v, c ^ 2 ∂μ := integral_add h1 (integrable_const _)
    _ = (∫ v, f v ^ 2 ∂μ - ∫ v, 2 * c * f v ∂μ) + c ^ 2 := by
        rw [integral_sub if2 (if1.const_mul _)]; simp
    _ = ∫ v, f v ^ 2 ∂μ - c ^ 2 := by rw [integral_const_mul]; ring

/-- One row: `|E(f d)| ≤ √(Var f)·√(E d²)` if `E d = 0`. -/
lemma row_cs {f d : V → ℝ} (if1 : Integrable f μ) (if2 : Integrable (fun v => f v ^ 2) μ)
    (id1 : Integrable d μ) (id2 : Integrable (fun v => d v ^ 2) μ)
    (ifd : Integrable (fun v => f v * d v) μ) (hd0 : ∫ v, d v ∂μ = 0) :
    |∫ v, f v * d v ∂μ| ≤ √(∫ v, f v ^ 2 ∂μ - (∫ v, f v ∂μ) ^ 2) * √(∫ v, d v ^ 2 ∂μ) := by
  set c := ∫ v, f v ∂μ
  have ifc2 : Integrable (fun v => (f v - c) ^ 2) μ := by
    have : (fun v => (f v - c) ^ 2) = fun v => f v ^ 2 - 2 * c * f v + c ^ 2 := by
      funext v; ring
    rw [this]; exact (if2.sub (if1.const_mul _)).add (integrable_const _)
  have hvar : ∫ v, (f v - c) ^ 2 ∂μ = ∫ v, f v ^ 2 ∂μ - c ^ 2 := int_sq_sub_mean if1 if2
  have ifcd : Integrable (fun v => (f v - c) * d v) μ := by
    have : (fun v => (f v - c) * d v) = fun v => f v * d v - c * d v := by funext v; ring
    rw [this]; exact ifd.sub (id1.const_mul _)
  have hfd : ∫ v, f v * d v ∂μ = ∫ v, (f v - c) * d v ∂μ := by
    have : (fun v => (f v - c) * d v) = fun v => f v * d v - c * d v := by funext v; ring
    rw [this, integral_sub ifd (id1.const_mul _), integral_const_mul, hd0]; ring
  rw [hfd, ← hvar]
  rw [abs_le]
  constructor
  · have h := BstLean.Part170.int_cs (μ := μ) (f := fun v => f v - c) (g := fun v => -d v) ifc2
      (by simpa using id2) (by simpa [mul_neg] using ifcd.neg)
    simp only [mul_neg, integral_neg, neg_sq] at h
    linarith
  · exact BstLean.Part170.int_cs ifc2 id2 ifcd

/-- **The local estimate**: `|Q(ξ') − Q(ξ)| ≤ 2√(Q_v(ξ))·√(tΛ|ξ' − ξ|²) + 2tΛ|ξ' − ξ|²`
(`Q = flQ`, `Q_v = flQv`: the gradient of the energy sees only the centred energy). -/
theorem flQ_local {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ξ ξ' : Fin m × Fin m → ℝ) :
    |flQ μ a h M₀ (matOf t ξ') - flQ μ a h M₀ (matOf t ξ)| ≤
      2 * √(flQv μ a h M₀ (matOf t ξ)) * √(t * Λ * ∑ i, (ξ' i - ξ i) ^ 2) +
        2 * (t * Λ * ∑ i, (ξ' i - ξ i) ^ 2) := by
  obtain ⟨iD, iD2, hD0, hDs⟩ := incr_facts ha hK hΛ0 hΛ h ht ξ ξ'
  set S := t * Λ * ∑ i, (ξ' i - ξ i) ^ 2 with hS
  set R : Fin m → V → ℝ := fun j v => Rf μ a h M₀ (matOf t ξ) j (a v)
  set R' : Fin m → V → ℝ := fun j v => Rf μ a h M₀ (matOf t ξ') j (a v)
  set d : Fin m → V → ℝ := fun j v => (matOf t ξ' *ᵥ wT μ a h (a v)) j -
    (matOf t ξ *ᵥ wT μ a h (a v)) j
  have hRR : ∀ j v, R' j v = relu ((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ wT μ a h (a v)) j + d j v) := by
    intro j v; simp only [R', d, Rf]; congr 1; ring
  have hR : ∀ j v, R j v = relu ((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ wT μ a h (a v)) j) := fun j v => rfl
  have iR : ∀ j, Integrable (R j) μ := fun j => int_comp_bdd ha hK (continuous_Rf a h M₀ _ j)
  have iR2 : ∀ j, Integrable (fun v => R j v ^ 2) μ := fun j =>
    int_comp_bdd ha hK ((continuous_Rf a h M₀ _ j).pow 2)
  have iR'2 : ∀ j, Integrable (fun v => R' j v ^ 2) μ := fun j =>
    int_comp_bdd ha hK ((continuous_Rf a h M₀ _ j).pow 2)
  have iRd : ∀ j, Integrable (fun v => R j v * d j v) μ := fun j => by
    have cD : Continuous (fun y : Fin m → ℝ => (matOf t ξ' *ᵥ wT μ a h y) j -
        (matOf t ξ *ᵥ wT μ a h y) j) :=
      ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        (continuous_wT a h))).sub ((continuous_apply j).comp (Continuous.matrix_mulVec
        continuous_const (continuous_wT a h)))
    exact int_comp_bdd (f := fun y => Rf μ a h M₀ (matOf t ξ) j y *
      ((matOf t ξ' *ᵥ wT μ a h y) j - (matOf t ξ *ᵥ wT μ a h y) j)) ha hK
      ((continuous_Rf a h M₀ _ j).mul cD)
  -- the Taylor split per row
  set E : Fin m → V → ℝ := fun j v => R' j v ^ 2 - R j v ^ 2 - 2 * R j v * d j v
  have hE : ∀ j v, |E j v| ≤ 2 * d j v ^ 2 := fun j v => by
    simp only [E]; rw [hRR, hR]; exact relu_sq_taylor _ _
  have iE : ∀ j, Integrable (E j) μ := fun j =>
    ((iR'2 j).sub (iR2 j)).sub ((iRd j).const_mul 2 |>.congr (Filter.Eventually.of_forall
      fun v => by simp only; ring))
  have hdiff : flQ μ a h M₀ (matOf t ξ') - flQ μ a h M₀ (matOf t ξ) =
      2 * ∑ j, ∫ v, R j v * d j v ∂μ + ∑ j, ∫ v, E j v ∂μ := by
    rw [flQ_eq_Rf, flQ_eq_Rf, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_sub (iR'2 j) (iR2 j), ← integral_const_mul, ← integral_add
      ((iRd j).const_mul 2) (iE j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [E, R, R']; ring
  -- the error part
  have hEs : |∑ j, ∫ v, E j v ∂μ| ≤ 2 * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |∫ v, E j v ∂μ| ≤ ∑ j, ∫ v, 2 * d j v ^ 2 ∂μ := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (abs_integral_le_integral_abs).trans ?_
          exact integral_mono (iE j).abs ((iD2 j).const_mul 2) (hE j)
      _ = 2 * ∑ j, ∫ v, d j v ^ 2 ∂μ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
      _ ≤ 2 * S := by linarith
  -- the linear part
  have hlin : |∑ j, ∫ v, R j v * d j v ∂μ| ≤ √(flQv μ a h M₀ (matOf t ξ)) * √S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ j, |∫ v, R j v * d j v ∂μ| ≤ √(∫ v, R j v ^ 2 ∂μ - (∫ v, R j v ∂μ) ^ 2) *
        √(∫ v, d j v ^ 2 ∂μ) := fun j =>
      row_cs (iR j) (iR2 j) (iD j) (iD2 j) (iRd j) (hD0 j)
    refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun j => √(∫ v, R j v ^ 2 ∂μ - (∫ v, R j v ∂μ) ^ 2)) (fun j => √(∫ v, d j v ^ 2 ∂μ))
    have hv0 : ∀ j, 0 ≤ ∫ v, R j v ^ 2 ∂μ - (∫ v, R j v ∂μ) ^ 2 := fun j => by
      have hv : 0 ≤ ∫ v, (R j v - ∫ w, R j w ∂μ) ^ 2 ∂μ := integral_nonneg fun v => sq_nonneg _
      have e : ∫ v, (R j v - ∫ w, R j w ∂μ) ^ 2 ∂μ =
          ∫ v, R j v ^ 2 ∂μ - (∫ v, R j v ∂μ) ^ 2 := int_sq_sub_mean (iR j) (iR2 j)
      linarith
    have e1 : ∑ j, √(∫ v, R j v ^ 2 ∂μ - (∫ v, R j v ∂μ) ^ 2) ^ 2 =
        flQv μ a h M₀ (matOf t ξ) := by
      rw [flQv_eq_Rf]; exact Finset.sum_congr rfl fun j _ => Real.sq_sqrt (hv0 j)
    have e2 : ∑ j, √(∫ v, d j v ^ 2 ∂μ) ^ 2 = ∑ j, ∫ v, d j v ^ 2 ∂μ :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (integral_nonneg fun v => sq_nonneg _)
    rw [e1, e2] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDs) (Real.sqrt_nonneg _))
  rw [hdiff]
  calc |2 * ∑ j, ∫ v, R j v * d j v ∂μ + ∑ j, ∫ v, E j v ∂μ|
      ≤ |2 * ∑ j, ∫ v, R j v * d j v ∂μ| + |∑ j, ∫ v, E j v ∂μ| := abs_add_le _ _
    _ ≤ 2 * (√(flQv μ a h M₀ (matOf t ξ)) * √S) + 2 * S := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    _ = _ := by ring

lemma flQv_nonneg {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (h : Fin m → ℝ) (M₀ N : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ flQv μ a h M₀ N := by
  rw [flQv_eq_Rf]
  refine Finset.sum_nonneg fun j _ => ?_
  have i1 := int_comp_bdd (μ := μ) ha hK (continuous_Rf (μ := μ) a h M₀ N j)
  have i2 := int_comp_bdd (μ := μ) ha hK ((continuous_Rf (μ := μ) a h M₀ N j).pow 2)
  rw [← int_sq_sub_mean i1 i2]
  exact integral_nonneg fun v => sq_nonneg _

/-- **The energy fluctuation by the centred gradient** (truncated Gaussian `L⁸` Poincaré):
`E_ξ|Q − EQ|⁸ ≤ (π/2)⁸·E|g|⁸·(4tΛ)⁴·E_ξ Q_v⁴`. -/
theorem flQ_grad_conc {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ξ, ENNReal.ofReal (|flQ μ a h M₀ (matOf t ξ) -
        ∫ ξ', flQ μ a h M₀ (matOf t ξ') ∂stdGauss (Fin m × Fin m)| ^ 8) ∂stdGauss (Fin m × Fin m) ≤
      ENNReal.ofReal ((π / 2) ^ 8 * gmom 8 * (4 * (t * Λ)) ^ 4) *
        ∫⁻ ξ, ENNReal.ofReal (flQv μ a h M₀ (matOf t ξ) ^ 4) ∂stdGauss (Fin m × Fin m) := by
  set Q : (Fin m × Fin m → ℝ) → ℝ := fun ξ => flQ μ a h M₀ (matOf t ξ) with hQd
  set Qv : (Fin m × Fin m → ℝ) → ℝ := fun ξ => flQv μ a h M₀ (matOf t ξ) with hQvd
  have hQ0 : ∀ ξ, 0 ≤ Q ξ := fun ξ => flQ_nonneg _ _ _ _
  have hQv0 : ∀ ξ, 0 ≤ Qv ξ := fun ξ => flQv_nonneg (μ := μ) ha hK h M₀ _
  have hS := sqrtQ_euLip ha hK hΛ0 hΛ h M₀ ht
  set L := √(t * Λ) with hLd
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have iQ : Integrable Q (stdGauss (Fin m × Fin m)) := by
    have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
  have cQ : Continuous Q :=
    ((hS.continuous hL0).pow 2).congr fun ζ => Real.sq_sqrt (flQ_nonneg _ _ _ _)
  set C₀ := (π / 2) ^ 8 * gmom 8 * (4 * (t * Λ)) ^ 4 with hC₀
  have hC₀0 : 0 ≤ C₀ := by have := gmom_nonneg 8; positivity
  -- the truncations
  set QN : ℕ → (Fin m × Fin m → ℝ) → ℝ := fun N ξ => min (Q ξ) ((N : ℝ) ^ 2) with hQNd
  have hQN_sq : ∀ N ξ, QN N ξ = (min (√(Q ξ)) (N : ℝ)) ^ 2 := by
    intro N ξ
    simp only [QN]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rcases le_total (√(Q ξ)) (N : ℝ) with h1 | h1
    · rw [min_eq_left h1, Real.sq_sqrt (hQ0 ξ)]
      have : Q ξ ≤ (N : ℝ) ^ 2 := by
        rw [← Real.sq_sqrt (hQ0 ξ)]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [min_eq_left this]
    · rw [min_eq_right h1]
      have : (N : ℝ) ^ 2 ≤ Q ξ := by
        rw [← Real.sq_sqrt (hQ0 ξ)]; exact pow_le_pow_left₀ hN0 h1 2
      rw [min_eq_right this]
  have hLip : ∀ N : ℕ, EuLip (QN N) (2 * N * L) := by
    intro N x y
    rw [hQN_sq, hQN_sq]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h0 : ∀ x, 0 ≤ min (√(Q x)) (N : ℝ) := fun x => le_min (Real.sqrt_nonneg _) hN0
    have hLN : |min (√(Q x)) (N : ℝ) - min (√(Q y)) N| ≤ L * √(∑ i, (x i - y i) ^ 2) := by
      have h := abs_min_sub_min_le_max (√(Q x)) (N : ℝ) (√(Q y)) N
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
      exact h.trans (hS x y)
    have e : (min (√(Q x)) (N : ℝ)) ^ 2 - (min (√(Q y)) N) ^ 2 =
        (min (√(Q x)) (N : ℝ) - min (√(Q y)) N) * (min (√(Q x)) (N : ℝ) + min (√(Q y)) N) := by
      ring
    have hs : |min (√(Q x)) (N : ℝ) + min (√(Q y)) N| ≤ 2 * N := by
      rw [abs_of_nonneg (add_nonneg (h0 x) (h0 y))]
      linarith [min_le_right (√(Q x)) (N : ℝ), min_le_right (√(Q y)) (N : ℝ)]
    rw [e, abs_mul]
    calc _ ≤ (L * √(∑ i, (x i - y i) ^ 2)) * (2 * N) :=
          mul_le_mul hLN hs (abs_nonneg _) (by positivity)
      _ = 2 * N * L * √(∑ i, (x i - y i) ^ 2) := by ring
  -- the gradient of the truncation
  have hgrad : ∀ N ξ, BstLean.Part151.gradSq (QN N) ξ ≤ 4 * (t * Λ) * Qv ξ := by
    intro N ξ
    have key := BstLean.Part153.gradSq_le_of_local (f := QN N) (ξ := ξ)
      (ℓ := 2 * √(Qv ξ) * L) ?_
    · unfold BstLean.Part151.gradSq
      refine key.trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, Real.sq_sqrt (hQv0 ξ), hLd, Real.sq_sqrt (by positivity)]; ring
    intro δ hδ
    have hcont : Continuous fun y : Fin m × Fin m → ℝ => 2 * (t * Λ) * √(∑ i, (y i - ξ i) ^ 2) :=
      continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_finsetSum _ fun i _ => ((continuous_apply i).sub continuous_const).pow 2))
    have hev : ∀ᶠ y in 𝓝 ξ, 2 * (t * Λ) * √(∑ i, (y i - ξ i) ^ 2) < δ := by
      refine Filter.Tendsto.eventually_lt_const ?_ (hcont.tendsto ξ)
      simpa using hδ
    filter_upwards [hev] with y hy
    have hloc := flQ_local ha hK hΛ0 hΛ h M₀ ht ξ y
    have hm : |QN N y - QN N ξ| ≤ |Q y - Q ξ| := by
      have := abs_min_sub_min_le_max (Q y) ((N : ℝ) ^ 2) (Q ξ) ((N : ℝ) ^ 2)
      rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this
    set d := √(∑ i, (y i - ξ i) ^ 2) with hdd
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hS2 : ∑ i, (y i - ξ i) ^ 2 = d ^ 2 := by
      rw [hdd, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have e1 : √(t * Λ * ∑ i, (y i - ξ i) ^ 2) = L * d := by
      rw [Real.sqrt_mul (by positivity), ← hLd]
    rw [e1, hS2] at hloc
    refine hm.trans (hloc.trans ?_)
    have : 2 * (t * Λ * d ^ 2) ≤ δ * d := by
      have := mul_le_mul_of_nonneg_right hy.le hd0
      nlinarith
    have e2 : 2 * √(flQv μ a h M₀ (matOf t ξ)) * (L * d) = 2 * √(Qv ξ) * L * d := by ring
    rw [e2]; nlinarith
  -- Poincaré for each truncation
  have hP : ∀ N : ℕ, ∫⁻ ξ, ENNReal.ofReal (|QN N ξ - ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)| ^ 8)
      ∂stdGauss (Fin m × Fin m) ≤ ENNReal.ofReal C₀ *
        ∫⁻ ξ, ENNReal.ofReal (Qv ξ ^ 4) ∂stdGauss (Fin m × Fin m) := by
    intro N
    have hLN0 : 0 ≤ 2 * (N : ℝ) * L := by positivity
    refine (BstLean.Part162.poincare_p_lint hLN0 (hLip N) (by norm_num : 1 ≤ 8)).trans ?_
    set g : (Fin m × Fin m → ℝ) → ℝ := fun x => √(BstLean.Part151.gradSq (QN N) x) ^ 8
    have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
    have hgb : ∀ x, g x ≤ (2 * N * L) ^ 8 := fun x => by
      have h1 := BstLean.Part151.gradSq_le hLN0 (hLip N) x
      have h2 : √(BstLean.Part151.gradSq (QN N) x) ≤ 2 * N * L := by
        rw [Real.sqrt_le_left hLN0]; exact h1
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 8
    have ig : Integrable g (stdGauss (Fin m × Fin m)) := by
      refine Integrable.mono' (integrable_const ((2 * N * L) ^ 8))
        ((BstLean.Part151.measurable_gradSq _).sqrt.pow_const 8).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgb x
    have hgq : ∀ x, g x ≤ (4 * (t * Λ)) ^ 4 * Qv x ^ 4 := fun x => by
      have e : g x = BstLean.Part151.gradSq (QN N) x ^ 4 := by
        simp only [g]
        rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul,
          Real.sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
      rw [e, ← mul_pow]
      exact pow_le_pow_left₀ (BstLean.Part151.gradSq_nonneg _ _) (hgrad N x) 4
    have hgm : ENNReal.ofReal (∫ x, g x ∂stdGauss (Fin m × Fin m)) ≤
        ENNReal.ofReal ((4 * (t * Λ)) ^ 4) *
          ∫⁻ ξ, ENNReal.ofReal (Qv ξ ^ 4) ∂stdGauss (Fin m × Fin m) := by
      rw [ofReal_integral_eq_lintegral_ofReal ig (Filter.Eventually.of_forall hg0),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hgq x)
    have hI0 : 0 ≤ ∫ x, g x ∂stdGauss (Fin m × Fin m) := integral_nonneg hg0
    calc ENNReal.ofReal ((π / 2) ^ 8 * (gmom 8 * ∫ x, g x ∂stdGauss (Fin m × Fin m)))
        = ENNReal.ofReal ((π / 2) ^ 8 * gmom 8) *
            ENNReal.ofReal (∫ x, g x ∂stdGauss (Fin m × Fin m)) := by
          rw [← ENNReal.ofReal_mul (by have := gmom_nonneg 8; positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal ((π / 2) ^ 8 * gmom 8) * (ENNReal.ofReal ((4 * (t * Λ)) ^ 4) *
            ∫⁻ ξ, ENNReal.ofReal (Qv ξ ^ 4) ∂stdGauss (Fin m × Fin m)) := by gcongr
      _ = ENNReal.ofReal C₀ * ∫⁻ ξ, ENNReal.ofReal (Qv ξ ^ 4) ∂stdGauss (Fin m × Fin m) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := gmom_nonneg 8; positivity)]
  -- the limit `N → ∞`
  have hpt : ∀ ξ, ∀ᶠ N : ℕ in atTop, QN N ξ = Q ξ := by
    intro ξ
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Q ξ)
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    simp only [QN]
    refine min_eq_left ?_
    have h1 : (N₀ : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
    have h2 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    nlinarith
  have hint : Tendsto (fun N : ℕ => ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)) atTop
      (𝓝 (∫ ξ', Q ξ' ∂stdGauss (Fin m × Fin m))) := by
    refine tendsto_integral_of_dominated_convergence Q (fun N => ?_) iQ (fun N => ?_) ?_
    · exact ((hLip N).continuous (by positivity)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hQ0 ξ) (by positivity))]
      exact min_le_left _ _
    · exact Filter.Eventually.of_forall fun ξ => tendsto_nhds_of_eventually_eq (hpt ξ)
  have hlim : ∀ ξ, Tendsto (fun N : ℕ => ENNReal.ofReal (|QN N ξ -
      ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)| ^ 8)) atTop
      (𝓝 (ENNReal.ofReal (|Q ξ - ∫ ξ', Q ξ' ∂stdGauss (Fin m × Fin m)| ^ 8))) := by
    intro ξ
    have h1 : Tendsto (fun N : ℕ => QN N ξ - ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)) atTop
        (𝓝 (Q ξ - ∫ ξ', Q ξ' ∂stdGauss (Fin m × Fin m))) :=
      (tendsto_nhds_of_eventually_eq (hpt ξ)).sub hint
    have hc : Continuous fun x : ℝ => ENNReal.ofReal (|x| ^ 8) :=
      ENNReal.continuous_ofReal.comp (continuous_abs.pow 8)
    exact (hc.tendsto _).comp h1
  have mN : ∀ N : ℕ, Measurable (fun ξ => ENNReal.ofReal (|QN N ξ -
      ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)| ^ 8)) := fun N =>
    ENNReal.measurable_ofReal.comp
      ((((hLip N).continuous (by positivity)).measurable.sub_const _).abs.pow_const 8)
  calc ∫⁻ ξ, ENNReal.ofReal (|Q ξ - ∫ ξ', Q ξ' ∂stdGauss (Fin m × Fin m)| ^ 8)
        ∂stdGauss (Fin m × Fin m)
      = ∫⁻ ξ, liminf (fun N : ℕ => ENNReal.ofReal (|QN N ξ -
          ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)| ^ 8)) atTop ∂stdGauss (Fin m × Fin m) :=
        lintegral_congr fun ξ => ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun N : ℕ => ∫⁻ ξ, ENNReal.ofReal (|QN N ξ -
          ∫ ξ', QN N ξ' ∂stdGauss (Fin m × Fin m)| ^ 8) ∂stdGauss (Fin m × Fin m)) atTop :=
        lintegral_liminf_le mN
    _ ≤ ENNReal.ofReal C₀ * ∫⁻ ξ, ENNReal.ofReal (Qv ξ ^ 4) ∂stdGauss (Fin m × Fin m) :=
        Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hP)

end core

section meas
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [SFinite μ]

/-- `M ↦ Qvar μ a M` is measurable. -/
lemma measurable_Qvar {a : V → Fin m → ℝ} (ha : Measurable a) :
    Measurable (fun M : Matrix (Fin m) (Fin m) ℝ => Qvar μ a M) := by
  unfold Qvar
  refine Finset.measurable_sum _ fun j _ => ?_
  have c1 : Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => relu ((p.1 *ᵥ p.2) j)) :=
    continuous_relu.comp ((continuous_apply j).comp
      (Continuous.matrix_mulVec continuous_fst continuous_snd))
  have m1 : Measurable (fun p : Matrix (Fin m) (Fin m) ℝ × V => relu ((p.1 *ᵥ a p.2) j)) :=
    c1.measurable.comp (measurable_fst.prodMk (ha.comp measurable_snd))
  have m2 : Measurable (fun p : Matrix (Fin m) (Fin m) ℝ × V => relu ((p.1 *ᵥ a p.2) j) ^ 2) :=
    m1.pow_const 2
  exact (m2.stronglyMeasurable.integral_prod_right').measurable.sub
    ((m1.stronglyMeasurable.integral_prod_right').measurable.pow_const 2)

end meas

section net
open BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part157 (cOf reb)
variable {n : ℕ}

/-- The centred energy at fixed plane coordinates is the centred energy of the whole matrix. -/
lemma flQv_Mpl (c : Ret n) (s : ℝ) (c₁ c₂ : Fin (mA n) → ℝ) (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    flQv (stdGauss (Fin (n - 1))) (aLat c s) (hB c)
      (Mpl (hB c) (res (hB c) (a1Bar c s)) c₁ c₂ 0) N =
    Qvar (stdGauss (Fin (n - 1))) (aLat c s) (Mpl (hB c) (res (hB c) (a1Bar c s)) c₁ c₂ N) := by
  unfold flQv Qvar
  rw [vmean_aLat]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Mpl_mulVec (hB c) (res (hB c) (a1Bar c s)) c₁ c₂ N]
  rfl

/-- The fourth moment of the centred energy at fixed plane coordinates. -/
noncomputable def GQ (c : Ret n) (s : ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ N, ENNReal.ofReal (Qvar (stdGauss (Fin (n - 1))) (aLat c s) (reb (hB c) (cOf (tA n) (hB c) ξ₁)
    (reb (res (hB c) (a1Bar c s)) (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) N)) ^ 4)
    ∂gaussMat (mA n) (mA n) (tA n)

lemma measurable_Qvar4 (c : Ret n) (s : ℝ) : Measurable (fun M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
    ENNReal.ofReal (Qvar (stdGauss (Fin (n - 1))) (aLat c s) M ^ 4)) :=
  ENNReal.measurable_ofReal.comp ((measurable_Qvar (measurable_aLat c s)).pow_const 4)

lemma measurable_GQ (c : Ret n) (s : ℝ) :
    Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => GQ c s p.1 p.2) := by
  have : Measurable (fun p : ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (Qvar (stdGauss (Fin (n - 1)))
        (aLat c s) (reb (hB c) (cOf (tA n) (hB c) p.1.1) (reb (res (hB c) (a1Bar c s))
          (cOf (tA n) (res (hB c) (a1Bar c s)) p.1.2) p.2)) ^ 4)) :=
    (measurable_Qvar4 c s).comp (BstLean.Part157.measurable_reb_comp measurable_const
      (BstLean.Part157.measurable_cOf_comp (tA n) measurable_const
        (measurable_fst.comp measurable_fst))
      (BstLean.Part157.measurable_reb_comp measurable_const
        (BstLean.Part157.measurable_cOf_comp (tA n) measurable_const
          (measurable_snd.comp measurable_fst)) measurable_snd))
  exact this.lintegral_prod_right'

lemma measurable_GQ2 (c : Ret n) (s : ℝ) (ξ₁ : Fin (mA n) → ℝ) : Measurable (GQ c s ξ₁) :=
  Measurable.of_uncurry_left (f := GQ c s) (measurable_GQ c s)

lemma GQ_tot (c : Ret n) (s : ℝ) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, GQ c s ξ₁ ξ₂ ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) =
      ∫⁻ M, ENNReal.ofReal (Qvar (stdGauss (Fin (n - 1))) (aLat c s) M ^ 4)
        ∂gaussMat (mA n) (mA n) (tA n) := by
  have mFQ : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (Qvar (stdGauss (Fin (n - 1))) (aLat c s) p.2.2 ^ 4)) :=
    (measurable_Qvar4 c s).comp (measurable_snd.comp measurable_snd)
  have hpsQ := BstLean.Part167.plane_split (q := mA n) (tA n) (hB c) (a1Bar c s) mFQ
  exact hpsQ.symm

/-- **The centred energy fluctuation at a node, given the fourth moment of the centred energy.** -/
theorem exWn_mom_J_of (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 < O) (h1 : OpB (A1 c) O) {q : ℝ} (hq0 : 0 < q) (hq : 1 - nodeS c g ^ 2 ≤ q) {B : ℝ}
    (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8))
    (hQ4 : ∫⁻ M, ENNReal.ofReal (Qvar (stdGauss (Fin (n - 1))) (aLat c (nodeS c g)) M ^ 4)
      ∂gaussMat (mA n) (mA n) (tA n) ≤ ENNReal.ofReal ((√((mA n : ℝ) * tA n *
        (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2) + π / 2 * (18 / 10) * (√(tA n) * O)) ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((WflJ n O q + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set μv := stdGauss (Fin (n - 1))
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hΛ0 : 0 < Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean μv (aLat c s))) ^ 2
      ∂μv ≤ Λ * normSq e := fun e =>
    (BstLean.Part173.cov_bound_lat hn c hs hO.le h1 e).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) h2n.le)
      (normSq_nonneg e))
  set L := √(tA n * Λ) with hLd
  have hL : 0 < L := Real.sqrt_pos.mpr (mul_pos htA hΛ0)
  set Y := √((mA n : ℝ) * tA n * (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2) +
    π / 2 * (18 / 10) * (√(tA n) * O) with hYd
  have hY : 0 < Y := by
    have : 0 < π / 2 * (18 / 10) * (√(tA n) * O) := by
      have := Real.sqrt_pos.mpr htA; positivity
    have := Real.sqrt_nonneg ((mA n : ℝ) * tA n * (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2)
    linarith
  set A := WflJ n O q with hAd
  have hAe : A = 2 * (π / 2 * (18 / 10) * L) * Y := by rw [hAd]; unfold WflJ; rfl
  have hA : 0 < A := by rw [hAe]; positivity
  set C₀ := (π / 2) ^ 8 * gmom 8 * (4 * (tA n * Λ)) ^ 4 with hC₀
  have hC₀0 : 0 ≤ C₀ := by have := gmom_nonneg 8; positivity
  have hCA : C₀ * Y ^ 8 ≤ A ^ 8 := by
    rw [hAe, hC₀]
    have hg := gmom8_le
    have hL2 : L ^ 2 = tA n * Λ := by rw [hLd]; exact Real.sq_sqrt (by positivity)
    have e : (2 * (π / 2 * (18 / 10) * L) * Y) ^ 8 =
        (π / 2) ^ 8 * (18 / 10) ^ 8 * (4 * (tA n * Λ)) ^ 4 * Y ^ 8 := by
      rw [← hL2]; ring
    rw [e]
    have : 0 ≤ (π / 2) ^ 8 * (4 * (tA n * Λ)) ^ 4 * Y ^ 8 := by positivity
    nlinarith
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have hGtot : ∫⁻ ξ₁, ∫⁻ ξ₂, GQ c s ξ₁ ξ₂ ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ≤
      ENNReal.ofReal (Y ^ 8) := by
    rw [GQ_tot]; exact hQ4
  have e0 : ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * GQ c s ξ₁ ξ₂) +
        ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set C₀' := ∑ j, G2 √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set E : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ := fun N =>
      exWn (withA2 c (reb h c₁ (reb r c₂ N))) g
    have mE : Measurable E :=
      measurable_exWn_comp ((measurable_withA2 c).comp (BstLean.Part157.measurable_reb_comp
        measurable_const measurable_const (BstLean.Part157.measurable_reb_comp measurable_const
          measurable_const measurable_id))) measurable_const
    have hE : ∀ N, E N = flQ μv (aLat c s) h M₀ N - C₀' := fun N =>
      exWn_Mpl hn1 c g hK c₁ c₂ N
    set F : (Fin (mA n) × Fin (mA n) → ℝ) → ℝ := fun ζ =>
      flQ μv (aLat c s) h M₀ (matOf (tA n) ζ)
    have hS := sqrtQ_euLip (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
    have iF : Integrable F (stdGauss (Fin (mA n) × Fin (mA n))) := by
      have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
      refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
      exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
    set qb := ∫ ζ, F ζ ∂stdGauss (Fin (mA n) × Fin (mA n))
    have hmE : biasW c g ξ₁ ξ₂ = qb - C₀' := by
      have e0 : biasW c g ξ₁ ξ₂ = ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) := rfl
      rw [e0, gaussMat_eq, integral_map (measurable_matOf _).aemeasurable mE.aestronglyMeasurable]
      have : (fun ζ => E (matOf (tA n) ζ)) = fun ζ => F ζ - C₀' := funext fun ζ => hE _
      rw [this]
      rw [integral_sub iF (integrable_const _)]
      simp
      rfl
    have hfl := flQ_grad_conc (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
    have hGeq : ∫⁻ ζ, ENNReal.ofReal (flQv μv (aLat c s) h M₀ (matOf (tA n) ζ) ^ 4)
        ∂stdGauss (Fin (mA n) × Fin (mA n)) = GQ c s ξ₁ ξ₂ := by
      have hmN : Measurable (fun N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
          ENNReal.ofReal (Qvar μv (aLat c s) (reb h c₁ (reb r c₂ N)) ^ 4)) :=
        (measurable_Qvar4 c s).comp (BstLean.Part157.measurable_reb_comp measurable_const
          measurable_const
          (BstLean.Part157.measurable_reb_comp measurable_const measurable_const measurable_id))
      show _ = ∫⁻ N, ENNReal.ofReal (Qvar μv (aLat c s) (reb h c₁ (reb r c₂ N)) ^ 4)
        ∂gaussMat (mA n) (mA n) (tA n)
      rw [gaussMat_eq, lintegral_map hmN (measurable_matOf _)]
      refine lintegral_congr fun ζ => ?_
      simp only [M₀]
      rw [flQv_Mpl]
      rfl
    have hpt : ∀ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|F ζ - qb| ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
      intro ζ
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (F ζ - qb) (biasW c g ξ₁ ξ₂) hA hB0
      have e8 : |biasW c g ξ₁ ξ₂| ^ 8 = biasW c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      have e : E (matOf (tA n) ζ) = F ζ - qb + biasW c g ξ₁ ξ₂ := by rw [hE, hmE]; ring
      rw [e]; exact this
    have cF : Continuous F :=
      ((hS.continuous (Real.sqrt_nonneg _)).pow 2).congr fun ζ => Real.sq_sqrt (flQ_nonneg _ _ _ _)
    have mfl : Measurable (fun ζ => ENNReal.ofReal (|F ζ - qb| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((cF.measurable.sub_const _).abs).pow_const 8)
    rw [gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (E N ^ 8))
      (ENNReal.measurable_ofReal.comp (mE.pow_const 8)) (measurable_matOf _)]
    calc ∫⁻ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ∂stdGauss (Fin (mA n) × Fin (mA n))
        ≤ ∫⁻ ζ, (ENNReal.ofReal k₁ * ENNReal.ofReal (|F ζ - qb| ^ 8) +
          ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n) × Fin (mA n)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ ζ, ENNReal.ofReal (|F ζ - qb| ^ 8)
            ∂stdGauss (Fin (mA n) × Fin (mA n)) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * GQ c s ξ₁ ξ₂) +
            ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          gcongr
          rw [← hGeq]
          exact hfl
      _ = _ := by rw [ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * GQ c s ξ₁ ξ₂) +
          ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8))
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * ∫⁻ ξ₁, ∫⁻ ξ₂, GQ c s ξ₁ ξ₂
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))) +
          ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have e1 : ∀ ξ₁ : Fin (mA n) → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ *
            GQ c s ξ₁ ξ₂) + ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8))
            ∂stdGauss (Fin (mA n)) =
            ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * ∫⁻ ξ₂, GQ c s ξ₁ ξ₂ ∂stdGauss (Fin (mA n))) +
            ENNReal.ofReal k₂ * ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)
              ∂stdGauss (Fin (mA n)) := fun ξ₁ => by
          have mI1 : Measurable (fun ξ₂ : Fin (mA n) → ℝ =>
              ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * GQ c s ξ₁ ξ₂)) :=
            measurable_const.mul (measurable_const.mul (measurable_GQ2 c s ξ₁))
          rw [lintegral_add_left mI1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        have mJ : Measurable (fun ξ₁ : Fin (mA n) → ℝ => ENNReal.ofReal k₁ *
            (ENNReal.ofReal C₀ * ∫⁻ ξ₂, GQ c s ξ₁ ξ₂ ∂stdGauss (Fin (mA n)))) :=
          measurable_const.mul (measurable_const.mul (measurable_GQ c s).lintegral_prod_right')
        rw [lintegral_add_left mJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal k₁ * (ENNReal.ofReal C₀ * ENNReal.ofReal (Y ^ 8)) +
          ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
    _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
        rw [← ENNReal.ofReal_mul hC₀0]
        exact ENNReal.ofReal_le_ofReal hCA
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_mul hk₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

/-- **The centred energy fluctuation bound** (`EnJ_stmt`): Part 174's `exWn_mom_r` with the
allowance `WflJ`. -/
theorem EnJ_proved : EnJ_stmt := by
  intro n hn c g hs O hO h1 q hq0 hq B hB0 hBias
  refine exWn_mom_J_of hn c g hs hO h1 hq0 hq hB0 hBias ?_
  have hn1 : 1 ≤ n := by omega
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hK2 : ∀ v, normSq (aLat c (nodeS c g) v) ≤ O ^ 2 := aLat_normSq_le hn1 c hs h1
  have hT : ∫ v, normSq (aLat c (nodeS c g) v - vmean (stdGauss (Fin (n - 1)))
      (aLat c (nodeS c g))) ∂stdGauss (Fin (n - 1)) ≤ q * n * O ^ 2 / ((n : ℝ) - 2) := by
    rw [vmean_aLat]
    refine (trCov_lat hn c hs hO.le h1).trans ?_
    refine div_le_div_of_nonneg_right ?_ h2n.le
    have : (0 : ℝ) ≤ n * O ^ 2 := by positivity
    nlinarith
  have h4 := Qvar_mom4_gm (μ := stdGauss (Fin (n - 1))) (measurable_aLat c (nodeS c g)) hK hK2
    (by positivity) htA hT
  have e : √(tA n * O ^ 2) = √(tA n) * O := by
    rw [Real.sqrt_mul htA.le, Real.sqrt_sq hO.le]
  rw [e] at h4
  exact h4

end net

end BstLean.Part183

#print axioms BstLean.Part183.flQ_local
#print axioms BstLean.Part183.flQ_grad_conc
#print axioms BstLean.Part183.exWn_mom_J_of
#print axioms BstLean.Part183.EnJ_proved
