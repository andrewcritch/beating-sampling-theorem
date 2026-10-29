import BstLean.Part158Basic

/-!
# Part 158 (file `Coord`): the coordinate derivatives of `U`, `T` and `exp T / U`

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι]
  {F : X → (ι → ℝ) → ℝ} {dF : X → (ι → ℝ) → ι → ℝ} {a b C : ℝ}

omit [Fintype ι] in
lemma hasDerivAt_curve [DecidableEq ι] (c s : ℝ) (k : ι) (ξ ξ' : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => c • Function.update ξ k t + s • ξ') (c • (Pi.single k (1 : ℝ))) t := by
  rw [hasDerivAt_pi]
  intro j
  by_cases hj : j = k
  · subst hj
    have h1 : HasDerivAt (fun t : ℝ => c * t + s * ξ' j) (c * 1) t :=
      ((hasDerivAt_id t).const_mul c).add_const _
    simpa using h1
  · have h1 : HasDerivAt (fun _ : ℝ => c * ξ j + s * ξ' j) 0 t := hasDerivAt_const _ _
    simpa [hj] using h1

lemma Fam.F_curve [DecidableEq ι] (h : Fam F dF a b C) (c s : ℝ) (x : X) (k : ι)
    (ξ ξ' : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => F x (c • Function.update ξ k t + s • ξ'))
      (c * dF x (c • Function.update ξ k t + s • ξ') k) t := by
  have h1 := (h.hd x (c • Function.update ξ k t + s • ξ')).comp_hasDerivAt t
    (hasDerivAt_curve c s k ξ ξ' t)
  have e : dotL (dF x (c • Function.update ξ k t + s • ξ')) (c • (Pi.single k (1 : ℝ))) =
      c * dF x (c • Function.update ξ k t + s • ξ') k := by
    rw [dotL_apply]
    simp [Pi.single_apply, mul_comm]
  rw [e] at h1
  exact h1

/-- The derivative of `U` in the coordinate `k` at every point of the line. -/
lemma Fam.U_coord' [DecidableEq ι] (h : Fam F dF a b C) (c s : ℝ) (x : X) (k : ι)
    (ξ : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => U F c s x (Function.update ξ k t))
      (c * Abar dF c s x (Function.update ξ k t) k) t := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGauss ι)
    (F := fun t ξ' => F x (c • Function.update ξ k t + s • ξ'))
    (F' := fun t ξ' => c * dF x (c • Function.update ξ k t + s • ξ') k)
    (x₀ := t) (bound := fun _ => |c| * C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (h.integrable_F c s x _).aestronglyMeasurable)
    (h.integrable_F c s x _)
    ((h.integrable_dF c s x _ k).const_mul c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ' t _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h.hC _ _ _) (abs_nonneg _))
    (integrable_const _)
    (Filter.Eventually.of_forall fun ξ' t _ => h.F_curve c s x k ξ ξ' t)
  have h2 := key.2
  rw [integral_const_mul] at h2
  exact h2

theorem Fam.U_coord [DecidableEq ι] (h : Fam F dF a b C) (c s : ℝ) (x : X) (k : ι) (ξ : ι → ℝ) :
    HasDerivAt (fun t => U F c s x (Function.update ξ k t)) (c * Abar dF c s x ξ k) (ξ k) := by
  have h1 := h.U_coord' c s x k ξ (ξ k)
  rw [Function.update_eq_self] at h1
  exact h1

lemma Fam.T_coord' [DecidableEq ι] (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ]
    (L c s : ℝ) (k : ι) (ξ : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => T μ L F c s (Function.update ξ k t))
      (c * Vv μ L F dF c s (Function.update ξ k t) k) t := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t x => log (U F c s x (Function.update ξ k t)))
    (F' := fun t x => c * wv F dF c s x (Function.update ξ k t) k)
    (x₀ := t) (bound := fun _ => |c| * (C / a)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (h.integrable_logU μ c s _).aestronglyMeasurable)
    (h.integrable_logU μ c s _)
    ((h.integrable_wv μ c s _ k).const_mul c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h.wv_le _ _ _ _ _) (abs_nonneg _))
    (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ => by
      have h1 := (h.U_coord' c s x k ξ t).log (h.U_pos c s x _).ne'
      have e : c * Abar dF c s x (Function.update ξ k t) k / U F c s x (Function.update ξ k t) =
          c * wv F dF c s x (Function.update ξ k t) k := by
        unfold wv; ring
      rw [e] at h1
      exact h1)
  have h2 := key.2.const_mul L⁻¹
  rw [integral_const_mul] at h2
  have e : L⁻¹ * (c * ∫ x, wv F dF c s x (Function.update ξ k t) k ∂μ) =
      c * Vv μ L F dF c s (Function.update ξ k t) k := by
    unfold Vv; ring
  rw [e] at h2
  exact h2

theorem Fam.T_coord [DecidableEq ι] (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ]
    (L c s : ℝ) (k : ι) (ξ : ι → ℝ) :
    HasDerivAt (fun t => T μ L F c s (Function.update ξ k t)) (c * Vv μ L F dF c s ξ k) (ξ k) := by
  have h1 := h.T_coord' μ L c s k ξ (ξ k)
  rw [Function.update_eq_self] at h1
  exact h1

theorem Fam.W_coord [DecidableEq ι] (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ]
    (L c s : ℝ) (x : X) (k : ι) (ξ : ι → ℝ) :
    HasDerivAt
      (fun t => exp (T μ L F c s (Function.update ξ k t)) / U F c s x (Function.update ξ k t))
      (exp (T μ L F c s ξ) / U F c s x ξ * (c * Vv μ L F dF c s ξ k - c * wv F dF c s x ξ k))
      (ξ k) := by
  have hU0 : U F c s x ξ ≠ 0 := (h.U_pos c s x ξ).ne'
  have h1 := ((h.T_coord μ L c s k ξ).exp).div (h.U_coord c s x k ξ)
    (by rw [Function.update_eq_self]; exact hU0)
  simp only [Function.update_eq_self] at h1
  convert h1 using 1
  unfold wv
  field_simp

end BstLean.Part158

open BstLean.Part158 in
#print axioms Fam.U_coord
open BstLean.Part158 in
#print axioms Fam.T_coord
open BstLean.Part158 in
#print axioms Fam.W_coord
