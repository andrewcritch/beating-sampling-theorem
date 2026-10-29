import BstLean.Part208RotatedMoment
import BstLean.Part182SchurI

/-! Part 208: the actual core input set and weight in axial coordinates. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53)
open BstLean.Part153 (nrm)
open BstLean.Part161 (hhMat hh_normSq)
open BstLean.Part182 (OmegaS wN uC)

def axialCore (n : ℕ) (t0 z0 Z r : ℝ) : Prop :=
  |Z| ≤ t0 ∧ (n : ℝ) - 2 * √((n : ℝ) * z0) ≤ Z ^ 2 + r ^ 2 ∧
    Z ^ 2 + r ^ 2 ≤ (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0

noncomputable def coreAxialWeight (n : ℕ) (a τ t0 z0 Z r : ℝ) : ℝ := by
  classical
  exact if axialCore n t0 z0 Z r then τ ^ 2 / ((a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2) else 0

lemma coreAxialWeight_measurable (n : ℕ) (a τ t0 z0 : ℝ) :
    Measurable (Function.uncurry (coreAxialWeight n a τ t0 z0)) := by
  classical
  have hZ : Measurable (fun y : ℝ × ℝ => |y.1|) := by fun_prop
  have hN : Measurable (fun y : ℝ × ℝ => y.1 ^ 2 + y.2 ^ 2) := by fun_prop
  have hS : MeasurableSet {y : ℝ × ℝ | axialCore n t0 z0 y.1 y.2} := by
    unfold axialCore
    exact (measurableSet_le hZ measurable_const).inter
      ((measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const))
  change Measurable (fun y : ℝ × ℝ => if axialCore n t0 z0 y.1 y.2 then
    τ ^ 2 / ((a + τ * y.1) ^ 2 + τ ^ 2 * y.2 ^ 2) else 0)
  exact Measurable.ite hS (by fun_prop) measurable_const

lemma coreAxialWeight_nonneg (n : ℕ) (a τ t0 z0 Z r : ℝ) :
    0 ≤ coreAxialWeight n a τ t0 z0 Z r := by
  unfold coreAxialWeight
  split_ifs <;> positivity

lemma uC_smul_unit {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1) {a : ℝ} (ha : 0 < a) :
    uC (a • u) = u := by
  have he : nrm (a • u) = a := by
    unfold nrm
    rw [BstLean.Part130.normSq_smul, hu, mul_one, sqrt_sq ha.le]
  unfold uC
  rw [he, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

lemma omega_axial_iff {d : ℕ} {u : Fin (d + 1) → ℝ} (hu : normSq u = 1)
    {a : ℝ} (ha : 0 < a) (t0 z0 : ℝ) (ξ : Fin (d + 1) → ℝ) :
    ξ ∈ OmegaS (a • u) t0 z0 ↔ axialCore (d + 1) t0 z0 ((hhMat u *ᵥ ξ) 0)
      (radF53 (Fin.tail (hhMat u *ᵥ ξ))) := by
  have hN : normSq ξ = ((hhMat u *ᵥ ξ) 0) ^ 2 +
      (radF53 (Fin.tail (hhMat u *ᵥ ξ))) ^ 2 := by
    rw [BstLean.Part162.radF_sq]
    have h := normSq_cons ((hhMat u *ᵥ ξ) 0) (Fin.tail (hhMat u *ᵥ ξ))
    rwa [Fin.cons_self_tail, hh_normSq] at h
  simp only [OmegaS, mem_setOf_eq, uC_smul_unit hu ha, axialCore,
    hh_zero_coordinate hu, hN]

lemma shift_normSq_axial {d : ℕ} {u : Fin (d + 1) → ℝ} (hu : normSq u = 1)
    (a τ : ℝ) (ξ : Fin (d + 1) → ℝ) :
    normSq (a • u + τ • ξ) = (a + τ * ((hhMat u *ᵥ ξ) 0)) ^ 2 +
      τ ^ 2 * (radF53 (Fin.tail (hhMat u *ᵥ ξ))) ^ 2 := by
  have he : a • u + τ • ξ = hhMat u *ᵥ
      Fin.cons (a + τ * ((hhMat u *ᵥ ξ) 0)) (τ • Fin.tail (hhMat u *ᵥ ξ)) := by
    rw [← shift_cons, Fin.cons_self_tail, hh_shift hu, hh_involutive]
  rw [he, hh_normSq, normSq_cons, BstLean.Part130.normSq_smul, BstLean.Part162.radF_sq]
  rfl

/-- The radial weight is exactly the original core indicator times the original weight. -/
theorem axialWeight_core_eq {d : ℕ} {u : Fin (d + 1) → ℝ} (hu : normSq u = 1)
    {a : ℝ} (ha : 0 < a) (τ t0 z0 : ℝ) :
    axialWeight u (coreAxialWeight (d + 1) a τ t0 z0) =
      (OmegaS (a • u) t0 z0).indicator (wN (a • u) τ) := by
  funext ξ
  unfold axialWeight coreAxialWeight
  rw [← omega_axial_iff hu ha]
  by_cases h : ξ ∈ OmegaS (a • u) t0 z0
  · rw [if_pos h, indicator_of_mem h]
    unfold wN
    rw [shift_normSq_axial hu]
    exact div_eq_mul_inv _ _
  · rw [if_neg h, indicator_of_notMem h]

lemma axialLong_sq (a τ r : ℝ) :
    axialLong a τ r ^ 2 = a ^ 2 / (a ^ 2 + τ ^ 2 * r ^ 2) := by
  unfold axialLong axialDen
  rw [div_pow, sq_sqrt (by positivity)]

/-- A scalar latitude guard supplies the required bound on the concrete radial weight. -/
theorem coreAxialWeight_plane (n : ℕ) (a τ t0 z0 : ℝ) {sp : ℝ}
    (hplane : ∀ Z r, axialCore n t0 z0 Z r →
      (a + τ * Z) ^ 2 / ((a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2) ≤ sp) :
    ∀ Z r, coreAxialWeight n a τ t0 z0 Z r * axialLong (a + τ * Z) τ r ^ 2 ≤
      sp * coreAxialWeight n a τ t0 z0 Z r := by
  intro Z r
  by_cases h : axialCore n t0 z0 Z r
  · have he := mul_le_mul_of_nonneg_left (hplane Z r h)
      (coreAxialWeight_nonneg n a τ t0 z0 Z r)
    rw [← axialLong_sq] at he
    simpa only [mul_comm] using he
  · simp [coreAxialWeight, h]

end BstLean.Part208
