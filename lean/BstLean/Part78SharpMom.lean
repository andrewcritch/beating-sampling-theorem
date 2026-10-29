import BstLean.Part78SharpComb
import BstLean.Part29Sphere

/-!
# Part 78 (sharp), sphere moments of `(linear + quadratic)²`

For `ν` uniform on `S^{n−1}`: `E (a·x + xᵀAx)² = ‖a‖²/n + ((tr A)² + Σ A_ij² + Σ A_ij A_ji)/(n(n+2))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part29 (uniformSphere SphereMoments)

variable {n : ℕ}

/-- A continuous function is integrable under the uniform distribution on the sphere. -/
lemma sphere_cont_integrable' (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

/-- The linear form `a·x`. -/
def linF (a : Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, a i * x i

/-- The quadratic form `xᵀAx`. -/
def quadF (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * (x i * x j)

lemma continuous_linF (a : Fin n → ℝ) : Continuous (linF a) := by
  unfold linF; fun_prop

lemma continuous_quadF (A : Fin n → Fin n → ℝ) : Continuous (quadF A) := by
  unfold quadF; fun_prop

lemma int_lin_lin (hn : 1 ≤ n) (a b : Fin n → ℝ) :
    ∫ x, linF a x * linF b x ∂uniformSphere n = (∑ i, a i * b i) / n := by
  classical
  have h := BstLean.Part29.uniformSphere_moments n hn
  have hexp : ∀ x : Fin n → ℝ, linF a x * linF b x = ∑ i, ∑ j, a i * b j * (x i * x j) := by
    intro x; unfold linF
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (h.int2 i j).const_mul _)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (h.int2 i j).const_mul _)]
  simp_rw [integral_const_mul, h.m2]
  simp
  ring

lemma int_lin_quad (hn : 1 ≤ n) (a : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    ∫ x, linF a x * quadF A x ∂uniformSphere n = 0 := by
  classical
  have h := BstLean.Part29.uniformSphere_moments n hn
  have hexp : ∀ x : Fin n → ℝ, linF a x * quadF A x =
      ∑ i, ∑ j, ∑ k, a i * A j k * (x i * x j * x k) := by
    intro x; unfold linF quadF
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => (h.int3 i j k).const_mul _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => (h.int3 i j k).const_mul _)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => (h.int3 i j k).const_mul _)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, h.m3, mul_zero]

lemma int_quad_quad (hn : 1 ≤ n) (A C : Fin n → Fin n → ℝ) :
    ∫ x, quadF A x * quadF C x ∂uniformSphere n =
      ((∑ i, A i i) * (∑ i, C i i) + ∑ i, ∑ j, A i j * C i j + ∑ i, ∑ j, A i j * C j i) /
        ((n : ℝ) * (n + 2)) := by
  classical
  have h := BstLean.Part29.uniformSphere_moments n hn
  have hexp : ∀ x : Fin n → ℝ, quadF A x * quadF C x =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * C k l * (x i * x j * x k * x l) := by
    intro x; unfold quadF
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  have e : ∫ x, ∑ i, ∑ j, ∑ k, ∑ l, A i j * C k l * (x i * x j * x k * x l) ∂uniformSphere n =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * C k l *
        (((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
          (if i = l ∧ j = k then 1 else 0)) / ((n : ℝ) * (n + 2))) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
        (h.int4 i j k l).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => (h.int4 i j k l).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ =>
        (h.int4 i j k l).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun l _ => (h.int4 i j k l).const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, h.m4]
  rw [e]
  have t1 : ∑ i, ∑ j, ∑ k, ∑ l, A i j * C k l * (if i = j ∧ k = l then (1 : ℝ) else 0) =
      (∑ i, A i i) * (∑ i, C i i) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_and]
  have t2 : ∑ i, ∑ j, ∑ k, ∑ l, A i j * C k l * (if i = k ∧ j = l then (1 : ℝ) else 0) =
      ∑ i, ∑ j, A i j * C i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ite_and]
  have t3 : ∑ i, ∑ j, ∑ k, ∑ l, A i j * C k l * (if i = l ∧ j = k then (1 : ℝ) else 0) =
      ∑ i, ∑ j, A i j * C j i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ite_and]
  rw [← t1, ← t2, ← t3]
  simp only [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end BstLean.Part78
