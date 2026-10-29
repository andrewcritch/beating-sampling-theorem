import BstLean.Part205Geometry

/-! Radial-weight moments used in the deterministic distance mean. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part133

lemma radial_deviation_le {a : ℝ} (ha : 0 ≤ a) :
    (a - 1) ^ 2 ≤ (a ^ 2 - 1) ^ 2 := by
  have h := mul_nonneg (mul_nonneg ha (by linarith : 0 ≤ a + 2)) (sq_nonneg (a - 1))
  nlinarith [h]

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {a : Ω → ℝ}

/-- Coordinate Jensen gives the squared norm of the vector mean. -/
lemma vector_mean_sq_le {m : ℕ} {f : Ω → Fin m → ℝ}
    (hi : ∀ j, Integrable (fun x => f x j ^ 2) μ) :
    normSq (fun j => ∫ x, f x j ∂μ) ≤ ∫ x, normSq (f x) ∂μ := by
  unfold normSq
  rw [integral_finsetSum _ (fun j _ => hi j)]
  exact Finset.sum_le_sum fun j _ => sq_integral_le (hi j)

/-- A constant-norm vector field converts radial deviation to centroid displacement. -/
lemma radial_centroid_bound {m : ℕ} {z : Ω → Fin m → ℝ} {Q : ℝ}
    (hz : ∀ᵐ x ∂μ, normSq (z x) = Q)
    (hi : ∀ j, Integrable (fun x => ((1 - a x) • z x) j ^ 2) μ) :
    normSq (fun j => ∫ x, ((1 - a x) • z x) j ∂μ) ≤
      Q * ∫ x, (a x - 1) ^ 2 ∂μ := by
  refine (vector_mean_sq_le hi).trans (le_of_eq ?_)
  calc (∫ x, normSq ((1 - a x) • z x) ∂μ) =
      ∫ x, Q * (a x - 1) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hz] with x hx
        rw [normSq_smul, hx]
        ring
    _ = _ := integral_const_mul _ _

lemma radial_second_le (ha : ∀ᵐ x ∂μ, 0 ≤ a x)
    (hi : Integrable (fun x => (a x - 1) ^ 2) μ)
    (hi' : Integrable (fun x => (a x ^ 2 - 1) ^ 2) μ) :
    (∫ x, (a x - 1) ^ 2 ∂μ) ≤ ∫ x, (a x ^ 2 - 1) ^ 2 ∂μ := by
  exact integral_mono_ae hi hi' (ha.mono fun x hx => radial_deviation_le hx)

/-- The pair radial moment uses independent inputs, with the same radial field. -/
theorem radial_pair_second (hi : Integrable a μ)
    (hi2 : Integrable (fun x => a x ^ 2) μ) (h2 : ∫ x, a x ^ 2 ∂μ = 1) :
    Integrable (fun p : Ω × Ω => (1 - a p.1 * a p.2) ^ 2) (μ.prod μ) ∧
    (∫ p : Ω × Ω, (1 - a p.1 * a p.2) ^ 2 ∂μ.prod μ) =
      2 * (1 - (∫ x, a x ∂μ) ^ 2) := by
  have iP := hi.mul_prod hi
  have iP2 := hi2.mul_prod hi2
  have hexp : (fun p : Ω × Ω => (1 - a p.1 * a p.2) ^ 2) =
      fun p => 1 - 2 * (a p.1 * a p.2) + a p.1 ^ 2 * a p.2 ^ 2 := by
    funext p
    ring
  rw [hexp]
  have iC : Integrable (fun p : Ω × Ω => 1 - 2 * (a p.1 * a p.2)) (μ.prod μ) :=
    (integrable_const 1).sub (iP.const_mul 2)
  refine ⟨iC.add iP2, ?_⟩
  rw [integral_add iC iP2,
    integral_sub (integrable_const 1) (iP.const_mul 2), integral_const_mul,
    integral_prod_mul a a, integral_prod_mul (fun x => a x ^ 2) (fun x => a x ^ 2), h2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem radial_pair_second_le (hi : Integrable a μ)
    (hi2 : Integrable (fun x => a x ^ 2) μ) (h2 : ∫ x, a x ^ 2 ∂μ = 1) :
    (∫ p : Ω × Ω, (1 - a p.1 * a p.2) ^ 2 ∂μ.prod μ) ≤
      2 * (∫ x, (a x - 1) ^ 2 ∂μ) := by
  have hexp : (fun x => (a x - 1) ^ 2) = fun x => a x ^ 2 - 2 * a x + 1 := by
    funext x
    ring
  have iC : Integrable (fun x => a x ^ 2 - 2 * a x) μ := hi2.sub (hi.const_mul 2)
  rw [(radial_pair_second hi hi2 h2).2, hexp,
    integral_add iC (integrable_const 1),
    integral_sub hi2 (hi.const_mul 2), integral_const_mul, h2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  nlinarith [sq_nonneg ((∫ x, a x ∂μ) - 1)]

end
end BstLean.Part205

#print axioms BstLean.Part205.radial_second_le
#print axioms BstLean.Part205.radial_pair_second
#print axioms BstLean.Part205.radial_pair_second_le
#print axioms BstLean.Part205.vector_mean_sq_le
#print axioms BstLean.Part205.radial_centroid_bound
