import BstLean.Part209OverlapMoment
import BstLean.Part209Comparison
import BstLean.Part209Lengths

/-! Correlation comparison on the good-length set. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

lemma product_deviation_le (L R : ℝ) :
    |L * R - 1| ≤ |L - 1| + |R - 1| + |L - 1| * |R - 1| := by
  have he : L * R - 1 = ((L - 1) + (R - 1)) + (L - 1) * (R - 1) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by rw [abs_mul]; gcongr; exact abs_add_le _ _)

lemma normalized_correlation_le {L R C k η : ℝ} (hη : η < 1)
    (hL : |L - 1| ≤ η) (hR : |R - 1| ≤ η) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    |C / (L * R) - k| ≤
      (|C - k| + |L - 1| + |R - 1| + |L - 1| * |R - 1|) / (1 - η) ^ 2 := by
  have hL0 : 0 < L := by have := (abs_le.mp hL).1; linarith
  have hR0 : 0 < R := by have := (abs_le.mp hR).1; linarith
  have hD : (1 - η) ^ 2 ≤ L * R := by
    have hl : 1 - η ≤ L := by have := (abs_le.mp hL).1; linarith
    have hr : 1 - η ≤ R := by have := (abs_le.mp hR).1; linarith
    simpa only [sq] using mul_le_mul hl hr (by linarith) hL0.le
  have hnum : |C - k * (L * R)| ≤ |C - k| + |L - 1| + |R - 1| + |L - 1| * |R - 1| := by
    have he : C - k * (L * R) = (C - k) + k * (1 - L * R) := by ring
    rw [he]
    have hh := abs_add_le (C - k) (k * (1 - L * R))
    rw [abs_mul, abs_of_nonneg hk0, abs_sub_comm 1 (L * R)] at hh
    have hb := mul_le_mul_of_nonneg_right hk1 (abs_nonneg (L * R - 1))
    have hp := product_deviation_le L R
    linarith
  have he : C / (L * R) - k = (C - k * (L * R)) / (L * R) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hL0 hR0)]
  exact (div_le_div_of_nonneg_right hnum (mul_pos hL0 hR0).le).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (by linarith)) hD)

variable {n : ℕ}

lemma pairCos_eq_normalizedOverlap (hn : 1 ≤ n)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) (x x' : Fin n → ℝ) :
    pairCos (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) =
      firstOverlap x x' A / (layerLength A x * layerLength A x') := by
  rw [layerLength_eq hn, layerLength_eq hn, div_mul_div_comm, mul_self_sqrt (by positivity)]
  unfold firstOverlap pairCos
  rw [div_div_div_cancel_right₀ (by positivity : (n : ℝ) ≠ 0)]

def goodLength (x x' : Fin n → ℝ) (η : ℝ) : Set (Matrix (Fin (n ^ 2)) (Fin n) ℝ) :=
  {A | |layerLength A x - 1| ≤ η ∧ |layerLength A x' - 1| ≤ η}

lemma measurableSet_goodLength (x x' : Fin n → ℝ) (η : ℝ) : MeasurableSet (goodLength x x' η) :=
  (measurableSet_le ((measurable_layerLength x).sub measurable_const).abs measurable_const).inter
    (measurableSet_le ((measurable_layerLength x').sub measurable_const).abs measurable_const)

noncomputable def goodCorrelation (x x' : Fin n → ℝ) (η : ℝ)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) : ℝ :=
  (goodLength x x' η).indicator
    (fun A => |pairCos (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) - kappa (dotp x x')|) A

lemma measurable_goodCorrelation (hn : 1 ≤ n) (x x' : Fin n → ℝ) (η : ℝ) :
    Measurable (goodCorrelation x x' η) := by
  unfold goodCorrelation
  apply Measurable.indicator _ (measurableSet_goodLength x x' η)
  simp_rw [pairCos_eq_normalizedOverlap hn]
  exact (((measurable_firstOverlap x x').div
    ((measurable_layerLength x).mul (measurable_layerLength x'))).sub_const _).abs

lemma goodCorrelation_nonneg (x x' : Fin n → ℝ) (η : ℝ) (A) :
    0 ≤ goodCorrelation x x' η A := indicator_nonneg (fun _ _ => abs_nonneg _) _

theorem goodCorrelation_le (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {η : ℝ} (hη : η < 1)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) :
    goodCorrelation x x' η A ≤
      (|firstOverlap x x' A - kappa (dotp x x')| + |layerLength A x - 1| +
        |layerLength A x' - 1| + |layerLength A x - 1| * |layerLength A x' - 1|) / (1 - η) ^ 2 := by
  classical
  by_cases hA : A ∈ goodLength x x' η
  · rw [goodCorrelation, indicator_of_mem hA, pairCos_eq_normalizedOverlap hn]
    have hk := kappa_mem (unit_dot_mem hx hx').1 (unit_dot_mem hx hx').2
    exact normalized_correlation_le hη hA.1 hA.2 hk.1 hk.2
  · rw [goodCorrelation, indicator_of_notMem hA]
    positivity

end BstLean.Part209
