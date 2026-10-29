import BstLean.Part209Correlation
import BstLean.Part209MomentTools

/-! The paper correlation allowance, integrated on the good-length set. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

lemma lengthAlpha_nonneg (n P : ℕ) : 0 ≤ lengthAlpha n P := by
  unfold lengthAlpha
  exact add_nonneg (by positivity) (mul_nonneg (by positivity) (twoGaussConst_nonneg P))

lemma overlapC_nonneg (n P : ℕ) : 0 ≤ overlapC n P := by unfold overlapC; positivity

/-- This is the paper `Delta_(4P)` at cutoff `eta`. -/
noncomputable def pairDelta (n P : ℕ) (η : ℝ) : ℝ :=
  (overlapC n P + 2 * lengthAlpha n P + lengthAlpha n (2 * P) ^ 2) / (1 - η) ^ 2

/-- Lengths and overlaps use the same first-layer matrix. No independence premise is used. -/
theorem goodCorrelation_moment {n P : ℕ} (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {η : ℝ} (hη : η < 1) :
    Integrable (fun A => goodCorrelation x x' η A ^ (2 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, goodCorrelation x x' η A ^ (2 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      pairDelta n P η ^ (2 * P) := by
  let X := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => |layerLength A x - 1|
  let Y := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => |layerLength A x' - 1|
  let C := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => |firstOverlap x x' A - kappa (dotp x x')|
  have hX : Measurable X := ((measurable_layerLength x).sub measurable_const).abs
  have hY : Measurable Y := ((measurable_layerLength x').sub measurable_const).abs
  have hC : Measurable C := ((measurable_firstOverlap x x').sub measurable_const).abs
  have hX0 : ∀ A, 0 ≤ X A := fun _ => abs_nonneg _
  have hY0 : ∀ A, 0 ≤ Y A := fun _ => abs_nonneg _
  have hC0 : ∀ A, 0 ≤ C A := fun _ => abs_nonneg _
  obtain ⟨hiX, hbX⟩ := layerLength_deviation_moment hn hP hx
  obtain ⟨hiY, hbY⟩ := layerLength_deviation_moment hn hP hx'
  obtain ⟨hiC, hbC⟩ := firstOverlap_deviation_moment (by omega : 1 ≤ n) hP hx hx'
  obtain ⟨hiX2, hbX2⟩ := layerLength_deviation_moment hn (by omega : 1 ≤ 2 * P) hx
  obtain ⟨hiY2, hbY2⟩ := layerLength_deviation_moment hn (by omega : 1 ≤ 2 * P) hx'
  obtain ⟨hiXY, hbXY⟩ := moment_mul hX hY hX0 hY0
    (lengthAlpha_nonneg n (2 * P)) (lengthAlpha_nonneg n (2 * P)) hiX2 hiY2 hbX2 hbY2
  obtain ⟨hiCX, hbCX⟩ := moment_add hC hX hC0 hX0 (by omega : 1 ≤ 2 * P)
    (overlapC_nonneg n P) (lengthAlpha_nonneg n P) hiC hiX hbC hbX
  obtain ⟨hiCXY, hbCXY⟩ := moment_add (hC.add hX) hY
    (fun A => add_nonneg (hC0 A) (hX0 A)) hY0 (by omega : 1 ≤ 2 * P)
    (add_nonneg (overlapC_nonneg n P) (lengthAlpha_nonneg n P)) (lengthAlpha_nonneg n P)
    hiCX hiY hbCX hbY
  obtain ⟨hiN, hbN⟩ := moment_add ((hC.add hX).add hY) (hX.mul hY)
    (fun A => add_nonneg (add_nonneg (hC0 A) (hX0 A)) (hY0 A))
    (fun A => mul_nonneg (hX0 A) (hY0 A)) (by omega : 1 ≤ 2 * P)
    (add_nonneg (add_nonneg (overlapC_nonneg n P) (lengthAlpha_nonneg n P)) (lengthAlpha_nonneg n P))
    (mul_nonneg (lengthAlpha_nonneg n (2 * P)) (lengthAlpha_nonneg n (2 * P))) hiCXY hiXY hbCXY hbXY
  let N := fun A => C A + X A + Y A + X A * Y A
  have hN0 : ∀ A, 0 ≤ N A := fun A => add_nonneg
    (add_nonneg (add_nonneg (hC0 A) (hX0 A)) (hY0 A)) (mul_nonneg (hX0 A) (hY0 A))
  have hiS : Integrable (fun A => (N A / (1 - η) ^ 2) ^ (2 * P))
      (gaussMat (n ^ 2) n (2 / n)) := by
    simp_rw [div_pow]
    exact hiN.div_const _
  have hbS : (∫ A, (N A / (1 - η) ^ 2) ^ (2 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      pairDelta n P η ^ (2 * P) := by
    simp_rw [div_pow]
    rw [integral_div]
    have hb := div_le_div_of_nonneg_right hbN (pow_nonneg (sq_nonneg (1 - η)) (2 * P))
    convert hb using 1
    unfold pairDelta
    rw [div_pow]
    congr 2
    ring
  have hd : ∀ A, goodCorrelation x x' η A ^ (2 * P) ≤ (N A / (1 - η) ^ 2) ^ (2 * P) := by
    intro A
    exact pow_le_pow_left₀ (goodCorrelation_nonneg x x' η A)
      (goodCorrelation_le (by omega) hx hx' hη A) _
  have hi := hiS.mono'
    ((measurable_goodCorrelation (by omega) x x' η).pow_const (2 * P)).aestronglyMeasurable
    (ae_of_all _ fun A => by
      rw [Real.norm_of_nonneg (pow_nonneg (goodCorrelation_nonneg x x' η A) _)]
      exact hd A)
  exact ⟨hi, (integral_mono hi hiS hd).trans hbS⟩

lemma pairDelta_nonneg (n P : ℕ) (η : ℝ) : 0 ≤ pairDelta n P η := by
  unfold pairDelta
  exact div_nonneg (add_nonneg (add_nonneg (overlapC_nonneg n P)
    (mul_nonneg (by norm_num) (lengthAlpha_nonneg n P))) (sq_nonneg _)) (sq_nonneg _)

/-- The square-root correlation term has the exact `sqrt Delta` moment allowance. -/
theorem sqrt_goodCorrelation_moment {n P : ℕ} (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {η : ℝ} (hη : η < 1) :
    Integrable (fun A => sqrt (goodCorrelation x x' η A) ^ (4 * P))
      (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, sqrt (goodCorrelation x x' η A) ^ (4 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      sqrt (pairDelta n P η) ^ (4 * P) := by
  have he : ∀ z : ℝ, 0 ≤ z → sqrt z ^ (4 * P) = z ^ (2 * P) := by
    intro z hz
    rw [show 4 * P = 2 * (2 * P) by omega, pow_mul, sq_sqrt hz]
  simp_rw [he _ (goodCorrelation_nonneg x x' η _), he _ (pairDelta_nonneg n P η)]
  exact goodCorrelation_moment hn hP hx hx' hη

end BstLean.Part209
