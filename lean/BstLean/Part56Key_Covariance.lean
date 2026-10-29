import BstLean.Part56Key_Tensor

namespace BstLean.Part56

open MeasureTheory

noncomputable def covEntry56 {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ι → Ω → ℝ) (p q : ι) : ℝ := ∫ g, F p g * F q g ∂μ

noncomputable def covEnergy56 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : ι → Ω → ℝ) : ℝ := ∑ p, ∑ q, covEntry56 μ F p q ^ 2

theorem cross_integral_cov56 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F G : ι → Ω → ℝ)
    (hF : ∀ p q, Integrable (fun g => F p g * F q g) μ)
    (hG : ∀ p q, Integrable (fun g => G p g * G q g) μ) :
    (∫ g, ∫ h, (∑ p, F p g * G p h) ^ 2 ∂μ ∂μ) =
      ∑ p, ∑ q, covEntry56 μ F p q * covEntry56 μ G p q := by
  have he (g h : Ω) : (∑ p, F p g * G p h) ^ 2 =
      ∑ p, ∑ q, (F p g * F q g) * (G p h * G q h) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hi (g : Ω) : (∫ h, (∑ p, F p g * G p h) ^ 2 ∂μ) =
      ∑ p, ∑ q, (F p g * F q g) * covEntry56 μ G p q := by
    simp_rw [he]
    rw [integral_finsetSum _ fun p hp => integrable_finsetSum _
      fun q hq => (hG p q).const_mul (F p g * F q g)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_finsetSum _ fun q hq => (hG p q).const_mul (F p g * F q g)]
    simp only [integral_const_mul, covEntry56]
  simp_rw [hi]
  rw [integral_finsetSum _ fun p hp => integrable_finsetSum _
    fun q hq => (hF p q).mul_const (covEntry56 μ G p q)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_finsetSum _ fun q hq => (hF p q).mul_const (covEntry56 μ G p q)]
  simp only [integral_mul_const, covEntry56]

theorem same_integral_cov56 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : ι → Ω → ℝ)
    (hF : ∀ p q, Integrable (fun g => F p g * F q g) μ) :
    (∫ g, ∫ h, (∑ p, F p g * F p h) ^ 2 ∂μ ∂μ) = covEnergy56 μ F := by
  simpa only [covEnergy56, pow_two] using cross_integral_cov56 μ F F hF hF

theorem cross_integral_sq_le56 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F G : ι → Ω → ℝ)
    (hF : ∀ p q, Integrable (fun g => F p g * F q g) μ)
    (hG : ∀ p q, Integrable (fun g => G p g * G q g) μ) :
    (∫ g, ∫ h, (∑ p, F p g * G p h) ^ 2 ∂μ ∂μ) ^ 2 ≤ covEnergy56 μ F * covEnergy56 μ G := by
  rw [cross_integral_cov56 μ F G hF hG]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => covEntry56 μ F p.1 p.2) (fun p => covEntry56 μ G p.1 p.2)
  simpa only [Fintype.sum_prod_type, covEnergy56] using h

private lemma sum_injective_le56 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (F : κ → ℝ) (hF : ∀ p, 0 ≤ F p) :
    (∑ p : ι, F (f p)) ≤ ∑ q : κ, F q := by
  classical
  calc
    _ = ∑ q ∈ Finset.univ.image f, F q := by
      rw [Finset.sum_image (fun p hp q hq h => hf h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun q hq hq' => hF q)

/-- Removing repeated ordered coordinates contracts the squared covariance norm. -/
theorem covEnergy_restrict_le56 {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (μ : Measure Ω) (F : κ → Ω → ℝ) (f : ι → κ) (hf : Function.Injective f) :
    covEnergy56 μ (fun p => F (f p)) ≤ covEnergy56 μ F := by
  unfold covEnergy56
  calc
    _ ≤ ∑ p : ι, ∑ q : κ, covEntry56 μ F (f p) q ^ 2 :=
      Finset.sum_le_sum fun p hp => sum_injective_le56 f hf _ (fun q => sq_nonneg _)
    _ ≤ _ := sum_injective_le56 f hf _ (fun p => Finset.sum_nonneg fun q hq => sq_nonneg _)

end BstLean.Part56
