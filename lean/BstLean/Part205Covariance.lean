import BstLean.Part205ANOVA
import BstLean.Part205Mean

/-! Exact covariance normalization for the pair moment in the Taylor mean bound. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part139

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (g : Ω → Fin m → ℝ)

noncomputable def covarianceT (Q : ℝ) : ℝ :=
  ((∑ i, ∑ j, covV μ g i j ^ 2) +
    2 * (∑ i, ∑ j, meanV μ g i * covV μ g i j * meanV μ g j)) / Q ^ 2

lemma dotp_pair_mean (hg : ∀ i, BM (fun x => g x i)) :
    (∫ p : Ω × Ω, dotp (g p.1) (g p.2) ∂μ.prod μ) = normSq (meanV μ g) := by
  unfold dotp normSq
  rw [integral_finsetSum _ (fun i _ => ((hg i).integrable μ).mul_prod ((hg i).integrable μ))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_mul (fun x => g x i) (fun x => g x i), pow_two]
  rfl

lemma dotp_mean_right (hg : ∀ i, BM (fun x => g x i)) (h : Fin m → ℝ) :
    (∫ x, dotp (g x) h ∂μ) = dotp (meanV μ g) h := by
  unfold dotp
  rw [integral_finsetSum _ (fun i _ => ((hg i).integrable μ).mul_const (h i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const]
  rfl

theorem covariance_pair_moment (hg : ∀ i, BM (fun x => g x i)) {Q : ℝ} (hQ : 0 < Q) :
    (∫ p : Ω × Ω, (dotp (g p.1) (g p.2) / Q - normSq (meanV μ g) / Q) ^ 2
      ∂μ.prod μ) = covarianceT μ g Q := by
  have hraw : ∀ p : Ω × Ω,
      (dotp (g p.1) (g p.2) / Q - normSq (meanV μ g) / Q) ^ 2 =
      (dotp (g p.1) (g p.2) - normSq (meanV μ g)) ^ 2 / Q ^ 2 := by
    intro p
    ring
  simp_rw [hraw]
  rw [integral_div, pair_anova μ g hg, meanDirection_second μ g hg]
  rfl

theorem covarianceT_nonneg (hg : ∀ i, BM (fun x => g x i)) {Q : ℝ} (hQ : 0 < Q) :
    0 ≤ covarianceT μ g Q := by
  rw [← covariance_pair_moment μ g hg hQ]
  exact integral_nonneg fun _ => sq_nonneg _

theorem covariance_pair_L2 (hg : ∀ i, BM (fun x => g x i)) {Q : ℝ} (hQ : 0 < Q) :
    L2le (μ.prod μ)
      (fun p => dotp (g p.1) (g p.2) / Q - normSq (meanV μ g) / Q)
      (√(covarianceT μ g Q)) := by
  have hb : BM (fun p : Ω × Ω => dotp (g p.1) (g p.2) / Q -
      normSq (meanV μ g) / Q) := by
    have hdot : BM (fun p : Ω × Ω => dotp (g p.1) (g p.2)) :=
      BM.sum _ fun i _ => (hg i).fst.mul (hg i).snd
    convert (hdot.mul (BM.const (1 / Q))).sub (BM.const (normSq (meanV μ g) / Q)) using 1
    ext p
    simp [div_eq_mul_inv]
  refine ⟨hb.1.aestronglyMeasurable, hb.sq.integrable _, ?_⟩
  rw [covariance_pair_moment μ g hg hQ, Real.sq_sqrt (covarianceT_nonneg μ g hg hQ)]

theorem covariance_single_L2 (hg : ∀ i, BM (fun x => g x i)) {Q : ℝ} (hQ : 0 < Q) :
    L2le μ (fun x => dotp (g x) (meanV μ g) / Q - normSq (meanV μ g) / Q)
      (√(covarianceT μ g Q)) := by
  have h := (covariance_pair_L2 μ g hg hQ).integral_right
  refine h.congr_fun fun x => ?_
  have hi : Integrable (fun y => dotp (g x) (g y) / Q) μ := by
    have hb : BM (fun y => dotp (g x) (g y)) :=
      BM.sum _ fun i _ => (BM.const (g x i)).mul (hg i)
    simpa [div_eq_mul_inv] using (hb.mul (BM.const (1 / Q))).integrable μ
  rw [integral_sub hi (integrable_const _), integral_div]
  have hd : (∫ y, dotp (g x) (g y) ∂μ) = dotp (g x) (meanV μ g) := by
    unfold dotp
    rw [integral_finsetSum _ (fun i _ => ((hg i).integrable μ).const_mul (g x i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    rfl
  rw [hd]
  simp

end
end BstLean.Part205

#print axioms BstLean.Part205.covariance_pair_moment
#print axioms BstLean.Part205.covariance_pair_L2
#print axioms BstLean.Part205.covariance_single_L2
