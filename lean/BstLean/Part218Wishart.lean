import BstLean.Part218Ordered
import BstLean.Part218PairMoments

/-! The off-diagonal Wishart variance is supplied under the actual Gaussian matrix distribution. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part214

noncomputable def wishartKernel (N : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  dotp p.2 p.1 ^ 2

lemma wishartKernel_measurable (N : ℕ) : Measurable (wishartKernel N) :=
  (continuous_dotp.measurable.comp (measurable_snd.prodMk measurable_fst)).pow_const 2

lemma wishartKernel_memLp (N : ℕ) :
    MemLp (wishartKernel N) 2 ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
  apply (memLp_two_iff_integrable_sq (wishartKernel_measurable N).aestronglyMeasurable).mpr
  simpa only [wishartKernel, ← pow_mul] using (pair_kernel_moments N).2.2.1

lemma wishartKernel_symm (N : ℕ) (x y : Fin N → ℝ) :
    wishartKernel N (x, y) = wishartKernel N (y, x) := by
  unfold wishartKernel dotp
  simp_rw [mul_comm]

noncomputable def wishartOff (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∑ p : Fin m × Fin m, orderedRow (wishartKernel N) p M

lemma wishartOff_memLp (N m : ℕ) : MemLp (wishartOff N m) 2 (gaussMat m N 1) := by
  rw [gaussMat_one_pi]
  exact memLp_finsetSum _ (fun p _ => orderedRow_memLp _ (wishartKernel_memLp N) p)

/-- The complete `Var U₁` formula includes all shared-row contributions. -/
theorem wishartOff_variance {N m : ℕ} (hN : 1 ≤ N) :
    Var[wishartOff N m; gaussMat m N 1] =
      2 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (N : ℝ) ^ 2 + 6 * N) +
        8 * N * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
  rw [gaussMat_one_pi]
  have h2 : (∫ p, wishartKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) -
      (∫ p, wishartKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ^ 2 =
      2 * (N : ℝ) ^ 2 + 6 * N := by
    simp only [wishartKernel, ← pow_mul]
    rw [(pair_kernel_moments N).2.1, (pair_kernel_moments N).2.2.2]
    ring
  have h1 : (∫ p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)),
      wishartKernel N (p.1, p.2.1) * wishartKernel N (p.1, p.2.2)
      ∂(stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) -
      (∫ p, wishartKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ^ 2 =
      2 * (N : ℝ) := by
    change (∫ p, dotp p.2.1 p.1 ^ 2 * dotp p.2.2 p.1 ^ 2
      ∂(stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) -
      (∫ p, dotp p.2 p.1 ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ^ 2 = _
    rw [(shared_pair_raw hN).2, (pair_kernel_moments N).2.1]
    ring
  have h := iid_ordered_pair_variance (m := m) (stdGauss (Fin N))
    (wishartKernel_measurable N) (wishartKernel_memLp N) (wishartKernel_symm N) h2 h1
  exact h.trans (by ring)

/-- The mean of the ordered off-diagonal sum. -/
theorem wishartOff_mean (N m : ℕ) :
    (∫ M, wishartOff N m M ∂gaussMat m N 1) = (m : ℝ) * ((m : ℝ) - 1) * N := by
  classical
  rw [gaussMat_one_pi]
  change (∫ x : Fin m → Fin N → ℝ, ∑ p : Fin m × Fin m, orderedRow (wishartKernel N) p x
    ∂Measure.pi fun _ : Fin m => stdGauss (Fin N)) = _
  rw [integral_finsetSum _ (fun p _ =>
    (orderedRow_memLp (stdGauss (Fin N)) (wishartKernel_memLp N) p).integrable one_le_two)]
  have he : ∀ p : Fin m × Fin m,
      (∫ x, orderedRow (wishartKernel N) p x ∂Measure.pi fun _ : Fin m => stdGauss (Fin N)) =
      (N : ℝ) - if p.1 = p.2 then (N : ℝ) else 0 := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [orderedRow, hp]
    · simp only [orderedRow, hp, ite_false, sub_zero]
      exact (pair_mean _ (wishartKernel_measurable N) hp).trans (pair_kernel_moments N).2.1
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_sub_distrib]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.wishartOff_variance
#print axioms BstLean.Part218.wishartOff_mean
