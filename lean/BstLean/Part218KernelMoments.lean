import BstLean.Part218RadialAngular
import BstLean.Part218OrderedBound

/-! Actual Gaussian row moments for the covariance remainder kernel. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part36 BstLean.Part105 BstLean.Part130 BstLean.Part132 BstLean.Part214

lemma angularK_abs_le {N : ℕ} (hN : 1 ≤ N) (e : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |angularK N e x| ≤ angularA N + |e| + angularB N := by
  obtain ⟨hl, hu⟩ := angularK_decomp hN hx
  have ha : 0 ≤ angularA N := by unfold angularA; positivity
  have hb := angularB_nonneg N
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hx4 : x ^ 4 ≤ 1 := by nlinarith [sq_nonneg x]
  have hg : 0 ≤ angularG x / (2 * N) := by nlinarith [mul_nonneg ha (sq_nonneg x)]
  have hp := abs_add_le (angularG x / (2 * N)) e
  rw [abs_of_nonneg hg] at hp
  unfold angularK
  nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hx4 hb]

lemma radial_angularK_integrable {N : ℕ} (hN : 1 ≤ N) (k q : ℕ) (e : ℝ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      radialAngular k (fun c => angularK N e c ^ q) p.2 p.1)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
  apply radialAngular_integrable hN k ((continuous_angularK N e).pow q).measurable
    (B := (angularA N + |e| + angularB N) ^ q)
  intro c hc
  change |angularK N e c ^ q| ≤ (angularA N + |e| + angularB N) ^ q
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (angularK_abs_le hN e hc) q

noncomputable def remainderKernel (N : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  normSq p.1 * normSq p.2 * angularK N (angularOffset N) (rowCos p.1 p.2) ^ 2

lemma remainderKernel_measurable (N : ℕ) : Measurable (remainderKernel N) := by
  unfold remainderKernel rowCos nrm dotp normSq
  have hk := (continuous_angularK N (angularOffset N)).measurable
  fun_prop

lemma remainderKernel_symm (N : ℕ) (x y : Fin N → ℝ) :
    remainderKernel N (x, y) = remainderKernel N (y, x) := by
  unfold remainderKernel
  rw [rowCos_symm x y]
  ring

lemma remainderKernel_radial (N : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    remainderKernel N p = radialAngular 1 (fun c => angularK N (angularOffset N) c ^ 2) p.2 p.1 := by
  unfold remainderKernel radialAngular
  rw [rowCos_symm p.1 p.2]
  ring

lemma remainderKernel_square_radial (N : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    remainderKernel N p ^ 2 = radialAngular 2 (fun c => angularK N (angularOffset N) c ^ 4) p.2 p.1 := by
  unfold remainderKernel radialAngular
  rw [rowCos_symm p.1 p.2]
  ring

lemma remainderKernel_memLp {N : ℕ} (hN : 1 ≤ N) :
    MemLp (remainderKernel N) 2 ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
  apply (memLp_two_iff_integrable_sq (remainderKernel_measurable N).aestronglyMeasurable).mpr
  simp_rw [remainderKernel_square_radial]
  exact radial_angularK_integrable hN 2 4 (angularOffset N)

theorem remainderKernel_mean_bound {N : ℕ} (hN : 2 ≤ N) :
    (∫ p, remainderKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ≤
      (N : ℝ) ^ 2 * angularJ2 N (angularOffset N) := by
  have hn : 1 ≤ N := by omega
  simp_rw [remainderKernel_radial]
  rw [radialAngular_integral (F := fun c => angularK N (angularOffset N) c ^ 2)
    hn (by norm_num : 1 ≤ 1)
    ((continuous_angularK N (angularOffset N)).pow 2).measurable
    (radial_angularK_integrable hn 1 2 (angularOffset N))]
  simpa [rhoD] using mul_le_mul_of_nonneg_left
    (angular_second_moment hn ⟨0, hn⟩ (angularOffset_nonpos hN)) (sq_nonneg (N : ℝ))

theorem remainderKernel_second_bound {N : ℕ} (hN : 1 ≤ N) :
    (∫ p, remainderKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ≤
      ((N : ℝ) * (N + 2)) ^ 2 * angularJ4 N (angularOffset N) := by
  simp_rw [remainderKernel_square_radial]
  rw [radialAngular_integral (F := fun c => angularK N (angularOffset N) c ^ 4)
    hN (by norm_num : 1 ≤ 2)
    ((continuous_angularK N (angularOffset N)).pow 4).measurable
    (radial_angularK_integrable hN 2 4 (angularOffset N))]
  have h := mul_le_mul_of_nonneg_left (angular_fourth_moment hN ⟨0, hN⟩ (angularOffset N))
    (sq_nonneg ((N : ℝ) * (N + 2)))
  simpa [rhoD, Finset.prod_range_succ] using h

end BstLean.Part218
#print axioms BstLean.Part218.remainderKernel_mean_bound
#print axioms BstLean.Part218.remainderKernel_second_bound
