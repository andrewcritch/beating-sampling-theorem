import BstLean.Part218SquaredSphere

/-! The input norm kernel has the explicit paper second moment and ordered variance bound. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part36 BstLean.Part105 BstLean.Part130

lemma normKernel_square_radial {N : ℕ} (hN : 1 ≤ N) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    normKernel N p ^ 2 = radialAngular 2 (fun c => squaredAngularB N c ^ 2) p.2 p.1 := by
  rw [show normKernel N p = normKernel N (p.1, p.2) from rfl, normKernel_formula hN]
  unfold radialAngular
  rw [rowCos_symm p.1 p.2]
  ring

theorem normKernel_second_bound {N : ℕ} (hN : 1 ≤ N) :
    (∫ p, normKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ≤
      ((N : ℝ) * (N + 2)) ^ 2 * angularJb N := by
  have mf : Measurable (fun c => squaredAngularB N c ^ 2) := by
    unfold squaredAngularB
    exact ((reluSquarePair_measurable.div_const _).sub_const _).pow_const 2
  have hi := (normKernel_memLp hN).integrable_sq
  simp_rw [normKernel_square_radial hN] at hi ⊢
  rw [radialAngular_integral hN (by norm_num : 1 ≤ 2) mf hi]
  have h := mul_le_mul_of_nonneg_left (squaredAngular_second_moment hN ⟨0, hN⟩)
    (sq_nonneg ((N : ℝ) * (N + 2)))
  simpa [rhoD, Finset.prod_range_succ] using h

theorem normKernel_variance_bound {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Var[fun x : Fin m → Fin N → ℝ => ∑ p : Fin m × Fin m, orderedRow (normKernel N) p x;
      Measure.pi fun _ : Fin m => stdGauss (Fin N)] ≤
      2 * (m : ℝ) ^ 2 * ((N : ℝ) * (N + 2)) ^ 2 * angularJb N := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [normKernel_ordered_variance hN]
  have hE : 0 ≤ ∫ p, normKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)) :=
    integral_nonneg fun _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_right (show 2 * (m : ℝ) * ((m : ℝ) - 1) ≤ 2 * (m : ℝ) ^ 2 by nlinarith) hE
  have h2 := mul_le_mul_of_nonneg_left (normKernel_second_bound hN) (show 0 ≤ 2 * (m : ℝ) ^ 2 by positivity)
  exact h1.trans (h2.trans_eq (by ring))

end BstLean.Part218
#print axioms BstLean.Part218.normKernel_second_bound
#print axioms BstLean.Part218.normKernel_variance_bound
