import BstLean.Part218KernelMoments
import BstLean.Part218NormMomentBound
import BstLean.Part218OffStatistics

/-! The two nonlinear ordered statistics have concrete He-scaled supplies. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130

noncomputable def covarianceMean (N m : ℕ) : ℝ :=
  (2 / (N : ℝ)) ^ 2 * ((m : ℝ) * ((m : ℝ) - 1) *
    ∫ p, remainderKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)))
noncomputable def covarianceMeanBound (N m : ℕ) : ℝ :=
  4 * m * ((m : ℝ) - 1) * angularJ2 N (angularOffset N)
noncomputable def covarianceVarianceBound (N m : ℕ) : ℝ :=
  (4 * (m : ℝ) ^ 3 + 2 * (m : ℝ) ^ 2) * (4 * (N + 2) / (N : ℝ)) ^ 2 *
    angularJ4 N (angularOffset N)
noncomputable def normVarianceBound (N m : ℕ) : ℝ :=
  2 * (m : ℝ) ^ 2 * (4 * (N + 2) / (N : ℝ)) ^ 2 * angularJb N

lemma remainderKernel_scale (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (x y : Fin N → ℝ) :
    remainderKernel N (a • x, a • y) = a ^ 4 * remainderKernel N (x, y) := by
  rcases ha.eq_or_lt with h0 | ha
  · subst a
    simp [remainderKernel, normSq]
  · unfold remainderKernel
    rw [normSq_smul, normSq_smul, rowCos_smul_left ha,
      rowCos_symm x (a • y), rowCos_smul_left ha, rowCos_symm y x]
    ring

theorem covarianceOff_supply {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m) :
    Integrable (fun M => (offStatistic (remainderKernel N) m M - covarianceMean N m) ^ 2)
      (gaussMat m N (2 / (N : ℝ))) ∧
    covarianceMean N m ≤ covarianceMeanBound N m ∧
    (∫ M, (offStatistic (remainderKernel N) m M - covarianceMean N m) ^ 2
      ∂gaussMat m N (2 / (N : ℝ))) ≤ covarianceVarianceBound N m := by
  have hn : 1 ≤ N := by omega
  have hn' : (0 : ℝ) < N := by exact_mod_cast hn
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 ≤ (m : ℝ) - 1 := by linarith
  have ht := offStatistic_scaled_moments (m := m) (remainderKernel_measurable N)
    (remainderKernel_memLp hn) (fun a ha x y => remainderKernel_scale N ha x y)
    (by positivity : 0 ≤ 2 / (N : ℝ))
  refine ⟨ht.2.2.1, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left (remainderKernel_mean_bound hN)
      (show 0 ≤ (2 / (N : ℝ)) ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) by positivity)
    unfold covarianceMean covarianceMeanBound
    convert h using 1 <;> field_simp <;> ring
  · have htvar := ht.2.2.2
    change (∫ M, (offStatistic (remainderKernel N) m M - covarianceMean N m) ^ 2
      ∂gaussMat m N (2 / (N : ℝ))) = _ at htvar
    rw [htvar]
    have hv : Var[offStatistic (remainderKernel N) m; gaussMat m N 1] ≤
        (4 * (m : ℝ) ^ 3 + 2 * (m : ℝ) ^ 2) *
          ∫ p, remainderKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)) := by
      rw [gaussMat_one_pi]
      exact iid_ordered_pair_variance_bound _ (remainderKernel_measurable N)
        (remainderKernel_memLp hn) hm (remainderKernel_symm N)
    have hv' := hv.trans (mul_le_mul_of_nonneg_left (remainderKernel_second_bound hn) (by positivity))
    have h := mul_le_mul_of_nonneg_left hv' (show 0 ≤ (2 / (N : ℝ)) ^ 4 by positivity)
    apply h.trans_eq
    unfold covarianceVarianceBound
    field_simp
    ring

theorem normOff_supply {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun M => offStatistic (normKernel N) m M ^ 2) (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M, offStatistic (normKernel N) m M ^ 2 ∂gaussMat m N (2 / (N : ℝ))) ≤ normVarianceBound N m := by
  have hn' : (0 : ℝ) < N := by exact_mod_cast hN
  have ht := offStatistic_scaled_moments (m := m) (normKernel_measurable hN) (normKernel_memLp hN)
    (fun a ha x y => (normKernel_scale a a ha ha x y).trans (by ring))
    (by positivity : 0 ≤ 2 / (N : ℝ))
  rw [normKernel_mean_zero hN] at ht
  simp only [mul_zero, sub_zero] at ht
  refine ⟨ht.2.2.1, ?_⟩
  rw [ht.2.2.2]
  have hv : Var[offStatistic (normKernel N) m; gaussMat m N 1] ≤
      2 * (m : ℝ) ^ 2 * ((N : ℝ) * (N + 2)) ^ 2 * angularJb N := by
    rw [gaussMat_one_pi]
    exact normKernel_variance_bound hN hm
  have h := mul_le_mul_of_nonneg_left hv (show 0 ≤ (2 / (N : ℝ)) ^ 4 by positivity)
  apply h.trans_eq
  unfold normVarianceBound
  field_simp
  ring

end BstLean.Part218
#print axioms BstLean.Part218.covarianceOff_supply
#print axioms BstLean.Part218.normOff_supply
