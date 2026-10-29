import BstLean.Part56MC_Density
import BstLean.Part56Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Polynomial annihilators vanish in the Gaussian L2 space. -/

namespace BstLean.Part56

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open scoped ENNReal

private lemma polynomial_integrable {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e _
  have hprod (x : ι → ℝ) : e.prod (fun i a => x i ^ a) = ∏ i, x i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _

theorem mc56_polynomial_memLp {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    MemLp (fun x => MvPolynomial.eval x p) 2 (stdGauss ι) := by
  apply (memLp_two_iff_integrable_sq p.continuous_eval.aestronglyMeasurable).mpr
  convert polynomial_integrable (p ^ 2) using 1
  ext x
  exact (MvPolynomial.eval_pow (f := x) (p := p) 2).symm

private lemma linear_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  classical
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  apply Finset.sum_congr rfl
  intro i _
  change L (Pi.single i (x i)) = _
  have hs : Pi.single i (x i) = x i • (Pi.single i (1 : ℝ)) := by
    ext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  rw [hs, L.map_smul]
  simp [mul_comm]

theorem mc56_gaussian_exp_memLp {ι : Type*} [Fintype ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    MemLp (fun x => Real.exp (t * L x)) 2 (stdGauss ι) := by
  classical
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have hpoint (x : ι → ℝ) : Real.exp (t * L x) ^ 2 =
      ∏ i, Real.exp ((2 * t * L (Pi.single i 1)) * x i) := by
    rw [← Real.exp_nat_mul, linear_expand, ← Real.exp_sum]
    congr 1
    simp only [Nat.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal _)

theorem mc56_gaussian_power_memLp {ι : Type*} [Fintype ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (k : ℕ) :
    MemLp (fun x => L x ^ k) 2 (stdGauss ι) := by
  classical
  let p : MvPolynomial ι ℝ := ∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i
  have hp (x : ι → ℝ) : MvPolynomial.eval x p = L x := by
    simp only [p, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact (linear_expand L x).symm
  simpa only [MvPolynomial.eval_pow, hp] using mc56_polynomial_memLp (p ^ k)

theorem mc56_gaussian_annihilator {ι : Type*} [Fintype ι]
    (F : (ι → ℝ) → ℝ) (hF : MemLp F 2 (stdGauss ι))
    (hm : ∀ p : MvPolynomial ι ℝ, (∫ x, F x * MvPolynomial.eval x p ∂stdGauss ι) = 0) :
    F =ᵐ[stdGauss ι] 0 := by
  classical
  apply mc56_annihilator F hF mc56_gaussian_exp_memLp mc56_gaussian_power_memLp
  intro L k
  let p : MvPolynomial ι ℝ := ∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i
  have hp (x : ι → ℝ) : MvPolynomial.eval x p = L x := by
    simp only [p, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact (linear_expand L x).symm
  simpa only [MvPolynomial.eval_pow, hp] using hm (p ^ k)

noncomputable def mc56_polynomialToLp {ι : Type*} [Fintype ι] :
    MvPolynomial ι ℝ →ₗ[ℝ] Lp ℝ 2 (stdGauss ι) where
  toFun p := (mc56_polynomial_memLp p).toLp (fun x => MvPolynomial.eval x p)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(mc56_polynomial_memLp (p + q)).coeFn_toLp,
      (mc56_polynomial_memLp p).coeFn_toLp, (mc56_polynomial_memLp q).coeFn_toLp,
      Lp.coeFn_add ((mc56_polynomial_memLp p).toLp _) ((mc56_polynomial_memLp q).toLp _)]
      with x hx hp hq hadd
    rw [hx, hadd]
    simp only [Pi.add_apply, hp, hq, MvPolynomial.eval_add]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [(mc56_polynomial_memLp (c • p)).coeFn_toLp,
      (mc56_polynomial_memLp p).coeFn_toLp,
      Lp.coeFn_smul c ((mc56_polynomial_memLp p).toLp _)] with x hx hp hsmul
    change ((mc56_polynomial_memLp (c • p)).toLp _) x =
      (c • ((mc56_polynomial_memLp p).toLp _)) x
    rw [hx, hsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hp, MvPolynomial.smul_eval]

theorem mc56_polynomials_dense {ι : Type*} [Fintype ι] :
    (LinearMap.range (mc56_polynomialToLp (ι := ι))).topologicalClosure = ⊤ := by
  classical
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro F hF
  change F = 0
  apply Lp.ext
  have hann : F =ᵐ[stdGauss ι] (0 : (ι → ℝ) → ℝ) := by
    apply mc56_gaussian_annihilator F (Lp.memLp F)
    intro p
    have hinner := (Submodule.mem_orthogonal' _ _).mp hF (mc56_polynomialToLp p)
      (show mc56_polynomialToLp p ∈ LinearMap.range mc56_polynomialToLp from ⟨p, rfl⟩)
    have he : (∫ x, F x * MvPolynomial.eval x p ∂stdGauss ι) =
        inner ℝ F (mc56_polynomialToLp p) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(mc56_polynomial_memLp p).coeFn_toLp] with x hx
      simp [mc56_polynomialToLp, hx, mul_comm]
    exact he.trans hinner
  exact hann.trans (Lp.coeFn_zero ℝ 2 (stdGauss ι)).symm

end BstLean.Part56
