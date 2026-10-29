import BstLean.Part53Defs

/-! Polynomial representation and integrability for the Gaussian proxy. -/

namespace BstLean.Part53

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens colM contr trL glue)

private lemma polynomial_integrable53 {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _

private noncomputable def linPoly53 {n d : ℕ} (s : ℝ) (ψ : Mono n d → ℝ)
    (a : Fin n) : MvPolynomial (CoefIdxD n d) ℝ :=
  ∑ p, MvPolynomial.C (s * ψ p) * MvPolynomial.X ⟨p.1, (p.2, a)⟩

private lemma linPoly53_eval {n d : ℕ} (s : ℝ) (ψ : Mono n d → ℝ)
    (Z : CoefIdxD n d → ℝ) (a : Fin n) :
    MvPolynomial.eval Z (linPoly53 s ψ a) = (s • linZ Z ψ) a := by
  classical
  simp only [linPoly53, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Pi.smul_apply, smul_eq_mul, linZ, colM, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private noncomputable def fvPoly53 {n d : ℕ} (k : ℕ) (s : ℝ) (A : Tens n)
    (ψ : Mono n d → ℝ) : MvPolynomial (CoefIdxD n d) ℝ :=
  ∑ c ∈ Finset.range (k + 1), ∑ w : Fin c → Fin n,
    MvPolynomial.C (A c w) * ∏ t, linPoly53 s ψ (w t)

private lemma fvPoly53_eval {n d : ℕ} (k : ℕ) (s : ℝ) (A : Tens n)
    (ψ : Mono n d → ℝ) (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (fvPoly53 k s A ψ) = fvA k A (s • linZ Z ψ) := by
  classical
  simp [fvPoly53, fvA, contr, linPoly53_eval]

/-- The integrability conjunct of Lemma W, without symmetry assumptions. -/
theorem wick_product_integrable53 {n d : ℕ} (k : ℕ) (s : ℝ) (A A' : Tens n)
    (ψ ψ' : Mono n d → ℝ) :
    Integrable (fun Z => fvA k A (s • linZ Z ψ) * fvA k A' (s • linZ Z ψ'))
      (stdGauss (CoefIdxD n d)) := by
  have h := polynomial_integrable53 (fvPoly53 k s A ψ * fvPoly53 k s A' ψ')
  simpa only [map_mul, fvPoly53_eval] using h

private lemma heatA_zero53 {n : ℕ} (v : ℝ) (A : Tens n) : heatA 0 v A 0 = A 0 := by
  classical
  funext w
  simp only [heatA, Finset.range_one, Finset.filter_singleton, Nat.zero_add,
    Nat.mul_zero, le_refl, ite_true, Finset.sum_singleton, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, mul_one, one_mul, trL,
    Fintype.sum_unique]
  congr 1

/-- Lemma W for constant polynomials, including dimension zero. -/
theorem wick_degree_zero53 : LemmaW53 0 := by
  classical
  intro n d s A A' hA hA' ψ ψ'
  refine ⟨wick_product_integrable53 0 s A A' ψ ψ', ?_⟩
  simp [fvA, contr, wpair, heatA_zero53, tinner]

end BstLean.Part53
