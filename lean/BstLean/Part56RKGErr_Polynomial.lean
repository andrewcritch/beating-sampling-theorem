import BstLean.Part56Orth_Integrability

/-! Polynomial integrability for shifted linear fields and independent Gaussian pairs. -/
namespace BstLean.Part56.RKGErr

set_option autoImplicit false

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Tens fval contr Mono colM)
open BstLean.Part53 (linZ)

theorem gaussian_polynomial_integrable {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
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

theorem polynomial_memLp {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    MemLp (fun z => MvPolynomial.eval z p) 2 (stdGauss ι) := by
  apply (memLp_two_iff_integrable_sq p.continuous_eval.aestronglyMeasurable).2
  convert gaussian_polynomial_integrable (p ^ 2) using 1
  funext z
  exact (MvPolynomial.eval_pow (f := z) (p := p) 2).symm

noncomputable def fPoly {n : ℕ} (k : ℕ) (f0 : ℝ) (T : Tens n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C f0 + ∑ j ∈ Finset.Icc 1 k, ∑ w : Fin j → Fin n,
    MvPolynomial.C (T j w) * ∏ r, MvPolynomial.X (w r)

theorem fPoly_eval {n : ℕ} (k : ℕ) (f0 : ℝ) (T : Tens n) (z : Fin n → ℝ) :
    MvPolynomial.eval z (fPoly k f0 T) = fval k f0 T z := by
  classical
  simp [fPoly, fval, contr]

theorem fval_continuous {n : ℕ} (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Continuous (fval k f0 T) := by
  simpa only [fPoly_eval] using (fPoly k f0 T).continuous_eval

theorem fPoly_comp_eval {n : ℕ} {ι : Type*} (k : ℕ) (f0 : ℝ) (T : Tens n)
    (Q : Fin n → MvPolynomial ι ℝ) (z : ι → ℝ) :
    MvPolynomial.eval z (MvPolynomial.eval₂Hom MvPolynomial.C Q (fPoly k f0 T)) =
      fval k f0 T (fun a => MvPolynomial.eval z (Q a)) := by
  rw [← fPoly_eval]
  have he : (MvPolynomial.eval z).comp (MvPolynomial.eval₂Hom MvPolynomial.C Q) =
      MvPolynomial.eval (fun a => MvPolynomial.eval z (Q a)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro a
      simp
  exact congrArg (fun f => f (fPoly k f0 T)) he

theorem fval_scaled_memLp {n : ℕ} (k : ℕ) (f0 : ℝ) (T : Tens n) (a : ℝ) (y : Fin n → ℝ) :
    MemLp (fun g : Fin n → ℝ => fval k f0 T (y + a • g)) 2 (stdGauss (Fin n)) := by
  let Q := fun i : Fin n => MvPolynomial.C (y i) + MvPolynomial.C a * MvPolynomial.X i
  have hp := polynomial_memLp (MvPolynomial.eval₂Hom MvPolynomial.C Q (fPoly k f0 T))
  have he (z : Fin n → ℝ) :
      MvPolynomial.eval z (MvPolynomial.eval₂Hom MvPolynomial.C Q (fPoly k f0 T)) =
        fval k f0 T (y + a • z) := by
    rw [fPoly_comp_eval]
    congr 1
    funext i
    simp [Q]
  simpa only [he] using hp

theorem fval_linear_memLp {n d : ℕ} (k : ℕ) (f0 : ℝ) (T : Tens n)
    (ψ : Mono n d → ℝ) (y : Fin n → ℝ) :
    MemLp (fun Z : CoefIdxD n d → ℝ => fval k f0 T (y + linZ Z ψ))
      2 (stdGauss (CoefIdxD n d)) := by
  classical
  let Q : Fin n → MvPolynomial (CoefIdxD n d) ℝ := fun a => MvPolynomial.C (y a) +
    ∑ p : Mono n d, MvPolynomial.C (ψ p) * MvPolynomial.X ⟨p.1, (p.2, a)⟩
  have hp := polynomial_memLp (MvPolynomial.eval₂Hom MvPolynomial.C Q (fPoly k f0 T))
  have he (z : CoefIdxD n d → ℝ) :
      MvPolynomial.eval z (MvPolynomial.eval₂Hom MvPolynomial.C Q (fPoly k f0 T)) =
        fval k f0 T (y + linZ z ψ) := by
    rw [fPoly_comp_eval]
    congr 1
    funext a
    simp only [Q, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Pi.add_apply, linZ, colM]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simpa only [he] using hp

theorem gaussian_pair_poly_memLp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : MvPolynomial (ι ⊕ κ) ℝ) :
    MemLp (fun z : (ι → ℝ) × (κ → ℝ) => MvPolynomial.eval (Sum.elim z.1 z.2) P)
      2 ((stdGauss ι).prod (stdGauss κ)) := by
  have hm := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : ι ⊕ κ => ProbabilityTheory.gaussianReal 0 1)
  convert (polynomial_memLp P).comp_measurePreserving hm using 1 <;> rfl

theorem gaussian_pair_poly_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : MvPolynomial (ι ⊕ κ) ℝ) :
    Integrable (fun z : (ι → ℝ) × (κ → ℝ) => MvPolynomial.eval (Sum.elim z.1 z.2) P)
      ((stdGauss ι).prod (stdGauss κ)) :=
  (gaussian_pair_poly_memLp P).integrable (by norm_num)

end BstLean.Part56.RKGErr
