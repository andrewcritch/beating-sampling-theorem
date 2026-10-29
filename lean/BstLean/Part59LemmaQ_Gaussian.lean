import BstLean.Part59Defs
import BstLean.Part43Floor

namespace BstLean.Part59
open MeasureTheory
open BstLean.Part29 (stdGauss)

noncomputable section

lemma gaussian_eval_integrable59x {ι : Type*} [Fintype ι]
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

def gaussianExpectation59x {ι : Type*} [Fintype ι] : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ Z, MvPolynomial.eval Z p ∂stdGauss ι
  map_add' p q := by
    simp only [MvPolynomial.eval_add]
    exact integral_add (gaussian_eval_integrable59x p) (gaussian_eval_integrable59x q)
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, smul_eq_mul]
    exact integral_const_mul _ _

elab "gaussianSteinImported59x" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part43Floor.0.BstLean.Part43.gaussian_polynomial_stein")
    | throwError "Part43Floor.gaussian_polynomial_stein is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

lemma gaussianExpectation_X_mul59x {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) :
    gaussianExpectation59x (MvPolynomial.X i * p) =
      gaussianExpectation59x (MvPolynomial.pderiv i p) := by
  simpa only [gaussianExpectation59x, LinearMap.coe_mk, AddHom.coe_mk,
    MvPolynomial.eval_mul, MvPolynomial.eval_X] using gaussianSteinImported59x p i

lemma gaussianExpectation_C_mul59x {ι : Type*} [Fintype ι]
    (c : ℝ) (p : MvPolynomial ι ℝ) :
    gaussianExpectation59x (MvPolynomial.C c * p) = c * gaussianExpectation59x p := by
  simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (gaussianExpectation59x (ι := ι)).map_smul c p

lemma gaussianExpectation_C59x {ι : Type*} [Fintype ι] (c : ℝ) :
    gaussianExpectation59x (MvPolynomial.C c : MvPolynomial ι ℝ) = c := by
  simp [gaussianExpectation59x]

def affine59x {ι : Type*} (i : ι) (t s : ℝ) : MvPolynomial ι ℝ :=
  MvPolynomial.C t + MvPolynomial.C s * MvPolynomial.X i

lemma affine_moment_step59x {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (t s : ℝ) (e : ℕ) :
    gaussianExpectation59x (affine59x i t s ^ (e + 2)) =
      t * gaussianExpectation59x (affine59x i t s ^ (e + 1)) +
      ((e : ℝ) + 1) * s ^ 2 * gaussianExpectation59x (affine59x i t s ^ e) := by
  have hd : MvPolynomial.pderiv i (affine59x i t s ^ (e + 1)) =
      MvPolynomial.C (((e : ℝ) + 1) * s) * affine59x i t s ^ e := by
    simp [MvPolynomial.pderiv_pow, affine59x, mul_assoc, mul_comm, mul_left_comm]
  have hp : affine59x i t s ^ (e + 2) =
      MvPolynomial.C t * affine59x i t s ^ (e + 1) +
      MvPolynomial.C s * (MvPolynomial.X i * affine59x i t s ^ (e + 1)) := by
    rw [show e + 2 = (e + 1) + 1 by omega, pow_succ]
    unfold affine59x
    ring
  rw [hp, map_add,
    gaussianExpectation_C_mul59x, gaussianExpectation_C_mul59x,
    gaussianExpectation_X_mul59x, hd, gaussianExpectation_C_mul59x]
  ring

lemma qH_gaussian_moment59x {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (t s : ℝ) (e : ℕ) :
    gaussianExpectation59x (affine59x i t s ^ e) = qH e t (s ^ 2) := by
  induction e using Nat.twoStepInduction with
  | zero => simpa [qH] using gaussianExpectation_C59x (ι := ι) 1
  | one =>
    simp only [pow_one, affine59x, map_add, gaussianExpectation_C59x,
      gaussianExpectation_C_mul59x, qH]
    have hx := gaussianExpectation_X_mul59x i (1 : MvPolynomial ι ℝ)
    simp only [mul_one, MvPolynomial.pderiv_one, map_zero] at hx
    rw [hx]
    ring
  | more e he he1 =>
    rw [affine_moment_step59x, he, he1, qH]

lemma qH_scalar_moment59x (t s : ℝ) (e : ℕ) :
    (∫ z : ℝ, (t + s * z) ^ e ∂ProbabilityTheory.gaussianReal 0 1) =
      qH e t (s ^ 2) := by
  have h := qH_gaussian_moment59x (ι := Fin 1) 0 t s e
  change (∫ Z, MvPolynomial.eval Z (affine59x (0 : Fin 1) t s ^ e)
    ∂stdGauss (Fin 1)) = _ at h
  simp only [map_pow, affine59x, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X] at h
  have he : (∫ Z : Fin 1 → ℝ, (t + s * Z 0) ^ e ∂stdGauss (Fin 1)) =
      ∫ z : ℝ, (t + s * z) ^ e ∂ProbabilityTheory.gaussianReal 0 1 := by
    simpa [stdGauss] using
      (integral_fintype_prod_eq_prod (fun (_ : Fin 1) (z : ℝ) => (t + s * z) ^ e)
        (μ := fun _ => ProbabilityTheory.gaussianReal 0 1))
  exact he.symm.trans h

lemma qH_product_moment59x {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (e : Fin n → ℕ) :
    (∫ Z, ∏ i, (y i + s * Z i) ^ e i ∂stdGauss (Fin n)) =
      ∏ i, qH (e i) (y i) (s ^ 2) := by
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) => (y i + s * z) ^ e i)]
  simp_rw [qH_scalar_moment59x]

end
end BstLean.Part59
