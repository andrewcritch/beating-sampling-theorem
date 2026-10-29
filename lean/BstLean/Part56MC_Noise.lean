import BstLean.Part56MC_GaussianDensity
import BstLean.Part53Wick
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! The polynomial Gaussian noise operator. -/

namespace BstLean.Part56

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def leftExp (e : (ι ⊕ ι) →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e (.inl i))

private noncomputable def rightExp (e : (ι ⊕ ι) →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e (.inr i))

private noncomputable def moment (e : ι →₀ ℕ) : ℝ :=
  ∫ h, MvPolynomial.eval h (MvPolynomial.monomial e (1 : ℝ)) ∂stdGauss ι

private noncomputable def average : MvPolynomial (ι ⊕ ι) ℝ →ₗ[ℝ] MvPolynomial ι ℝ :=
  (Finsupp.lsum ℝ (fun e : (ι ⊕ ι) →₀ ℕ =>
    LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
      (MvPolynomial.monomial (leftExp e) (moment (rightExp e))))).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

private lemma average_monomial (e : (ι ⊕ ι) →₀ ℕ) (b : ℝ) :
    average (MvPolynomial.monomial e b) =
      MvPolynomial.monomial (leftExp e) (b * moment (rightExp e)) := by
  change Finsupp.lsum ℝ (fun e : (ι ⊕ ι) →₀ ℕ =>
    LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
      (MvPolynomial.monomial (leftExp e) (moment (rightExp e)))) (Finsupp.single e b) = _
  rw [Finsupp.lsum_single]
  simp only [LinearMap.smulRight_apply, LinearMap.id_coe, id_eq, MvPolynomial.smul_monomial,
    smul_eq_mul]

private lemma average_eval (p : MvPolynomial (ι ⊕ ι) ℝ) (g : ι → ℝ) :
    MvPolynomial.eval g (average p) =
      ∫ h, MvPolynomial.eval (Sum.elim g h) p ∂stdGauss ι := by
  classical
  have he (e : (ι ⊕ ι) →₀ ℕ) (b : ℝ) (h : ι → ℝ) :
      MvPolynomial.eval (Sum.elim g h) (MvPolynomial.monomial e b) =
        (b * MvPolynomial.eval g (MvPolynomial.monomial (leftExp e) 1)) *
          MvPolynomial.eval h (MvPolynomial.monomial (rightExp e) 1) := by
    simp only [MvPolynomial.eval_monomial, one_mul]
    rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    simp [leftExp, rightExp, mul_assoc]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, average_monomial]
  simp_rw [he]
  rw [integral_finsetSum _ (fun e _ =>
    ((mc56_polynomial_memLp (MvPolynomial.monomial (rightExp e) 1)).integrable
      (by simp)).const_mul _)]
  simp only [integral_const_mul, MvPolynomial.eval_monomial, moment, mul_assoc]
  apply Finset.sum_congr rfl
  intro e _
  ring

private lemma left_sub (e : (ι ⊕ ι) →₀ ℕ) (i : ι) :
    leftExp (e - Finsupp.single (.inl i) 1) = leftExp e - Finsupp.single i 1 := by
  ext j
  simp [leftExp, Finsupp.single_apply]

private lemma right_sub_left (e : (ι ⊕ ι) →₀ ℕ) (i : ι) :
    rightExp (e - Finsupp.single (.inl i) 1) = rightExp e := by
  ext j
  simp [rightExp, Finsupp.single_apply]

private lemma average_deriv (i : ι) (p : MvPolynomial (ι ⊕ ι) ℝ) :
    MvPolynomial.pderiv i (average p) = average (MvPolynomial.pderiv (.inl i) p) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, average_monomial, MvPolynomial.pderiv_monomial, left_sub, right_sub_left]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  simp [leftExp, mul_assoc, mul_comm, mul_left_comm]

private noncomputable def sectionAt (g : ι → ℝ) :
    MvPolynomial (ι ⊕ ι) ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  MvPolynomial.aeval (Sum.elim (fun i => MvPolynomial.C (g i)) MvPolynomial.X)

private lemma section_eval (g h : ι → ℝ) (p : MvPolynomial (ι ⊕ ι) ℝ) :
    MvPolynomial.eval h (sectionAt g p) = MvPolynomial.eval (Sum.elim g h) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [sectionAt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp]
    congr 1
    cases j <;> simp [sectionAt]

private lemma section_deriv (g : ι → ℝ) (i : ι) (p : MvPolynomial (ι ⊕ ι) ℝ) :
    MvPolynomial.pderiv i (sectionAt g p) = sectionAt g (MvPolynomial.pderiv (.inr i) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [sectionAt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hp]
    cases j with
    | inl j =>
      rw [show sectionAt g (MvPolynomial.X (.inl j)) = MvPolynomial.C (g j) by simp [sectionAt]]
      simp
    | inr j =>
      rw [show sectionAt g (MvPolynomial.X (.inr j)) = MvPolynomial.X j by simp [sectionAt]]
      by_cases h : i = j
      · subst j; simp
      · simp [h]

elab "mc56SteinImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part43Floor.0.BstLean.Part43.gaussian_polynomial_stein")
    | throwError "Part43Floor.gaussian_polynomial_stein is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

private lemma average_stein (i : ι) (p : MvPolynomial (ι ⊕ ι) ℝ) :
    average (MvPolynomial.X (.inr i) * p) = average (MvPolynomial.pderiv (.inr i) p) := by
  apply MvPolynomial.funext
  intro g
  rw [average_eval, average_eval]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Sum.elim_inr]
  have h := mc56SteinImported (sectionAt g p) i
  simpa only [section_eval, section_deriv] using h

noncomputable def mc56_noisy (a b : ℝ) :
    MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial (ι ⊕ ι) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C a * MvPolynomial.X (.inl i) +
    MvPolynomial.C b * MvPolynomial.X (.inr i))

noncomputable def mc56_noise (a b : ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ :=
  average.comp (mc56_noisy a b).toLinearMap

theorem mc56_noisy_eval (a b : ℝ) (p : MvPolynomial ι ℝ) (g h : ι → ℝ) :
    MvPolynomial.eval (Sum.elim g h) (mc56_noisy a b p) =
      MvPolynomial.eval (a • g + b • h) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [mc56_noisy]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mc56_noisy, Pi.smul_apply, smul_eq_mul, Pi.add_apply]

theorem mc56_noise_eval (a b : ℝ) (p : MvPolynomial ι ℝ) (g : ι → ℝ) :
    MvPolynomial.eval g (mc56_noise a b p) =
      ∫ h, MvPolynomial.eval (a • g + b • h) p ∂stdGauss ι := by
  rw [mc56_noise, LinearMap.comp_apply, average_eval]
  apply integral_congr_ae
  filter_upwards [] with h
  exact mc56_noisy_eval a b p g h

private lemma average_left (i : ι) (p : MvPolynomial (ι ⊕ ι) ℝ) :
    average (MvPolynomial.X (.inl i) * p) = MvPolynomial.X i * average p := by
  apply MvPolynomial.funext
  intro g
  rw [average_eval]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Sum.elim_inl,
    integral_const_mul, average_eval]

private lemma noisy_deriv (a b : ℝ) (i : ι) (p : MvPolynomial ι ℝ)
    (j : ι ⊕ ι) (c : ℝ)
    (hj : j = .inl i ∧ c = a ∨ j = .inr i ∧ c = b) :
    MvPolynomial.pderiv j (mc56_noisy a b p) =
      c • mc56_noisy a b (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [mc56_noisy]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hp]
    have hx : MvPolynomial.pderiv j (mc56_noisy a b (MvPolynomial.X k)) =
        c • mc56_noisy a b (MvPolynomial.pderiv i (MvPolynomial.X k : MvPolynomial ι ℝ)) := by
      rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        by_cases h : i = k <;> simp [mc56_noisy, h, Algebra.smul_def]
    rw [hx]
    by_cases h : i = k
    · subst k
      simp [smul_add, smul_mul_assoc, mul_smul_comm]
    · simp [h, smul_mul_assoc]

theorem mc56_noise_deriv (a b : ℝ) (i : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial.pderiv i (mc56_noise a b p) =
      a • mc56_noise a b (MvPolynomial.pderiv i p) := by
  change MvPolynomial.pderiv i (average (mc56_noisy a b p)) = _
  rw [average_deriv, noisy_deriv a b i p (.inl i) a (Or.inl ⟨rfl, rfl⟩), map_smul]
  rfl

theorem mc56_noise_mul_X (a b : ℝ) (i : ι) (p : MvPolynomial ι ℝ) :
    mc56_noise a b (MvPolynomial.X i * p) =
      a • (MvPolynomial.X i * mc56_noise a b p) +
        (b * b) • mc56_noise a b (MvPolynomial.pderiv i p) := by
  change average (mc56_noisy a b (MvPolynomial.X i * p)) = _
  rw [map_mul]
  rw [show mc56_noisy a b (MvPolynomial.X i) =
    a • MvPolynomial.X (.inl i) + b • MvPolynomial.X (.inr i) by
      simp [mc56_noisy, Algebra.smul_def]]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, map_add, map_smul, map_smul,
    average_left, average_stein,
    noisy_deriv a b i p (.inr i) b (Or.inr ⟨rfl, rfl⟩), map_smul, smul_smul]
  rfl

theorem mc56_noise_raise (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (i : ι) (p : MvPolynomial ι ℝ) :
    mc56_noise a b (MvPolynomial.X i * p - MvPolynomial.pderiv i p) =
      a • (MvPolynomial.X i * mc56_noise a b p -
        MvPolynomial.pderiv i (mc56_noise a b p)) := by
  rw [map_sub, mc56_noise_mul_X, mc56_noise_deriv, smul_sub, smul_smul]
  have hb : b * b - 1 = -(a * a) := by nlinarith [hab]
  have he : (b * b) • mc56_noise a b (MvPolynomial.pderiv i p) -
      mc56_noise a b (MvPolynomial.pderiv i p) =
      (b * b - 1) • mc56_noise a b (MvPolynomial.pderiv i p) := by
    rw [sub_smul, one_smul]
  rw [add_sub_assoc, he, hb, neg_smul]
  abel

noncomputable def mc56_wickWord : List ι → MvPolynomial ι ℝ
  | [] => 1
  | i :: w => MvPolynomial.X i * mc56_wickWord w - MvPolynomial.pderiv i (mc56_wickWord w)

theorem mc56_noise_one (a b : ℝ) : mc56_noise (ι := ι) a b 1 = 1 := by
  apply MvPolynomial.funext
  intro g
  rw [mc56_noise_eval]
  simp

theorem mc56_noise_wickWord (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (w : List ι) :
    mc56_noise a b (mc56_wickWord w) = a ^ w.length • mc56_wickWord w := by
  induction w with
  | nil => simp [mc56_wickWord, mc56_noise_one]
  | cons i w ih =>
    rw [mc56_wickWord, mc56_noise_raise a b hab, ih]
    rw [(MvPolynomial.pderiv i).map_smul]
    simp only [mul_smul_comm, ← smul_sub, smul_smul, List.length_cons]
    rw [pow_succ, mul_comm]

end BstLean.Part56
