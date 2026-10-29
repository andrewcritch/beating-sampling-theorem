import BstLean.Part59LemmaQ_Gaussian

namespace BstLean.Part59
open BstLean.Part41

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shift59x (y : ι → ℝ) : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (y i))

lemma shift_pderiv59x (y : ι → ℝ) (i : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial.pderiv i (shift59x y p) = shift59x y (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [shift59x]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hp]
    simp [shift59x, MvPolynomial.pderiv_X, Pi.single_apply]

lemma shifted_raise_expectation59x (y : ι → ℝ) (i : ι) (p : MvPolynomial ι ℝ) :
    gaussianExpectation59x (shift59x y
      (MvPolynomial.X i * p - MvPolynomial.pderiv i p)) =
      y i * gaussianExpectation59x (shift59x y p) := by
  have hx : shift59x y (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (y i) := by simp [shift59x]
  rw [map_sub, map_mul, hx, add_mul, map_sub, map_add,
    gaussianExpectation_X_mul59x, shift_pderiv59x, gaussianExpectation_C_mul59x]
  ring

lemma shifted_wick_expectation59x (m : ℕ) (H : List ι → ℝ) (y : ι → ℝ) :
    gaussianExpectation59x (shift59x y (wickL m H)) =
      ∑ w : Fin m → ι, H (List.ofFn w) * ∏ t, y (w t) := by
  induction m generalizing H with
  | zero => simp [wickL_zero, shift59x, gaussianExpectation_C59x]
  | succ m ih =>
    rw [wickL_succ, map_sum, map_sum, sum_pi_succ]
    apply Finset.sum_congr rfl
    intro i hi
    change gaussianExpectation59x (shift59x y
      (MvPolynomial.X i * wickL m (fun u => H (i :: u)) -
        MvPolynomial.pderiv i (wickL m (fun u => H (i :: u))))) = _
    rw [shifted_raise_expectation59x, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [ofFn_cons', Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring

end
end BstLean.Part59
