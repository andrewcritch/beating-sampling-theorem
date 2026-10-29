import BstLean.Part59LemmaQ_Coeff
import BstLean.Part59LemmaQ_Heat

namespace BstLean.Part59
open MeasureTheory
open BstLean.Part41 (Mono Tens IsSymmT contr mset)
open BstLean.Part36 (monoVal)
open BstLean.Part53 (fvA heatA)
open BstLean.Part29 (stdGauss)
noncomputable section

lemma mono_powers59x {n : ℕ} (x : Fin n → ℝ) (u : Multiset (Fin n)) :
    monoVal x u = ∏ a, x a ^ u.count a := by
  classical
  induction u using Multiset.induction_on with
  | empty => simp [monoVal]
  | @cons a u ih =>
    simp only [monoVal, Multiset.map_cons, Multiset.prod_cons] at *
    rw [ih]
    simp only [Multiset.count_cons]
    have he (b : Fin n) : x b ^ (u.count b + (if b = a then 1 else 0)) =
        (if b = a then x a else 1) * x b ^ u.count b := by
      split_ifs with h
      · subst b; rw [pow_add, pow_one]; ring
      · simp
    simp_rw [he, Finset.prod_mul_distrib]
    simp

def shiftedPoly59x {n k : ℕ} (c : Mono n k → ℝ) (y : Fin n → ℝ) (s : ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ α, MvPolynomial.C (c α) * ∏ i, affine59x i (y i) s ^ α.2.val.count i

lemma shiftedPoly_eval59x {n k : ℕ} (c : Mono n k → ℝ) (y : Fin n → ℝ)
    (s : ℝ) (Z : Fin n → ℝ) :
    MvPolynomial.eval Z (shiftedPoly59x c y s) = polyEval k c (fun i => y i + s * Z i) := by
  classical
  simp only [shiftedPoly59x, map_sum, map_mul, map_prod, map_pow,
    affine59x, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X,
    polyEval, BstLean.Part41.phiM, mono_powers59x]

lemma polyEval_shift_integral59x {n k : ℕ} (c : Mono n k → ℝ) (y : Fin n → ℝ)
    (s : ℝ) :
    (∫ Z, polyEval k c (fun i => y i + s * Z i) ∂stdGauss (Fin n)) =
      ∑ α, c α * ∏ i, qH (α.2.val.count i) (y i) (s ^ 2) := by
  classical
  have hpoly : gaussianExpectation59x (shiftedPoly59x c y s) =
      ∫ Z, polyEval k c (fun i => y i + s * Z i) ∂stdGauss (Fin n) := by
    change (∫ Z, MvPolynomial.eval Z (shiftedPoly59x c y s) ∂stdGauss (Fin n)) = _
    simp_rw [shiftedPoly_eval59x]
  rw [← hpoly, shiftedPoly59x, map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [gaussianExpectation_C_mul59x]
  congr 1
  change (∫ Z, MvPolynomial.eval Z (∏ i, affine59x i (y i) s ^ α.2.val.count i)
    ∂stdGauss (Fin n)) = _
  simp only [map_prod, map_pow, affine59x, map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact qH_product_moment59x y s _

lemma qH_zero59x (e : ℕ) (t : ℝ) : qH e t 0 = t ^ e := by
  induction e using Nat.twoStepInduction with
  | zero => simp [qH]
  | one => simp [qH]
  | more e he he1 => simp [qH, he1, pow_succ, mul_comm]

lemma fvA_heat_zero59x {n : ℕ} (k : ℕ) (A : Tens n) (y : Fin n → ℝ) :
    fvA k (heatA k 0 A) y = fvA k A y := by
  unfold fvA
  apply Finset.sum_congr rfl
  intro j hj
  rw [BstLean.Part53.error53_heat_zero k j (by simp only [Finset.mem_range] at hj; omega)]

lemma heat_coeff_identity59x {n k : ℕ} [Inhabited (Fin n)]
    (c : Mono n k → ℝ) (y : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    fvA k (heatA k a (tensOf k c)) y =
      ∑ α, c α * ∏ i, qH (α.2.val.count i) (y i) a := by
  classical
  by_cases hz : a = 0
  · subst a
    rw [fvA_heat_zero59x, fvA_tensOf59x]
    simp only [polyEval, BstLean.Part41.phiM, qH_zero59x, mono_powers59x]
  · have hs : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ha (Ne.symm hz))
    have h := heat_integral_square59x k (Real.sqrt a) hs (tensOf k c)
      (tensOf_symm59x n k c) y
    simp_rw [fvA_tensOf59x] at h
    rw [polyEval_shift_integral59x, Real.sq_sqrt ha] at h
    exact h.symm

lemma mono_zero_dim59x (k : ℕ) (p : Mono 0 k) : p = default := by
  have hm : p.2.val = 0 := Multiset.eq_zero_of_forall_notMem (fun i => Fin.elim0 i)
  have hi : p.1.val = 0 := by
    have h := p.2.property
    rw [hm, Multiset.card_zero] at h
    exact h.symm
  cases p with
  | mk i q =>
    have he : i = (0 : Fin (k + 1)) := Fin.ext hi
    subst i
    apply congrArg (Sigma.mk (0 : Fin (k + 1)))
    exact Subtype.ext hm

lemma fvA_zero_dim59x (k : ℕ) (A : Tens 0) (y : Fin 0 → ℝ) :
    fvA k A y = A 0 Fin.elim0 := by
  classical
  unfold fvA
  rw [Finset.sum_eq_single 0]
  · unfold contr
    rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → Fin 0)]
    · simp
    · intro w hw hne
      exact False.elim (hne (funext (fun t => Fin.elim0 t)))
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  · intro j hj hj0
    haveI : IsEmpty (Fin j → Fin 0) := ⟨fun w => Fin.elim0 (w ⟨0, by omega⟩)⟩
    simp [contr]
  · simp

lemma tensOf_zero_block59x (n k : ℕ) (c : Mono n k → ℝ) (w : Fin 0 → Fin n) :
    tensOf k c 0 w = c default := by
  have h := congrFun (congrFun (TF_tensOf59x n k c) 0) w
  simpa only [BstLean.Part53.TF, ite_true] using h.symm

lemma aH_nonneg59x (n d : ℕ) : 0 ≤ BstLean.Part53.aH n d := by
  have hc : (1 : ℝ) ≤ BstLean.Part53.c0 d := by
    unfold BstLean.Part53.c0
    have h := Finset.single_le_sum
      (s := Finset.range (d + 1)) (f := fun j => (1 : ℝ) / (j.factorial : ℝ))
      (fun j hj => by positivity) (by simp : 0 ∈ Finset.range (d + 1))
    simpa using h
  exact div_nonneg (sub_nonneg.mpr hc) (by unfold BstLean.Part36.DD; positivity)

end
end BstLean.Part59
