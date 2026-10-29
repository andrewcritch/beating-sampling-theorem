import BstLean.Part78VarA
import BstLean.Part78VarB

/-!
# Part 78, variance bound, file C: the polynomials `F_x`, `T_i`, `Q_x`, `V` and the gradient of `V`
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

lemma PP.deg {ι : Type} [Fintype ι] {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A)
    (x : Fin n → ℝ) : (A x).totalDegree ≤ d := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  rw [hA]
  refine totalDegree_finsetSum_le fun s _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simpa using hM s

lemma PP.sq {ι : Type} [Fintype ι] {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) :
    PP (d + d) (fun x => A x ^ 2) := by
  simpa only [pow_two] using hA.mul hA

/-- `z_i` as a polynomial in `W`. -/
noncomputable def Zp (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (WIdx n) ℝ :=
  ∑ q : JJ n, C (pf x q) * X (q, i)

/-- `F_x` as a polynomial in `W`. -/
noncomputable def Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial (WIdx n) ℝ :=
  ∑ i, C (a i) * Zp x i + ∑ i, ∑ j, C (H i j) * Zp x i * Zp x j

/-- `T_i = a_i + 2 Σ_j H_ij z_j`. -/
noncomputable def Tv (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : WIdx n → ℝ) : ℝ := a i + 2 * ∑ j, H i j * zv W (pf x) j

/-- `T_i` as a polynomial in `W`. -/
noncomputable def Tp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) :
    MvPolynomial (WIdx n) ℝ := C (a i) + C 2 * ∑ j, C (H i j) * Zp x j

@[simp] lemma eval_Zp (x : Fin n → ℝ) (i : Fin n) (W : WIdx n → ℝ) :
    eval W (Zp x i) = zv W (pf x) i := by
  simp only [Zp, zv, map_sum, map_mul, eval_C, eval_X]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

@[simp] lemma eval_Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (W : WIdx n → ℝ) : eval W (Fp a H x) = FG a H W x := by
  simp only [Fp, FG, Phi, map_sum, map_add, map_mul, eval_C, eval_Zp]

@[simp] lemma eval_Tp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : WIdx n → ℝ) : eval W (Tp a H i x) = Tv a H i x W := by
  simp only [Tp, Tv, map_sum, map_add, map_mul, eval_C, eval_Zp]

lemma pderiv_Zp (x : Fin n → ℝ) (q : JJ n) (i j : Fin n) :
    pderiv (q, i) (Zp x j) = if j = i then C (pf x q) else 0 := by
  classical
  simp only [Zp, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, Pi.single_apply, Prod.mk.injEq,
    smul_eq_mul, mul_zero, add_zero]
  by_cases h : j = i <;> simp [h]

lemma eval_pderiv_Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (x : Fin n → ℝ) (q : JJ n) (i : Fin n) (W : WIdx n → ℝ) :
    eval W (pderiv (q, i) (Fp a H x)) = pf x q * Tv a H i x W := by
  classical
  have hs : ∀ k, H k i = H i k := fun k => by
    have := congrFun (congrFun hH i) k; simpa [Matrix.transpose_apply] using this
  simp only [Fp, Tv, map_sum, map_add, Derivation.leibniz, pderiv_C, pderiv_Zp, smul_eq_mul,
    mul_zero, add_zero, map_mul, eval_C, eval_Zp, mul_ite, apply_ite (eval W), map_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, zero_add]
  simp only [hs, mul_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, mul_comm (a i)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

lemma Tv_aff (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : WIdx n → ℝ) :
    Tv a H i x W = a i + ∑ β : WIdx n, (2 * H i β.2 * pf x β.1) * W β := by
  unfold Tv zv
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma PP_Zp (i : Fin n) : PP 1 (fun x : Fin n → ℝ => Zp x i) := by
  unfold Zp
  refine PP.sum _ fun q _ => ?_
  have := (PP.coef (ι := WIdx n) (continuous_pf q)).mul
    (PP.const (n := n) (d := 1) (X (q, i) : MvPolynomial (WIdx n) ℝ) (by simp))
  simpa using this

lemma PP_C (c : ℝ) : PP (n := n) 0 (fun _ => (C c : MvPolynomial (WIdx n) ℝ)) :=
  PP.const _ (by simp)

lemma PP_Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : PP 2 (Fp a H) := by
  unfold Fp
  refine PP.add (PP.sum _ fun i _ => ?_) (PP.sum _ fun i _ => PP.sum _ fun j _ => ?_)
  · exact (((PP_C (a i)).mul (PP_Zp i))).mono (by norm_num)
  · exact ((((PP_C (H i j)).mul (PP_Zp i))).mul (PP_Zp j)).mono (by norm_num)

lemma PP_Tp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : PP 1 (Tp a H i) := by
  unfold Tp
  refine PP.add ((PP_C (a i)).mono (by norm_num)) ?_
  have := (PP_C (n := n) 2).mul (PP.sum Finset.univ fun j _ => (PP_C (H i j)).mul (PP_Zp j))
  exact this.mono (by norm_num)

/-! ### The mean, `Q_x`, and `V` as polynomials -/

/-- `E_y F_y` as a polynomial in `W`. -/
noncomputable def Fbar (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (WIdx n) ℝ := Classical.choose ((PP_Fp a H).int hn)

lemma Fbar_deg (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    (Fbar hn a H).totalDegree ≤ 2 := (Classical.choose_spec ((PP_Fp a H).int hn)).1

lemma Fbar_eval (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    eval W (Fbar hn a H) = ∫ x, FG a H W x ∂uniformSphere n := by
  have := (Classical.choose_spec ((PP_Fp a H).int hn)).2.1 W
  unfold Fbar
  simpa only [eval_Fp] using this

/-- `Q_x = F_x − E_y F_y`. -/
noncomputable def Qp (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial (WIdx n) ℝ := Fp a H x - Fbar hn a H

lemma PP_Qp (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : PP 2 (Qp hn a H) :=
  (PP_Fp a H).sub (PP.const _ (Fbar_deg hn a H))

lemma Qp_mean (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    ∫ x, eval W (Qp hn a H x) ∂uniformSphere n = 0 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have he : (fun x => eval W (Qp hn a H x)) = fun x => FG a H W x - eval W (Fbar hn a H) := by
    funext x; simp [Qp]
  have hi : Integrable (fun x => FG a H W x) (uniformSphere n) := by
    have := (PP_Fp a H).int_x hn W
    simpa only [eval_Fp] using this
  rw [he, integral_sub hi (integrable_const _), integral_const, Fbar_eval]
  simp

/-- `V` as a polynomial in `W`. -/
noncomputable def PVp (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (WIdx n) ℝ := Classical.choose ((PP_Qp hn a H).sq.int hn)

lemma PVp_eval (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    eval W (PVp hn a H) = VG a H W := by
  have := (Classical.choose_spec ((PP_Qp hn a H).sq.int hn)).2.1 W
  rw [PVp, this]
  simp [VG, varU, Qp, Fbar_eval]

lemma PVp_eval' (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) :
    VG a H W = ∫ x, (eval W (Qp hn a H x)) ^ 2 ∂uniformSphere n := by
  have := (Classical.choose_spec ((PP_Qp hn a H).sq.int hn)).2.1 W
  rw [← PVp_eval hn, PVp, this]
  simp

/-- The gradient of `V`. -/
lemma PVp_grad (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (q : JJ n) (i : Fin n) (W : WIdx n → ℝ) :
    eval W (pderiv (q, i) (PVp hn a H)) =
      2 * ∫ x, (eval W (Qp hn a H x) * Tv a H i x W) * pf x q ∂uniformSphere n := by
  have h := (Classical.choose_spec ((PP_Qp hn a H).sq.int hn)).2.2 (q, i) W
  rw [PVp, h]
  set cW := eval W (pderiv (q, i) (Fbar hn a H)) with hcW
  have e : (fun x => eval W (pderiv (q, i) (Qp hn a H x ^ 2))) = fun x =>
      2 * ((eval W (Qp hn a H x) * Tv a H i x W) * pf x q) - (2 * cW) * eval W (Qp hn a H x) := by
    funext x
    have h1 : eval W (pderiv (q, i) (Qp hn a H x)) = pf x q * Tv a H i x W - cW := by
      simp only [Qp, map_sub, eval_pderiv_Fp a H hH, hcW]
    rw [pow_two, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, h1]
    ring
  have i1 : Integrable (fun x => 2 * ((eval W (Qp hn a H x) * Tv a H i x W) * pf x q))
      (uniformSphere n) := by
    refine (sphere_cont_integrable78 hn ?_).const_mul _
    refine (((PP_Qp hn a H).cont_x W).mul ?_).mul (continuous_pf q)
    have := (PP_Tp a H i).cont_x W
    simpa only [eval_Tp] using this
  have i2 : Integrable (fun x => (2 * cW) * eval W (Qp hn a H x)) (uniformSphere n) :=
    ((PP_Qp hn a H).int_x hn W).const_mul _
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, Qp_mean]
  ring

end BstLean.Part78
