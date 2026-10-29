import BstLean.Part82Defs
import BstLean.Part78Var4

/-!
# Part 82, variance bound, file A: the polynomials `F_x`, `G_i`, `Q_x`, `V` at degree `(3,3)` and
the gradient of `V`

The cubic copy of `Part78VarC.lean`. All names are in `BstLean.Part82.VarAux`.
-/

namespace BstLean.Part82.VarAux

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part78 (PP zv sphere_cont_integrable78 gpi78 poly_cs78)
open BstLean.Part82

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n : ℕ}

lemma continuous_pf3 (q : JJ3 n) : Continuous fun x : Fin n → ℝ => pf3 x q := by
  unfold pf3 BstLean.Part41.phiM BstLean.Part36.monoVal
  exact continuous_multiset_prod _ fun i _ => continuous_apply i

/-- `z_i` as a polynomial in `W`. -/
noncomputable def Zp3 (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (WIdx3 n) ℝ :=
  ∑ q : JJ3 n, C (pf3 x q) * X (q, i)

/-- `F_x` as a polynomial in `W`. -/
noncomputable def Fp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (x : Fin n → ℝ) :
    MvPolynomial (WIdx3 n) ℝ :=
  ∑ i, C (a i) * Zp3 x i + ∑ i, ∑ j, C (H i j) * Zp3 x i * Zp3 x j +
    ∑ i, ∑ j, ∑ k, C (T i j k) * Zp3 x i * Zp3 x j * Zp3 x k

/-- `G_i = a_i + 2 (Hz)_i + 3 T_i[z,z]` as a polynomial in `W`. -/
noncomputable def Gp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (i : Fin n)
    (x : Fin n → ℝ) : MvPolynomial (WIdx3 n) ℝ :=
  C (a i) + C 2 * ∑ j, C (H i j) * Zp3 x j + C 3 * ∑ j, ∑ k, C (T i j k) * Zp3 x j * Zp3 x k

@[simp] lemma eval_Zp3 (x : Fin n → ℝ) (i : Fin n) (W : WIdx3 n → ℝ) :
    eval W (Zp3 x i) = zv W (pf3 x) i := by
  simp only [Zp3, zv, map_sum, map_mul, eval_C, eval_X]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

@[simp] lemma eval_Fp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (x : Fin n → ℝ)
    (W : WIdx3 n → ℝ) : eval W (Fp3 a H T x) = FG3 a H T W x := by
  simp only [Fp3, FG3, Phi3, map_sum, map_add, map_mul, eval_C, eval_Zp3]

@[simp] lemma eval_Gp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (i : Fin n)
    (x : Fin n → ℝ) (W : WIdx3 n → ℝ) : eval W (Gp3 a H T i x) = gradF3 a H T W x i := by
  simp only [Gp3, gradF3, map_sum, map_add, map_mul, eval_C, eval_Zp3]

lemma pderiv_Zp3 (x : Fin n → ℝ) (q : JJ3 n) (i j : Fin n) :
    pderiv (q, i) (Zp3 x j) = if j = i then C (pf3 x q) else 0 := by
  classical
  simp only [Zp3, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, Pi.single_apply, Prod.mk.injEq,
    smul_eq_mul, mul_zero, add_zero]
  by_cases h : j = i <;> simp [h]

lemma eval_pderiv_Zp3 (x : Fin n → ℝ) (q : JJ3 n) (i j : Fin n) (W : WIdx3 n → ℝ) :
    eval W (pderiv (q, i) (Zp3 x j)) = if j = i then pf3 x q else 0 := by
  rw [pderiv_Zp3]; split_ifs <;> simp

/-- The algebra of the chain rule. -/
lemma chain_alg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (T : T3 n)
    (hT : SymT T) (z : Fin n → ℝ) (i : Fin n) (p : ℝ) (d : Fin n → ℝ)
    (hd : ∀ j, d j = if j = i then p else 0) :
    ∑ j, a j * d j + ∑ j, ∑ k, H j k * (d j * z k + z j * d k) +
      ∑ j, ∑ k, ∑ l, T j k l * (d j * z k * z l + z j * d k * z l + z j * z k * d l) =
    p * (a i + 2 * ∑ j, H i j * z j + 3 * ∑ j, ∑ k, T i j k * z j * z k) := by
  classical
  have hs : ∀ k, H k i = H i k := fun k => by
    have := congrFun (congrFun hH i) k; simpa [Matrix.transpose_apply] using this
  have s1 : ∀ f : Fin n → ℝ, ∑ j, f j * d j = f i * p := by
    intro f; simp [hd]
  have e1 : ∑ j, ∑ k, H j k * (d j * z k + z j * d k) =
      ∑ j, (∑ k, H j k * z k) * d j + ∑ k, (∑ j, H j k * z j) * d k := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ j, ∑ k, ∑ l, T j k l * (d j * z k * z l + z j * d k * z l + z j * z k * d l) =
      ∑ j, (∑ k, ∑ l, T j k l * z k * z l) * d j + ∑ k, (∑ j, ∑ l, T j k l * z j * z l) * d k +
        ∑ l, (∑ j, ∑ k, T j k l * z j * z k) * d l := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun l _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun l _ => by ring
    · have : ∀ j, ∑ k, ∑ l, T j k l * (z j * z k * d l) = ∑ l, ∑ k, T j k l * z j * z k * d l := by
        intro j; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      simp only [this]
      rw [Finset.sum_comm]
  rw [e1, e2]
  simp only [s1]
  have t1 : ∑ j, H j i * z j = ∑ j, H i j * z j :=
    Finset.sum_congr rfl fun j _ => by rw [hs]
  have t2 : ∑ j, ∑ l, T j i l * z j * z l = ∑ j, ∑ k, T i j k * z j * z k :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [(hT j i l).1]
  have t3 : ∑ j, ∑ k, T j k i * z j * z k = ∑ j, ∑ k, T i j k * z j * z k :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [(hT j k i).2, (hT j i k).1]
  rw [t1, t2, t3]
  ring

lemma eval_pderiv_Fp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (T : T3 n)
    (hT : SymT T) (x : Fin n → ℝ) (q : JJ3 n) (i : Fin n) (W : WIdx3 n → ℝ) :
    eval W (pderiv (q, i) (Fp3 a H T x)) = pf3 x q * gradF3 a H T W x i := by
  classical
  rw [gradF3, ← chain_alg a H hH T hT (zv W (pf3 x)) i (pf3 x q)
    (fun j => eval W (pderiv (q, i) (Zp3 x j))) (fun j => eval_pderiv_Zp3 x q i j W)]
  simp only [Fp3, map_sum, map_add, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero,
    zero_mul, zero_add, map_mul, eval_C, eval_Zp3]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · rfl
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => by ring

lemma PP_Zp3 (i : Fin n) : PP 1 (fun x : Fin n → ℝ => Zp3 x i) := by
  unfold Zp3
  refine PP.sum _ fun q _ => ?_
  have := (PP.coef (ι := WIdx3 n) (continuous_pf3 q)).mul
    (PP.const (n := n) (d := 1) (X (q, i) : MvPolynomial (WIdx3 n) ℝ) (by simp))
  simpa using this

lemma PP_C3 (c : ℝ) : PP (n := n) 0 (fun _ => (C c : MvPolynomial (WIdx3 n) ℝ)) :=
  PP.const _ (by simp)

lemma PP_Fp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) : PP 3 (Fp3 a H T) := by
  unfold Fp3
  refine PP.add (PP.add (PP.sum _ fun i _ => ?_) (PP.sum _ fun i _ => PP.sum _ fun j _ => ?_))
    (PP.sum _ fun i _ => PP.sum _ fun j _ => PP.sum _ fun k _ => ?_)
  · exact (((PP_C3 (a i)).mul (PP_Zp3 i))).mono (by norm_num)
  · exact ((((PP_C3 (H i j)).mul (PP_Zp3 i))).mul (PP_Zp3 j)).mono (by norm_num)
  · exact (((((PP_C3 (T i j k)).mul (PP_Zp3 i))).mul (PP_Zp3 j)).mul (PP_Zp3 k)).mono (by norm_num)

lemma PP_Gp3 (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (i : Fin n) :
    PP 2 (Gp3 a H T i) := by
  unfold Gp3
  refine PP.add (PP.add ((PP_C3 (a i)).mono (by norm_num)) ?_) ?_
  · have := (PP_C3 (n := n) 2).mul (PP.sum Finset.univ fun j _ => (PP_C3 (H i j)).mul (PP_Zp3 j))
    exact this.mono (by norm_num)
  · have := (PP_C3 (n := n) 3).mul (PP.sum Finset.univ fun j _ => PP.sum Finset.univ fun k _ =>
      ((PP_C3 (T i j k)).mul (PP_Zp3 j)).mul (PP_Zp3 k))
    exact this.mono (by norm_num)

/-! ### The mean, `Q_x`, and `V` as polynomials -/

/-- `E_y F_y` as a polynomial in `W`. -/
noncomputable def Fbar3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    MvPolynomial (WIdx3 n) ℝ := Classical.choose ((PP_Fp3 a H T).int hn)

lemma Fbar3_deg (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    (Fbar3 hn a H T).totalDegree ≤ 3 := (Classical.choose_spec ((PP_Fp3 a H T).int hn)).1

lemma Fbar3_eval (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) :
    eval W (Fbar3 hn a H T) = ∫ x, FG3 a H T W x ∂uniformSphere n := by
  have := (Classical.choose_spec ((PP_Fp3 a H T).int hn)).2.1 W
  unfold Fbar3
  simpa only [eval_Fp3] using this

/-- `Q_x = F_x − E_y F_y`. -/
noncomputable def Qp3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (x : Fin n → ℝ) : MvPolynomial (WIdx3 n) ℝ := Fp3 a H T x - Fbar3 hn a H T

lemma PP_Qp3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    PP 3 (Qp3 hn a H T) :=
  (PP_Fp3 a H T).sub (PP.const _ (Fbar3_deg hn a H T))

lemma eval_Qp3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (x : Fin n → ℝ) (W : WIdx3 n → ℝ) :
    eval W (Qp3 hn a H T x) = FG3 a H T W x - ∫ y, FG3 a H T W y ∂uniformSphere n := by
  simp [Qp3, Fbar3_eval]

lemma Qp3_mean (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) :
    ∫ x, eval W (Qp3 hn a H T x) ∂uniformSphere n = 0 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have he : (fun x => eval W (Qp3 hn a H T x)) =
      fun x => FG3 a H T W x - eval W (Fbar3 hn a H T) := by
    funext x; simp [Qp3]
  have hi : Integrable (fun x => FG3 a H T W x) (uniformSphere n) := by
    have := (PP_Fp3 a H T).int_x hn W
    simpa only [eval_Fp3] using this
  rw [he, integral_sub hi (integrable_const _), integral_const, Fbar3_eval]
  simp

/-- `V` as a polynomial in `W`. -/
noncomputable def PVp3 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    MvPolynomial (WIdx3 n) ℝ := Classical.choose ((PP_Qp3 hn a H T).sq.int hn)

lemma PVp3_eval (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) : eval W (PVp3 hn a H T) = VG3 a H T W := by
  have := (Classical.choose_spec ((PP_Qp3 hn a H T).sq.int hn)).2.1 W
  rw [PVp3, this]
  simp [VG3, varU, eval_Qp3]

lemma PVp3_eval' (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : WIdx3 n → ℝ) :
    VG3 a H T W = ∫ x, (eval W (Qp3 hn a H T x)) ^ 2 ∂uniformSphere n := by
  have := (Classical.choose_spec ((PP_Qp3 hn a H T).sq.int hn)).2.1 W
  rw [← PVp3_eval hn, PVp3, this]
  simp

/-- The gradient of `V`. -/
lemma PVp3_grad (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (T : T3 n) (hT : SymT T) (q : JJ3 n) (i : Fin n) (W : WIdx3 n → ℝ) :
    eval W (pderiv (q, i) (PVp3 hn a H T)) =
      2 * ∫ x, (eval W (Qp3 hn a H T x) * gradF3 a H T W x i) * pf3 x q ∂uniformSphere n := by
  have h := (Classical.choose_spec ((PP_Qp3 hn a H T).sq.int hn)).2.2 (q, i) W
  rw [PVp3, h]
  set cW := eval W (pderiv (q, i) (Fbar3 hn a H T)) with hcW
  have e : (fun x => eval W (pderiv (q, i) (Qp3 hn a H T x ^ 2))) = fun x =>
      2 * ((eval W (Qp3 hn a H T x) * gradF3 a H T W x i) * pf3 x q) -
        (2 * cW) * eval W (Qp3 hn a H T x) := by
    funext x
    have h1 : eval W (pderiv (q, i) (Qp3 hn a H T x)) = pf3 x q * gradF3 a H T W x i - cW := by
      simp only [Qp3, map_sub, eval_pderiv_Fp3 a H hH T hT, hcW]
    rw [pow_two, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, h1]
    ring
  have i1 : Integrable (fun x => 2 * ((eval W (Qp3 hn a H T x) * gradF3 a H T W x i) * pf3 x q))
      (uniformSphere n) := by
    refine (sphere_cont_integrable78 hn ?_).const_mul _
    refine (((PP_Qp3 hn a H T).cont_x W).mul ?_).mul (continuous_pf3 q)
    have := (PP_Gp3 a H T i).cont_x W
    simpa only [eval_Gp3] using this
  have i2 : Integrable (fun x => (2 * cW) * eval W (Qp3 hn a H T x)) (uniformSphere n) :=
    ((PP_Qp3 hn a H T).int_x hn W).const_mul _
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, Qp3_mean]
  ring

end BstLean.Part82.VarAux
