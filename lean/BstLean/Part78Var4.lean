import BstLean.Part78Var3
import BstLean.Part78Defs4
import BstLean.Part78Wick

/-!
# Part 78: `varBoundK2` — the kernel form of the variance bound with the first chaos separated
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part48 (gauss_poly_integrable)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n : ℕ}

/-- `r_i(x) = E_W[Q_x T_i]`. -/
noncomputable def rv (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∫ W, eval W (Qp hn a H x) * Tv a H i x W ∂stdGauss (WIdx n)

lemma continuous_rv (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Continuous (rv hn a H i) := by
  have h := ((PP_Qp hn a H).mul (PP_Tp a H i)).cont_gauss
  simp only [map_mul, eval_Tp] at h
  exact h

/-- `E_W ∂_{(q,i)} V = 2 E_x[r_i p_q]`. -/
lemma mean_grad (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (q : JJ n) (i : Fin n) :
    ∫ W, eval W (pderiv (q, i) (PVp hn a H)) ∂stdGauss (WIdx n) =
      2 * ∫ x, rv hn a H i x * pf x q ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  simp only [PVp_grad hn a H hH]
  rw [integral_const_mul]
  congr 1
  have hPP : PP (((2 + 1) + 0)) (fun x => (Qp hn a H x * Tp a H i x) *
      (C (pf x q) : MvPolynomial (WIdx n) ℝ)) :=
    ((PP_Qp hn a H).mul (PP_Tp a H i)).mul (PP.coef (continuous_pf q))
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n → ℝ) =>
      eval W ((Qp hn a H x * Tp a H i x) * (C (pf x q) : MvPolynomial (WIdx n) ℝ)))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n)) (hPP.int_prod hn)
  simp only [map_mul, eval_Tp, eval_C] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [rv]
  rw [integral_mul_const]

lemma mean_grad_sq_le (hn : 1 ≤ n) (CF : ℝ) (hCF : 0 ≤ CF) (hF : FeatOp n CF) (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i : Fin n) :
    ∑ q : JJ n, (∫ W, eval W (pderiv (q, i) (PVp hn a H)) ∂stdGauss (WIdx n)) ^ 2 ≤
      4 * (CF / (n : ℝ)) * ∫ x, rv hn a H i x ^ 2 ∂uniformSphere n := by
  have hb := bessel hn CF hCF hF _ (continuous_rv hn a H i)
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [mean_grad hn a H hH, e]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-! ### The value of `r_i` -/

lemma FG_mean (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (y : Fin n → ℝ) : ∫ W, FG a H W y ∂stdGauss (WIdx n) = trH H * kap y y := by
  have h := (hW (JJ n) n a H hH (pf y) (pf y)).1
  simp only [FG, kap, h]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by ring

lemma cubic_zero {ι : Type} [Fintype ι] (H : Fin n → Fin n → ℝ) (B : Fin n → ι → ℝ)
    (c : ι → ℝ) :
    ∫ W, ∑ i, ∑ j, H i j * (lin (B i) W * lin (B j) W * lin c W) ∂stdGauss ι = 0 := by
  classical
  rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (lin3_int _ _ _).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ => (lin3_int _ _ _).const_mul _, integral_const_mul, lin3]
  simp

lemma FG_z (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (y x : Fin n → ℝ) (k : Fin n) :
    ∫ W, FG a H W y * zv W (pf x) k ∂stdGauss (WIdx n) = a k * kap y x := by
  classical
  have e : (fun W : WIdx n → ℝ => FG a H W y * zv W (pf x) k) = fun W =>
      ∑ i, a i * (lin (bv (pf y) i) W * lin (bv (pf x) k) W) +
      ∑ i, ∑ j, H i j * (lin (bv (pf y) i) W * lin (bv (pf y) j) W * lin (bv (pf x) k) W) := by
    funext W
    simp only [FG, Phi, zv_lin, add_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have i1 : Integrable (fun W : WIdx n → ℝ =>
      ∑ i, a i * (lin (bv (pf y) i) W * lin (bv (pf x) k) W)) (stdGauss (WIdx n)) :=
    integrable_finsetSum _ fun i _ => (lin2_int _ _).const_mul _
  have i2 : Integrable (fun W : WIdx n → ℝ => ∑ i, ∑ j, H i j *
      (lin (bv (pf y) i) W * lin (bv (pf y) j) W * lin (bv (pf x) k) W)) (stdGauss (WIdx n)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (lin3_int _ _ _).const_mul _
  have h2 : ∫ W : WIdx n → ℝ, ∑ i, ∑ j, H i j *
      (lin (bv (pf y) i) W * lin (bv (pf y) j) W * lin (bv (pf x) k) W) ∂stdGauss (WIdx n) = 0 :=
    cubic_zero (fun i j => H i j) (fun i => bv (pf y) i) (bv (pf x) k)
  rw [e, integral_add i1 i2, h2, integral_finsetSum _ fun i _ => (lin2_int _ _).const_mul _]
  simp_rw [integral_const_mul, lin2, bv_dot]
  simp [kap]

lemma Fbar_mean (hn : 1 ≤ n) (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ W, eval W (Fbar hn a H) ∂stdGauss (WIdx n) = trH H * tG n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n → ℝ) => eval W (Fp a H x))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n)) ((PP_Fp a H).int_prod hn)
  simp only [eval_Fp] at h
  simp only [Fbar_eval]
  rw [← h]
  simp only [FG_mean hW a H hH, tG]
  rw [integral_const_mul]

lemma Fbar_z (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (k : Fin n) :
    ∫ W, eval W (Fbar hn a H) * zv W (pf x) k ∂stdGauss (WIdx n) =
      a k * ∫ y, kap x y ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hPP : PP (2 + 1) (fun y => Fp a H y * Zp x k) :=
    (PP_Fp a H).mul (PP.const _ ((PP_Zp k).deg x))
  have h := integral_integral_swap
    (f := fun (y : Fin n → ℝ) (W : WIdx n → ℝ) => eval W (Fp a H y * Zp x k))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n)) (hPP.int_prod hn)
  simp only [map_mul, eval_Fp, eval_Zp] at h
  simp only [Fbar_eval]
  simp_rw [← integral_mul_const]
  rw [← h]
  simp only [FG_z]
  rw [integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [kap]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

lemma rv_eq (hn : 1 ≤ n) (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (i : Fin n) (x : Fin n → ℝ) : rv hn a H i x = rT a H i x := by
  have iQ : Integrable (fun W => eval W (Qp hn a H x)) (stdGauss (WIdx n)) :=
    gauss_poly_integrable _
  have iF : Integrable (fun W => FG a H W x) (stdGauss (WIdx n)) := by
    have := gauss_poly_integrable (Fp a H x); simpa only [eval_Fp] using this
  have iB : Integrable (fun W => eval W (Fbar hn a H)) (stdGauss (WIdx n)) :=
    gauss_poly_integrable _
  have iQz (k : Fin n) : Integrable (fun W => eval W (Qp hn a H x) * zv W (pf x) k)
      (stdGauss (WIdx n)) := by
    have := gauss_poly_integrable (Qp hn a H x * Zp x k)
    simpa only [map_mul, eval_Zp] using this
  have iFz (k : Fin n) : Integrable (fun W => FG a H W x * zv W (pf x) k)
      (stdGauss (WIdx n)) := by
    have := gauss_poly_integrable (Fp a H x * Zp x k)
    simpa only [map_mul, eval_Zp, eval_Fp] using this
  have iBz (k : Fin n) : Integrable (fun W => eval W (Fbar hn a H) * zv W (pf x) k)
      (stdGauss (WIdx n)) := by
    have := gauss_poly_integrable (Fbar hn a H * Zp x k)
    simpa only [map_mul, eval_Zp] using this
  have mQ : ∫ W, eval W (Qp hn a H x) ∂stdGauss (WIdx n) = trH H * (kap x x - tG n) := by
    have e : (fun W => eval W (Qp hn a H x)) = fun W => FG a H W x - eval W (Fbar hn a H) := by
      funext W; simp [Qp]
    rw [e, integral_sub iF iB, FG_mean hW a H hH, Fbar_mean hn hW a H hH]; ring
  have mQz (k : Fin n) : ∫ W, eval W (Qp hn a H x) * zv W (pf x) k ∂stdGauss (WIdx n) =
      a k * (kap x x - ∫ y, kap x y ∂uniformSphere n) := by
    have e : (fun W => eval W (Qp hn a H x) * zv W (pf x) k) = fun W =>
        FG a H W x * zv W (pf x) k - eval W (Fbar hn a H) * zv W (pf x) k := by
      funext W; simp [Qp, sub_mul]
    rw [e, integral_sub (iFz k) (iBz k), FG_z, Fbar_z]; ring
  have e : (fun W => eval W (Qp hn a H x) * Tv a H i x W) = fun W =>
      a i * eval W (Qp hn a H x) +
        ∑ k, (2 * H i k) * (eval W (Qp hn a H x) * zv W (pf x) k) := by
    funext W
    simp only [Tv, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have i2 : Integrable (fun W => ∑ k, (2 * H i k) * (eval W (Qp hn a H x) * zv W (pf x) k))
      (stdGauss (WIdx n)) := integrable_finsetSum _ fun k _ => (iQz k).const_mul _
  have i1 : Integrable (fun W => a i * eval W (Qp hn a H x)) (stdGauss (WIdx n)) :=
    iQ.const_mul _
  unfold rv rT
  rw [e, integral_add i1 i2, integral_finsetSum _ fun k _ => (iQz k).const_mul _,
    integral_const_mul, mQ]
  simp only [integral_const_mul, mQz, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The first sum (as in `varBoundK`) -/

lemma grad_sum_le (n : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hF : FeatOp n CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ∑ α : WIdx n, ∫ z, (eval z (pderiv α (PVp hn a H))) ^ 2 ∂stdGauss (WIdx n) ≤
      4 * CF * s1 * s2 / (n : ℝ) *
        ∫ x, (nsq a + 4 * frobH H * kap x x) * wQ a H x ∂uniformSphere n := by
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  have hlam : 0 ≤ CF / (n : ℝ) := by positivity
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have step1 (i : Fin n) :
      ∑ q : JJ n, ∫ z, (eval z (pderiv (q, i) (PVp hn a H))) ^ 2 ∂stdGauss (WIdx n) ≤
        4 * (CF / (n : ℝ)) * ∫ x, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2
          ∂stdGauss (WIdx n) ∂uniformSphere n := by
    rw [← integral_finsetSum _ (fun q _ => gpi78 _ 2), swap_G, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun q _ => gpi78 _ 2)
      ((int_G_W hn a H i).const_mul _) (fun W => grad_sq_le hn CF hCF hF a H hH i W)
  refine (Finset.sum_le_sum fun i _ => step1 i).trans ?_
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => int_G hn a H i)]
  have hc : Continuous fun x => (nsq a + 4 * frobH H * kap x x) * wQ a H x :=
    (continuous_const.add (continuous_const.mul continuous_kap)).mul (continuous_wQ hn a H)
  have step2 : ∫ x, ∑ i, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2
        ∂stdGauss (WIdx n) ∂uniformSphere n ≤
      s2 * s1 * ∫ x, (nsq a + 4 * frobH H * kap x x) * wQ a H x ∂uniformSphere n := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun i _ => int_G hn a H i)
      ((sphere_cont_integrable78 hn hc).const_mul _)
      (fun x => pointwise_K hn K1 s1 K2 s2 hs1 hK1 hs2 hK2 hA hD hG a H x)
  have h4 : 0 ≤ 4 * (CF / (n : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left step2 h4).trans (le_of_eq ?_)
  ring

/-- **The conditional variance bound, kernel form, first chaos separated.** -/
theorem varBoundK2 (n : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hP2 : PoincareMv2) (hF : FeatOp n CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (hW : WickTwoPoint) :
    VarBoundK2 n (4 * CF * s1 * s2) (4 * CF) := by
  intro a H hH
  have hpoin := hP2 (WIdx n) (PVp hn a H)
  simp only [PVp_eval] at hpoin
  refine hpoin.trans ?_
  have h1 := grad_sum_le n hn CF K1 s1 K2 s2 hCF hs1 hK1 hs2 hK2 hF hA hD hG a H hH
  have h2 : ∑ α : WIdx n, (∫ z, eval z (pderiv α (PVp hn a H)) ∂stdGauss (WIdx n)) ^ 2 ≤
      4 * CF / (n : ℝ) * ∫ x, ∑ i, rT a H i x ^ 2 ∂uniformSphere n := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine (Finset.sum_le_sum fun i _ => mean_grad_sq_le hn CF hCF hF a H hH i).trans
      (le_of_eq ?_)
    have e : (fun x => ∑ i, rT a H i x ^ 2) = fun x => ∑ i, rv hn a H i x ^ 2 := by
      funext x; simp only [rv_eq hn hW a H hH]
    have hi (i : Fin n) : Integrable (fun x => rv hn a H i x ^ 2) (uniformSphere n) :=
      sphere_cont_integrable78 hn ((continuous_rv hn a H i).pow 2)
    rw [e, integral_finsetSum _ fun i _ => hi i, ← Finset.mul_sum]
    ring
  linarith

end BstLean.Part78

#print axioms BstLean.Part78.varBoundK2
