import BstLean.Part81Defs
import BstLean.Part81Var3

/-!
# Part 81, variance bound: degree-`d` port of the Part 78 chain (varBoundK2)
-/

namespace BstLean.Part81.VarP

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (PP gpi78 poly_cs78 aff_second sphere_cont_integrableB sphere_cont_integrable78
  holder_pt2 nsq frobH trH zv Phi GaussLin AffFourth Deg2Fourth PoincareMv PoincareMv2 WickTwoPoint
  lin bv zv_lin bv_dot lin2 lin2_int lin3 lin3_int cubic_zero)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n d : ℕ}

/-- `r_i(x) = E_W[Q_x T_i]`. -/
noncomputable def rv (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∫ W, eval W (Qp (d := d) hn a H x) * Tv a H i x W ∂stdGauss (WIdx n d)

lemma continuous_rv (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Continuous (rv (d := d) hn a H i) := by
  have h := ((PP_Qp (d := d) hn a H).mul (PP_Tp (d := d) a H i)).cont_gauss
  simp only [map_mul, eval_Tp] at h
  exact h

/-- `E_W ∂_{(q,i)} V = 2 E_x[r_i p_q]`. -/
lemma mean_grad (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (q : JJ n d) (i : Fin n) :
    ∫ W, eval W (pderiv (q, i) (PVp (d := d) hn a H)) ∂stdGauss (WIdx n d) =
      2 * ∫ x, rv (d := d) hn a H i x * pf x q ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  simp only [PVp_grad hn a H hH]
  rw [integral_const_mul]
  congr 1
  have hPP : PP (((2 + 1) + 0)) (fun x => (Qp (d := d) hn a H x * Tp (d := d) a H i x) *
      (C (pf x q) : MvPolynomial (WIdx n d) ℝ)) :=
    ((PP_Qp (d := d) hn a H).mul (PP_Tp (d := d) a H i)).mul (BstLean.Part78.PP.coef (continuous_pf q))
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n d → ℝ) =>
      eval W ((Qp (d := d) hn a H x * Tp (d := d) a H i x) * (C (pf x q) : MvPolynomial (WIdx n d) ℝ)))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n d)) (hPP.int_prod hn)
  simp only [map_mul, eval_Tp, eval_C] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [rv]
  rw [integral_mul_const]

lemma mean_grad_sq_le (hn : 1 ≤ n) (CF : ℝ) (hCF : 0 ≤ CF) (hF : FeatOp n d CF) (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i : Fin n) :
    ∑ q : JJ n d, (∫ W, eval W (pderiv (q, i) (PVp (d := d) hn a H)) ∂stdGauss (WIdx n d)) ^ 2 ≤
      4 * (CF / (n : ℝ)) * ∫ x, rv (d := d) hn a H i x ^ 2 ∂uniformSphere n := by
  have hb := bessel hn CF hCF hF _ (continuous_rv (d := d) hn a H i)
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [mean_grad hn a H hH, e]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-! ### The value of `r_i` -/

lemma FG_mean (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (y : Fin n → ℝ) : ∫ W, FG a H W y ∂stdGauss (WIdx n d) = trH H * kap d y y := by
  have h := (hW (JJ n d) n a H hH (pf y) (pf y)).1
  simp only [FG, kap, h]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by ring

lemma FG_z (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (y x : Fin n → ℝ) (k : Fin n) :
    ∫ W, FG a H W y * zv W (pf x) k ∂stdGauss (WIdx n d) = a k * kap d y x := by
  classical
  have e : (fun W : WIdx n d → ℝ => FG a H W y * zv W (pf x) k) = fun W =>
      ∑ i, a i * (lin (bv (pf y) i) W * lin (bv (pf x) k) W) +
      ∑ i, ∑ j, H i j * (lin (bv (pf y) i) W * lin (bv (pf y) j) W * lin (bv (pf x) k) W) := by
    funext W
    simp only [FG, Phi, zv_lin, add_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have i1 : Integrable (fun W : WIdx n d → ℝ =>
      ∑ i, a i * (lin (bv (pf y) i) W * lin (bv (pf x) k) W)) (stdGauss (WIdx n d)) :=
    integrable_finsetSum _ fun i _ => (lin2_int _ _).const_mul _
  have i2 : Integrable (fun W : WIdx n d → ℝ => ∑ i, ∑ j, H i j *
      (lin (bv (pf y) i) W * lin (bv (pf y) j) W * lin (bv (pf x) k) W)) (stdGauss (WIdx n d)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (lin3_int _ _ _).const_mul _
  have h2 : ∫ W : WIdx n d → ℝ, ∑ i, ∑ j, H i j *
      (lin (bv (pf y) i) W * lin (bv (pf y) j) W * lin (bv (pf x) k) W) ∂stdGauss (WIdx n d) = 0 :=
    cubic_zero (fun i j => H i j) (fun i => bv (pf y) i) (bv (pf x) k)
  rw [e, integral_add i1 i2, h2, integral_finsetSum _ fun i _ => (lin2_int _ _).const_mul _]
  simp_rw [integral_const_mul, lin2, bv_dot]
  simp [kap]

lemma Fbar_mean (hn : 1 ≤ n) (hW : WickTwoPoint) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ W, eval W (Fbar (d := d) hn a H) ∂stdGauss (WIdx n d) = trH H * tG n d := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n d → ℝ) => eval W (Fp (d := d) a H x))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n d)) ((PP_Fp (d := d) a H).int_prod hn)
  simp only [eval_Fp] at h
  simp only [Fbar_eval]
  rw [← h]
  simp only [FG_mean hW a H hH, tG]
  rw [integral_const_mul]

lemma Fbar_z (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (k : Fin n) :
    ∫ W, eval W (Fbar (d := d) hn a H) * zv W (pf x) k ∂stdGauss (WIdx n d) =
      a k * ∫ y, kap d x y ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hPP : PP (2 + 1) (fun y => Fp (d := d) a H y * Zp (d := d) x k) :=
    (PP_Fp (d := d) a H).mul (BstLean.Part78.PP.const _ ((PP_Zp (d := d) k).deg x))
  have h := integral_integral_swap
    (f := fun (y : Fin n → ℝ) (W : WIdx n d → ℝ) => eval W (Fp (d := d) a H y * Zp (d := d) x k))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n d)) (hPP.int_prod hn)
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
    (hH : H.IsSymm) (i : Fin n) (x : Fin n → ℝ) : rv (d := d) hn a H i x = rT d a H i x := by
  have iQ : Integrable (fun W => eval W (Qp (d := d) hn a H x)) (stdGauss (WIdx n d)) :=
    gauss_poly_integrable _
  have iF : Integrable (fun W => FG a H W x) (stdGauss (WIdx n d)) := by
    have := gauss_poly_integrable (Fp (d := d) a H x); simpa only [eval_Fp] using this
  have iB : Integrable (fun W => eval W (Fbar (d := d) hn a H)) (stdGauss (WIdx n d)) :=
    gauss_poly_integrable _
  have iQz (k : Fin n) : Integrable (fun W => eval W (Qp (d := d) hn a H x) * zv W (pf x) k)
      (stdGauss (WIdx n d)) := by
    have := gauss_poly_integrable (Qp (d := d) hn a H x * Zp (d := d) x k)
    simpa only [map_mul, eval_Zp] using this
  have iFz (k : Fin n) : Integrable (fun W => FG a H W x * zv W (pf x) k)
      (stdGauss (WIdx n d)) := by
    have := gauss_poly_integrable (Fp (d := d) a H x * Zp (d := d) x k)
    simpa only [map_mul, eval_Zp, eval_Fp] using this
  have iBz (k : Fin n) : Integrable (fun W => eval W (Fbar (d := d) hn a H) * zv W (pf x) k)
      (stdGauss (WIdx n d)) := by
    have := gauss_poly_integrable (Fbar (d := d) hn a H * Zp (d := d) x k)
    simpa only [map_mul, eval_Zp] using this
  have mQ : ∫ W, eval W (Qp (d := d) hn a H x) ∂stdGauss (WIdx n d) = trH H * (kap d x x - tG n d) := by
    have e : (fun W => eval W (Qp (d := d) hn a H x)) = fun W => FG a H W x - eval W (Fbar (d := d) hn a H) := by
      funext W; simp [Qp]
    rw [e, integral_sub iF iB, FG_mean hW a H hH, Fbar_mean hn hW a H hH]; ring
  have mQz (k : Fin n) : ∫ W, eval W (Qp (d := d) hn a H x) * zv W (pf x) k ∂stdGauss (WIdx n d) =
      a k * (kap d x x - ∫ y, kap d x y ∂uniformSphere n) := by
    have e : (fun W => eval W (Qp (d := d) hn a H x) * zv W (pf x) k) = fun W =>
        FG a H W x * zv W (pf x) k - eval W (Fbar (d := d) hn a H) * zv W (pf x) k := by
      funext W; simp [Qp, sub_mul]
    rw [e, integral_sub (iFz k) (iBz k), FG_z, Fbar_z]; ring
  have e : (fun W => eval W (Qp (d := d) hn a H x) * Tv a H i x W) = fun W =>
      a i * eval W (Qp (d := d) hn a H x) +
        ∑ k, (2 * H i k) * (eval W (Qp (d := d) hn a H x) * zv W (pf x) k) := by
    funext W
    simp only [Tv, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have i2 : Integrable (fun W => ∑ k, (2 * H i k) * (eval W (Qp (d := d) hn a H x) * zv W (pf x) k))
      (stdGauss (WIdx n d)) := integrable_finsetSum _ fun k _ => (iQz k).const_mul _
  have i1 : Integrable (fun W => a i * eval W (Qp (d := d) hn a H x)) (stdGauss (WIdx n d)) :=
    iQ.const_mul _
  unfold rv rT
  rw [e, integral_add i1 i2, integral_finsetSum _ fun k _ => (iQz k).const_mul _,
    integral_const_mul, mQ]
  simp only [integral_const_mul, mQz, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The first sum (as in `varBoundK`) -/

lemma grad_sum_le (n d : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hF : FeatOp n d CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ∑ α : WIdx n d, ∫ z, (eval z (pderiv α (PVp (d := d) hn a H))) ^ 2 ∂stdGauss (WIdx n d) ≤
      4 * CF * s1 * s2 / (n : ℝ) *
        ∫ x, (nsq a + 4 * frobH H * kap d x x) * wQ d a H x ∂uniformSphere n := by
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  have hlam : 0 ≤ CF / (n : ℝ) := by positivity
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have step1 (i : Fin n) :
      ∑ q : JJ n d, ∫ z, (eval z (pderiv (q, i) (PVp (d := d) hn a H))) ^ 2 ∂stdGauss (WIdx n d) ≤
        4 * (CF / (n : ℝ)) * ∫ x, ∫ W, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2
          ∂stdGauss (WIdx n d) ∂uniformSphere n := by
    rw [← integral_finsetSum _ (fun q _ => gpi78 _ 2), swap_G, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun q _ => gpi78 _ 2)
      ((int_G_W hn a H i).const_mul _) (fun W => grad_sq_le hn CF hCF hF a H hH i W)
  refine (Finset.sum_le_sum fun i _ => step1 i).trans ?_
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => int_G hn a H i)]
  have hc : Continuous fun x => (nsq a + 4 * frobH H * kap d x x) * wQ d a H x :=
    (continuous_const.add (continuous_const.mul continuous_kap)).mul (continuous_wQ hn a H)
  have step2 : ∫ x, ∑ i, ∫ W, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2
        ∂stdGauss (WIdx n d) ∂uniformSphere n ≤
      s2 * s1 * ∫ x, (nsq a + 4 * frobH H * kap d x x) * wQ d a H x ∂uniformSphere n := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun i _ => int_G hn a H i)
      ((sphere_cont_integrable78 hn hc).const_mul _)
      (fun x => pointwise_K hn K1 s1 K2 s2 hs1 hK1 hs2 hK2 hA hD hG a H x)
  have h4 : 0 ≤ 4 * (CF / (n : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left step2 h4).trans (le_of_eq ?_)
  ring

end BstLean.Part81.VarP

namespace BstLean.Part81

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (PP gpi78 sphere_cont_integrable78 nsq frobH trH GaussLin AffFourth Deg2Fourth
  PoincareMv PoincareMv2 WickTwoPoint)
open BstLean.Part81.VarP

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n d : ℕ}

/-- **The conditional variance bound, kernel form, first chaos separated.** -/
theorem varBoundK2 (n d : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hP2 : PoincareMv2) (hF : FeatOp n d CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (hW : WickTwoPoint) :
    VarBoundK2 n d (4 * CF * s1 * s2) (4 * CF) := by
  intro a H hH
  have hpoin := hP2 (WIdx n d) (PVp (d := d) hn a H)
  simp only [PVp_eval] at hpoin
  refine hpoin.trans ?_
  have h1 := grad_sum_le n d hn CF K1 s1 K2 s2 hCF hs1 hK1 hs2 hK2 hF hA hD hG a H hH
  have h2 : ∑ α : WIdx n d, (∫ z, eval z (pderiv α (PVp (d := d) hn a H)) ∂stdGauss (WIdx n d)) ^ 2 ≤
      4 * CF / (n : ℝ) * ∫ x, ∑ i, rT d a H i x ^ 2 ∂uniformSphere n := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine (Finset.sum_le_sum fun i _ => mean_grad_sq_le hn CF hCF hF a H hH i).trans
      (le_of_eq ?_)
    have e : (fun x => ∑ i, rT d a H i x ^ 2) = fun x => ∑ i, rv (d := d) hn a H i x ^ 2 := by
      funext x; simp only [rv_eq hn hW a H hH]
    have hi (i : Fin n) : Integrable (fun x => rv (d := d) hn a H i x ^ 2) (uniformSphere n) :=
      sphere_cont_integrable78 hn ((continuous_rv (d := d) hn a H i).pow 2)
    rw [e, integral_finsetSum _ fun i _ => hi i, ← Finset.mul_sum]
    ring
  linarith


end BstLean.Part81

#print axioms BstLean.Part81.varBoundK
#print axioms BstLean.Part81.varBoundK2
