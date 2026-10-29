import BstLean.Part81Defs
import BstLean.Part81VarC

/-!
# Part 81, variance bound: degree-`d` port of the Part 78 chain (varBoundK)
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

lemma PP_R (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    PP ((2 + 1) + (2 + 1)) (fun x => (Qp (d := d) hn a H x * Tp (d := d) a H i x) ^ 2) :=
  ((PP_Qp (d := d) hn a H).mul (PP_Tp (d := d) a H i)).sq

/-- Step 3: Bessel, for each `W` and `i`. -/
lemma grad_sq_le (hn : 1 ≤ n) (CF : ℝ) (hCF : 0 ≤ CF) (hF : FeatOp n d CF) (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i : Fin n) (W : WIdx n d → ℝ) :
    ∑ q : JJ n d, (eval W (pderiv (q, i) (PVp (d := d) hn a H))) ^ 2 ≤
      4 * (CF / (n : ℝ)) *
        ∫ x, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂uniformSphere n := by
  have hc : Continuous fun x => eval W (Qp (d := d) hn a H x) * Tv a H i x W := by
    refine ((PP_Qp (d := d) hn a H).cont_x W).mul ?_
    have := (PP_Tp (d := d) a H i).cont_x W
    simpa only [eval_Tp] using this
  have hb := bessel hn CF hCF hF _ hc
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [PVp_grad hn a H hH, e]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma int_G (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Integrable (fun x => ∫ W, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n d))
      (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := ((PP_R (d := d) hn a H i).int_prod hn).integral_prod_left
  simpa only [map_pow, map_mul, eval_Tp] using h

lemma swap_G (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∫ x, ∫ W, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n d) ∂uniformSphere n =
      ∫ W, ∫ x, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂uniformSphere n ∂stdGauss (WIdx n d) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n d → ℝ) => eval W ((Qp (d := d) hn a H x * Tp (d := d) a H i x) ^ 2))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n d)) ((PP_R (d := d) hn a H i).int_prod hn)
  simpa only [map_pow, map_mul, eval_Tp] using h

lemma int_G_W (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Integrable (fun W => ∫ x, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂uniformSphere n)
      (stdGauss (WIdx n d)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := ((PP_R (d := d) hn a H i).int_prod hn).integral_prod_right
  simpa only [map_pow, map_mul, eval_Tp] using h

lemma int_Q2 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => ∫ W, (eval W (Qp (d := d) hn a H x)) ^ 2 ∂stdGauss (WIdx n d))
      (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := ((PP_Qp (d := d) hn a H).sq.int_prod hn).integral_prod_left
  simpa only [map_pow] using h

lemma swap_Q2 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, ∫ W, (eval W (Qp (d := d) hn a H x)) ^ 2 ∂stdGauss (WIdx n d) ∂uniformSphere n =
      ∫ W, VG a H W ∂stdGauss (WIdx n d) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n d → ℝ) => eval W ((Qp (d := d) hn a H x) ^ 2))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n d)) ((PP_Qp (d := d) hn a H).sq.int_prod hn)
  simp only [map_pow] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => (PVp_eval' hn a H W).symm)

/-- `E_W T_i² = a_i² + 4 Σ_j H_ij² κ(x,x)`. -/
lemma Tv_second (hG : GaussLin) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    ∫ W, (Tv a H i x W) ^ 2 ∂stdGauss (WIdx n d) = a i ^ 2 + 4 * (∑ j, H i j ^ 2) * kap d x x := by
  simp only [Tv_aff]
  rw [aff_second hG, Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  unfold kap
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma wQ_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    wQ d a H x = ∫ W, (eval W (Qp (d := d) hn a H x)) ^ 2 ∂stdGauss (WIdx n d) := by
  simp [wQ, Qp, Fbar_eval]

lemma continuous_wQ (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (wQ d a H) := by
  have h := (PP_Qp (d := d) hn a H).sq.cont_gauss
  simp only [map_pow] at h
  have e : wQ d a H = fun x => ∫ W, (eval W (Qp (d := d) hn a H x)) ^ 2 ∂stdGauss (WIdx n d) :=
    funext fun x => wQ_eq hn a H x
  rw [e]; exact h

lemma continuous_kap : Continuous fun x : Fin n → ℝ => kap d x x := by
  unfold kap
  exact continuous_finsetSum _ fun q _ => (continuous_pf q).mul (continuous_pf q)

lemma pointwise_K (hn : 1 ≤ n) (K1 s1 K2 s2 : ℝ) (hs1 : 0 ≤ s1) (hK1 : K1 ≤ s1 ^ 2)
    (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ i, ∫ W, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n d) ≤
      s2 * s1 * ((nsq a + 4 * frobH H * kap d x x) * wQ d a H x) := by
  rw [wQ_eq hn]
  set u2 := ∫ W, (eval W (Qp (d := d) hn a H x)) ^ 2 ∂stdGauss (WIdx n d) with hu2
  have hi (i : Fin n) : ∫ W, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n d) ≤
      s2 * s1 * u2 * (a i ^ 2 + 4 * (∑ j, H i j ^ 2) * kap d x x) := by
    have hT : ∫ z, (eval z (Tp (d := d) a H i x)) ^ 4 ∂stdGauss (WIdx n d) ≤
        s1 ^ 2 * (∫ z, (eval z (Tp (d := d) a H i x)) ^ 2 ∂stdGauss (WIdx n d)) ^ 2 := by
      have h := hA (WIdx n d) (a i) (fun β => 2 * H i β.2 * pf x β.1)
      simp only [eval_Tp, Tv_aff]
      refine h.trans (mul_le_mul_of_nonneg_right hK1 (sq_nonneg _))
    have hU : ∫ z, (eval z (Qp (d := d) hn a H x)) ^ 4 ∂stdGauss (WIdx n d) ≤
        s2 ^ 2 * (∫ z, (eval z (Qp (d := d) hn a H x)) ^ 2 ∂stdGauss (WIdx n d)) ^ 2 :=
      (hD (WIdx n d) (Qp (d := d) hn a H x) ((PP_Qp (d := d) hn a H).deg x)).trans
        (mul_le_mul_of_nonneg_right hK2 (sq_nonneg _))
    have hh := holder_pt2 (Qp (d := d) hn a H x) (Tp (d := d) a H i x) s1 s2 hs1 hs2 hU hT
    simp only [eval_Tp, ← mul_pow] at hh
    rw [Tv_second hG] at hh
    exact hh
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [nsq, frobH]
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

/-- **The conditional variance bound, kernel form.** -/
theorem varBoundK (n d : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hP : PoincareMv) (hF : FeatOp n d CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin) :
    VarBoundK n d (4 * CF * s1 * s2) := by
  intro a H hH
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  refine ⟨continuous_wQ hn a H, ?_, ?_⟩
  · rw [← swap_Q2 hn a H]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => wQ_eq hn a H x)
  have hlam : 0 ≤ CF / (n : ℝ) := by positivity
  have hpoin := hP (WIdx n d) (PVp (d := d) hn a H)
  simp only [PVp_eval] at hpoin
  refine hpoin.trans ?_
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

end BstLean.Part81

#print axioms BstLean.Part81.varBoundK
