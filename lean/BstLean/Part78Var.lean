import BstLean.Part78VarC

/-!
# Part 78: the conditional variance bound `VarBound n (100 * CF * s1)` (Gaussian Poincaré route)

`Var_W V ≤ (100 CF s1 / n)(‖a‖² + 8‖H‖²) E_W V`, from the Poincaré inequality (`PoincareMv`), the
feature operator bound (`FeatOp n CF`), the affine fourth moment (`AffFourth K1`, `K1 ≤ s1²`), the
second moment of a linear form (`GaussLin`) and `κ(x,x) ≤ 2` on the sphere. The degree-2 fourth
moment `E Q⁴ ≤ 5⁴ (E Q²)²` is `fourth_moment_5_2` (Part 62 criterion at `κ = 5`).
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part48 (gauss_poly_integrable)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n : ℕ}

lemma PP_R (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    PP ((2 + 1) + (2 + 1)) (fun x => (Qp hn a H x * Tp a H i x) ^ 2) :=
  ((PP_Qp hn a H).mul (PP_Tp a H i)).sq

/-- Step 3: Bessel, for each `W` and `i`. -/
lemma grad_sq_le (hn : 1 ≤ n) (CF : ℝ) (hCF : 0 ≤ CF) (hF : FeatOp n CF) (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i : Fin n) (W : WIdx n → ℝ) :
    ∑ q : JJ n, (eval W (pderiv (q, i) (PVp hn a H))) ^ 2 ≤
      4 * (CF / (n : ℝ)) *
        ∫ x, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂uniformSphere n := by
  have hc : Continuous fun x => eval W (Qp hn a H x) * Tv a H i x W := by
    refine ((PP_Qp hn a H).cont_x W).mul ?_
    have := (PP_Tp a H i).cont_x W
    simpa only [eval_Tp] using this
  have hb := bessel hn CF hCF hF _ hc
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [PVp_grad hn a H hH, e]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma int_G (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Integrable (fun x => ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n))
      (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := ((PP_R hn a H i).int_prod hn).integral_prod_left
  simpa only [map_pow, map_mul, eval_Tp] using h

lemma swap_G (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∫ x, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ∂uniformSphere n =
      ∫ W, ∫ x, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂uniformSphere n ∂stdGauss (WIdx n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n → ℝ) => eval W ((Qp hn a H x * Tp a H i x) ^ 2))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n)) ((PP_R hn a H i).int_prod hn)
  simpa only [map_pow, map_mul, eval_Tp] using h

lemma int_G_W (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Integrable (fun W => ∫ x, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂uniformSphere n)
      (stdGauss (WIdx n)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := ((PP_R hn a H i).int_prod hn).integral_prod_right
  simpa only [map_pow, map_mul, eval_Tp] using h

lemma int_Q2 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n))
      (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := ((PP_Qp hn a H).sq.int_prod hn).integral_prod_left
  simpa only [map_pow] using h

lemma swap_Q2 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) ∂uniformSphere n =
      ∫ W, VG a H W ∂stdGauss (WIdx n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : WIdx n → ℝ) => eval W ((Qp hn a H x) ^ 2))
    (μ := uniformSphere n) (ν := stdGauss (WIdx n)) ((PP_Qp hn a H).sq.int_prod hn)
  simp only [map_pow] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => (PVp_eval' hn a H W).symm)

/-- `E_W T_i² = a_i² + 4 Σ_j H_ij² κ(x,x)`. -/
lemma Tv_second (hG : GaussLin) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    ∫ W, (Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) = a i ^ 2 + 4 * (∑ j, H i j ^ 2) * kap x x := by
  simp only [Tv_aff]
  rw [aff_second hG, Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  unfold kap
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Step 5: Hölder and the fourth moments, for a fixed `x` with `κ(x,x) ≤ 2`. -/
lemma pointwise_le (hn : 1 ≤ n) (K1 s1 : ℝ) (hs1 : 0 ≤ s1) (hK1 : K1 ≤ s1 ^ 2)
    (hA : AffFourth K1) (hG : GaussLin) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : kap x x ≤ 2) :
    ∑ i, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ≤
      25 * s1 * (nsq a + 8 * frobH H) * ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) := by
  set u2 := ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) with hu2
  have hu0 : 0 ≤ u2 := integral_nonneg fun W => sq_nonneg _
  have hfr : ∀ i, 0 ≤ ∑ j, H i j ^ 2 := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hi (i : Fin n) : ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ≤
      25 * s1 * u2 * (a i ^ 2 + 8 * ∑ j, H i j ^ 2) := by
    have hT : ∫ z, (eval z (Tp a H i x)) ^ 4 ∂stdGauss (WIdx n) ≤
        s1 ^ 2 * (∫ z, (eval z (Tp a H i x)) ^ 2 ∂stdGauss (WIdx n)) ^ 2 := by
      have h := hA (WIdx n) (a i) (fun β => 2 * H i β.2 * pf x β.1)
      simp only [eval_Tp, Tv_aff]
      refine h.trans (mul_le_mul_of_nonneg_right hK1 (sq_nonneg _))
    have hh := holder_pt (Qp hn a H x) (Tp a H i x) ((PP_Qp hn a H).deg x) s1 hs1 hT
    simp only [eval_Tp, ← mul_pow] at hh
    rw [Tv_second hG] at hh
    refine hh.trans ?_
    rw [← hu2]
    have h0 : 0 ≤ 25 * s1 * u2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    nlinarith [hfr i]
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [nsq, frobH]
  ring

/-- **The conditional variance bound**, Poincaré route. -/
theorem varBound (n : ℕ) (hn : 1 ≤ n) (CF K1 s1 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2)
    (hP : PoincareMv) (hF : FeatOp n CF) (hA : AffFourth K1) (hG : GaussLin) (hW : WickTwoPoint)
    (hM : MeanIds n) (hR : RegIface n)
    (hkap : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → kap x x ≤ 2) :
    VarBound n (100 * CF * s1) := by
  intro a H hH
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  have hlam : 0 ≤ CF / (n : ℝ) := by positivity
  have hpoin := hP (WIdx n) (PVp hn a H)
  simp only [PVp_eval] at hpoin
  refine hpoin.trans ?_
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
  have step2 : ∫ x, ∑ i, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2
        ∂stdGauss (WIdx n) ∂uniformSphere n ≤
      25 * s1 * (nsq a + 8 * frobH H) * ∫ W, VG a H W ∂stdGauss (WIdx n) := by
    rw [← swap_Q2 hn a H, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => int_G hn a H i)
      ((int_Q2 hn a H).const_mul _) ?_
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact pointwise_le hn K1 s1 hs1 hK1 hA hG a H x (hkap x hx)
  have h4 : 0 ≤ 4 * (CF / (n : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left step2 h4).trans (le_of_eq ?_)
  ring

end BstLean.Part78

#print axioms BstLean.Part78.varBound
