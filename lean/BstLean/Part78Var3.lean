import BstLean.Part78Var2
import BstLean.Part78Defs3

/-!
# Part 78: `varBoundK` — the kernel form of the variance bound (no use of `κ(x,x) ≤ 2`)
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part48 (gauss_poly_integrable)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n : ℕ}

lemma PP.cont_gauss {ι : Type} [Fintype ι] {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ}
    (hA : PP d A) : Continuous (fun x => ∫ W, eval W (A x) ∂stdGauss ι) := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  have e : (fun x => ∫ W, eval W (A x) ∂stdGauss ι) =
      fun x => ∑ s, b s x * ∫ W, eval W (M s) ∂stdGauss ι := by
    funext x
    simp only [hA, map_sum, map_mul, eval_C]
    rw [integral_finsetSum _ fun s _ => (gauss_poly_integrable (M s)).const_mul _]
    exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
  rw [e]
  exact continuous_finsetSum _ fun s _ => (hb s).mul continuous_const

lemma wQ_eq (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    wQ a H x = ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) := by
  simp [wQ, Qp, Fbar_eval]

lemma continuous_wQ (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (wQ a H) := by
  have h := (PP_Qp hn a H).sq.cont_gauss
  simp only [map_pow] at h
  have e : wQ a H = fun x => ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) :=
    funext fun x => wQ_eq hn a H x
  rw [e]; exact h

lemma continuous_kap : Continuous fun x : Fin n → ℝ => kap x x := by
  unfold kap
  exact continuous_finsetSum _ fun q _ => (continuous_pf q).mul (continuous_pf q)

lemma pointwise_K (hn : 1 ≤ n) (K1 s1 K2 s2 : ℝ) (hs1 : 0 ≤ s1) (hK1 : K1 ≤ s1 ^ 2)
    (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ i, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ≤
      s2 * s1 * ((nsq a + 4 * frobH H * kap x x) * wQ a H x) := by
  rw [wQ_eq hn]
  set u2 := ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) with hu2
  have hi (i : Fin n) : ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ≤
      s2 * s1 * u2 * (a i ^ 2 + 4 * (∑ j, H i j ^ 2) * kap x x) := by
    have hT : ∫ z, (eval z (Tp a H i x)) ^ 4 ∂stdGauss (WIdx n) ≤
        s1 ^ 2 * (∫ z, (eval z (Tp a H i x)) ^ 2 ∂stdGauss (WIdx n)) ^ 2 := by
      have h := hA (WIdx n) (a i) (fun β => 2 * H i β.2 * pf x β.1)
      simp only [eval_Tp, Tv_aff]
      refine h.trans (mul_le_mul_of_nonneg_right hK1 (sq_nonneg _))
    have hU : ∫ z, (eval z (Qp hn a H x)) ^ 4 ∂stdGauss (WIdx n) ≤
        s2 ^ 2 * (∫ z, (eval z (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n)) ^ 2 :=
      (hD (WIdx n) (Qp hn a H x) ((PP_Qp hn a H).deg x)).trans
        (mul_le_mul_of_nonneg_right hK2 (sq_nonneg _))
    have hh := holder_pt2 (Qp hn a H x) (Tp a H i x) s1 s2 hs1 hs2 hU hT
    simp only [eval_Tp, ← mul_pow] at hh
    rw [Tv_second hG] at hh
    exact hh
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [nsq, frobH]
  ring

/-- **The conditional variance bound, kernel form.** -/
theorem varBoundK (n : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hP : PoincareMv) (hF : FeatOp n CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin) :
    VarBoundK n (4 * CF * s1 * s2) := by
  intro a H hH
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn
  refine ⟨continuous_wQ hn a H, ?_, ?_⟩
  · rw [← swap_Q2 hn a H]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => wQ_eq hn a H x)
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

end BstLean.Part78

#print axioms BstLean.Part78.varBoundK
