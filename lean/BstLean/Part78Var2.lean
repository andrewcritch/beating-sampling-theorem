import BstLean.Part78Var
import BstLean.Part78Defs2

/-!
# Part 78: `varBound2` — the variance bound with the degree-2 fourth-moment constant as a hypothesis
(`Deg2Fourth K2`, `K2 ≤ s2²`): `VarBound n (4 * CF * s1 * s2)`. `varBound` is the case `s2 = 25`.
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part48 (gauss_poly_integrable)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n : ℕ}

/-- Pointwise Hölder with the two fourth-moment bounds. -/
lemma holder_pt2 {κ : Type} [Fintype κ] (U T : MvPolynomial κ ℝ) (s1 s2 : ℝ) (hs1 : 0 ≤ s1)
    (hs2 : 0 ≤ s2)
    (hU4 : ∫ z, (eval z U) ^ 4 ∂stdGauss κ ≤ s2 ^ 2 * (∫ z, (eval z U) ^ 2 ∂stdGauss κ) ^ 2)
    (hT : ∫ z, (eval z T) ^ 4 ∂stdGauss κ ≤ s1 ^ 2 * (∫ z, (eval z T) ^ 2 ∂stdGauss κ) ^ 2) :
    ∫ z, (eval z U) ^ 2 * (eval z T) ^ 2 ∂stdGauss κ ≤
      s2 * s1 * (∫ z, (eval z U) ^ 2 ∂stdGauss κ) * (∫ z, (eval z T) ^ 2 ∂stdGauss κ) := by
  have hcs := poly_cs78 (U ^ 2) (T ^ 2)
  simp only [map_pow] at hcs
  have e4 (P : MvPolynomial κ ℝ) : (fun z => ((eval z P) ^ 2) ^ 2) = fun z => (eval z P) ^ 4 := by
    funext z; ring
  rw [e4, e4] at hcs
  set A := ∫ z, (eval z U) ^ 2 * (eval z T) ^ 2 ∂stdGauss κ
  set u2 := ∫ z, (eval z U) ^ 2 ∂stdGauss κ
  set t2 := ∫ z, (eval z T) ^ 2 ∂stdGauss κ
  set u4 := ∫ z, (eval z U) ^ 4 ∂stdGauss κ
  set t4 := ∫ z, (eval z T) ^ 4 ∂stdGauss κ
  have hA0 : 0 ≤ A := integral_nonneg fun z => by positivity
  have hu2 : 0 ≤ u2 := integral_nonneg fun z => by positivity
  have ht2 : 0 ≤ t2 := integral_nonneg fun z => by positivity
  have hu4 : 0 ≤ u4 := integral_nonneg fun z => by positivity
  have ht4 : 0 ≤ t4 := integral_nonneg fun z => by positivity
  have hB0 : 0 ≤ s2 * s1 * u2 * t2 := by positivity
  have hsq : A ^ 2 ≤ (s2 * s1 * u2 * t2) ^ 2 := by
    calc A ^ 2 ≤ u4 * t4 := hcs
      _ ≤ (s2 ^ 2 * u2 ^ 2) * (s1 ^ 2 * t2 ^ 2) := mul_le_mul hU4 hT ht4 (by positivity)
      _ = (s2 * s1 * u2 * t2) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ hA0 hB0 two_ne_zero).mp hsq

/-- Step 5: Hölder and the fourth moments, for a fixed `x` with `κ(x,x) ≤ 2`. -/
lemma pointwise_le2 (hn : 1 ≤ n) (K1 s1 K2 s2 : ℝ) (hs1 : 0 ≤ s1) (hK1 : K1 ≤ s1 ^ 2)
    (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : kap x x ≤ 2) :
    ∑ i, ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ≤
      s2 * s1 * (nsq a + 8 * frobH H) * ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) := by
  set u2 := ∫ W, (eval W (Qp hn a H x)) ^ 2 ∂stdGauss (WIdx n) with hu2
  have hu0 : 0 ≤ u2 := integral_nonneg fun W => sq_nonneg _
  have hfr : ∀ i, 0 ≤ ∑ j, H i j ^ 2 := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hi (i : Fin n) : ∫ W, (eval W (Qp hn a H x) * Tv a H i x W) ^ 2 ∂stdGauss (WIdx n) ≤
      s2 * s1 * u2 * (a i ^ 2 + 8 * ∑ j, H i j ^ 2) := by
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
    refine hh.trans ?_
    rw [← hu2]
    have h0 : 0 ≤ s2 * s1 * u2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    nlinarith [hfr i]
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [nsq, frobH]
  ring

/-- **The conditional variance bound**, Poincaré route. -/
theorem varBound2 (n : ℕ) (hn : 1 ≤ n) (CF K1 s1 K2 s2 : ℝ) (hCF : 0 ≤ CF) (hs1 : 0 ≤ s1)
    (hK1 : K1 ≤ s1 ^ 2) (hs2 : 0 ≤ s2) (hK2 : K2 ≤ s2 ^ 2)
    (hP : PoincareMv) (hF : FeatOp n CF) (hA : AffFourth K1) (hD : Deg2Fourth K2) (hG : GaussLin)
    (hkap : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → kap x x ≤ 2) :
    VarBound n (4 * CF * s1 * s2) := by
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
      s2 * s1 * (nsq a + 8 * frobH H) * ∫ W, VG a H W ∂stdGauss (WIdx n) := by
    rw [← swap_Q2 hn a H, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => int_G hn a H i)
      ((int_Q2 hn a H).const_mul _) ?_
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact pointwise_le2 hn K1 s1 K2 s2 hs1 hK1 hs2 hK2 hA hD hG a H x (hkap x hx)
  have h4 : 0 ≤ 4 * (CF / (n : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left step2 h4).trans (le_of_eq ?_)
  ring

end BstLean.Part78

#print axioms BstLean.Part78.varBound2
