import BstLean.Part107Defs
import BstLean.Part78Wick

/-!
# Part 107, (P1), step 1: Gaussian moments of `|h|²` and `h·x` for a unit vector `x`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (lin lin2 lin3 lin4 lin2_int lin3_int lin4_int)

variable {n : ℕ}

/-- The `k`-th coordinate vector. -/
noncomputable def eC (k : Fin n) : Fin n → ℝ := Pi.single k 1

lemma lin_eC (k : Fin n) (h : Fin n → ℝ) : lin (eC k) h = h k := by
  simp [lin, eC, Pi.single_apply]

lemma dot_eC (k l : Fin n) : BstLean.Part78.dot (eC k) (eC l) = if k = l then 1 else 0 := by
  simp [BstLean.Part78.dot, eC, Pi.single_apply, eq_comm]

lemma dot_eC_x (k : Fin n) (x : Fin n → ℝ) : BstLean.Part78.dot (eC k) x = x k := by
  simp [BstLean.Part78.dot, eC, Pi.single_apply]

lemma dot_x_eC (k : Fin n) (x : Fin n → ℝ) : BstLean.Part78.dot x (eC k) = x k := by
  simp [BstLean.Part78.dot, eC, Pi.single_apply]

/-- `|h|²`. -/
def Hs (h : Fin n → ℝ) : ℝ := ∑ i, h i ^ 2

lemma Hs_eq (h : Fin n → ℝ) : Hs h = ∑ k, lin (eC k) h * lin (eC k) h := by
  unfold Hs
  exact Finset.sum_congr rfl fun k _ => by rw [lin_eC]; ring

section
variable (x : Fin n → ℝ)

lemma iH : Integrable (fun h : Fin n → ℝ => Hs h) (stdGauss (Fin n)) := by
  simp_rw [Hs_eq]
  exact integrable_finsetSum _ fun k _ => lin2_int _ _

lemma mH : ∫ h : Fin n → ℝ, Hs h ∂stdGauss (Fin n) = n := by
  simp_rw [Hs_eq]
  rw [integral_finsetSum _ fun k _ => lin2_int _ _]
  simp [lin2, dot_eC]

lemma iX2 : Integrable (fun h : Fin n → ℝ => lin x h ^ 2) (stdGauss (Fin n)) := by
  simpa [pow_two] using lin2_int x x

lemma mX2 (hx : ∑ i, x i ^ 2 = 1) : ∫ h : Fin n → ℝ, lin x h ^ 2 ∂stdGauss (Fin n) = 1 := by
  simp_rw [pow_two (lin x _)]
  rw [lin2, ← hx]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma iX3 : Integrable (fun h : Fin n → ℝ => lin x h ^ 3) (stdGauss (Fin n)) := by
  have := lin3_int x x x
  refine this.congr (Filter.Eventually.of_forall fun h => ?_)
  simp only; ring

lemma mX3 : ∫ h : Fin n → ℝ, lin x h ^ 3 ∂stdGauss (Fin n) = 0 := by
  rw [← lin3 x x x]
  exact integral_congr_ae (Filter.Eventually.of_forall fun h => by simp only; ring)

lemma HX_eq (h : Fin n → ℝ) :
    Hs h * lin x h = ∑ k, lin (eC k) h * lin (eC k) h * lin x h := by
  rw [Hs_eq, Finset.sum_mul]

lemma iHX : Integrable (fun h : Fin n → ℝ => Hs h * lin x h) (stdGauss (Fin n)) := by
  simp_rw [HX_eq]
  exact integrable_finsetSum _ fun k _ => lin3_int _ _ _

lemma mHX : ∫ h : Fin n → ℝ, Hs h * lin x h ∂stdGauss (Fin n) = 0 := by
  simp_rw [HX_eq]
  rw [integral_finsetSum _ fun k _ => lin3_int _ _ _]
  simp [lin3]

lemma HX2_eq (h : Fin n → ℝ) :
    Hs h * lin x h ^ 2 = ∑ k, lin (eC k) h * lin (eC k) h * lin x h * lin x h := by
  rw [Hs_eq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma iHX2 : Integrable (fun h : Fin n → ℝ => Hs h * lin x h ^ 2) (stdGauss (Fin n)) := by
  simp_rw [HX2_eq]
  exact integrable_finsetSum _ fun k _ => lin4_int _ _ _ _

lemma mHX2 (hx : ∑ i, x i ^ 2 = 1) :
    ∫ h : Fin n → ℝ, Hs h * lin x h ^ 2 ∂stdGauss (Fin n) = (n : ℝ) + 2 := by
  simp_rw [HX2_eq]
  rw [integral_finsetSum _ fun k _ => lin4_int _ _ _ _]
  have hxx : BstLean.Part78.dot x x = 1 := by
    rw [← hx]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [lin4, dot_eC, dot_eC_x, hxx]
  simp only [ite_true, one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : ∑ k, x k * x k = 1 := by
    rw [← hx]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  ring

lemma H2_eq (h : Fin n → ℝ) :
    Hs h ^ 2 = ∑ k, ∑ l, lin (eC k) h * lin (eC k) h * lin (eC l) h * lin (eC l) h := by
  rw [pow_two, Hs_eq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma iH2 : Integrable (fun h : Fin n → ℝ => Hs h ^ 2) (stdGauss (Fin n)) := by
  simp_rw [H2_eq]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => lin4_int _ _ _ _

lemma mH2 : ∫ h : Fin n → ℝ, Hs h ^ 2 ∂stdGauss (Fin n) = (n : ℝ) * ((n : ℝ) + 2) := by
  simp_rw [H2_eq]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => lin4_int _ _ _ _]
  simp_rw [integral_finsetSum _ fun l _ => lin4_int _ _ _ _, lin4, dot_eC]
  simp only [ite_true, one_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ]
  ring

end

/-- The lower bound of `1 − a²` as a function of `h`, for `g = ρ x`. -/
noncomputable def lowF (n : ℕ) (x : Fin n → ℝ) (r s ρ : ℝ) (h : Fin n → ℝ) : ℝ :=
  1 - s ^ 2 * (Hs h - lin x h ^ 2) *
    (2 / (n : ℝ) - (r ^ 2 * ρ ^ 2 + 2 * r * s * ρ * lin x h + s ^ 2 * Hs h) / (n : ℝ) ^ 2)

lemma lowF_eq (x : Fin n → ℝ) (r s ρ : ℝ) (h : Fin n → ℝ) :
    lowF n x r s ρ h = 1 + ((-(2 * s ^ 2 / n) + s ^ 2 / n ^ 2 * (r ^ 2 * ρ ^ 2)) * Hs h +
      ((2 * s ^ 2 / n - s ^ 2 / n ^ 2 * (r ^ 2 * ρ ^ 2)) * lin x h ^ 2 +
      (s ^ 2 / n ^ 2 * s ^ 2 * Hs h ^ 2 +
      (-(s ^ 2 / n ^ 2 * s ^ 2) * (Hs h * lin x h ^ 2) +
      (s ^ 2 / n ^ 2 * (2 * r * s * ρ) * (Hs h * lin x h) +
      -(s ^ 2 / n ^ 2 * (2 * r * s * ρ)) * lin x h ^ 3))))) := by
  unfold lowF
  ring

lemma lowF_integrable (x : Fin n → ℝ) (r s ρ : ℝ) :
    Integrable (lowF n x r s ρ) (stdGauss (Fin n)) := by
  have : lowF n x r s ρ = fun h => _ := funext (lowF_eq x r s ρ)
  rw [this]
  exact (integrable_const _).add ((iH.const_mul _).add (((iX2 x).const_mul _).add
    ((iH2.const_mul _).add (((iHX2 x).const_mul _).add (((iHX x).const_mul _).add
      ((iX3 x).const_mul _))))))

lemma lowF_integral (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (r s ρ : ℝ) :
    ∫ h, lowF n x r s ρ h ∂stdGauss (Fin n) =
      1 - 2 * s ^ 2 * ((n : ℝ) - 1) / n +
        s ^ 2 / (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (r ^ 2 * ρ ^ 2 + s ^ 2 * ((n : ℝ) + 2)) := by
  have : lowF n x r s ρ = fun h => _ := funext (lowF_eq x r s ρ)
  rw [this]
  have i1 := (iH (n := n)).const_mul (-(2 * s ^ 2 / n) + s ^ 2 / n ^ 2 * (r ^ 2 * ρ ^ 2))
  have i2 := (iX2 x).const_mul (2 * s ^ 2 / n - s ^ 2 / n ^ 2 * (r ^ 2 * ρ ^ 2))
  have i3 := (iH2 (n := n)).const_mul (s ^ 2 / n ^ 2 * s ^ 2)
  have i4 := (iHX2 x).const_mul (-(s ^ 2 / n ^ 2 * s ^ 2))
  have i5 := (iHX x).const_mul (s ^ 2 / n ^ 2 * (2 * r * s * ρ))
  have i6 := (iX3 x).const_mul (-(s ^ 2 / n ^ 2 * (2 * r * s * ρ)))
  have j5 := i5.add i6
  have e5 := integral_add i5 i6
  have j4 := i4.add j5
  have e4 := integral_add i4 j5
  have j3 := i3.add j4
  have e3 := integral_add i3 j4
  have j2 := i2.add j3
  have e2 := integral_add i2 j3
  have j1 := i1.add j2
  have e1 := integral_add i1 j2
  have e0 := integral_add (integrable_const (μ := stdGauss (Fin n)) (1 : ℝ)) j1
  simp only [Pi.add_apply] at e0 e1 e2 e3 e4 e5
  beta_reduce
  rw [e0, e1, e2, e3, e4, e5]
  simp only [integral_const_mul, mH, mX2 x hx, mH2, mHX2 x hx, mHX, mX3]
  simp
  ring

end BstLean.Part107
