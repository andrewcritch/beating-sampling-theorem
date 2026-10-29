import BstLean.Part53Defs
import BstLean.Part48Defs
import BstLean.Part41Error

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (DD)
open BstLean.Part48 (SBLevel)

lemma dimension_ratio (n d k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 2 * d + 1) :
    (n : ℝ) ^ (k / 2) / DD n d ≤ (d.factorial : ℝ) / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hfac : (0 : ℝ) < d.factorial := by positivity
  have hb := Nat.pow_le_choose (α := ℝ) d (n + d)
  have he : n + d + 1 - d = n + 1 := by omega
  rw [he] at hb
  have hp : (n : ℝ) ^ d ≤ ((n + 1 : ℕ) : ℝ) ^ d :=
    pow_le_pow_left₀ hn0.le (by norm_cast; omega) d
  have hchoose : (n : ℝ) ^ d ≤ ((n + d).choose d : ℝ) * d.factorial := by
    exact hp.trans ((div_le_iff₀ hfac).mp hb)
  have hkd : k / 2 ≤ d := by omega
  apply (div_le_div_iff₀ hD hn0).mpr
  calc
    (n : ℝ) ^ (k / 2) * n ≤ (n : ℝ) ^ d * n :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hnR hkd) hn0.le
    _ ≤ ((n + d).choose d : ℝ) * d.factorial * n :=
      mul_le_mul_of_nonneg_right hchoose hn0.le
    _ = (d.factorial : ℝ) * DD n d := by rw [BstLean.Part36.DD_eq]; ring

/-- A positive small-ball level at degree at least two has a nonnegative probability bound. -/
lemma smallball_probability_nonneg (h : ℕ) (hh : 2 ≤ h) (p t : ℝ)
    (hSB : SBLevel h p t) (ht : 0 < t) : 0 ≤ p := by
  classical
  let P : MvPolynomial Unit ℝ := MvPolynomial.X () ^ 2
  have hdeg : P.totalDegree ≤ h := by
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simp [P]; omega)
  have he (z : Unit → ℝ) : MvPolynomial.eval z P = z () ^ 2 := by simp [P]
  have hm : (∫ z : Unit → ℝ, z () ^ 2 ∂stdGauss Unit) = 1 := by
    have hx := BstLean.Part41.p1_gauss_norm_moment (ι := Unit) 1
    simpa [BstLean.Part36.rhoD, Finset.prod_range_succ, Real.sq_sqrt (sq_nonneg _)] using hx
  have hb := hSB Unit P hdeg (fun z => by rw [he]; exact sq_nonneg _)
  simp_rw [he, hm, mul_one] at hb
  by_contra hp
  have hp' : p ≤ 0 := (lt_of_not_ge hp).le
  rw [ENNReal.ofReal_of_nonpos hp'] at hb
  have hz : stdGauss Unit {z | z () ^ 2 < t} = 0 := le_zero_iff.mp hb
  let S := {x : ℝ | x ^ 2 < t}
  have hS : MeasurableSet S := isOpen_lt (continuous_id.pow 2) continuous_const |>.measurableSet
  have hg : ProbabilityTheory.gaussianReal 0 1 S = 0 := by
    have heval := measurePreserving_eval (fun _ : Unit => ProbabilityTheory.gaussianReal 0 1) ()
    rw [← heval.measure_preimage hS.nullMeasurableSet]
    exact hz
  have hv : volume S = 0 :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num) hg
  have hs : Set.Ioo (-Real.sqrt t) (Real.sqrt t) ⊆ S := by
    intro x hx
    have ht0 := Real.sqrt_pos.mpr ht
    have hsqt := Real.sq_sqrt ht.le
    have hl := hx.1
    have hu := hx.2
    have hprod := mul_pos (sub_pos.mpr hu) (show 0 < Real.sqrt t + x by linarith)
    change x ^ 2 < t
    nlinarith
  have hi := measure_mono_null hs hv
  have hlen : volume (Set.Ioo (-Real.sqrt t) (Real.sqrt t)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by have := Real.sqrt_pos.mpr ht; linarith)).ne'
  exact hlen hi

end BstLean.Part53.T2Aux
