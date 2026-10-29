import BstLean.Part56MC_WickSpan
import BstLean.Part56MC_Laws
import BstLean.Part56MC_Spectral
import BstLean.Part56MC_Chaos
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Prod

namespace BstLean.Part56

open MeasureTheory
open BstLean.Part29 (stdGauss)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable abbrev H := Lp ℝ 2 (stdGauss ι)
private noncomputable abbrev HP := Lp ℝ 2 ((stdGauss ι).prod (stdGauss ι))

private noncomputable def firstLift : H (ι := ι) →L[ℝ] HP (ι := ι) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
    (measurePreserving_fst (μ := stdGauss ι) (ν := stdGauss ι))).toContinuousLinearMap

private noncomputable def mixLift (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    H (ι := ι) →L[ℝ] HP (ι := ι) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun p : (ι → ℝ) × (ι → ℝ) => a • p.1 + b • p.2)
    (mc56_mix_preserving a b hab)).toContinuousLinearMap

noncomputable def mc56_operator (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    H (ι := ι) →L[ℝ] H (ι := ι) :=
  firstLift.adjoint.comp (mixLift a b hab)

theorem mc56_operator_inner (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (F G : H (ι := ι)) :
    inner ℝ F (mc56_operator a b hab G) =
      ∫ g, ∫ h, F g * G (a • g + b • h) ∂stdGauss ι ∂stdGauss ι := by
  rw [mc56_operator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  have hF := Lp.coeFn_compMeasurePreserving F
    (measurePreserving_fst (μ := stdGauss ι) (ν := stdGauss ι))
  have hG := Lp.coeFn_compMeasurePreserving G (mc56_mix_preserving a b hab)
  have hi : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => F p.1 * G (a • p.1 + b • p.2))
      ((stdGauss ι).prod (stdGauss ι)) := by
    apply ((Lp.memLp (firstLift F)).integrable_mul (Lp.memLp (mixLift a b hab G))).congr
    filter_upwards [hF, hG] with p hp hq
    exact congrArg₂ (· * ·) hp hq
  rw [← integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hF, hG] with p hp hq
  change (mixLift a b hab G p) * (firstLift F p) = _
  change firstLift F p = F p.1 at hp
  change mixLift a b hab G p = G (a • p.1 + b • p.2) at hq
  rw [hp, hq]
  exact mul_comm _ _

theorem mc56_operator_polynomial (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (p : MvPolynomial ι ℝ) :
    mc56_operator a b hab (mc56_polynomialToLp p) =
      mc56_polynomialToLp (mc56_noise a b p) := by
  apply ext_inner_left ℝ
  intro F
  rw [mc56_operator_inner, L2.inner_def]
  have hp := (mc56_polynomial_memLp p).coeFn_toLp
  have hq := (mc56_polynomial_memLp (mc56_noise a b p)).coeFn_toLp
  have hpMix := (mc56_mix_preserving a b hab).quasiMeasurePreserving.ae hp
  have he : (∫ g, ∫ h, F g * (mc56_polynomialToLp p) (a • g + b • h)
      ∂stdGauss ι ∂stdGauss ι) =
      ∫ g, ∫ h, F g * MvPolynomial.eval (a • g + b • h) p ∂stdGauss ι ∂stdGauss ι := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hpMix] with g hg
    apply integral_congr_ae
    filter_upwards [hg] with h hh
    exact congrArg (F g * ·) hh
  rw [he]
  simp_rw [integral_const_mul, ← mc56_noise_eval]
  apply integral_congr_ae
  filter_upwards [hq] with g hg
  change mc56_polynomialToLp (mc56_noise a b p) g = _ at hg
  change F g * MvPolynomial.eval g (mc56_noise a b p) =
    (mc56_polynomialToLp (mc56_noise a b p) g) * F g
  rw [hg]
  exact mul_comm _ _

private noncomputable def unitLp : H (ι := ι) := mc56_polynomialToLp 1

private noncomputable def meanProjection : H (ι := ι) →L[ℝ] H (ι := ι) :=
  (innerSL ℝ (unitLp (ι := ι))).smulRight unitLp

noncomputable def mc56_centeredOperator (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    H (ι := ι) →L[ℝ] H (ι := ι) := mc56_operator a b hab - meanProjection

private lemma unit_inner (F : H (ι := ι)) : inner ℝ unitLp F = ∫ x, F x ∂stdGauss ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(mc56_polynomial_memLp (1 : MvPolynomial ι ℝ)).coeFn_toLp] with x hx
  change unitLp x = MvPolynomial.eval x (1 : MvPolynomial ι ℝ) at hx
  change F x * unitLp x = F x
  rw [hx]
  simp

theorem mc56_centeredOperator_inner (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (F G : H (ι := ι)) :
    inner ℝ F (mc56_centeredOperator a b hab G) =
      (∫ g, ∫ h, F g * G (a • g + b • h) ∂stdGauss ι ∂stdGauss ι) -
        (∫ g, F g ∂stdGauss ι) * (∫ g, G g ∂stdGauss ι) := by
  change inner ℝ F (mc56_operator a b hab G - meanProjection G) = _
  rw [inner_sub_right, mc56_operator_inner]
  congr 1
  change inner ℝ F (inner ℝ unitLp G • unitLp) = _
  rw [inner_smul_right, unit_inner, real_inner_comm, unit_inner, mul_comm]

theorem mc56_centeredOperator_word (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (w : List ι) :
    mc56_centeredOperator a b hab (mc56_wordLp w) =
      (if w.length = 0 then 0 else a ^ w.length) • mc56_wordLp w := by
  change mc56_operator a b hab (mc56_polynomialToLp (mc56_wickWord w)) -
    meanProjection (mc56_wordLp w) = _
  rw [mc56_operator_polynomial, mc56_noise_wickWord a b hab, map_smul]
  by_cases hw : w.length = 0
  · have he : w = [] := List.length_eq_zero_iff.mp hw
    subst w
    change (a ^ 0) • (unitLp (ι := ι)) - inner ℝ unitLp unitLp • unitLp = _
    have hn : inner ℝ (unitLp (ι := ι)) unitLp = 1 := by
      rw [unitLp, mc56_polynomial_inner]
      simp
    rw [hn]
    simp
  · have ho : inner ℝ (unitLp (ι := ι)) (mc56_wordLp w) = 0 := by
      change inner ℝ (mc56_polynomialToLp (mc56_wickWord []))
        (mc56_polynomialToLp (mc56_wickWord w)) = 0
      rw [mc56_polynomial_inner]
      exact mc56_wickWord_orthogonal [] w (by simpa using Ne.symm hw)
    change a ^ w.length • mc56_wordLp w - inner ℝ unitLp (mc56_wordLp w) • unitLp = _
    rw [ho]
    simp [hw]

theorem mc56_centeredOperator_bound (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (ha : |a| ≤ 1) (F : H (ι := ι)) :
    ‖mc56_centeredOperator a b hab F‖ ≤ |a| * ‖F‖ := by
  apply mc56_word_diagonal_bound (mc56_centeredOperator a b hab)
    (fun k => if k = 0 then 0 else a ^ k) |a| (abs_nonneg a)
    (mc56_centeredOperator_word a b hab) _ F
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, abs_pow]
    simpa only [pow_one] using pow_le_pow_of_le_one (abs_nonneg a) ha
      (Nat.one_le_iff_ne_zero.mpr hk)

end BstLean.Part56
