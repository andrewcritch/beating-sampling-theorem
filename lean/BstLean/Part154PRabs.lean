import BstLean.Part154PR
import BstLean.Part154K0
import BstLean.Part154App

/-!
# Part 154: Lemma PR in the forms of the paper

Paper source: `proofs/option-n/theorem5-06-centre.tex`, Lemma PR.

* `PRvecAbs_of`: Lemma PR (i) in absolute-value form for two linear forms `⟨z, g⟩`, `⟨z, g′⟩` of
  one standard Gaussian vector, with every constant `K ≥ sup U`.
* `PRvecAbs_K0`, `PRvec_K0`: the same with the constant `K₀ = (π − 2)/(4π)`.
* `PR_i`: Lemma PR (i), scalar form, with the constant `K₀`.
* `kappa_chord`: Lemma PR (ii), `κ(r) ≤ 1/π + (1 − 1/π)r` on `[0, 1]`.
* `PR_ii`: Lemma PR (ii) for two vectors of equal norm and nonnegative inner product.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part137 BstLean.Part153
open BstLean.Part105 (gaussLin105)

/-- `√U(v)·√U(v′) ≤ K` if `U ≤ K`. -/
private lemma sqrtU_le {K : ℝ} (hK : ∀ a, Ures a ≤ K) (v v' : ℝ) :
    √(Ures v) * √(Ures v') ≤ K := by
  have hK0 : 0 ≤ K := (Ures_nonneg 0).trans (hK 0)
  calc √(Ures v) * √(Ures v') ≤ √K * √K :=
        mul_le_mul (Real.sqrt_le_sqrt (hK _)) (Real.sqrt_le_sqrt (hK _)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = K := Real.mul_self_sqrt hK0

/-- **Lemma PR (i), absolute-value form, for two linear forms** of one standard Gaussian vector,
with every constant `K ≥ sup U`. -/
theorem PRvecAbs_of {K : ℝ} (hK : ∀ a, Ures a ≤ K) : PRvecAbs K := by
  intro m g g' a a'
  set σ := nrm g with hσd
  set σ' := nrm g' with hσd'
  set ρ := (g ⬝ᵥ g') / (σ * σ') with hρd
  have hσ0 : 0 ≤ σ := nrm_nonneg g
  have hσ0' : 0 ≤ σ' := nrm_nonneg g'
  have s1 : ∑ x, g x * g x = σ ^ 2 := by
    rw [hσd, nrm_sq]; unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
  have s4 : ∑ x, g' x * g' x = σ' ^ 2 := by
    rw [hσd', nrm_sq]; unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
  have hCS : (g ⬝ᵥ g') ^ 2 ≤ (σ * σ') ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g g'
    rw [mul_pow, hσd, hσd', nrm_sq, nrm_sq]
    exact this
  have hdot : σ * σ' * ρ = g ⬝ᵥ g' := by
    by_cases h0 : σ * σ' = 0
    · rw [h0, zero_pow two_ne_zero] at hCS
      have : g ⬝ᵥ g' = 0 := by nlinarith [sq_nonneg (g ⬝ᵥ g')]
      rw [this, h0, zero_mul]
    · rw [hρd, mul_div_assoc']; exact mul_div_cancel_left₀ _ h0
  have hρ2 : ρ ^ 2 ≤ 1 := by
    by_cases h0 : σ * σ' = 0
    · rw [hρd, h0, div_zero]; norm_num
    · rw [hρd, div_pow, div_le_one (by positivity)]; exact hCS
  have hρ : |ρ| ≤ 1 := (sq_le_one_iff_abs_le_one ρ).mp hρ2
  have hsq : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have s2 : ∑ x, g x * g' x = σ * σ' * ρ := by rw [hdot]; rfl
  have s3 : ∑ x, g' x * g x = σ * σ' * ρ := by
    rw [← s2]; exact Finset.sum_congr rfl fun i _ => by ring
  have law : ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) =
      ∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    let A : Matrix (Fin 2) (Fin m) ℝ := Matrix.of ![g, g']
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![σ, 0; σ' * ρ, σ' * √(1 - ρ ^ 2)]
    have hAB : A * A.transpose = B * B.transpose := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, s1, s2, s3, s4] <;> nlinarith
    have hl := gaussLin105 (Fin m) (Fin 2) (Fin 2) A B hAB
    let H : (Fin 2 → ℝ) → ℝ := fun y => relu (a + y 0) * relu (a' + y 1)
    have hH : Measurable H :=
      (measurable_relu.comp (measurable_const.add (measurable_pi_apply 0))).mul
        (measurable_relu.comp (measurable_const.add (measurable_pi_apply 1)))
    let G : ℝ × ℝ → ℝ := fun p =>
      relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
    have e1 : ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) =
        ∫ z, H (A.mulVec z) ∂stdGauss (Fin m) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp [H, A, dotProduct_comm]
    have e2 : ∫ z, H (A.mulVec z) ∂stdGauss (Fin m) =
        ∫ η, H (B.mulVec η) ∂stdGauss (Fin 2) := by
      rw [← integral_map (φ := fun ξ => A.mulVec ξ) (by fun_prop) hH.aestronglyMeasurable, hl,
        integral_map (φ := fun ξ => B.mulVec ξ) (by fun_prop) hH.aestronglyMeasurable]
    have e3 : ∫ η, H (B.mulVec η) ∂stdGauss (Fin 2) =
        ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' G
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun η => ?_)
      show H (B.mulVec η) = G (η 0, η 1)
      have b0 : B.mulVec η 0 = σ * η 0 := by
        simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have b1 : B.mulVec η 1 = σ' * (ρ * η 0 + √(1 - ρ ^ 2) * η 1) := by
        simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      show relu (a + B.mulVec η 0) * relu (a' + B.mulVec η 1) = _
      rw [b0, b1]
    rw [e1, e2, e3]
  rw [law]
  rcases (mul_nonneg hσ0 hσ0').eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := by rw [hρd, ← h0, div_zero]
    have hd0 : g ⬝ᵥ g' = 0 := by rw [← hdot, hρ0, mul_zero]
    have e : ∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = psiS σ a * psiS σ' a' := by
      rw [hρ0]
      simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero, Real.sqrt_one, one_mul]
      exact integral_prod_mul (fun z => relu (a + σ * z)) (fun z => relu (a' + σ' * z))
    rw [e, hd0]
    simp
  · have hσ : 0 < σ := by
      rcases hσ0.eq_or_lt with h | h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hσ' : 0 < σ' := by
      rcases hσ0'.eq_or_lt with h | h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have h := PR_scalar hρ a a' hσ hσ'
    have hU := sqrtU_le hK (a / σ) (a' / σ')
    have e : K * (g ⬝ᵥ g') ^ 2 / (σ * σ') = ρ ^ 2 * σ * σ' * K := by
      rw [← hdot]; field_simp
    have e2 : (g ⬝ᵥ g') * PhiG (a / σ) * PhiG (a' / σ') =
        ρ * σ * σ' * PhiG (a / σ) * PhiG (a' / σ') := by
      rw [← hdot]; ring
    rw [e, e2]
    refine h.trans ?_
    calc ρ ^ 2 * σ * σ' * √(Ures (a / σ)) * √(Ures (a' / σ'))
        = ρ ^ 2 * σ * σ' * (√(Ures (a / σ)) * √(Ures (a' / σ'))) := by ring
      _ ≤ ρ ^ 2 * σ * σ' * K := mul_le_mul_of_nonneg_left hU (by positivity)

/-- Lemma PR (i), absolute-value form, with the constant `K₀`. -/
theorem PRvecAbs_K0 : PRvecAbs K0 := PRvecAbs_of Ures_le_K0

/-- Lemma PR (i), upper bound, with the constant `K₀`. -/
theorem PRvec_K0 : PRvecBound K0 := PRvec_of Ures_le_K0

/-- Lemma PR (i) of the paper, scalar form with the constant K₀: for |ρ| ≤ 1, σ, σ′ > 0:
|Cov(relu(a + σZ), relu(a′ + σ′Z′)) − ρσσ′Φ(a/σ)Φ(a′/σ′)| ≤ K₀ρ²σσ′ -/
theorem PR_i {ρ : ℝ} (hρ : |ρ| ≤ 1) (a a' : ℝ) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') :
    |∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) -
        psiS σ a * psiS σ' a' - ρ * σ * σ' * PhiG (a / σ) * PhiG (a' / σ')| ≤
      K0 * ρ ^ 2 * σ * σ' := by
  refine (PR_scalar hρ a a' hσ hσ').trans ?_
  have hU := sqrtU_le Ures_le_K0 (a / σ) (a' / σ')
  calc ρ ^ 2 * σ * σ' * √(Ures (a / σ)) * √(Ures (a' / σ'))
      = ρ ^ 2 * σ * σ' * (√(Ures (a / σ)) * √(Ures (a' / σ'))) := by ring
    _ ≤ ρ ^ 2 * σ * σ' * K0 := mul_le_mul_of_nonneg_left hU (by positivity)
    _ = K0 * ρ ^ 2 * σ * σ' := by ring

/-- Lemma PR (ii): the chord of κ. -/
theorem kappa_chord {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    BstLean.Part130.kappa r ≤ 1 / π + (1 - 1 / π) * r := by
  have h := kappa_convexOn.2 (x := 0) (y := 1) (by constructor <;> norm_num)
    (by constructor <;> norm_num) (sub_nonneg.mpr h1) h0 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, kappa_zero, kappa_one] at h
  linarith

/-- **Lemma PR (ii) for two vectors** `h`, `h′` of `ℝ^k` with `|h|² = |h′|² = v > 0` and
`⟨h, h′⟩ ≥ 0`: `E[relu⟨z, h⟩·relu⟨z, h′⟩] ≤ v/(2π) + (1/2 − 1/(2π))⟨h, h′⟩`. -/
theorem PR_ii {k : ℕ} (h h' : Fin k → ℝ) {v : ℝ} (hv : 0 < v) (hh : normSq h = v)
    (hh' : normSq h' = v) (hd : 0 ≤ h ⬝ᵥ h') :
    ∫ z, relu (z ⬝ᵥ h) * relu (z ⬝ᵥ h') ∂stdGauss (Fin k) ≤
      v * (1 / (2 * π)) + (1 / 2 - 1 / (2 * π)) * (h ⬝ᵥ h') := by
  have hr := row_formula_std h h'
  have hcs := BstLean.Part130.abs_dot_le h h'
  rw [hh, hh', Real.mul_self_sqrt hv.le] at hr hcs
  change 2 * ∫ z, relu (z ⬝ᵥ h) * relu (z ⬝ᵥ h') ∂stdGauss (Fin k) =
    v * kappa ((h ⬝ᵥ h') / v) at hr
  have hcs' : h ⬝ᵥ h' ≤ v := (le_abs_self _).trans hcs
  have hc := kappa_chord (div_nonneg hd hv.le) ((div_le_one hv).mpr hcs')
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have e : v * (1 / π + (1 - 1 / π) * ((h ⬝ᵥ h') / v)) =
      v * (1 / π) + (1 - 1 / π) * (h ⬝ᵥ h') := by field_simp
  have h3 := mul_le_mul_of_nonneg_left hc hv.le
  rw [e] at h3
  have e4 : v * (1 / (2 * π)) + (1 / 2 - 1 / (2 * π)) * (h ⬝ᵥ h') =
      (v * (1 / π) + (1 - 1 / π) * (h ⬝ᵥ h')) / 2 := by field_simp
  rw [e4]
  linarith

end BstLean.Part154
