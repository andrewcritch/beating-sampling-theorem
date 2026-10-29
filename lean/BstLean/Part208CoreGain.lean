import BstLean.Part208CoreRow
import BstLean.Part208PairRows

/-! Part 208: the integrated tangential gain under the actual Gaussian input distribution. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)
open BstLean.Part182

noncomputable def fullPairFactor {Y : Type*} {n : ℕ} (w : Y → ℝ)
    (f : Y → Fin n → ℝ) (H : Set (Y × Y)) (p : Y × Y) : ℝ :=
  H.indicator (fun p => √(w p.2) * nrm (f p.1)) p

noncomputable def tangentPairFactor {Y : Type*} {n : ℕ} (w : Y → ℝ)
    (X f : Y → Fin n → ℝ) (H : Set (Y × Y)) (p : Y × Y) : ℝ :=
  H.indicator (fun p => √(w p.2) * |eTan (X p.1) (X p.2) ⬝ᵥ f p.1|) p

lemma fullPairFactor_sq {Y : Type*} {n : ℕ} (w : Y → ℝ)
    (f : Y → Fin n → ℝ) (H : Set (Y × Y)) (hw : ∀ y, 0 ≤ w y) (p : Y × Y) :
    fullPairFactor w f H p ^ 2 = H.indicator (fun p => w p.2 * normSq (f p.1)) p := by
  by_cases hp : p ∈ H
  · simp only [fullPairFactor, indicator_of_mem hp, mul_pow, sq_sqrt (hw _), nrm_sq]
  · simp [fullPairFactor, indicator_of_notMem hp]

lemma tangentPairFactor_sq {Y : Type*} {n : ℕ} (w : Y → ℝ)
    (X f : Y → Fin n → ℝ) (H : Set (Y × Y)) (hw : ∀ y, 0 ≤ w y) (p : Y × Y) :
    tangentPairFactor w X f H p ^ 2 =
      H.indicator (fun p => w p.2 * (eTan (X p.1) (X p.2) ⬝ᵥ f p.1) ^ 2) p := by
  by_cases hp : p ∈ H
  · simp only [tangentPairFactor, indicator_of_mem hp, mul_pow, sq_sqrt (hw _), sq_abs]
  · simp [tangentPairFactor, indicator_of_notMem hp]

/-- The actual core row estimate supplies the integrated mode coefficient.
All factors use the same pair set and the same Gaussian input distribution.
For a symmetric pair set the swapped factors carry its same indicator. -/
theorem omega_integrated_gain {d : ℕ} (hd : 3 ≤ d) (u : Fin (d + 1) → ℝ)
    (hu : normSq u = 1) {a τ t0 z0 cp sm : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (ht : 0 ≤ t0)
    (hR : 0 < axialRadiusLower (d + 1) a τ t0 z0) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (f : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℝ) (hfm : Measurable f)
    (hFi : Integrable (fun ξ => normSq (f ξ)) (stdGauss (Fin (d + 1))))
    (hft : ∀ ξ, sphPt (a • u + τ • ξ) ⬝ᵥ f ξ = 0)
    (hsm : ∀ ξ ∈ OmegaS (a • u) t0 z0, sm ≤ (u ⬝ᵥ sphPt (a • u + τ • ξ)) ^ 2)
    (H : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))) (hHm : MeasurableSet H)
    (hHΩ : H ⊆ OmegaS (a • u) t0 z0 ×ˢ OmegaS (a • u) t0 z0)
    (hc : ∀ p ∈ H, (sphPt (a • u + τ • p.1) ⬝ᵥ sphPt (a • u + τ • p.2)) ^ 2 ≤ cp ^ 2)
    {kE ko ks : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks) :
    let μ := stdGauss (Fin (d + 1))
    let X := fun ξ : Fin (d + 1) → ℝ => sphPt (a • u + τ • ξ)
    let A := fullPairFactor (wN (a • u) τ) f H
    let C := tangentPairFactor (wN (a • u) τ) X f H
    let χ := (axialPlaneUpper (d + 1) a τ t0 z0 * (1 - sm) + 1 / (d : ℝ)) / (1 - cp ^ 2)
    kE * (∫ p, A p * A p.swap ∂μ.prod μ) +
      ko * ((∫ p, C p * A p.swap ∂μ.prod μ) + ∫ p, A p * C p.swap ∂μ.prod μ) +
      ks * (∫ p, C p * C p.swap ∂μ.prod μ) ≤
      ((∫ ξ, wN (a • u) τ ξ ∂μ) * ∫ ξ, normSq (f ξ) ∂μ) *
        (kE + 2 * ko * √χ + ks * χ) := by
  dsimp only
  let μ := stdGauss (Fin (d + 1))
  let X := fun ξ : Fin (d + 1) → ℝ => sphPt (a • u + τ • ξ)
  let w := wN (a • u) τ
  let χ := (axialPlaneUpper (d + 1) a τ t0 z0 * (1 - sm) + 1 / (d : ℝ)) / (1 - cp ^ 2)
  have hXm : Measurable X := measurable_sphPt.comp (by fun_prop)
  have hwm : Measurable w := measurable_wN _ _
  have hw : ∀ ξ, 0 ≤ w ξ := wN_nonneg _ _
  have hwi : Integrable w μ := integrable_wN (by omega) _ hτ
  have hχ : 0 ≤ χ := by
    apply div_nonneg
    · exact add_nonneg
        (mul_nonneg (div_nonneg (sq_nonneg _) hR.le) (sub_nonneg.mpr hsm1))
        (div_nonneg zero_le_one (Nat.cast_nonneg d))
    · linarith
  have hden : 0 < 1 - cp ^ 2 := by linarith
  have hAm : Measurable (fullPairFactor w f H) := by
    apply Measurable.indicator _ hHm
    apply (hwm.comp measurable_snd).sqrt.mul
    unfold nrm normSq
    fun_prop
  have hCm : Measurable (tangentPairFactor w X f H) := by
    apply Measurable.indicator _ hHm
    apply (hwm.comp measurable_snd).sqrt.mul
    unfold eTan dotProduct
    fun_prop
  have hfull : ∀ p, fullPairFactor w f H p ^ 2 ≤ normSq (f p.1) * w p.2 := by
    intro p
    rw [fullPairFactor_sq w f H hw]
    by_cases hp : p ∈ H
    · rw [indicator_of_mem hp]; exact le_of_eq (mul_comm _ _)
    · rw [indicator_of_notMem hp]; exact mul_nonneg (normSq_nonneg _) (hw _)
  have htan : ∀ p, tangentPairFactor w X f H p ^ 2 ≤
      (normSq (f p.1) * w p.2) / (1 - cp ^ 2) := by
    intro p
    rw [tangentPairFactor_sq w X f H hw]
    by_cases hp : p ∈ H
    · rw [indicator_of_mem hp]
      have hdot := pow_le_pow_left₀ (abs_nonneg _) (abs_dot_le_nrm (X p.2) (f p.1)) 2
      rw [sq_abs, mul_pow, nrm_sq, nrm_sq, normSq_sphPt (by omega), one_mul] at hdot
      have he := (tangent_pair_sq (hft p.1) hcp (hc p hp)).trans
        (div_le_div_of_nonneg_right hdot hden.le)
      have h := mul_le_mul_of_nonneg_left he (hw p.2)
      convert h using 1 <;> ring
    · rw [indicator_of_notMem hp]
      exact div_nonneg (mul_nonneg (normSq_nonneg _) (hw _)) hden.le
  have hAi : Integrable (fun p => fullPairFactor w f H p ^ 2) (μ.prod μ) := by
    apply Integrable.mono' (hFi.mul_prod hwi) (hAm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hfull p
  have hCi : Integrable (fun p => tangentPairFactor w X f H p ^ 2) (μ.prod μ) := by
    apply Integrable.mono' ((hFi.mul_prod hwi).div_const (1 - cp ^ 2))
      (hCm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact htan p
  apply integrated_modes_of_rows μ (fullPairFactor w f H) (tangentPairFactor w X f H)
    (fun ξ => normSq (f ξ)) hAm hCm hAi hCi hFi (fun ξ => normSq_nonneg _)
    (integral_nonneg hw) hχ hkE hko hks
  · intro ξ
    have h := integral_mono_of_nonneg (ae_of_all _ fun ξ' => sq_nonneg _)
      (hwi.const_mul (normSq (f ξ))) (ae_of_all _ fun ξ' => hfull (ξ, ξ'))
    rw [integral_const_mul] at h
    simpa only [mul_comm] using h
  · intro ξ
    let Hξ := {ξ' | (ξ, ξ') ∈ H}
    have hHξ : MeasurableSet Hξ := hHm.preimage (measurable_const.prodMk measurable_id)
    have he : (∫ ξ', tangentPairFactor w X f H (ξ, ξ') ^ 2 ∂μ) =
        ∫ ξ' in Hξ, w ξ' * (eTan (X ξ) (X ξ') ⬝ᵥ f ξ) ^ 2 ∂μ := by
      rw [← integral_indicator hHξ]
      apply integral_congr_ae
      filter_upwards [] with ξ'
      rw [tangentPairFactor_sq w X f H hw]
      by_cases hp : (ξ, ξ') ∈ H
      · simp only [indicator_of_mem hp, indicator_of_mem (show ξ' ∈ Hξ from hp)]
      · simp only [indicator_of_notMem hp, indicator_of_notMem (show ξ' ∉ Hξ from hp)]
    rw [he]
    by_cases hξ : ξ ∈ OmegaS (a • u) t0 z0
    · exact omega_tangent_row hd u (X ξ) (f ξ) hu (normSq_sphPt (by omega) _)
        (hft ξ) ha hτ ht hR hcp (hsm ξ hξ) Hξ hHξ
        (fun ξ' hξ' => (hHΩ hξ').2) (fun ξ' hξ' => hc (ξ, ξ') hξ')
    · have hEmpty : Hξ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro ξ' hξ'
        exact hξ (hHΩ hξ').1
      rw [hEmpty, setIntegral_empty]
      exact mul_nonneg (mul_nonneg (integral_nonneg hw) hχ) (normSq_nonneg _)

end BstLean.Part208
