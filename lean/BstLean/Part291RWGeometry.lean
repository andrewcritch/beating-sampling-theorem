import BstLean.Part291RWRows

/-! The dependent row estimate is applied after restricting the pair overlap.
Only the constant part of the reciprocal weight uses the axial row theorem. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part182 BstLean.Part208
open BstLean.Part153 (nrm nrm_sq abs_dot_le_nrm)
open BstLean.Part188

theorem rw_tangent_row {k : ℕ} (hk : 5 ≤ k) (u x v : Fin (k + 1) → ℝ)
    (hu : normSq u = 1) (hx : normSq x = 1) (hv : x ⬝ᵥ v = 0)
    {r τ t z cp sm : ℝ} (hr : 0 < r) (hτ : 0 < τ) (ht : 0 ≤ t)
    (hRad : 0 < axialRadiusLower (k + 1) r τ t z)
    (hcp : cp ^ 2 < 1) (hsm : sm ≤ (u ⬝ᵥ x) ^ 2)
    (H : Set (Fin (k + 1) → ℝ)) (hHm : MeasurableSet H)
    (hHΩ : H ⊆ OmegaS (r • u) t z)
    (hc : ∀ ξ ∈ H, (x ⬝ᵥ sphPt (r • u + τ • ξ)) ^ 2 ≤ cp ^ 2)
    (f : (Fin (k + 1) → ℝ) → ℝ) (hfm : Measurable f)
    {a d m s K R : ℝ} (hd : 0 < d) (hY : d < a - m ^ 2)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hR : 0 ≤ R) (hfK : ∀ ξ, |f ξ| ≤ K)
    (hw2 : (∫ ξ, wN (r • u) τ ξ ^ 2 ∂stdGauss (Fin (k + 1))) ≤ R ^ 2)
    (hD : RWDeficitMoments (stdGauss (Fin (k + 1))) f m s) :
    (∫ ξ in H, weightSq a d (f ξ) * wN (r • u) τ ξ *
      (eTan x (sphPt (r • u + τ • ξ)) ⬝ᵥ v) ^ 2 ∂stdGauss (Fin (k + 1))) ≤
      ((∫ ξ, wN (r • u) τ ξ ∂stdGauss (Fin (k + 1))) *
        ((axialPlaneUpper (k + 1) r τ t z * (1 - sm) + 1 / (k : ℝ)) /
          (1 - cp ^ 2)) / (a - m ^ 2) +
        rwDelta a d m s * R / (1 - cp ^ 2)) * normSq v := by
  haveI : IsProbabilityMeasure (stdGauss (Fin (k + 1))) := by unfold stdGauss; infer_instance
  let X := fun ξ : Fin (k + 1) → ℝ => sphPt (r • u + τ • ξ)
  let g := H.indicator (fun ξ => (eTan x (X ξ) ⬝ᵥ v) ^ 2)
  have hden : 0 < 1 - cp ^ 2 := by linarith
  have hXm : Measurable X := measurable_sphPt.comp (by fun_prop)
  have hgm : Measurable g := by
    apply Measurable.indicator _ hHm
    unfold eTan dotProduct
    fun_prop
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun _ => indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hgB : ∀ ξ, g ξ ≤ normSq v / (1 - cp ^ 2) := by
    intro ξ
    by_cases hξ : ξ ∈ H
    · change H.indicator (fun ξ => (eTan x (X ξ) ⬝ᵥ v) ^ 2) ξ ≤ _
      rw [indicator_of_mem hξ]
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_dot_le_nrm (X ξ) v) 2
      rw [sq_abs, mul_pow, nrm_sq, nrm_sq, normSq_sphPt (by omega), one_mul] at h
      exact (tangent_pair_sq hv hcp (hc ξ hξ)).trans (div_le_div_of_nonneg_right h hden.le)
    · change H.indicator (fun ξ => (eTan x (X ξ) ⬝ᵥ v) ^ 2) ξ ≤ _
      rw [indicator_of_notMem hξ]
      exact div_nonneg (normSq_nonneg v) hden.le
  have he (ξ : Fin (k + 1) → ℝ) : wN (r • u) τ ξ * g ξ =
      H.indicator (fun ξ => wN (r • u) τ ξ * (eTan x (X ξ) ⬝ᵥ v) ^ 2) ξ := by
    by_cases hξ : ξ ∈ H <;> simp [g, hξ]
  have hrow := omega_tangent_row (by omega) u x v hu hx hv hr hτ ht hRad hcp hsm H hHm hHΩ hc
  have heI : (∫ ξ, wN (r • u) τ ξ * g ξ ∂stdGauss (Fin (k + 1))) =
      ∫ ξ in H, wN (r • u) τ ξ * (eTan x (X ξ) ⬝ᵥ v) ^ 2 ∂stdGauss (Fin (k + 1)) := by
    rw [← integral_indicator hHm]
    exact integral_congr_ae (ae_of_all _ he)
  have hrow' := heI.trans_le hrow
  have h := rw_row_of_bounds (stdGauss (Fin (k + 1))) f (wN (r • u) τ) g
    hfm (measurable_wN _ _) hgm hd hY hm hs hR (div_nonneg (normSq_nonneg _) hden.le)
    hfK (wN_nonneg _ _) hg0 hgB (integrable_wN (by omega) _ hτ)
    (integrable_wN2 (by omega) _ hτ) hrow' hw2 hD
  have heq : (∫ ξ, weightSq a d (f ξ) * (wN (r • u) τ ξ * g ξ)
      ∂stdGauss (Fin (k + 1))) =
      ∫ ξ in H, weightSq a d (f ξ) * wN (r • u) τ ξ *
        (eTan x (X ξ) ⬝ᵥ v) ^ 2 ∂stdGauss (Fin (k + 1)) := by
    rw [← integral_indicator hHm]
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      by_cases hξ : ξ ∈ H <;> simp [g, hξ, mul_assoc]
  rw [heq] at h
  convert h using 1 <;> ring

end BstLean.BlueprintLow
