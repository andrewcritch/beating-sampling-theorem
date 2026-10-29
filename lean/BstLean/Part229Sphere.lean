import BstLean.Part153S

/-! Differentiability under the Gaussian distribution after radial normalization. -/
namespace BstLean.Part229
open MeasureTheory Filter Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153
open BstLean.Part148 (EuLip)

theorem ae_diff_sphere {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ K : ℝ}
    (hτ : 0 < τ) (hK : 0 ≤ K) {Φ : (Fin n → ℝ) → ℝ} (hΦ : EuLip Φ K) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      DifferentiableAt ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ := by
  have hall : ∀ᵐ ξ ∂stdGauss (Fin n), ∀ j : ℕ,
      DifferentiableAt ℝ (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) ξ := by
    rw [ae_all_iff]
    intro j
    exact (cutF_lip c hτ (epsSeq_pos j) hK hΦ).ae_diff
      (div_nonneg (mul_nonneg hK hτ.le) (epsSeq_pos j).le)
  filter_upwards [hall, ae_normSq_ne hn c hτ.ne'] with ξ hξ hne
  have hpos : 0 < normSq (c + τ • ξ) :=
    lt_of_le_of_ne (normSq_nonneg _) hne.symm
  have ht := epsSeq_tendsto.eventually (gt_mem_nhds (Real.sqrt_pos.mpr hpos))
  obtain ⟨j, hj⟩ := ht.exists
  have he : (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) =ᶠ[𝓝 ξ]
      (fun ξ => Φ (sphPt (c + τ • ξ))) := by
    have hc : Continuous (fun ξ : Fin n → ℝ => Real.sqrt (normSq (c + τ • ξ))) :=
      Real.continuous_sqrt.comp (cont_ns c τ)
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hj)] with ξ' h'
    rw [cut_eq_sphPt (epsSeq_pos j) h'.le]
  exact (hξ j).congr_of_eventuallyEq he.symm

end BstLean.Part229
