import BstLean.Part53Error_Moments

namespace BstLean.Part53

open MeasureTheory
open BstLean.Part41 (Mono phiM phiSq frob)
open BstLean.Part40 (SphLaw)

variable {n d : ℕ}

private lemma phi_zero (x : Fin n → ℝ) : phiM x (default : Mono n d) = 1 := by
  rfl

private lemma phi_cont (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) :=
  continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)

private lemma dens_sph {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (h : DensLaw n μ Λ) :
    SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

/-- The main-term feature tensor estimate, with an explicit constant at every order. -/
theorem error53_feature_tensor {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hμ : DensLaw n μ Λ) (hG : LemmaG53 d) (c : ℕ) :
    frob (fun w : Fin c → Mono n d =>
      (∫ x, ∏ t, phiM x (w t) ∂μ) - ∏ t, if w t = default then (1 : ℝ) else 0) ≤
        (4 * ((d : ℝ) + 1)) ^ c * (Real.exp Λ * cG d / n) := by
  classical
  let e : Mono n d → ℝ := fun p => if p = default then 1 else 0
  let η : ℝ := Real.exp Λ * cG d / n
  have hη : 0 < η := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    dsimp [η, cG]
    positivity
  have he : ∑ p, e p ^ 2 = 1 := by simp [e]
  have hbound : ∀ᵐ x ∂μ, ∑ p : Mono n d, phiM x p ^ 2 ≤ (d : ℝ) + 1 := by
    filter_upwards [(dens_sph hμ).sphere] with x hx
    exact (BstLean.Part43.phiSq_bounds (by omega) x hx).2
  have hop : ∀ a : Mono n d → ℝ,
      ∫ x, (∑ p, a p * (phiM x p - e p)) ^ 2 ∂μ ≤ η * ∑ p, a p ^ 2 := by
    intro a
    let b : Mono n d → ℝ := fun p => if p = default then 0 else a p
    have hb0 : b default = 0 := by simp [b]
    have hsum (x : Fin n → ℝ) :
        (∑ p, a p * (phiM x p - e p)) = ∑ p, b p * phiM x p := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = default
      · subst p
        simp [e, b, phi_zero]
      · simp [e, b, hp]
    simp_rw [hsum]
    have hb : nsq b ≤ ∑ p, a p ^ 2 := by
      unfold nsq
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p = default
      · simp [b, hp, sq_nonneg]
      · simp [b, hp]
    exact (error53_feature_operator hn hμ hG b hb0).trans
      (mul_le_mul_of_nonneg_left hb hη.le)
  exact error53_tensor_mean (dens_sph hμ) (fun p x => phiM x p) phi_cont e he
    η ((d : ℝ) + 1) hη (by have := Nat.cast_nonneg (α := ℝ) d; linarith) hbound hop c

end BstLean.Part53
