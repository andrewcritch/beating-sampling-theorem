import BstLean.Part233Cancellation

/-! The cancellation Lipschitz constant has a factor one half. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part205
open BstLean.Part29 BstLean.Part105 BstLean.Part133
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)

theorem world_row_lipschitz {N m : ℕ} (hN : 1 ≤ N)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (σ : ℝ) :
    BstLean.Part148.EuLip
      (fun ξ => rowMean (fun u => reluV (M₁.mulVec u)) ξ -
        rowSmooth (h1bar M₁) σ ξ)
      ((√(firstQ M₁) + nrm (h1bar M₁)) / 2) := by
  have := uniformSphere_isProbability N hN
  let g := fun u => reluV (M₁.mulVec u)
  have hg : Continuous g := continuous_h1_u M₁
  have hn : Continuous (fun u => nrm (g u)) :=
    (continuous_normSq.comp hg).sqrt
  have inrm := sphere_cont_integrable hN hn
  have insq := sphere_cont_integrable hN (hn.pow 2)
  have havg : (∫ u, nrm (g u) ∂uniformSphere N) ≤ √(firstQ M₁) := by
    have hs := sq_integral_le insq
    have he : (∫ u, nrm (g u) ^ 2 ∂uniformSphere N) = firstQ M₁ := by
      simp only [nrm_sq]; rfl
    rw [he] at hs
    have hQ : 0 ≤ firstQ M₁ := integral_nonneg fun _ => normSq_nonneg _
    nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg (firstQ M₁)]
  intro ξ η
  change |(rowMean (fun u => reluV (M₁.mulVec u)) ξ - rowSmooth (h1bar M₁) σ ξ) -
    (rowMean (fun u => reluV (M₁.mulVec u)) η - rowSmooth (h1bar M₁) σ η)| ≤ _
  have idot (w : Fin m → ℝ) :
      Integrable (fun u => dotp w (g u)) (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_dotp.comp (continuous_const.prodMk hg))
  have hA := BstLean.Part141.abs_int_sub_le (idot ξ).abs (idot η).abs
    (inrm.const_mul (nrm (ξ - η))) (fun u =>
      (abs_abs_sub_abs_le_abs_sub _ _).trans (by
        change |ξ ⬝ᵥ g u - η ⬝ᵥ g u| ≤ _
        rw [← sub_dotProduct]
        exact abs_dot_le_nrm (ξ - η) (g u)))
  rw [integral_const_mul] at hA
  have hA' := hA.trans
    (mul_le_mul_of_nonneg_left havg (nrm_nonneg (ξ - η)))
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    simpa using integrable_pow_gauss 1
  have iz (w : Fin m → ℝ) :=
    (integrable_const (dotp w (h1bar M₁))).add (hz.const_mul σ)
  have hB := BstLean.Part141.abs_int_sub_le (iz ξ).abs (iz η).abs
    (integrable_const (nrm (ξ - η) * nrm (h1bar M₁))) (fun z =>
      (abs_abs_sub_abs_le_abs_sub _ _).trans (by
        dsimp only [Pi.add_apply]
        rw [show dotp ξ (h1bar M₁) + σ * z -
          (dotp η (h1bar M₁) + σ * z) = dotp (ξ - η) (h1bar M₁) by
            change ξ ⬝ᵥ h1bar M₁ + σ * z - (η ⬝ᵥ h1bar M₁ + σ * z) =
              (ξ - η) ⬝ᵥ h1bar M₁
            rw [sub_dotProduct]; ring]
        exact abs_dot_le_nrm _ _))
  simp only [Pi.add_apply] at hB
  simp at hB
  rw [world_row_cancellation hN, world_row_cancellation hN]
  have he : ∀ a b c d : ℝ, (a - b) / 2 - (c - d) / 2 =
      ((a - c) - (b - d)) / 2 := by intros; ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := abs_sub_le
    ((∫ u, |dotp ξ (g u)| ∂uniformSphere N) -
      (∫ u, |dotp η (g u)| ∂uniformSphere N)) 0
    ((∫ z, |dotp ξ (h1bar M₁) + σ * z| ∂gaussianReal 0 1) -
      (∫ z, |dotp η (h1bar M₁) + σ * z| ∂gaussianReal 0 1))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  change _ ≤ ((√(firstQ M₁) + nrm (h1bar M₁)) / 2) * nrm (ξ - η)
  dsimp only [g] at hA' ht
  linarith

end BstLean.Part233
#print axioms BstLean.Part233.world_row_lipschitz
