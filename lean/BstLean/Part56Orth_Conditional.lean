import BstLean.Part56Orth_Integrability
import BstLean.Part56Orth_Projection

namespace BstLean.Part56.Orth

set_option maxHeartbeats 1000000

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Tens)
open BstLean.Part43 (BofQ)
open BstLean.Part53 (sg)

variable {n d : ℕ}

/-- Residual resampling preserves the predictor. -/
theorem heat_resampling (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (s : ℝ) (Z W : CoefIdxD n d → ℝ) :
    gLineH μ k f0 T v (s • (projA v Z + (W - projA v W))) =
      gLineH μ k f0 T v (s • Z) := by
  have ha (j : ℕ) (hj : j ≤ d) :
      ancRK (s • (projA v Z + (W - projA v W))) v j = ancRK (s • Z) v j := by
    rw [anchor_smul, anchor_resampling v hv Z W j hj, anchor_smul]
  unfold gLineH
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    apply congrArg (BstLean.Part53.fvA k _)
    unfold mux
    apply Finset.sum_congr rfl
    intro j hj
    rw [ha j (by have := Finset.mem_range.mp hj; omega)])

/-- Orthogonality follows from the residual mean identity and the split interface. -/
theorem orthogonal_of_residual_mean (hS : PropSplit56 d)
    {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) (hv : UnitV v)
    (hmean : ∀ Z : CoefIdxD n d → ℝ,
      (∫ W, (BofQ μ k f0 T (sg n d • (projA v Z + (W - projA v W))) -
        gLineH μ k f0 T v (sg n d • Z)) ∂stdGauss (CoefIdxD n d)) = 0)
    (h : (Fin (d + 1) → Fin n → ℝ) → ℝ)
    (hh : MemLp (fun Z : CoefIdxD n d → ℝ =>
      h (fun j => ancRK (sg n d • Z) v j)) 2 (stdGauss (CoefIdxD n d))) :
    (∫ Z, (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) *
      h (fun j => ancRK (sg n d • Z) v j) ∂stdGauss (CoefIdxD n d)) = 0 := by
  let F := fun Z : CoefIdxD n d → ℝ =>
    (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) *
      h (fun j => ancRK (sg n d • Z) v j)
  let r := fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
    projA v p.1 + (p.2 - projA v p.2)
  have hi : Integrable F (stdGauss (CoefIdxD n d)) :=
    ((B_memLp hμ k f0 T (sg n d)).sub (heat_memLp hμ k f0 T v)).integrable_mul hh
  have hmp := resampling_measurePreserving hS v hv
  have hip : Integrable (F ∘ r) ((stdGauss (CoefIdxD n d)).prod
      (stdGauss (CoefIdxD n d))) := hmp.integrable_comp_of_integrable hi
  have heq : (∫ Z, F Z ∂stdGauss (CoefIdxD n d)) =
      ∫ p, F (r p) ∂(stdGauss (CoefIdxD n d)).prod (stdGauss (CoefIdxD n d)) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable
      (hmp.map_eq.symm ▸ hi.aestronglyMeasurable)
  rw [show (∫ Z, (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) *
    h (fun j => ancRK (sg n d • Z) v j) ∂stdGauss (CoefIdxD n d)) =
      ∫ Z, F Z ∂stdGauss (CoefIdxD n d) from rfl,
    heq, integral_prod (fun p => F (r p)) hip]
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun Z => by
    have ha (W : CoefIdxD n d → ℝ) :
        (fun j : Fin (d + 1) => ancRK (sg n d • r (Z, W)) v j) =
          (fun j : Fin (d + 1) => ancRK (sg n d • Z) v j) := by
      funext j
      rw [anchor_smul, anchor_smul]
      dsimp [r]
      rw [anchor_resampling v hv Z W j (by omega)]
    simp only [F, ha]
    simp only [r, heat_resampling μ k f0 T v hv (sg n d)]
    rw [integral_mul_const, hmean, zero_mul]
    rfl)

end BstLean.Part56.Orth
