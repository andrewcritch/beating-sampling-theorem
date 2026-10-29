import BstLean.Part169Sig

/-!
# Part 272: first and second coordinate moments

These results do not assert the coordinate density.
The second moment follows from the existing linear direction moment.
-/

namespace BstLean.Part272

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)

/-- Normalized coordinates lie in the closed unit interval, including at zero. -/
theorem coord_mem {N : ℕ} (v : Fin N → ℝ) (i : Fin N) :
    unitF53 v i ∈ Set.Icc (-1 : ℝ) 1 := by
  have h : |unitF53 v i| ≤ 1 := calc
    |unitF53 v i| = √((unitF53 v i)^2) := (sqrt_sq_eq_abs _).symm
    _ ≤ √(∑ j, (unitF53 v j)^2) := sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (unitF53 v j)) (Finset.mem_univ i))
    _ ≤ 1 := BstLean.Part162.radF_unitF_le v
  exact abs_le.mp h

/-- The left integral in the coordinate-law statement is integrable. -/
theorem integrable_coord_comp {N : ℕ} (i : Fin N) {g : ℝ → ℝ}
    (hg : Measurable g) (hb : ∃ M, ∀ z ∈ Set.Icc (-1 : ℝ) 1, |g z| ≤ M) :
    Integrable (fun v => g (unitF53 v i)) (stdGauss (Fin N)) := by
  obtain ⟨M, hM⟩ := hb
  refine (integrable_const M).mono'
    (hg.comp ((measurable_pi_apply i).comp measurable_unitF)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => hM _ (coord_mem v i)

/-- Negation commutes with normalization, including at zero. -/
theorem unitF_neg {N : ℕ} (v : Fin N → ℝ) : unitF53 (-v) = -unitF53 v := by
  unfold unitF53
  simp [smul_neg]

/-- Every coordinate of the normalized Gaussian has mean zero. -/
theorem coord_mean_at {N : ℕ} (i : Fin N) :
    ∫ v, unitF53 v i ∂stdGauss (Fin N) = 0 := by
  have hm : Measurable (fun v : Fin N → ℝ => unitF53 v i) :=
    (measurable_pi_apply i).comp measurable_unitF
  have h := integral_map (μ := stdGauss (Fin N)) measurable_neg.aemeasurable
    hm.aestronglyMeasurable
  rw [BstLean.Part135.stdGauss_neg] at h
  simp only [unitF_neg, Pi.neg_apply, integral_neg] at h
  linarith

/-- Every coordinate of the normalized Gaussian has second moment `1/N`. -/
theorem coord_sq_at {N : ℕ} (hN : 1 ≤ N) (i : Fin N) :
    ∫ v, (unitF53 v i)^2 ∂stdGauss (Fin N) = 1/(N : ℝ) := by
  simpa [Pi.single_apply] using BstLean.Part169.dir_sq_mean hN (Pi.single i 1)

/-- The coordinate requested in V3a has mean zero. -/
theorem coord_mean {N : ℕ} (hN : 2 ≤ N) :
    ∫ v, unitF53 v ⟨0, by omega⟩ ∂stdGauss (Fin N) = 0 :=
  coord_mean_at _

/-- The coordinate requested in V3a has second moment `1/N`. -/
theorem coord_sq {N : ℕ} (hN : 1 ≤ N) :
    ∫ v, (unitF53 v ⟨0, by omega⟩)^2 ∂stdGauss (Fin N) = 1/(N : ℝ) :=
  coord_sq_at hN _

/-- Split off the first Gaussian coordinate before the scalar substitution. -/
theorem coord_split {N : ℕ} (hN : 1 ≤ N) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ v, g (unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin N) =
      ∫ p : ℝ × (Fin (N-1) → ℝ),
        g (p.1/√(p.1^2+(BstLean.Part53.radF53 p.2)^2))
          ∂((ProbabilityTheory.gaussianReal 0 1).prod (stdGauss (Fin (N-1)))) := by
  have hm : Measurable (fun v : Fin N → ℝ => g (unitF53 v ⟨0, by omega⟩)) :=
    hg.comp ((measurable_pi_apply _).comp measurable_unitF)
  rw [← BstLean.Part161.consV_map hN,
    integral_map BstLean.Part161.measurable_consV.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  show g (unitF53 (BstLean.Part161.consV (n := N) p.1 p.2) ⟨0, by omega⟩) =
    g (p.1/√(p.1^2+(BstLean.Part53.radF53 p.2)^2))
  congr 1
  change (1/√(BstLean.Part130.normSq (BstLean.Part161.consV (n := N) p.1 p.2)))*
    BstLean.Part161.consV (n := N) p.1 p.2 ⟨0, by omega⟩ = _
  rw [BstLean.Part161.normSq_consV hN, BstLean.Part161.consV_zero hN,
    BstLean.Part162.radF_sq]
  simp only [BstLean.Part130.normSq]
  ring

end BstLean.Part272

#print axioms BstLean.Part272.coord_mean
#print axioms BstLean.Part272.coord_sq
