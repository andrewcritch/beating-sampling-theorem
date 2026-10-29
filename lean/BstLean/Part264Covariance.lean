import BstLean.Part264Repair

/-! Per-cell TI supplies and rational repairs give an actual covariance contract. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263

theorem grid_world_window {n : ℕ} (hn : 12225 ≤ n) (R : ScalarRow n) :
    Icc R.grid.worldLower R.grid.worldUpper ⊆ Icc (46 / 100 : ℝ) (528 / 1000) := by
  intro θ hθ
  rw [R.grid_lower, R.grid_upper] at hθ
  exact ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
    hθ.2.trans ((world_upper_le hn).trans (by norm_num))⟩

noncomputable def covarianceInputs_from_supplies {n : ℕ} (hn : 12225 ≤ n)
    {R : ScalarRow n} (A : FrameRepair n R)
    (S : ∀ j, Supply n (parameters j) (cellLower R.grid (sourceIndex j))
      (cellUpper R.grid (sourceIndex j)))
    (hR : ∀ j θ, θ ∈ cell R.grid (sourceIndex j) →
      BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
      BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius) :
    CovarianceInputs n R.grid parameters (caps A) where
  supplies := S
  world_window := grid_world_window hn R
  wide_radius := fun j θ hθ => (hR j θ hθ).1
  core_radius := fun j θ hθ => (hR j θ hθ).2
  scalar := fun i θ hθ => selected_envelope (by omega) A i hθ

end BstLean.Part264
