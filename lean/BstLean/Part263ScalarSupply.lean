import BstLean.Part263Coverage
import BstLean.Part263Source

/-! The scalar tables supply exact World-cell coverage and actual energy moments. -/
namespace BstLean.Part263
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part188
open BstLean.Part169 (paperDesignP)

theorem scalarRow_cell_subset {n : ℕ} (R : ScalarRow n) (i : Fin 60) :
    cell R.grid i ⊆ Icc (R.table i).lower (R.table i).upper := by
  intro θ hθ
  have hs := cell_source hθ
  rw [R.grid_top] at hs
  exact ⟨(R.containment i).1.trans hs.1, hs.2.trans (R.containment i).2⟩

theorem scalarRow_world_cover {n : ℕ} (R : ScalarRow n) {θ : ℝ}
    (hθ : θ ∈ Icc (BstLean.Part227.noiseLower (202225 / 100000))
      (BstLean.Part227.noiseUpper n (202831 / 100000))) :
    ∃ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) ∧ θ ∈ cell R.grid i := by
  have hθ' : θ ∈ Icc R.grid.worldLower R.grid.worldUpper := by
    simpa only [R.grid_lower, R.grid_upper] using hθ
  have hs := select_member R.grid hθ'
  exact ⟨_, cell_needed hs, hs⟩

theorem scalarRow_energy_moment {n : ℕ} (hn : 2 ≤ n) (R : ScalarRow n) (c : Ret n)
    (hc : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2 ((paperDesignP n).tau0 c)) :
    EnergyMoment (paperDesignP n) c R.H :=
  energy_on_event hn c hc R.energy_allowance

end BstLean.Part263
