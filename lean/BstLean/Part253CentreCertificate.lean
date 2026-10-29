import BstLean.Part253GroupBounds
import BstLean.Part253EnergyCells
import BstLean.Part253RetunedScalar
import BstLean.Part253Direction

/-! The scalar Part211 centre certificate is supplied for every needed cell. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem cell_world_signal {i : Fin 60} (hi : needed i) :
    1 - noiseNode i.val ∈ Icc (0 : ℝ) 0.54 := by
  have hm : noiseNode i.val ∈ cell i := ⟨le_rfl, noiseNode_mono (Nat.le_succ _)⟩
  have hw := needed_direction_window hi hm
  exact ⟨by linarith [hw.2], by linarith [hw.1]⟩

theorem energy_root_guard : 2 * √(12 : ℝ) / 12225 < √(1 - 2 / (12225 : ℝ) ^ 2) := by
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : (0.9999999933 : ℝ) ≤ √(1 - 2 / (12225 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  linarith

noncomputable def localCentreCertificate {i : Fin 60} (hi : needed i) :
    CentreCertificate 12225 12225 0.011 1.22 1.12 0.46
      (groupTheta (centreGroup i)) (groupProfile (centreGroup i)) 1.22
      (1 - noiseNode i.val) (fun _ => 0.006) := by
  have hg := needed_group hi
  have G := group_scalar hg
  have R := retuned_on_needed hi
  have hq := cell_world_signal hi
  have hE := upper_energy_on_needed hi hq.1 le_rfl
  have hw (θ : ℝ) (hθ : θ ∈ Icc (0.46 : ℝ) (groupTheta (centreGroup i))) :
      θ ∈ Icc (0.46 : ℝ) 0.532 :=
    ⟨hθ.1, hθ.2.trans (G.window.2.trans (by norm_num))⟩
  exact {
    toMomentCertificate := groupMomentCertificate hg
    delta_upper := by norm_num
    signal_domain := ⟨by linarith [hq.1], by linarith [hq.2]⟩
    energy_domain := hE.1
    energy_root := by simpa only [Nat.cast_ofNat] using energy_root_guard
    energy_lower := by have := gMinus_lower; linarith
    energy_upper := by have := gPlus_upper; linarith
    relative_gap := group_relative_gap hg
    finite_guard := by convert group_finite_guard using 1 <;> norm_num
    lower_root := fun θ hθ => le_trans (by norm_num) (mean_lower_window (hw θ hθ)).1
    lower_bracket := fun θ hθ => by
      convert (energy_lower_data (hw θ hθ)).1 using 1 <;> norm_num
    lower_guard := fun θ hθ => by
      have h := le_trans (by norm_num : (0 : ℝ) ≤ 0.81583) (energy_lower_data (hw θ hθ)).2.1
      convert h using 1 <;> norm_num
    upper_clip := by convert hE.2.trans R.energy_upper using 1 <;> norm_num }

end BstLean.Part253
