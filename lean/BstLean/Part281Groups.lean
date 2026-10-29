import BstLean.Part281HS
import BstLean.Part277Mono
namespace BstLean.Part281.Groups
open Real Set BstLean.Part211
abbrev NeededGroup := BstLean.Part253.NeededGroup
abbrev centreGroup := BstLean.Part253.centreGroup
noncomputable def groupTheta (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.474440844
  | 2 => 0.481661266
  | 3 => 0.488881687
  | 4 => 0.496102109
  | 5 => 0.503322531
  | 6 => 0.510542952
  | 7 => 0.517763374
  | 8 => 0.524983796
  | _ => 0.5

noncomputable def groupProfile (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.161942450477
  | 2 => 0.164466752264
  | 3 => 0.166975170815
  | 4 => 0.169467336900
  | 5 => 0.171942889019
  | 6 => 0.174401474165
  | 7 => 0.176842748529
  | 8 => 0.179266375202
  | _ => 0.17

structure GroupScalarCertificate (g : Fin 10) : Prop where
  window : groupTheta g ∈ Icc (0.46 : ℝ) 0.525
  profile_nonneg : 0 ≤ groupProfile g
  profile_le : groupProfile g ≤ 0.1793

theorem group_scalar {g : Fin 10} (hg : NeededGroup g) : GroupScalarCertificate g := by
  fin_cases g <;> norm_num [NeededGroup, BstLean.Part253.NeededGroup] at hg
  all_goals constructor <;> norm_num [groupTheta,groupProfile]

theorem hsProfile_le {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    hsProfile n θ 0.006 ≤ hsProfile 11883 θ 0.006 :=
  BstLean.Part277.hsProfile_leP (by norm_num) hn hθ hθ1

theorem profile_on_group {g : Fin 10} (hg : NeededGroup g) {θ : ℝ}
    (hw : θ ∈ Icc (0.46 : ℝ) (groupTheta g)) :
    hsProfile 11883 θ 0.006 * (θ * √θ) ≤ groupProfile g := by
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact BstLean.Part281.HS11883.hsGroup1_11883 hw
  | ⟨2,h⟩ => exact BstLean.Part281.HS11883.hsGroup2_11883 hw
  | ⟨3,h⟩ => exact BstLean.Part281.HS11883.hsGroup3_11883 hw
  | ⟨4,h⟩ => exact BstLean.Part281.HS11883.hsGroup4_11883 hw
  | ⟨5,h⟩ => exact BstLean.Part281.HS11883.hsGroup5_11883 hw
  | ⟨6,h⟩ => exact BstLean.Part281.HS11883.hsGroup6_11883 hw
  | ⟨7,h⟩ => exact BstLean.Part281.HS11883.hsGroup7_11883 hw
  | ⟨8,h⟩ => exact BstLean.Part281.HS11883.hsGroup8_11883 hw
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)
end BstLean.Part281.Groups
