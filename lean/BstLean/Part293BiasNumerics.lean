import BstLean.Part293EndpointInterface
import BstLean.Part242Pass
import BstLean.Part285IntervalTools

/-! Rounded SY bias bounds use only the required root allowance. -/
namespace BstLean.Part293
open Real BstLean.Part242

structure BiasNumerics (χ vmax aw af F8 F24 Γ Cv : ℝ) : Prop where
  centre : 0 ≤ χ ∧ χ ≤ 1.081
  variance_max : 0 ≤ vmax ∧ vmax ≤ 0.00411
  energy_error : 0 ≤ aw ∧ aw ≤ 0.1802
  location_error : 0 ≤ af ∧ af ≤ 0.05125
  location8 : 0 ≤ F8 ∧ F8 ≤ 0.85428
  location24 : 0 ≤ F24 ∧ F24 ≤ 0.86139
  reciprocal : 0 ≤ Γ ∧ Γ ≤ 3.721
  variance_norm : 0 ≤ Cv ∧ Cv ≤ 0.0003804

theorem bias_root_le {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {χ vmax aw af F8 F24 Γ Cv : ℝ} (B : BiasNumerics χ vmax aw af F8 F24 Γ Cv) :
    syBiasRoot n χ 0.17919 0.028 vmax aw af F8 F24 Γ Cv ≤ 0.00406 := by
  have hl : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (n : ℝ) ≤ 11882 := by exact_mod_cast hn'
  rcases B with ⟨hχ, hv, haw, haf, hf8, hf24, hΓ, hCv⟩
  unfold syBiasRoot
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold syBiasPrice syPrice syScale BstLean.Part241.exceptionalMass
  interval_num

/-- The final root can use these simpler component caps. -/
theorem root_le_allowance {removal mixture displacement bias tail arithmetic : ℝ}
    (hr : removal ≤ 0.000029) (hm : mixture ≤ 0.00194)
    (hd : displacement ≤ 0.00036) (hb : bias ≤ 0.00406)
    (ht : tail ≤ 2 / 10 ^ 8) (ha : arithmetic ≤ 1 / 10 ^ 20) :
    removal + mixture + displacement + bias + tail + arithmetic ≤ rootAllowance := by
  norm_num [rootAllowance] at *
  linarith

end BstLean.Part293

/-- info: 'BstLean.Part293.bias_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.bias_root_le
