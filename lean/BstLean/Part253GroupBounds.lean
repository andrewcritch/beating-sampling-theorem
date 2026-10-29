import BstLean.Part253GroupData
import BstLean.Part253Parallel

/-! The local centre groups have complete moment certificates and parallel scalar bounds. -/
namespace BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12225 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12225 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.0535 ∧
    0 ≤ bN 12225 csC (groupTheta g) ∧ bN 12225 csC (groupTheta g) ≤ 0.001438 := by
  have G := group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := moment_upper G.window G.profile_nonneg
  have hb := bn_upper hΘ
  exact ⟨centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

noncomputable def groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12225 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := group_scalar hg
  exact {
    delta_nonneg := by norm_num
    delta_lt := by norm_num
    k_gt := by norm_num
    k3_gt := by norm_num
    theta_lower := by norm_num
    v_pos := by intro θ hθ; norm_num
    supremum := fun θ hθ => profile_on_group hg hθ
    ratio := by have := rho_bounds.2; linarith
    ratio_gamma := by have := (gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (second_gap_lower G.window) }

theorem group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12225 12225 0.011
      (momentAllowance 12225 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12225 csC (groupTheta g))
      (√(momentAllowance 12225 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12225 csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ parallelCap := by
  have G := group_scalar hg
  obtain ⟨hxi0, hxi1, hbn0, hbn1⟩ := group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12225 csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12225 csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231301 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := deviation_upper hΘ G.window.2
  exact parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12225 0.011
      (momentAllowance 12225 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12225 csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0, hxi1, hbn0, hbn1⟩ := group_moment_bounds hg
  exact (emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

theorem group_finite_guard : finiteEnergy 12225 12225 0.011 / √12225 < plow 12225 0.011 := by
  have hf : finiteEnergy 12225 12225 0.011 ≤ 0.008646 := by
    convert finite_centre_upper using 1 <;> norm_num
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have h : finiteEnergy 12225 12225 0.011 / √12225 ≤ 0.008646 / 110.566721 := by
    gcongr
  exact lt_of_le_of_lt h (lt_of_lt_of_le (by norm_num) plow_lower)

end BstLean.Part253
