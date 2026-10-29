import BstLean.Part291FrameWitness

namespace BstLean.BlueprintLow
open Real Set BstLean.Part215 BstLean.Part255 BstLean.Part188 BstLean.Part222

noncomputable def FrameEnvelopeWitness.scalar {nlo nhi : ℕ} {Θ full E : ℝ} {p : Parameters}
    {pair outside bad cp2 cp4 cp12 : ℝ}
    (W : FrameEnvelopeWitness nlo nhi Θ full E p pair outside bad cp2 cp4 cp12) : FrameScalarData where
  projected := W.schur
  cap := W.cap
  mean1 := W.W2 * full
  mean2 := W.V
  mass := W.mass
  projectedRoot := W.rootN
  capRoot := W.rootB
  mean1Root := W.rootU
  mean2Root := W.rootV

theorem FrameEnvelopeWitness.scalar_checked {nlo nhi : ℕ} {Θ full E : ℝ} {p : Parameters}
    {pair outside bad cp2 cp4 cp12 : ℝ}
    (W : FrameEnvelopeWitness nlo nhi Θ full E p pair outside bad cp2 cp4 cp12) :
    FrameScalarCertificate W.scalar := by
  rcases W.nonneg with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hN,hB,hU,hV⟩
  exact ⟨⟨hN,hB,hU,hV⟩,⟨W.rootN_sq,W.rootB_sq,W.rootU_sq,W.rootV_sq⟩,W.total⟩

structure FrameEnclosures (n : ℕ) (θ full E : ℝ) (p : Parameters)
    (cov schur cap W2 V mass : ℝ) : Prop where
  gap : 0.216 < (1 - 0.0045) ^ 2 - lowFrameMean n E ^ 2
  covariance : lowFrameCov n θ p ≤ cov
  projected : lowFrameSchur n θ p E ≤ schur
  cap_energy : frameGB n ((1 - 0.0045) ^ 2) 0.216 agentDirectionCap
    (agentEnergyMomentCap / n) cov full ≤ cap
  weight_mean : rwWeightMean ((1 - 0.0045) ^ 2) 0.216 (lowFrameMean n E)
    (√(agentDirectionCap / n)) ≤ W2
  variance : (((1 - 0.0045) ^ 2 - 0.216) / 0.216 ^ 3) * (agentDirectionCap / n) * cov ≤ V
  bad_input : massBound n agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap E
    0.0045 0.216 ≤ mass

theorem FrameEnvelopeWitness.bound {n nlo nhi : ℕ} (hnlo : 8000 ≤ nlo)
    (hn : n ∈ Icc nlo nhi) {Θ full E : ℝ} {p : Parameters}
    {pair outside bad cp2 cp4 cp12 : ℝ}
    (W : FrameEnvelopeWitness nlo nhi Θ full E p pair outside bad cp2 cp4 cp12)
    (hp : Valid p) (hfull : 0 ≤ full) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ Θ)
    (hpair : BstLean.Part254.gaussianPair lowCoreWindow ≤ pair)
    (hout : BstLean.Part254.gaussianOutside lowCoreWindow ≤ outside)
    (hbad : lowFrameBad ≤ bad)
    (hc2 : BstLean.Part195.rotationConstant 2 ≤ cp2)
    (hc4 : BstLean.Part195.rotationConstant 4 ≤ cp4)
    (hc12 : BstLean.Part195.rotationConstant 12 ≤ cp12) :
    FrameEnclosures n θ full E p W.cov W.schur W.cap W.W2 W.V W.mass := by
  rcases W.nonneg with ⟨he0,hxi0,hs0,hmu0,hr10,hr20,hD20,hD40,hdelt0,hW20,hshell0,
    hcov0,hschur0,hG10,hG20,hG30,hcap0,hV0,hrN,hrB,hrU,hrV⟩
  have hnR : (nlo : ℝ) ≤ n := by exact_mod_cast hn.1
  have hnU : (n : ℝ) ≤ nhi := by exact_mod_cast hn.2
  have hloR : (8000 : ℝ) ≤ nlo := by exact_mod_cast hnlo
  have hlo0 : (0 : ℝ) < nlo := by linarith
  have hn0 : (0 : ℝ) < n := hlo0.trans_le hnR
  have hΘ0 : 0 ≤ Θ := hθ0.trans hθ
  have hM0 : 0 ≤ agentDirectionCap := by norm_num [agentDirectionCap]
  have hH0 : 0 ≤ agentEnergyMomentCap := by norm_num [agentEnergyMomentCap]
  have hxiP0 : 0 ≤ agentParallelCap := by norm_num [agentParallelCap]
  have hmu : lowFrameMean n E ≤ W.mu := by
    have he := sqrt_le_iff.mpr ⟨he0,W.e_sq⟩
    have hxi : √(agentParallelCap / n) ≤ W.xiRoot :=
      sqrt_le_iff.mpr ⟨hxi0,(by gcongr : agentParallelCap / n ≤ agentParallelCap / nlo).trans W.xi_sq⟩
    exact (add_le_add he hxi).trans W.mu_cap
  have hmu' : 0 ≤ lowFrameMean n E := by unfold lowFrameMean; positivity
  have hs : √(agentDirectionCap / n) ≤ W.s :=
    sqrt_le_iff.mpr ⟨hs0,(by gcongr : agentDirectionCap / n ≤ agentDirectionCap / nlo).trans W.s_sq⟩
  have hY0 : 0 < W.Y := lt_trans (by norm_num) W.Y_pos
  have hY : W.Y ≤ (1 - 0.0045) ^ 2 - lowFrameMean n E ^ 2 := by
    have hsq := pow_le_pow_left₀ hmu' hmu 2
    linarith [W.Y_cap]
  have hgap := W.Y_pos.trans_le hY
  have hc20 : 0 ≤ cp2 := (BstLean.Part195.rotationConstant_nonneg 2).trans hc2
  have hc40 : 0 ≤ cp4 := (BstLean.Part195.rotationConstant_nonneg 4).trans hc4
  have hc120 : 0 ≤ cp12 := (BstLean.Part195.rotationConstant_nonneg 12).trans hc12
  have hrc2 := BstLean.Part195.rotationConstant_nonneg 2
  have hrc4 := BstLean.Part195.rotationConstant_nonneg 4
  have hrc12 := BstLean.Part195.rotationConstant_nonneg 12
  have hD2 : rwD2 (lowFrameMean n E) (√(agentDirectionCap / n)) ≤ W.D2 := by
    unfold rwD2
    apply le_trans ?_ W.D2_cap
    gcongr
    all_goals positivity
  have hD4 : rwD4 (lowFrameMean n E) (√(agentDirectionCap / n)) ≤ W.D4 := by
    unfold rwD4
    apply le_trans ?_ W.D4_cap
    gcongr
    all_goals positivity
  have hD2pos : 0 ≤ rwD2 (lowFrameMean n E) (√(agentDirectionCap / n)) := by unfold rwD2; positivity
  have hD4pos : 0 ≤ rwD4 (lowFrameMean n E) (√(agentDirectionCap / n)) := by
    unfold rwD4
    have := BstLean.Part195.rotationConstant_nonneg 4
    positivity
  have hdelt : rwDelta ((1 - 0.0045) ^ 2) 0.216 (lowFrameMean n E)
      (√(agentDirectionCap / n)) ≤ W.delta := by
    unfold rwDelta
    apply le_trans ?_ W.delta_cap
    gcongr
  have hdeltpos : 0 ≤ rwDelta ((1 - 0.0045) ^ 2) 0.216 (lowFrameMean n E)
      (√(agentDirectionCap / n)) := by unfold rwDelta; positivity
  have h4 : 0 < 1 - 4 * Θ / nlo := by
    have h : 4 * Θ / (nlo : ℝ) ≤ 6 * Θ / nlo := by gcongr <;> norm_num
    linarith [W.r_den]
  have hr1 : radiusCoefficient n 1 θ ≤ W.r1 := by
    unfold radiusCoefficient
    norm_num only [Nat.cast_ofNat]
    apply le_trans ?_ W.r1_cap
    gcongr
  have hr2 : radiusCoefficient n 2 θ ≤ W.r2 := by
    unfold radiusCoefficient
    norm_num only [Nat.cast_ofNat]
    apply le_trans ?_ W.r2_cap
    gcongr
    exact W.r_den
  have hden1 : 0 < 1 - 4 * θ / (n : ℝ) := by
    have : 4 * θ / (n : ℝ) ≤ 4 * Θ / nlo := by gcongr
    linarith
  have hden2 : 0 < 1 - 6 * θ / (n : ℝ) := by
    have : 6 * θ / (n : ℝ) ≤ 6 * Θ / nlo := by gcongr
    linarith [W.r_den]
  have hr1pos : 0 ≤ radiusCoefficient n 1 θ := by
    unfold radiusCoefficient
    norm_num only [Nat.cast_ofNat]
    exact div_nonneg hθ0 hden1.le
  have hr2pos : 0 ≤ radiusCoefficient n 2 θ := by
    unfold radiusCoefficient
    norm_num only [Nat.cast_ofNat]
    exact div_nonneg hθ0 hden2.le
  have hwden : 0 < 1 - p.wRadius := sub_pos.mpr hp.wRadius_lt
  have hcden : 0 < 1 - p.cRadius := sub_pos.mpr hp.cRadius_lt
  have hp0 : 0 ≤ BstLean.Part254.gaussianPair lowCoreWindow := BstLean.Part254.gaussianTail_nonneg _
  have ho0 : 0 ≤ BstLean.Part254.gaussianOutside lowCoreWindow :=
    add_nonneg (BstLean.Part254.gaussianTail_nonneg _) (by positivity)
  have hpair0 : 0 ≤ pair := hp0.trans hpair
  have hout0 : 0 ≤ outside := ho0.trans hout
  have hshell : lowFrameShell θ p ≤ W.shell := by
    unfold lowFrameShell
    apply le_trans ?_ W.shell_cap
    have hw0 := hp.wLam_nonneg
    gcongr
  have hC : lowFrameCov n θ p ≤ W.cov := by
    unfold lowFrameCov
    apply le_trans ?_ W.cov_cap
    have hc0 := hp.cLam_nonneg
    gcongr
  have hN : lowFrameSchur n θ p E ≤ W.schur := by
    unfold lowFrameSchur
    apply le_trans ?_ W.schur_cap
    have hc0 := hp.cLam_nonneg
    gcongr
  have hW : rwWeightMean ((1 - 0.0045) ^ 2) 0.216 (lowFrameMean n E)
      (√(agentDirectionCap / n)) ≤ W.W2 := by
    unfold rwWeightMean
    apply le_trans ?_ W.W2_cap
    gcongr
  have hG1 := rpow_fraction_bound (by positivity : 0 ≤ (W.cov + full) / (0.216 * nlo))
    hG10 (by norm_num : (45 : ℕ) ≠ 0) W.G1_cap
  have hG2 := rpow_fraction_bound (by norm_num : 0 ≤ (1 / (0.216 : ℝ)))
    hG20 (by norm_num : (45 : ℕ) ≠ 0) W.G2_cap
  have hG3 := rpow_fraction_bound (by positivity : 0 ≤ 1 + agentEnergyMomentCap / nlo)
    hG30 (by norm_num : (45 : ℕ) ≠ 0) W.G3_cap
  norm_num only [Nat.cast_ofNat] at hG1 hG3
  have hG1n : ((W.cov + full) / (0.216 * n)) ^ (41 / 45 : ℝ) ≤ W.G1 := by
    apply le_trans ?_ hG1
    apply rpow_le_rpow (by positivity) _ (by norm_num)
    gcongr
    norm_num
  have hG3n : (1 + agentEnergyMomentCap / n) ^ (8 / 45 : ℝ) ≤ W.G3 := by
    apply le_trans ?_ hG3
    apply rpow_le_rpow (by positivity) _ (by norm_num)
    gcongr
  push_cast at hG2
  have hG2n : (1 / (0.216 : ℝ)) ^ (4 / 45 : ℝ) ≤ W.G2 := hG2
  have hcap : frameGB n ((1 - 0.0045) ^ 2) 0.216 agentDirectionCap
      (agentEnergyMomentCap / n) W.cov full ≤ W.cap := by
    rw [frameGB_dimension_normalized (by have := hn.1; omega) (by norm_num)
      (add_nonneg hcov0 hfull)]
    apply le_trans ?_ W.cap_cap
    gcongr
  have hV : (((1 - 0.0045) ^ 2 - 0.216) / 0.216 ^ 3) *
      (agentDirectionCap / n) * W.cov ≤ W.V := by
    apply le_trans ?_ W.V_cap
    gcongr
  have hsg : W.gap + W.mu ≤ √((1 - 0.0045) ^ 2 - (0.216 : ℝ)) := le_sqrt_of_sq_le W.gap_sq
  have hgap' : W.gap ≤ √((1 - 0.0045) ^ 2 - (0.216 : ℝ)) - lowFrameMean n E := by linarith
  have hmass : massBound n agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap E
      0.0045 0.216 ≤ W.mass := by
    unfold massBound
    change (n : ℝ) * ((agentEnergyMomentCap / n / 0.0045) ^ 32 +
      (BstLean.Part195.rotationConstant 12 ^ 24 * (agentDirectionCap / n) ^ 12) /
      (√((1 - 0.0045) ^ 2 - 0.216) - lowFrameMean n E) ^ 24) ≤ W.mass
    apply le_trans ?_ W.mass_cap
    have hg0 := W.gap_pos
    gcongr
  exact ⟨hgap,hC,hN,hcap,hW,hV,hmass⟩

end BstLean.BlueprintLow
