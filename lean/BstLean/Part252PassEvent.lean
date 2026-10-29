import BstLean.Part252EnergyEvent
import BstLean.Part252Centre
import BstLean.Part252MatrixEvent
import BstLean.Part252VarianceMoment
import BstLean.Part252LatitudeCap

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12225) :=
  agentEv (paperDesignP 12225) (Energy32 12225) ∩
  agentEv (paperDesignP 12225) (freshRetainedEvent160 12225 4) ∩
  agentEv (paperDesignP 12225) (FirstMatrix 12225) ∩
  BstLean.Part164.Eop2 12225 ∩ outputCentreEvent (paperCentres 12225)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12225)).real
      (agentEv (paperDesignP 12225) (FirstMatrix 12225))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12225)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12225 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12225)).real (BstLean.Part164.Eop2 12225)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12225)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12225)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12225) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12225) hτ
  have hL := fresh_retained_charge160 (n := 12225) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12225) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12225 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12225) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12225 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12225) (hw : WINDOW (paperDesignP 12225) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12225))
    (hW : ∫ a in K, ((12225 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12225 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12225 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12225 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12225) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12225 : ℝ)) * eR c * 12225 * chi :=
  outputCentre_row hc.2

end BstLean.Part252
