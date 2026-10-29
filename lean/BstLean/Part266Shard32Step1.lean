import BstLean.Part266Shard32Step0


/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13150
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13150 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13150).real (BstLean.Part211.CentreSource 13150 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13150) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13150 160 (6 / 1000)
  have hj := jS_160_le (n := 13150) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13150 160 (6 / 1000) ^ 2 * 13150 /
      (((13150 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13150 160 (6 / 1000) ^ 2 * 13150 /
      (((13150 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13150 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13150 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13150) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13150 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13150

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13150
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13150) :=
  Ethm (paperCentres 13150) ∩ Ethp (paperCentres 13150)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13150)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13150)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13150) (paperCentres 13150)
  have he : exp (-(45 / 10000 * (13150 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13150 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13150) :=
  (passEvent ∩ agentEv (paperDesignP 13150) (DirectionError 13150) ∩
    agentEv (paperDesignP 13150) (CentreSources 13150 13150)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13150)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13150) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13150) hτ
  have hC := centreSources_ret_charge_row 13150 (paperDesignP 13150) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13150)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13150) (CentreSources 13150 13150)
  direction : analyticBase ⊆ agentEv (paperDesignP 13150) (DirectionError 13150)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13150)) : Set (Ret 13150) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13150)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13150)}
    (hT : (retDist (paperCentres 13150)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13150)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13150)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13150)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13150)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13150)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13150

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13150
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13150 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13150 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13150 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13150 13150 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13150)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13150)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13150
  have hb0 := BstLean.Part150.betaJ_nonneg 13150
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13150 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13150 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13150 * BstLean.Part150.betaJ 13150) * 13150) ≤
      (1630633 / 10000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13150)) * 13150 := by gcongr <;> linarith
      _ ≤ ((1630633 / 10000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13150 * 13150 *
      (1 + BstLean.Part154.deltaChi 13150 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186645781 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13150 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186645781 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13150 : ℝ) / BstLean.Part154.csC) ≤ (100761073 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13150 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100761073 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13150 : ℝ) * (1630633 / 10000) +
        2 * (1792 / 10000 / 13150) * (186645781 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (100761073 / 1000000) *
          (81 / 1000 / 13150 + (1792 / 10000 / 13150) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13150

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13150
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13150 ∧
    1 ≤ gPlus 13150 ∧ gPlus 13150 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13150 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13150 : ℝ) < √(1 - 2 / (13150 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13150 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13150 (gMinus 13150) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13150 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13150 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13150 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13150)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13150 (gMinus 13150) (gPlus 13150)
      (finiteEnergy 13150 13150 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13150 (gMinus 13150) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13150 (gMinus 13150) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13150 (gMinus 13150) (54 / 100))
    (by linarith : energyRatio 13150 (gMinus 13150) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13150 (gMinus 13150) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13150 * kappa (energyRatio 13150 (gMinus 13150) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13150) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13150 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13150 13150 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13150 13150 (11 / 1000) / √13150 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13150)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13150 * kappa (energyRatio 13150 (gMinus 13150) (54 / 100))) +
      2 * √(12 * gPlus 13150) / 13150 + finiteEnergy 13150 13150 (11 / 1000) / √13150 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13150 θ ∧ meanLowerRoot 13150 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13150 - 2 / (13150 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13150 - 2 / (13150 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13150 θ ^ 2 / gPlus 13150) - 2 / (13150 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13150 * (kappa (meanLowerRoot 13150 θ ^ 2 / gPlus 13150) -
        2 / (13150 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13150) / 13150 -
        finiteEnergy 13150 13150 (11 / 1000) / √13150 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13150 θ ^ 2 / gPlus 13150 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13150)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13150 θ ^ 2 / gPlus 13150 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13150)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13150 θ ^ 2 / gPlus 13150 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13150 ^ 2 ≤
      kappa (meanLowerRoot 13150 θ ^ 2 / gPlus 13150) - 2 / (13150 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13150 *
      (kappa (meanLowerRoot 13150 θ ^ 2 / gPlus 13150) - 2 / (13150 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13150 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13150)
    linarith
  have ht : √(12 * gPlus 13150) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13150 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13150 13150 (11 / 1000) / √13150 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13150)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13150 (gMinus 13150) (gPlus 13150)
      (finiteEnergy 13150 13150 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13150) (hτ : 0 < (paperDesignP 13150).tau0 c) :
    eR c = (2 / (mA 13150 : ℝ)) *
      normSq (BstLean.Part150.bT 13150 13150 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13150).tau0 c)) /
      (2 / (13150 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13150).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13150).tau0 c))⁻¹ •
      BstLean.Part150.bT 13150 13150 (A1 c) (A2 c) c.1.2 ((paperDesignP 13150).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13150 : ℝ)) * normSq (bR c) / (2 / (13150 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13150}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13150) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13150).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13150 : ℝ) * (paperDesignP 13150).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13150 13150 c.1.2 ((paperDesignP 13150).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13150

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13151
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13151 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13151).real (BstLean.Part211.CentreSource 13151 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13151) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13151 160 (6 / 1000)
  have hj := jS_160_le (n := 13151) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13151 160 (6 / 1000) ^ 2 * 13151 /
      (((13151 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13151 160 (6 / 1000) ^ 2 * 13151 /
      (((13151 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13151 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13151 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13151) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13151 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13151

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13151
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13151) :=
  Ethm (paperCentres 13151) ∩ Ethp (paperCentres 13151)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13151)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13151)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13151) (paperCentres 13151)
  have he : exp (-(45 / 10000 * (13151 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13151 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13151) :=
  (passEvent ∩ agentEv (paperDesignP 13151) (DirectionError 13151) ∩
    agentEv (paperDesignP 13151) (CentreSources 13151 13151)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13151)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13151) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13151) hτ
  have hC := centreSources_ret_charge_row 13151 (paperDesignP 13151) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13151)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13151) (CentreSources 13151 13151)
  direction : analyticBase ⊆ agentEv (paperDesignP 13151) (DirectionError 13151)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13151)) : Set (Ret 13151) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13151)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13151)}
    (hT : (retDist (paperCentres 13151)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13151)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13151)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13151)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13151)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13151)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13151

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13151
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13151 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13151 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13151 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13151 13151 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13151)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13151)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13151
  have hb0 := BstLean.Part150.betaJ_nonneg 13151
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13151 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13151 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13151 * BstLean.Part150.betaJ 13151) * 13151) ≤
      (326139 / 2000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13151)) * 13151 := by gcongr <;> linarith
      _ ≤ ((326139 / 2000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13151 * 13151 *
      (1 + BstLean.Part154.deltaChi 13151 12 + 2 / π) / BstLean.Part154.csC) ≤
      (93326439 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13151 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((93326439 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13151 : ℝ) / BstLean.Part154.csC) ≤ (12595613 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13151 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12595613 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13151 : ℝ) * (326139 / 2000) +
        2 * (1792 / 10000 / 13151) * (93326439 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (12595613 / 125000) *
          (81 / 1000 / 13151 + (1792 / 10000 / 13151) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13151

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13151
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13151 ∧
    1 ≤ gPlus 13151 ∧ gPlus 13151 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13151 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13151 : ℝ) < √(1 - 2 / (13151 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13151 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13151 (gMinus 13151) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13151 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13151 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13151 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13151)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13151 (gMinus 13151) (gPlus 13151)
      (finiteEnergy 13151 13151 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13151 (gMinus 13151) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13151 (gMinus 13151) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13151 (gMinus 13151) (54 / 100))
    (by linarith : energyRatio 13151 (gMinus 13151) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13151 (gMinus 13151) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13151 * kappa (energyRatio 13151 (gMinus 13151) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13151) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13151 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13151 13151 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13151 13151 (11 / 1000) / √13151 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13151)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13151 * kappa (energyRatio 13151 (gMinus 13151) (54 / 100))) +
      2 * √(12 * gPlus 13151) / 13151 + finiteEnergy 13151 13151 (11 / 1000) / √13151 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13151 θ ∧ meanLowerRoot 13151 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13151 - 2 / (13151 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13151 - 2 / (13151 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13151 θ ^ 2 / gPlus 13151) - 2 / (13151 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13151 * (kappa (meanLowerRoot 13151 θ ^ 2 / gPlus 13151) -
        2 / (13151 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13151) / 13151 -
        finiteEnergy 13151 13151 (11 / 1000) / √13151 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13151 θ ^ 2 / gPlus 13151 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13151)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13151 θ ^ 2 / gPlus 13151 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13151)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13151 θ ^ 2 / gPlus 13151 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13151 ^ 2 ≤
      kappa (meanLowerRoot 13151 θ ^ 2 / gPlus 13151) - 2 / (13151 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13151 *
      (kappa (meanLowerRoot 13151 θ ^ 2 / gPlus 13151) - 2 / (13151 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13151 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13151)
    linarith
  have ht : √(12 * gPlus 13151) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13151 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13151 13151 (11 / 1000) / √13151 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13151)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13151 (gMinus 13151) (gPlus 13151)
      (finiteEnergy 13151 13151 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13151) (hτ : 0 < (paperDesignP 13151).tau0 c) :
    eR c = (2 / (mA 13151 : ℝ)) *
      normSq (BstLean.Part150.bT 13151 13151 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13151).tau0 c)) /
      (2 / (13151 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13151).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13151).tau0 c))⁻¹ •
      BstLean.Part150.bT 13151 13151 (A1 c) (A2 c) c.1.2 ((paperDesignP 13151).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13151 : ℝ)) * normSq (bR c) / (2 / (13151 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13151}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13151) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13151).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13151 : ℝ) * (paperDesignP 13151).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13151 13151 c.1.2 ((paperDesignP 13151).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13151

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13152
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13152 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13152).real (BstLean.Part211.CentreSource 13152 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13152) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13152 160 (6 / 1000)
  have hj := jS_160_le (n := 13152) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13152 160 (6 / 1000) ^ 2 * 13152 /
      (((13152 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13152 160 (6 / 1000) ^ 2 * 13152 /
      (((13152 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13152 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13152 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13152) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13152 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13152

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13152
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13152) :=
  Ethm (paperCentres 13152) ∩ Ethp (paperCentres 13152)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13152)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13152)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13152) (paperCentres 13152)
  have he : exp (-(45 / 10000 * (13152 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13152 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13152) :=
  (passEvent ∩ agentEv (paperDesignP 13152) (DirectionError 13152) ∩
    agentEv (paperDesignP 13152) (CentreSources 13152 13152)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13152)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13152) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13152) hτ
  have hC := centreSources_ret_charge_row 13152 (paperDesignP 13152) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13152)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13152) (CentreSources 13152 13152)
  direction : analyticBase ⊆ agentEv (paperDesignP 13152) (DirectionError 13152)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13152)) : Set (Ret 13152) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13152)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13152)}
    (hT : (retDist (paperCentres 13152)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13152)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13152)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13152)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13152)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13152)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13152

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13152
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13152 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13152 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13152 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13152 13152 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13152)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13152)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13152
  have hb0 := BstLean.Part150.betaJ_nonneg 13152
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13152 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13152 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13152 * BstLean.Part150.betaJ 13152) * 13152) ≤
      (163075699 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13152)) * 13152 := by gcongr <;> linarith
      _ ≤ ((163075699 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13152 * 13152 *
      (1 + BstLean.Part154.deltaChi 13152 12 + 2 / π) / BstLean.Part154.csC) ≤
      (93329987 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13152 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((93329987 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13152 : ℝ) / BstLean.Part154.csC) ≤ (20153747 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13152 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((20153747 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13152 : ℝ) * (163075699 / 1000000) +
        2 * (1792 / 10000 / 13152) * (93329987 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (20153747 / 200000) *
          (81 / 1000 / 13152 + (1792 / 10000 / 13152) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13152

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13152
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13152 ∧
    1 ≤ gPlus 13152 ∧ gPlus 13152 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13152 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13152 : ℝ) < √(1 - 2 / (13152 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13152 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13152 (gMinus 13152) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13152 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13152 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13152 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13152)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13152 (gMinus 13152) (gPlus 13152)
      (finiteEnergy 13152 13152 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13152 (gMinus 13152) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13152 (gMinus 13152) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13152 (gMinus 13152) (54 / 100))
    (by linarith : energyRatio 13152 (gMinus 13152) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13152 (gMinus 13152) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13152 * kappa (energyRatio 13152 (gMinus 13152) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13152) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13152 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13152 13152 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13152 13152 (11 / 1000) / √13152 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13152)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13152 * kappa (energyRatio 13152 (gMinus 13152) (54 / 100))) +
      2 * √(12 * gPlus 13152) / 13152 + finiteEnergy 13152 13152 (11 / 1000) / √13152 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13152 θ ∧ meanLowerRoot 13152 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13152 - 2 / (13152 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13152 - 2 / (13152 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13152 θ ^ 2 / gPlus 13152) - 2 / (13152 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13152 * (kappa (meanLowerRoot 13152 θ ^ 2 / gPlus 13152) -
        2 / (13152 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13152) / 13152 -
        finiteEnergy 13152 13152 (11 / 1000) / √13152 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13152 θ ^ 2 / gPlus 13152 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13152)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13152 θ ^ 2 / gPlus 13152 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13152)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13152 θ ^ 2 / gPlus 13152 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13152 ^ 2 ≤
      kappa (meanLowerRoot 13152 θ ^ 2 / gPlus 13152) - 2 / (13152 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13152 *
      (kappa (meanLowerRoot 13152 θ ^ 2 / gPlus 13152) - 2 / (13152 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13152 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13152)
    linarith
  have ht : √(12 * gPlus 13152) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13152 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13152 13152 (11 / 1000) / √13152 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13152)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13152 (gMinus 13152) (gPlus 13152)
      (finiteEnergy 13152 13152 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13152) (hτ : 0 < (paperDesignP 13152).tau0 c) :
    eR c = (2 / (mA 13152 : ℝ)) *
      normSq (BstLean.Part150.bT 13152 13152 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13152).tau0 c)) /
      (2 / (13152 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13152).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13152).tau0 c))⁻¹ •
      BstLean.Part150.bT 13152 13152 (A1 c) (A2 c) c.1.2 ((paperDesignP 13152).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13152 : ℝ)) * normSq (bR c) / (2 / (13152 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13152}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13152) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13152).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13152 : ℝ) * (paperDesignP 13152).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13152 13152 c.1.2 ((paperDesignP 13152).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13152

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13153
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13153 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13153).real (BstLean.Part211.CentreSource 13153 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13153) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13153 160 (6 / 1000)
  have hj := jS_160_le (n := 13153) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13153 160 (6 / 1000) ^ 2 * 13153 /
      (((13153 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13153 160 (6 / 1000) ^ 2 * 13153 /
      (((13153 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13153 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13153 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13153) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13153 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13153

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13153
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13153) :=
  Ethm (paperCentres 13153) ∩ Ethp (paperCentres 13153)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13153)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13153)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13153) (paperCentres 13153)
  have he : exp (-(45 / 10000 * (13153 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13153 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13153) :=
  (passEvent ∩ agentEv (paperDesignP 13153) (DirectionError 13153) ∩
    agentEv (paperDesignP 13153) (CentreSources 13153 13153)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13153)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13153) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13153) hτ
  have hC := centreSources_ret_charge_row 13153 (paperDesignP 13153) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13153)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13153) (CentreSources 13153 13153)
  direction : analyticBase ⊆ agentEv (paperDesignP 13153) (DirectionError 13153)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13153)) : Set (Ret 13153) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13153)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13153)}
    (hT : (retDist (paperCentres 13153)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13153)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13153)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13153)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13153)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13153)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13153

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13153
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13153 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13153 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13153 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13153 13153 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13153)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13153)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13153
  have hb0 := BstLean.Part150.betaJ_nonneg 13153
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13153 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13153 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13153 * BstLean.Part150.betaJ 13153) * 13153) ≤
      (163081899 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13153)) * 13153 := by gcongr <;> linarith
      _ ≤ ((163081899 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13153 * 13153 *
      (1 + BstLean.Part154.deltaChi 13153 12 + 2 / π) / BstLean.Part154.csC) ≤
      (18666707 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13153 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((18666707 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13153 : ℝ) / BstLean.Part154.csC) ≤ (50386283 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13153 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50386283 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13153 : ℝ) * (163081899 / 1000000) +
        2 * (1792 / 10000 / 13153) * (18666707 / 100000) +
        4 * (1 / 2.506628) * 1.036505 * (50386283 / 500000) *
          (81 / 1000 / 13153 + (1792 / 10000 / 13153) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13153

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13153
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13153 ∧
    1 ≤ gPlus 13153 ∧ gPlus 13153 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13153 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13153 : ℝ) < √(1 - 2 / (13153 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13153 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13153 (gMinus 13153) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13153 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13153 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13153 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13153)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13153 (gMinus 13153) (gPlus 13153)
      (finiteEnergy 13153 13153 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13153 (gMinus 13153) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13153 (gMinus 13153) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13153 (gMinus 13153) (54 / 100))
    (by linarith : energyRatio 13153 (gMinus 13153) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13153 (gMinus 13153) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13153 * kappa (energyRatio 13153 (gMinus 13153) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13153) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13153 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13153 13153 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13153 13153 (11 / 1000) / √13153 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13153)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13153 * kappa (energyRatio 13153 (gMinus 13153) (54 / 100))) +
      2 * √(12 * gPlus 13153) / 13153 + finiteEnergy 13153 13153 (11 / 1000) / √13153 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13153 θ ∧ meanLowerRoot 13153 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13153 - 2 / (13153 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13153 - 2 / (13153 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13153 θ ^ 2 / gPlus 13153) - 2 / (13153 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13153 * (kappa (meanLowerRoot 13153 θ ^ 2 / gPlus 13153) -
        2 / (13153 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13153) / 13153 -
        finiteEnergy 13153 13153 (11 / 1000) / √13153 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13153 θ ^ 2 / gPlus 13153 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13153)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13153 θ ^ 2 / gPlus 13153 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13153)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13153 θ ^ 2 / gPlus 13153 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13153 ^ 2 ≤
      kappa (meanLowerRoot 13153 θ ^ 2 / gPlus 13153) - 2 / (13153 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13153 *
      (kappa (meanLowerRoot 13153 θ ^ 2 / gPlus 13153) - 2 / (13153 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13153 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13153)
    linarith
  have ht : √(12 * gPlus 13153) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13153 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13153 13153 (11 / 1000) / √13153 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13153)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13153 (gMinus 13153) (gPlus 13153)
      (finiteEnergy 13153 13153 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13153) (hτ : 0 < (paperDesignP 13153).tau0 c) :
    eR c = (2 / (mA 13153 : ℝ)) *
      normSq (BstLean.Part150.bT 13153 13153 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13153).tau0 c)) /
      (2 / (13153 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13153).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13153).tau0 c))⁻¹ •
      BstLean.Part150.bT 13153 13153 (A1 c) (A2 c) c.1.2 ((paperDesignP 13153).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13153 : ℝ)) * normSq (bR c) / (2 / (13153 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13153}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13153) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13153).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13153 : ℝ) * (paperDesignP 13153).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13153 13153 c.1.2 ((paperDesignP 13153).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13153

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13154
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13154 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13154).real (BstLean.Part211.CentreSource 13154 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13154) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13154 160 (6 / 1000)
  have hj := jS_160_le (n := 13154) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13154 160 (6 / 1000) ^ 2 * 13154 /
      (((13154 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13154 160 (6 / 1000) ^ 2 * 13154 /
      (((13154 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13154 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13154 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13154) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13154 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13154

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13154
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13154) :=
  Ethm (paperCentres 13154) ∩ Ethp (paperCentres 13154)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13154)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13154)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13154) (paperCentres 13154)
  have he : exp (-(45 / 10000 * (13154 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13154 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13154) :=
  (passEvent ∩ agentEv (paperDesignP 13154) (DirectionError 13154) ∩
    agentEv (paperDesignP 13154) (CentreSources 13154 13154)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13154)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13154) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13154) hτ
  have hC := centreSources_ret_charge_row 13154 (paperDesignP 13154) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13154)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13154) (CentreSources 13154 13154)
  direction : analyticBase ⊆ agentEv (paperDesignP 13154) (DirectionError 13154)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13154)) : Set (Ret 13154) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13154)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13154)}
    (hT : (retDist (paperCentres 13154)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13154)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13154)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13154)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13154)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13154)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13154

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13154
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13154 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13154 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13154 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13154 13154 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13154)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13154)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13154
  have hb0 := BstLean.Part150.betaJ_nonneg 13154
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13154 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13154 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13154 * BstLean.Part150.betaJ 13154) * 13154) ≤
      (81544049 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13154)) * 13154 := by gcongr <;> linarith
      _ ≤ ((81544049 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13154 * 13154 *
      (1 + BstLean.Part154.deltaChi 13154 12 + 2 / π) / BstLean.Part154.csC) ≤
      (93337083 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13154 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((93337083 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13154 : ℝ) / BstLean.Part154.csC) ≤ (100776397 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13154 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100776397 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13154 : ℝ) * (81544049 / 500000) +
        2 * (1792 / 10000 / 13154) * (93337083 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100776397 / 1000000) *
          (81 / 1000 / 13154 + (1792 / 10000 / 13154) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13154

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13154
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13154 ∧
    1 ≤ gPlus 13154 ∧ gPlus 13154 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13154 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13154 : ℝ) < √(1 - 2 / (13154 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13154 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13154 (gMinus 13154) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13154 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13154 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13154 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13154)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13154 (gMinus 13154) (gPlus 13154)
      (finiteEnergy 13154 13154 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13154 (gMinus 13154) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13154 (gMinus 13154) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13154 (gMinus 13154) (54 / 100))
    (by linarith : energyRatio 13154 (gMinus 13154) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13154 (gMinus 13154) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13154 * kappa (energyRatio 13154 (gMinus 13154) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13154) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13154 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13154 13154 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13154 13154 (11 / 1000) / √13154 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13154)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13154 * kappa (energyRatio 13154 (gMinus 13154) (54 / 100))) +
      2 * √(12 * gPlus 13154) / 13154 + finiteEnergy 13154 13154 (11 / 1000) / √13154 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13154 θ ∧ meanLowerRoot 13154 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13154 - 2 / (13154 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13154 - 2 / (13154 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13154 θ ^ 2 / gPlus 13154) - 2 / (13154 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13154 * (kappa (meanLowerRoot 13154 θ ^ 2 / gPlus 13154) -
        2 / (13154 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13154) / 13154 -
        finiteEnergy 13154 13154 (11 / 1000) / √13154 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13154 θ ^ 2 / gPlus 13154 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13154)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13154 θ ^ 2 / gPlus 13154 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13154)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13154 θ ^ 2 / gPlus 13154 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13154 ^ 2 ≤
      kappa (meanLowerRoot 13154 θ ^ 2 / gPlus 13154) - 2 / (13154 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13154 *
      (kappa (meanLowerRoot 13154 θ ^ 2 / gPlus 13154) - 2 / (13154 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13154 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13154)
    linarith
  have ht : √(12 * gPlus 13154) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13154 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13154 13154 (11 / 1000) / √13154 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13154)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13154 (gMinus 13154) (gPlus 13154)
      (finiteEnergy 13154 13154 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13154) (hτ : 0 < (paperDesignP 13154).tau0 c) :
    eR c = (2 / (mA 13154 : ℝ)) *
      normSq (BstLean.Part150.bT 13154 13154 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13154).tau0 c)) /
      (2 / (13154 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13154).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13154).tau0 c))⁻¹ •
      BstLean.Part150.bT 13154 13154 (A1 c) (A2 c) c.1.2 ((paperDesignP 13154).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13154 : ℝ)) * normSq (bR c) / (2 / (13154 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13154}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13154) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13154).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13154 : ℝ) * (paperDesignP 13154).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13154 13154 c.1.2 ((paperDesignP 13154).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13154

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13155
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13155 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13155).real (BstLean.Part211.CentreSource 13155 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13155) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13155 160 (6 / 1000)
  have hj := jS_160_le (n := 13155) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13155 160 (6 / 1000) ^ 2 * 13155 /
      (((13155 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13155 160 (6 / 1000) ^ 2 * 13155 /
      (((13155 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13155 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13155 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13155) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13155 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13155

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13155
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13155) :=
  Ethm (paperCentres 13155) ∩ Ethp (paperCentres 13155)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13155)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13155)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13155) (paperCentres 13155)
  have he : exp (-(45 / 10000 * (13155 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13155 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13155) :=
  (passEvent ∩ agentEv (paperDesignP 13155) (DirectionError 13155) ∩
    agentEv (paperDesignP 13155) (CentreSources 13155 13155)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13155)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13155) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13155) hτ
  have hC := centreSources_ret_charge_row 13155 (paperDesignP 13155) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13155)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13155) (CentreSources 13155 13155)
  direction : analyticBase ⊆ agentEv (paperDesignP 13155) (DirectionError 13155)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13155)) : Set (Ret 13155) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13155)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13155)}
    (hT : (retDist (paperCentres 13155)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13155)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13155)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13155)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13155)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13155)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13155

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13155
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13155 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13155 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13155 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13155 13155 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13155)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13155)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13155
  have hb0 := BstLean.Part150.betaJ_nonneg 13155
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13155 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13155 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13155 * BstLean.Part150.betaJ 13155) * 13155) ≤
      (163094297 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13155)) * 13155 := by gcongr <;> linarith
      _ ≤ ((163094297 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13155 * 13155 *
      (1 + BstLean.Part154.deltaChi 13155 12 + 2 / π) / BstLean.Part154.csC) ≤
      (93340631 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13155 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((93340631 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13155 : ℝ) / BstLean.Part154.csC) ≤ (100780227 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13155 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100780227 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13155 : ℝ) * (163094297 / 1000000) +
        2 * (1792 / 10000 / 13155) * (93340631 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100780227 / 1000000) *
          (81 / 1000 / 13155 + (1792 / 10000 / 13155) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13155

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13155
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13155 ∧
    1 ≤ gPlus 13155 ∧ gPlus 13155 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13155 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13155 : ℝ) < √(1 - 2 / (13155 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13155 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13155 (gMinus 13155) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13155 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13155 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13155 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13155)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13155 (gMinus 13155) (gPlus 13155)
      (finiteEnergy 13155 13155 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13155 (gMinus 13155) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13155 (gMinus 13155) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13155 (gMinus 13155) (54 / 100))
    (by linarith : energyRatio 13155 (gMinus 13155) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13155 (gMinus 13155) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13155 * kappa (energyRatio 13155 (gMinus 13155) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13155) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13155 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13155 13155 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13155 13155 (11 / 1000) / √13155 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13155)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13155 * kappa (energyRatio 13155 (gMinus 13155) (54 / 100))) +
      2 * √(12 * gPlus 13155) / 13155 + finiteEnergy 13155 13155 (11 / 1000) / √13155 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13155 θ ∧ meanLowerRoot 13155 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13155 - 2 / (13155 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13155 - 2 / (13155 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13155 θ ^ 2 / gPlus 13155) - 2 / (13155 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13155 * (kappa (meanLowerRoot 13155 θ ^ 2 / gPlus 13155) -
        2 / (13155 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13155) / 13155 -
        finiteEnergy 13155 13155 (11 / 1000) / √13155 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13155 θ ^ 2 / gPlus 13155 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13155)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13155 θ ^ 2 / gPlus 13155 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13155)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13155 θ ^ 2 / gPlus 13155 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13155 ^ 2 ≤
      kappa (meanLowerRoot 13155 θ ^ 2 / gPlus 13155) - 2 / (13155 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13155 *
      (kappa (meanLowerRoot 13155 θ ^ 2 / gPlus 13155) - 2 / (13155 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13155 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13155)
    linarith
  have ht : √(12 * gPlus 13155) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13155 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13155 13155 (11 / 1000) / √13155 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13155)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13155 (gMinus 13155) (gPlus 13155)
      (finiteEnergy 13155 13155 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13155) (hτ : 0 < (paperDesignP 13155).tau0 c) :
    eR c = (2 / (mA 13155 : ℝ)) *
      normSq (BstLean.Part150.bT 13155 13155 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13155).tau0 c)) /
      (2 / (13155 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13155).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13155).tau0 c))⁻¹ •
      BstLean.Part150.bT 13155 13155 (A1 c) (A2 c) c.1.2 ((paperDesignP 13155).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13155 : ℝ)) * normSq (bR c) / (2 / (13155 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13155}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13155) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13155).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13155 : ℝ) * (paperDesignP 13155).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13155 13155 c.1.2 ((paperDesignP 13155).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13155

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13156
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13156 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13156).real (BstLean.Part211.CentreSource 13156 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13156) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13156 160 (6 / 1000)
  have hj := jS_160_le (n := 13156) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13156 160 (6 / 1000) ^ 2 * 13156 /
      (((13156 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13156 160 (6 / 1000) ^ 2 * 13156 /
      (((13156 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13156 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13156 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13156) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13156 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13156

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13156
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13156) :=
  Ethm (paperCentres 13156) ∩ Ethp (paperCentres 13156)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13156)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13156)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13156) (paperCentres 13156)
  have he : exp (-(45 / 10000 * (13156 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13156 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13156) :=
  (passEvent ∩ agentEv (paperDesignP 13156) (DirectionError 13156) ∩
    agentEv (paperDesignP 13156) (CentreSources 13156 13156)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13156)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13156) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13156) hτ
  have hC := centreSources_ret_charge_row 13156 (paperDesignP 13156) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13156)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13156) (CentreSources 13156 13156)
  direction : analyticBase ⊆ agentEv (paperDesignP 13156) (DirectionError 13156)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13156)) : Set (Ret 13156) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13156)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13156)}
    (hT : (retDist (paperCentres 13156)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13156)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13156)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13156)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13156)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13156)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13156

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13156
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13156 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13156 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13156 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13156 13156 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13156)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13156)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13156
  have hb0 := BstLean.Part150.betaJ_nonneg 13156
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13156 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13156 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13156 * BstLean.Part150.betaJ 13156) * 13156) ≤
      (10193781 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13156)) * 13156 := by gcongr <;> linarith
      _ ≤ ((10193781 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13156 * 13156 *
      (1 + BstLean.Part154.deltaChi 13156 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186688357 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13156 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186688357 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13156 : ℝ) / BstLean.Part154.csC) ≤ (50392029 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13156 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50392029 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13156 : ℝ) * (10193781 / 62500) +
        2 * (1792 / 10000 / 13156) * (186688357 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (50392029 / 500000) *
          (81 / 1000 / 13156 + (1792 / 10000 / 13156) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13156

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13156
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13156 ∧
    1 ≤ gPlus 13156 ∧ gPlus 13156 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13156 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13156 : ℝ) < √(1 - 2 / (13156 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13156 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13156 (gMinus 13156) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13156 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13156 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13156 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13156)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13156 (gMinus 13156) (gPlus 13156)
      (finiteEnergy 13156 13156 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13156 (gMinus 13156) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13156 (gMinus 13156) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13156 (gMinus 13156) (54 / 100))
    (by linarith : energyRatio 13156 (gMinus 13156) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13156 (gMinus 13156) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13156 * kappa (energyRatio 13156 (gMinus 13156) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13156) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13156 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13156 13156 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13156 13156 (11 / 1000) / √13156 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13156)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13156 * kappa (energyRatio 13156 (gMinus 13156) (54 / 100))) +
      2 * √(12 * gPlus 13156) / 13156 + finiteEnergy 13156 13156 (11 / 1000) / √13156 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13156 θ ∧ meanLowerRoot 13156 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13156 - 2 / (13156 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13156 - 2 / (13156 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13156 θ ^ 2 / gPlus 13156) - 2 / (13156 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13156 * (kappa (meanLowerRoot 13156 θ ^ 2 / gPlus 13156) -
        2 / (13156 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13156) / 13156 -
        finiteEnergy 13156 13156 (11 / 1000) / √13156 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13156 θ ^ 2 / gPlus 13156 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13156)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13156 θ ^ 2 / gPlus 13156 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13156)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13156 θ ^ 2 / gPlus 13156 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13156 ^ 2 ≤
      kappa (meanLowerRoot 13156 θ ^ 2 / gPlus 13156) - 2 / (13156 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13156 *
      (kappa (meanLowerRoot 13156 θ ^ 2 / gPlus 13156) - 2 / (13156 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13156 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13156)
    linarith
  have ht : √(12 * gPlus 13156) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13156 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13156 13156 (11 / 1000) / √13156 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13156)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13156 (gMinus 13156) (gPlus 13156)
      (finiteEnergy 13156 13156 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13156) (hτ : 0 < (paperDesignP 13156).tau0 c) :
    eR c = (2 / (mA 13156 : ℝ)) *
      normSq (BstLean.Part150.bT 13156 13156 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13156).tau0 c)) /
      (2 / (13156 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13156).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13156).tau0 c))⁻¹ •
      BstLean.Part150.bT 13156 13156 (A1 c) (A2 c) c.1.2 ((paperDesignP 13156).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13156 : ℝ)) * normSq (bR c) / (2 / (13156 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13156}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13156) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13156).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13156 : ℝ) * (paperDesignP 13156).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13156 13156 c.1.2 ((paperDesignP 13156).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13156

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13157
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13157 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13157).real (BstLean.Part211.CentreSource 13157 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13157) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13157 160 (6 / 1000)
  have hj := jS_160_le (n := 13157) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13157 160 (6 / 1000) ^ 2 * 13157 /
      (((13157 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13157 160 (6 / 1000) ^ 2 * 13157 /
      (((13157 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13157 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13157 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13157) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13157 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13157

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13157
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13157) :=
  Ethm (paperCentres 13157) ∩ Ethp (paperCentres 13157)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13157)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13157)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13157) (paperCentres 13157)
  have he : exp (-(45 / 10000 * (13157 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13157 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13157) :=
  (passEvent ∩ agentEv (paperDesignP 13157) (DirectionError 13157) ∩
    agentEv (paperDesignP 13157) (CentreSources 13157 13157)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13157)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13157) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13157) hτ
  have hC := centreSources_ret_charge_row 13157 (paperDesignP 13157) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13157)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13157) (CentreSources 13157 13157)
  direction : analyticBase ⊆ agentEv (paperDesignP 13157) (DirectionError 13157)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13157)) : Set (Ret 13157) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13157)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13157)}
    (hT : (retDist (paperCentres 13157)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13157)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13157)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13157)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13157)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13157)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13157

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13157
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13157 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13157 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13157 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13157 13157 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13157)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13157)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13157
  have hb0 := BstLean.Part150.betaJ_nonneg 13157
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13157 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13157 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13157 * BstLean.Part150.betaJ 13157) * 13157) ≤
      (81553347 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13157)) * 13157 := by gcongr <;> linarith
      _ ≤ ((81553347 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13157 * 13157 *
      (1 + BstLean.Part154.deltaChi 13157 12 + 2 / π) / BstLean.Part154.csC) ≤
      (46673863 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13157 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((46673863 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13157 : ℝ) / BstLean.Part154.csC) ≤ (6299243 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13157 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((6299243 / 62500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13157 : ℝ) * (81553347 / 500000) +
        2 * (1792 / 10000 / 13157) * (46673863 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (6299243 / 62500) *
          (81 / 1000 / 13157 + (1792 / 10000 / 13157) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13157

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13157
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13157 ∧
    1 ≤ gPlus 13157 ∧ gPlus 13157 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13157 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13157 : ℝ) < √(1 - 2 / (13157 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13157 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13157 (gMinus 13157) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13157 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13157 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13157 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13157)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13157 (gMinus 13157) (gPlus 13157)
      (finiteEnergy 13157 13157 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13157 (gMinus 13157) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13157 (gMinus 13157) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13157 (gMinus 13157) (54 / 100))
    (by linarith : energyRatio 13157 (gMinus 13157) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13157 (gMinus 13157) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13157 * kappa (energyRatio 13157 (gMinus 13157) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13157) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13157 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13157 13157 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13157 13157 (11 / 1000) / √13157 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13157)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13157 * kappa (energyRatio 13157 (gMinus 13157) (54 / 100))) +
      2 * √(12 * gPlus 13157) / 13157 + finiteEnergy 13157 13157 (11 / 1000) / √13157 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13157 θ ∧ meanLowerRoot 13157 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13157 - 2 / (13157 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13157 - 2 / (13157 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13157 θ ^ 2 / gPlus 13157) - 2 / (13157 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13157 * (kappa (meanLowerRoot 13157 θ ^ 2 / gPlus 13157) -
        2 / (13157 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13157) / 13157 -
        finiteEnergy 13157 13157 (11 / 1000) / √13157 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13157 θ ^ 2 / gPlus 13157 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13157)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13157 θ ^ 2 / gPlus 13157 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13157)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13157 θ ^ 2 / gPlus 13157 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13157 ^ 2 ≤
      kappa (meanLowerRoot 13157 θ ^ 2 / gPlus 13157) - 2 / (13157 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13157 *
      (kappa (meanLowerRoot 13157 θ ^ 2 / gPlus 13157) - 2 / (13157 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13157 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13157)
    linarith
  have ht : √(12 * gPlus 13157) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13157 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13157 13157 (11 / 1000) / √13157 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13157)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13157 (gMinus 13157) (gPlus 13157)
      (finiteEnergy 13157 13157 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13157) (hτ : 0 < (paperDesignP 13157).tau0 c) :
    eR c = (2 / (mA 13157 : ℝ)) *
      normSq (BstLean.Part150.bT 13157 13157 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13157).tau0 c)) /
      (2 / (13157 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13157).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13157).tau0 c))⁻¹ •
      BstLean.Part150.bT 13157 13157 (A1 c) (A2 c) c.1.2 ((paperDesignP 13157).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13157 : ℝ)) * normSq (bR c) / (2 / (13157 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13157}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13157) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13157).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13157 : ℝ) * (paperDesignP 13157).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13157 13157 c.1.2 ((paperDesignP 13157).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13157

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13158
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13158 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13158).real (BstLean.Part211.CentreSource 13158 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13158) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13158 160 (6 / 1000)
  have hj := jS_160_le (n := 13158) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13158 160 (6 / 1000) ^ 2 * 13158 /
      (((13158 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13158 160 (6 / 1000) ^ 2 * 13158 /
      (((13158 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13158 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13158 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13158) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13158 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13158

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13158
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13158) :=
  Ethm (paperCentres 13158) ∩ Ethp (paperCentres 13158)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13158)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13158)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13158) (paperCentres 13158)
  have he : exp (-(45 / 10000 * (13158 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13158 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13158) :=
  (passEvent ∩ agentEv (paperDesignP 13158) (DirectionError 13158) ∩
    agentEv (paperDesignP 13158) (CentreSources 13158 13158)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13158)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13158) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13158) hτ
  have hC := centreSources_ret_charge_row 13158 (paperDesignP 13158) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13158)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13158) (CentreSources 13158 13158)
  direction : analyticBase ⊆ agentEv (paperDesignP 13158) (DirectionError 13158)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13158)) : Set (Ret 13158) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13158)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13158)}
    (hT : (retDist (paperCentres 13158)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13158)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13158)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13158)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13158)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13158)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13158

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13158
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13158 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13158 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13158 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13158 13158 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13158)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13158)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13158
  have hb0 := BstLean.Part150.betaJ_nonneg 13158
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13158 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13158 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13158 * BstLean.Part150.betaJ 13158) * 13158) ≤
      (40778223 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13158)) * 13158 := by gcongr <;> linarith
      _ ≤ ((40778223 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13158 * 13158 *
      (1 + BstLean.Part154.deltaChi 13158 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186702547 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13158 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186702547 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13158 : ℝ) / BstLean.Part154.csC) ≤ (50395859 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13158 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50395859 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13158 : ℝ) * (40778223 / 250000) +
        2 * (1792 / 10000 / 13158) * (186702547 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (50395859 / 500000) *
          (81 / 1000 / 13158 + (1792 / 10000 / 13158) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13158

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13158
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13158 ∧
    1 ≤ gPlus 13158 ∧ gPlus 13158 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13158 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13158 : ℝ) < √(1 - 2 / (13158 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13158 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13158 (gMinus 13158) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13158 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13158 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13158 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13158)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13158 (gMinus 13158) (gPlus 13158)
      (finiteEnergy 13158 13158 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13158 (gMinus 13158) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13158 (gMinus 13158) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13158 (gMinus 13158) (54 / 100))
    (by linarith : energyRatio 13158 (gMinus 13158) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13158 (gMinus 13158) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13158 * kappa (energyRatio 13158 (gMinus 13158) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13158) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13158 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13158 13158 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13158 13158 (11 / 1000) / √13158 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13158)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13158 * kappa (energyRatio 13158 (gMinus 13158) (54 / 100))) +
      2 * √(12 * gPlus 13158) / 13158 + finiteEnergy 13158 13158 (11 / 1000) / √13158 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13158 θ ∧ meanLowerRoot 13158 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13158 - 2 / (13158 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13158 - 2 / (13158 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13158 θ ^ 2 / gPlus 13158) - 2 / (13158 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13158 * (kappa (meanLowerRoot 13158 θ ^ 2 / gPlus 13158) -
        2 / (13158 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13158) / 13158 -
        finiteEnergy 13158 13158 (11 / 1000) / √13158 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13158 θ ^ 2 / gPlus 13158 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13158)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13158 θ ^ 2 / gPlus 13158 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13158)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13158 θ ^ 2 / gPlus 13158 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13158 ^ 2 ≤
      kappa (meanLowerRoot 13158 θ ^ 2 / gPlus 13158) - 2 / (13158 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13158 *
      (kappa (meanLowerRoot 13158 θ ^ 2 / gPlus 13158) - 2 / (13158 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13158 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13158)
    linarith
  have ht : √(12 * gPlus 13158) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13158 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13158 13158 (11 / 1000) / √13158 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13158)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13158 (gMinus 13158) (gPlus 13158)
      (finiteEnergy 13158 13158 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13158) (hτ : 0 < (paperDesignP 13158).tau0 c) :
    eR c = (2 / (mA 13158 : ℝ)) *
      normSq (BstLean.Part150.bT 13158 13158 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13158).tau0 c)) /
      (2 / (13158 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13158).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13158).tau0 c))⁻¹ •
      BstLean.Part150.bT 13158 13158 (A1 c) (A2 c) c.1.2 ((paperDesignP 13158).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13158 : ℝ)) * normSq (bR c) / (2 / (13158 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13158}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13158) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13158).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13158 : ℝ) * (paperDesignP 13158).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13158 13158 c.1.2 ((paperDesignP 13158).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13158

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13159
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13159 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13159).real (BstLean.Part211.CentreSource 13159 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13159) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13159 160 (6 / 1000)
  have hj := jS_160_le (n := 13159) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13159 160 (6 / 1000) ^ 2 * 13159 /
      (((13159 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13159 160 (6 / 1000) ^ 2 * 13159 /
      (((13159 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13159 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13159 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13159) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13159 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13159

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13159
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13159) :=
  Ethm (paperCentres 13159) ∩ Ethp (paperCentres 13159)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13159)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13159)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13159) (paperCentres 13159)
  have he : exp (-(45 / 10000 * (13159 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13159 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13159) :=
  (passEvent ∩ agentEv (paperDesignP 13159) (DirectionError 13159) ∩
    agentEv (paperDesignP 13159) (CentreSources 13159 13159)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13159)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13159) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13159) hτ
  have hC := centreSources_ret_charge_row 13159 (paperDesignP 13159) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13159)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13159) (CentreSources 13159 13159)
  direction : analyticBase ⊆ agentEv (paperDesignP 13159) (DirectionError 13159)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13159)) : Set (Ret 13159) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13159)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13159)}
    (hT : (retDist (paperCentres 13159)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13159)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13159)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13159)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13159)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13159)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13159

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13159
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13159 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13159 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13159 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13159 13159 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13159)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13159)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13159
  have hb0 := BstLean.Part150.betaJ_nonneg 13159
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13159 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13159 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13159 * BstLean.Part150.betaJ 13159) * 13159) ≤
      (16311909 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13159)) * 13159 := by gcongr <;> linarith
      _ ≤ ((16311909 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13159 * 13159 *
      (1 + BstLean.Part154.deltaChi 13159 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186709641 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13159 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186709641 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13159 : ℝ) / BstLean.Part154.csC) ≤ (25198887 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13159 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((25198887 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13159 : ℝ) * (16311909 / 100000) +
        2 * (1792 / 10000 / 13159) * (186709641 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (25198887 / 250000) *
          (81 / 1000 / 13159 + (1792 / 10000 / 13159) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13159

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13159
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13159 ∧
    1 ≤ gPlus 13159 ∧ gPlus 13159 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13159 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13159 : ℝ) < √(1 - 2 / (13159 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13159 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13159 (gMinus 13159) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13159 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13159 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13159 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13159)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13159 (gMinus 13159) (gPlus 13159)
      (finiteEnergy 13159 13159 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13159 (gMinus 13159) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13159 (gMinus 13159) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13159 (gMinus 13159) (54 / 100))
    (by linarith : energyRatio 13159 (gMinus 13159) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13159 (gMinus 13159) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13159 * kappa (energyRatio 13159 (gMinus 13159) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13159) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13159 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13159 13159 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13159 13159 (11 / 1000) / √13159 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13159)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13159 * kappa (energyRatio 13159 (gMinus 13159) (54 / 100))) +
      2 * √(12 * gPlus 13159) / 13159 + finiteEnergy 13159 13159 (11 / 1000) / √13159 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13159 θ ∧ meanLowerRoot 13159 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13159 - 2 / (13159 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13159 - 2 / (13159 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13159 θ ^ 2 / gPlus 13159) - 2 / (13159 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13159 * (kappa (meanLowerRoot 13159 θ ^ 2 / gPlus 13159) -
        2 / (13159 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13159) / 13159 -
        finiteEnergy 13159 13159 (11 / 1000) / √13159 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13159 θ ^ 2 / gPlus 13159 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13159)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13159 θ ^ 2 / gPlus 13159 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13159)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13159 θ ^ 2 / gPlus 13159 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13159 ^ 2 ≤
      kappa (meanLowerRoot 13159 θ ^ 2 / gPlus 13159) - 2 / (13159 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13159 *
      (kappa (meanLowerRoot 13159 θ ^ 2 / gPlus 13159) - 2 / (13159 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13159 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13159)
    linarith
  have ht : √(12 * gPlus 13159) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13159 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13159 13159 (11 / 1000) / √13159 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13159)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13159 (gMinus 13159) (gPlus 13159)
      (finiteEnergy 13159 13159 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13159) (hτ : 0 < (paperDesignP 13159).tau0 c) :
    eR c = (2 / (mA 13159 : ℝ)) *
      normSq (BstLean.Part150.bT 13159 13159 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13159).tau0 c)) /
      (2 / (13159 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13159).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13159).tau0 c))⁻¹ •
      BstLean.Part150.bT 13159 13159 (A1 c) (A2 c) c.1.2 ((paperDesignP 13159).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13159 : ℝ)) * normSq (bR c) / (2 / (13159 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13159}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13159) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13159).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13159 : ℝ) * (paperDesignP 13159).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13159 13159 c.1.2 ((paperDesignP 13159).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13159

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13160
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13160 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13160).real (BstLean.Part211.CentreSource 13160 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13160) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13160 160 (6 / 1000)
  have hj := jS_160_le (n := 13160) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13160 160 (6 / 1000) ^ 2 * 13160 /
      (((13160 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13160 160 (6 / 1000) ^ 2 * 13160 /
      (((13160 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13160 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13160 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13160) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13160 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13160

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13160
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13160) :=
  Ethm (paperCentres 13160) ∩ Ethp (paperCentres 13160)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13160)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13160)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13160) (paperCentres 13160)
  have he : exp (-(45 / 10000 * (13160 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13160 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13160) :=
  (passEvent ∩ agentEv (paperDesignP 13160) (DirectionError 13160) ∩
    agentEv (paperDesignP 13160) (CentreSources 13160 13160)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13160)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13160) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13160) hτ
  have hC := centreSources_ret_charge_row 13160 (paperDesignP 13160) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13160)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13160) (CentreSources 13160 13160)
  direction : analyticBase ⊆ agentEv (paperDesignP 13160) (DirectionError 13160)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13160)) : Set (Ret 13160) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13160)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13160)}
    (hT : (retDist (paperCentres 13160)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13160)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13160)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13160)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13160)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13160)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13160

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13160
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13160 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13160 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13160 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13160 13160 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13160)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13160)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13160
  have hb0 := BstLean.Part150.betaJ_nonneg 13160
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13160 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13160 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13160 * BstLean.Part150.betaJ 13160) * 13160) ≤
      (20390661 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13160)) * 13160 := by gcongr <;> linarith
      _ ≤ ((20390661 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13160 * 13160 *
      (1 + BstLean.Part154.deltaChi 13160 12 + 2 / π) / BstLean.Part154.csC) ≤
      (37343347 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13160 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((37343347 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13160 : ℝ) / BstLean.Part154.csC) ≤ (50399689 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13160 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50399689 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13160 : ℝ) * (20390661 / 125000) +
        2 * (1792 / 10000 / 13160) * (37343347 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (50399689 / 500000) *
          (81 / 1000 / 13160 + (1792 / 10000 / 13160) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13160

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13160
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13160 ∧
    1 ≤ gPlus 13160 ∧ gPlus 13160 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13160 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13160 : ℝ) < √(1 - 2 / (13160 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13160 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13160 (gMinus 13160) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13160 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13160 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13160 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13160)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13160 (gMinus 13160) (gPlus 13160)
      (finiteEnergy 13160 13160 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13160 (gMinus 13160) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13160 (gMinus 13160) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13160 (gMinus 13160) (54 / 100))
    (by linarith : energyRatio 13160 (gMinus 13160) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13160 (gMinus 13160) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13160 * kappa (energyRatio 13160 (gMinus 13160) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13160) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13160 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13160 13160 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13160 13160 (11 / 1000) / √13160 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13160)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13160 * kappa (energyRatio 13160 (gMinus 13160) (54 / 100))) +
      2 * √(12 * gPlus 13160) / 13160 + finiteEnergy 13160 13160 (11 / 1000) / √13160 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13160 θ ∧ meanLowerRoot 13160 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13160 - 2 / (13160 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13160 - 2 / (13160 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13160 θ ^ 2 / gPlus 13160) - 2 / (13160 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13160 * (kappa (meanLowerRoot 13160 θ ^ 2 / gPlus 13160) -
        2 / (13160 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13160) / 13160 -
        finiteEnergy 13160 13160 (11 / 1000) / √13160 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13160 θ ^ 2 / gPlus 13160 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13160)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13160 θ ^ 2 / gPlus 13160 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13160)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13160 θ ^ 2 / gPlus 13160 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13160 ^ 2 ≤
      kappa (meanLowerRoot 13160 θ ^ 2 / gPlus 13160) - 2 / (13160 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13160 *
      (kappa (meanLowerRoot 13160 θ ^ 2 / gPlus 13160) - 2 / (13160 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13160 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13160)
    linarith
  have ht : √(12 * gPlus 13160) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13160 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13160 13160 (11 / 1000) / √13160 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13160)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13160 (gMinus 13160) (gPlus 13160)
      (finiteEnergy 13160 13160 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13160) (hτ : 0 < (paperDesignP 13160).tau0 c) :
    eR c = (2 / (mA 13160 : ℝ)) *
      normSq (BstLean.Part150.bT 13160 13160 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13160).tau0 c)) /
      (2 / (13160 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13160).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13160).tau0 c))⁻¹ •
      BstLean.Part150.bT 13160 13160 (A1 c) (A2 c) c.1.2 ((paperDesignP 13160).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13160 : ℝ)) * normSq (bR c) / (2 / (13160 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13160}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13160) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13160).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13160 : ℝ) * (paperDesignP 13160).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13160 13160 c.1.2 ((paperDesignP 13160).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13160

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13161
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13161 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13161).real (BstLean.Part211.CentreSource 13161 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13161) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13161 160 (6 / 1000)
  have hj := jS_160_le (n := 13161) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13161 160 (6 / 1000) ^ 2 * 13161 /
      (((13161 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13161 160 (6 / 1000) ^ 2 * 13161 /
      (((13161 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13161 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13161 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13161) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13161 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13161

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13161
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13161) :=
  Ethm (paperCentres 13161) ∩ Ethp (paperCentres 13161)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13161)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13161)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13161) (paperCentres 13161)
  have he : exp (-(45 / 10000 * (13161 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13161 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13161) :=
  (passEvent ∩ agentEv (paperDesignP 13161) (DirectionError 13161) ∩
    agentEv (paperDesignP 13161) (CentreSources 13161 13161)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13161)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13161) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13161) hτ
  have hC := centreSources_ret_charge_row 13161 (paperDesignP 13161) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13161)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13161) (CentreSources 13161 13161)
  direction : analyticBase ⊆ agentEv (paperDesignP 13161) (DirectionError 13161)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13161)) : Set (Ret 13161) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13161)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13161)}
    (hT : (retDist (paperCentres 13161)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13161)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13161)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13161)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13161)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13161)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13161

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13161
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13161 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13161 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13161 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13161 13161 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13161)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13161)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13161
  have hb0 := BstLean.Part150.betaJ_nonneg 13161
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13161 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13161 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13161 * BstLean.Part150.betaJ 13161) * 13161) ≤
      (81565743 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13161)) * 13161 := by gcongr <;> linarith
      _ ≤ ((81565743 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13161 * 13161 *
      (1 + BstLean.Part154.deltaChi 13161 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186723829 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13161 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186723829 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13161 : ℝ) / BstLean.Part154.csC) ≤ (12600401 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13161 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12600401 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13161 : ℝ) * (81565743 / 500000) +
        2 * (1792 / 10000 / 13161) * (186723829 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (12600401 / 125000) *
          (81 / 1000 / 13161 + (1792 / 10000 / 13161) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13161

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13161
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13161 ∧
    1 ≤ gPlus 13161 ∧ gPlus 13161 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13161 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13161 : ℝ) < √(1 - 2 / (13161 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13161 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13161 (gMinus 13161) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13161 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13161 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13161 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13161)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13161 (gMinus 13161) (gPlus 13161)
      (finiteEnergy 13161 13161 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13161 (gMinus 13161) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13161 (gMinus 13161) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13161 (gMinus 13161) (54 / 100))
    (by linarith : energyRatio 13161 (gMinus 13161) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13161 (gMinus 13161) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13161 * kappa (energyRatio 13161 (gMinus 13161) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13161) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13161 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13161 13161 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13161 13161 (11 / 1000) / √13161 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13161)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13161 * kappa (energyRatio 13161 (gMinus 13161) (54 / 100))) +
      2 * √(12 * gPlus 13161) / 13161 + finiteEnergy 13161 13161 (11 / 1000) / √13161 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13161 θ ∧ meanLowerRoot 13161 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13161 - 2 / (13161 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13161 - 2 / (13161 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13161 θ ^ 2 / gPlus 13161) - 2 / (13161 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13161 * (kappa (meanLowerRoot 13161 θ ^ 2 / gPlus 13161) -
        2 / (13161 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13161) / 13161 -
        finiteEnergy 13161 13161 (11 / 1000) / √13161 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13161 θ ^ 2 / gPlus 13161 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13161)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13161 θ ^ 2 / gPlus 13161 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13161)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13161 θ ^ 2 / gPlus 13161 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13161 ^ 2 ≤
      kappa (meanLowerRoot 13161 θ ^ 2 / gPlus 13161) - 2 / (13161 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13161 *
      (kappa (meanLowerRoot 13161 θ ^ 2 / gPlus 13161) - 2 / (13161 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13161 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13161)
    linarith
  have ht : √(12 * gPlus 13161) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13161 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13161 13161 (11 / 1000) / √13161 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13161)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13161 (gMinus 13161) (gPlus 13161)
      (finiteEnergy 13161 13161 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13161) (hτ : 0 < (paperDesignP 13161).tau0 c) :
    eR c = (2 / (mA 13161 : ℝ)) *
      normSq (BstLean.Part150.bT 13161 13161 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13161).tau0 c)) /
      (2 / (13161 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13161).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13161).tau0 c))⁻¹ •
      BstLean.Part150.bT 13161 13161 (A1 c) (A2 c) c.1.2 ((paperDesignP 13161).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13161 : ℝ)) * normSq (bR c) / (2 / (13161 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13161}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13161) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13161).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13161 : ℝ) * (paperDesignP 13161).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13161 13161 c.1.2 ((paperDesignP 13161).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13161

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13162
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13162 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13162).real (BstLean.Part211.CentreSource 13162 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13162) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13162 160 (6 / 1000)
  have hj := jS_160_le (n := 13162) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13162 160 (6 / 1000) ^ 2 * 13162 /
      (((13162 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13162 160 (6 / 1000) ^ 2 * 13162 /
      (((13162 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13162 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13162 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13162) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13162 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13162

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13162
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13162) :=
  Ethm (paperCentres 13162) ∩ Ethp (paperCentres 13162)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13162)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13162)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13162) (paperCentres 13162)
  have he : exp (-(45 / 10000 * (13162 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13162 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13162) :=
  (passEvent ∩ agentEv (paperDesignP 13162) (DirectionError 13162) ∩
    agentEv (paperDesignP 13162) (CentreSources 13162 13162)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13162)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13162) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13162) hτ
  have hC := centreSources_ret_charge_row 13162 (paperDesignP 13162) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13162)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13162) (CentreSources 13162 13162)
  direction : analyticBase ⊆ agentEv (paperDesignP 13162) (DirectionError 13162)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13162)) : Set (Ret 13162) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13162)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13162)}
    (hT : (retDist (paperCentres 13162)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13162)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13162)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13162)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13162)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13162)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13162

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13162
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13162 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13162 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13162 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13162 13162 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13162)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13162)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13162
  have hb0 := BstLean.Part150.betaJ_nonneg 13162
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13162 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13162 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13162 * BstLean.Part150.betaJ 13162) * 13162) ≤
      (163137683 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13162)) * 13162 := by gcongr <;> linarith
      _ ≤ ((163137683 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13162 * 13162 *
      (1 + BstLean.Part154.deltaChi 13162 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186730923 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13162 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186730923 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13162 : ℝ) / BstLean.Part154.csC) ≤ (100807037 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13162 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100807037 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13162 : ℝ) * (163137683 / 1000000) +
        2 * (1792 / 10000 / 13162) * (186730923 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (100807037 / 1000000) *
          (81 / 1000 / 13162 + (1792 / 10000 / 13162) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13162

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13162
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13162 ∧
    1 ≤ gPlus 13162 ∧ gPlus 13162 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13162 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13162 : ℝ) < √(1 - 2 / (13162 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13162 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13162 (gMinus 13162) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13162 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13162 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13162 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13162)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13162 (gMinus 13162) (gPlus 13162)
      (finiteEnergy 13162 13162 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13162 (gMinus 13162) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13162 (gMinus 13162) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13162 (gMinus 13162) (54 / 100))
    (by linarith : energyRatio 13162 (gMinus 13162) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13162 (gMinus 13162) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13162 * kappa (energyRatio 13162 (gMinus 13162) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13162) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13162 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13162 13162 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13162 13162 (11 / 1000) / √13162 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13162)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13162 * kappa (energyRatio 13162 (gMinus 13162) (54 / 100))) +
      2 * √(12 * gPlus 13162) / 13162 + finiteEnergy 13162 13162 (11 / 1000) / √13162 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13162 θ ∧ meanLowerRoot 13162 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13162 - 2 / (13162 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13162 - 2 / (13162 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13162 θ ^ 2 / gPlus 13162) - 2 / (13162 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13162 * (kappa (meanLowerRoot 13162 θ ^ 2 / gPlus 13162) -
        2 / (13162 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13162) / 13162 -
        finiteEnergy 13162 13162 (11 / 1000) / √13162 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13162 θ ^ 2 / gPlus 13162 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13162)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13162 θ ^ 2 / gPlus 13162 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13162)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13162 θ ^ 2 / gPlus 13162 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13162 ^ 2 ≤
      kappa (meanLowerRoot 13162 θ ^ 2 / gPlus 13162) - 2 / (13162 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13162 *
      (kappa (meanLowerRoot 13162 θ ^ 2 / gPlus 13162) - 2 / (13162 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13162 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13162)
    linarith
  have ht : √(12 * gPlus 13162) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13162 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13162 13162 (11 / 1000) / √13162 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13162)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13162 (gMinus 13162) (gPlus 13162)
      (finiteEnergy 13162 13162 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13162) (hτ : 0 < (paperDesignP 13162).tau0 c) :
    eR c = (2 / (mA 13162 : ℝ)) *
      normSq (BstLean.Part150.bT 13162 13162 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13162).tau0 c)) /
      (2 / (13162 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13162).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13162).tau0 c))⁻¹ •
      BstLean.Part150.bT 13162 13162 (A1 c) (A2 c) c.1.2 ((paperDesignP 13162).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13162 : ℝ)) * normSq (bR c) / (2 / (13162 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13162}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13162) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13162).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13162 : ℝ) * (paperDesignP 13162).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13162 13162 c.1.2 ((paperDesignP 13162).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13162

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13163
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13163 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13163).real (BstLean.Part211.CentreSource 13163 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13163) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13163 160 (6 / 1000)
  have hj := jS_160_le (n := 13163) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13163 160 (6 / 1000) ^ 2 * 13163 /
      (((13163 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13163 160 (6 / 1000) ^ 2 * 13163 /
      (((13163 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13163 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13163 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13163) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13163 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13163

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13163
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13163) :=
  Ethm (paperCentres 13163) ∩ Ethp (paperCentres 13163)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13163)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13163)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13163) (paperCentres 13163)
  have he : exp (-(45 / 10000 * (13163 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13163 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13163) :=
  (passEvent ∩ agentEv (paperDesignP 13163) (DirectionError 13163) ∩
    agentEv (paperDesignP 13163) (CentreSources 13163 13163)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13163)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13163) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13163) hτ
  have hC := centreSources_ret_charge_row 13163 (paperDesignP 13163) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13163)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13163) (CentreSources 13163 13163)
  direction : analyticBase ⊆ agentEv (paperDesignP 13163) (DirectionError 13163)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13163)) : Set (Ret 13163) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13163)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13163)}
    (hT : (retDist (paperCentres 13163)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13163)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13163)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13163)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13163)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13163)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13163

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13163
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13163 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13163 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13163 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13163 13163 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13163)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13163)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13163
  have hb0 := BstLean.Part150.betaJ_nonneg 13163
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13163 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13163 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13163 * BstLean.Part150.betaJ 13163) * 13163) ≤
      (4078597 / 25000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13163)) * 13163 := by gcongr <;> linarith
      _ ≤ ((4078597 / 25000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13163 * 13163 *
      (1 + BstLean.Part154.deltaChi 13163 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186738017 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13163 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186738017 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13163 : ℝ) / BstLean.Part154.csC) ≤ (100810867 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13163 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100810867 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13163 : ℝ) * (4078597 / 25000) +
        2 * (1792 / 10000 / 13163) * (186738017 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (100810867 / 1000000) *
          (81 / 1000 / 13163 + (1792 / 10000 / 13163) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13163

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13163
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13163 ∧
    1 ≤ gPlus 13163 ∧ gPlus 13163 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13163 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13163 : ℝ) < √(1 - 2 / (13163 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13163 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13163 (gMinus 13163) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13163 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13163 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13163 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13163)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13163 (gMinus 13163) (gPlus 13163)
      (finiteEnergy 13163 13163 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13163 (gMinus 13163) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13163 (gMinus 13163) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13163 (gMinus 13163) (54 / 100))
    (by linarith : energyRatio 13163 (gMinus 13163) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13163 (gMinus 13163) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13163 * kappa (energyRatio 13163 (gMinus 13163) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13163) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13163 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13163 13163 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13163 13163 (11 / 1000) / √13163 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13163)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13163 * kappa (energyRatio 13163 (gMinus 13163) (54 / 100))) +
      2 * √(12 * gPlus 13163) / 13163 + finiteEnergy 13163 13163 (11 / 1000) / √13163 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13163 θ ∧ meanLowerRoot 13163 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13163 - 2 / (13163 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13163 - 2 / (13163 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13163 θ ^ 2 / gPlus 13163) - 2 / (13163 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13163 * (kappa (meanLowerRoot 13163 θ ^ 2 / gPlus 13163) -
        2 / (13163 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13163) / 13163 -
        finiteEnergy 13163 13163 (11 / 1000) / √13163 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13163 θ ^ 2 / gPlus 13163 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13163)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13163 θ ^ 2 / gPlus 13163 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13163)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13163 θ ^ 2 / gPlus 13163 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13163 ^ 2 ≤
      kappa (meanLowerRoot 13163 θ ^ 2 / gPlus 13163) - 2 / (13163 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13163 *
      (kappa (meanLowerRoot 13163 θ ^ 2 / gPlus 13163) - 2 / (13163 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13163 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13163)
    linarith
  have ht : √(12 * gPlus 13163) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13163 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13163 13163 (11 / 1000) / √13163 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13163)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13163 (gMinus 13163) (gPlus 13163)
      (finiteEnergy 13163 13163 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13163) (hτ : 0 < (paperDesignP 13163).tau0 c) :
    eR c = (2 / (mA 13163 : ℝ)) *
      normSq (BstLean.Part150.bT 13163 13163 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13163).tau0 c)) /
      (2 / (13163 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13163).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13163).tau0 c))⁻¹ •
      BstLean.Part150.bT 13163 13163 (A1 c) (A2 c) c.1.2 ((paperDesignP 13163).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13163 : ℝ)) * normSq (bR c) / (2 / (13163 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13163}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13163) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13163).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13163 : ℝ) * (paperDesignP 13163).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13163 13163 c.1.2 ((paperDesignP 13163).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13163

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13164
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13164 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13164).real (BstLean.Part211.CentreSource 13164 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13164) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13164 160 (6 / 1000)
  have hj := jS_160_le (n := 13164) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13164 160 (6 / 1000) ^ 2 * 13164 /
      (((13164 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13164 160 (6 / 1000) ^ 2 * 13164 /
      (((13164 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13164 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13164 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13164) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13164 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13164

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13164
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13164) :=
  Ethm (paperCentres 13164) ∩ Ethp (paperCentres 13164)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13164)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13164)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13164) (paperCentres 13164)
  have he : exp (-(45 / 10000 * (13164 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13164 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13164) :=
  (passEvent ∩ agentEv (paperDesignP 13164) (DirectionError 13164) ∩
    agentEv (paperDesignP 13164) (CentreSources 13164 13164)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13164)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13164) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13164) hτ
  have hC := centreSources_ret_charge_row 13164 (paperDesignP 13164) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13164)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13164) (CentreSources 13164 13164)
  direction : analyticBase ⊆ agentEv (paperDesignP 13164) (DirectionError 13164)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13164)) : Set (Ret 13164) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13164)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13164)}
    (hT : (retDist (paperCentres 13164)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13164)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13164)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13164)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13164)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13164)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13164

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13164
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13164 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13164 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13164 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13164 13164 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13164)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13164)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13164
  have hb0 := BstLean.Part150.betaJ_nonneg 13164
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13164 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13164 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13164 * BstLean.Part150.betaJ 13164) * 13164) ≤
      (163150077 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13164)) * 13164 := by gcongr <;> linarith
      _ ≤ ((163150077 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13164 * 13164 *
      (1 + BstLean.Part154.deltaChi 13164 12 + 2 / π) / BstLean.Part154.csC) ≤
      (18674511 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13164 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((18674511 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13164 : ℝ) / BstLean.Part154.csC) ≤ (12601837 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13164 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12601837 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13164 : ℝ) * (163150077 / 1000000) +
        2 * (1792 / 10000 / 13164) * (18674511 / 100000) +
        4 * (1 / 2.506628) * 1.036505 * (12601837 / 125000) *
          (81 / 1000 / 13164 + (1792 / 10000 / 13164) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13164

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13164
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13164 ∧
    1 ≤ gPlus 13164 ∧ gPlus 13164 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13164 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13164 : ℝ) < √(1 - 2 / (13164 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13164 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13164 (gMinus 13164) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13164 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13164 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13164 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13164)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13164 (gMinus 13164) (gPlus 13164)
      (finiteEnergy 13164 13164 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13164 (gMinus 13164) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13164 (gMinus 13164) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13164 (gMinus 13164) (54 / 100))
    (by linarith : energyRatio 13164 (gMinus 13164) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13164 (gMinus 13164) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13164 * kappa (energyRatio 13164 (gMinus 13164) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13164) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13164 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13164 13164 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13164 13164 (11 / 1000) / √13164 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13164)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13164 * kappa (energyRatio 13164 (gMinus 13164) (54 / 100))) +
      2 * √(12 * gPlus 13164) / 13164 + finiteEnergy 13164 13164 (11 / 1000) / √13164 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13164 θ ∧ meanLowerRoot 13164 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13164 - 2 / (13164 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13164 - 2 / (13164 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13164 θ ^ 2 / gPlus 13164) - 2 / (13164 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13164 * (kappa (meanLowerRoot 13164 θ ^ 2 / gPlus 13164) -
        2 / (13164 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13164) / 13164 -
        finiteEnergy 13164 13164 (11 / 1000) / √13164 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13164 θ ^ 2 / gPlus 13164 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13164)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13164 θ ^ 2 / gPlus 13164 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13164)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13164 θ ^ 2 / gPlus 13164 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13164 ^ 2 ≤
      kappa (meanLowerRoot 13164 θ ^ 2 / gPlus 13164) - 2 / (13164 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13164 *
      (kappa (meanLowerRoot 13164 θ ^ 2 / gPlus 13164) - 2 / (13164 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13164 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13164)
    linarith
  have ht : √(12 * gPlus 13164) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13164 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13164 13164 (11 / 1000) / √13164 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13164)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13164 (gMinus 13164) (gPlus 13164)
      (finiteEnergy 13164 13164 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13164) (hτ : 0 < (paperDesignP 13164).tau0 c) :
    eR c = (2 / (mA 13164 : ℝ)) *
      normSq (BstLean.Part150.bT 13164 13164 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13164).tau0 c)) /
      (2 / (13164 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13164).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13164).tau0 c))⁻¹ •
      BstLean.Part150.bT 13164 13164 (A1 c) (A2 c) c.1.2 ((paperDesignP 13164).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13164 : ℝ)) * normSq (bR c) / (2 / (13164 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13164}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13164) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13164).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13164 : ℝ) * (paperDesignP 13164).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13164 13164 c.1.2 ((paperDesignP 13164).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13164

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13165
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13165 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13165).real (BstLean.Part211.CentreSource 13165 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13165) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13165 160 (6 / 1000)
  have hj := jS_160_le (n := 13165) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13165 160 (6 / 1000) ^ 2 * 13165 /
      (((13165 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13165 160 (6 / 1000) ^ 2 * 13165 /
      (((13165 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13165 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13165 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13165) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13165 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13165

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13165
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13165) :=
  Ethm (paperCentres 13165) ∩ Ethp (paperCentres 13165)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13165)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13165)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13165) (paperCentres 13165)
  have he : exp (-(45 / 10000 * (13165 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13165 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13165) :=
  (passEvent ∩ agentEv (paperDesignP 13165) (DirectionError 13165) ∩
    agentEv (paperDesignP 13165) (CentreSources 13165 13165)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13165)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13165) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13165) hτ
  have hC := centreSources_ret_charge_row 13165 (paperDesignP 13165) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13165)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13165) (CentreSources 13165 13165)
  direction : analyticBase ⊆ agentEv (paperDesignP 13165) (DirectionError 13165)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13165)) : Set (Ret 13165) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13165)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13165)}
    (hT : (retDist (paperCentres 13165)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13165)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13165)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13165)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13165)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13165)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13165

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13165
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13165 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13165 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13165 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13165 13165 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13165)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13165)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13165
  have hb0 := BstLean.Part150.betaJ_nonneg 13165
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13165 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13165 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13165 * BstLean.Part150.betaJ 13165) * 13165) ≤
      (81578137 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13165)) * 13165 := by gcongr <;> linarith
      _ ≤ ((81578137 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13165 * 13165 *
      (1 + BstLean.Part154.deltaChi 13165 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186752203 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13165 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186752203 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13165 : ℝ) / BstLean.Part154.csC) ≤ (4032741 / 40000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13165 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((4032741 / 40000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13165 : ℝ) * (81578137 / 500000) +
        2 * (1792 / 10000 / 13165) * (186752203 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (4032741 / 40000) *
          (81 / 1000 / 13165 + (1792 / 10000 / 13165) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13165

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13165
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13165 ∧
    1 ≤ gPlus 13165 ∧ gPlus 13165 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13165 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13165 : ℝ) < √(1 - 2 / (13165 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13165 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13165 (gMinus 13165) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13165 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13165 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13165 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13165)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13165 (gMinus 13165) (gPlus 13165)
      (finiteEnergy 13165 13165 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13165 (gMinus 13165) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13165 (gMinus 13165) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13165 (gMinus 13165) (54 / 100))
    (by linarith : energyRatio 13165 (gMinus 13165) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13165 (gMinus 13165) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13165 * kappa (energyRatio 13165 (gMinus 13165) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13165) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13165 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13165 13165 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13165 13165 (11 / 1000) / √13165 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13165)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13165 * kappa (energyRatio 13165 (gMinus 13165) (54 / 100))) +
      2 * √(12 * gPlus 13165) / 13165 + finiteEnergy 13165 13165 (11 / 1000) / √13165 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13165 θ ∧ meanLowerRoot 13165 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13165 - 2 / (13165 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13165 - 2 / (13165 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13165 θ ^ 2 / gPlus 13165) - 2 / (13165 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13165 * (kappa (meanLowerRoot 13165 θ ^ 2 / gPlus 13165) -
        2 / (13165 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13165) / 13165 -
        finiteEnergy 13165 13165 (11 / 1000) / √13165 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13165 θ ^ 2 / gPlus 13165 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13165)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13165 θ ^ 2 / gPlus 13165 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13165)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13165 θ ^ 2 / gPlus 13165 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13165 ^ 2 ≤
      kappa (meanLowerRoot 13165 θ ^ 2 / gPlus 13165) - 2 / (13165 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13165 *
      (kappa (meanLowerRoot 13165 θ ^ 2 / gPlus 13165) - 2 / (13165 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13165 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13165)
    linarith
  have ht : √(12 * gPlus 13165) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13165 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13165 13165 (11 / 1000) / √13165 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13165)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13165 (gMinus 13165) (gPlus 13165)
      (finiteEnergy 13165 13165 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13165) (hτ : 0 < (paperDesignP 13165).tau0 c) :
    eR c = (2 / (mA 13165 : ℝ)) *
      normSq (BstLean.Part150.bT 13165 13165 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13165).tau0 c)) /
      (2 / (13165 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13165).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13165).tau0 c))⁻¹ •
      BstLean.Part150.bT 13165 13165 (A1 c) (A2 c) c.1.2 ((paperDesignP 13165).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13165 : ℝ)) * normSq (bR c) / (2 / (13165 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13165}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13165) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13165).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13165 : ℝ) * (paperDesignP 13165).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13165 13165 c.1.2 ((paperDesignP 13165).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13165

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13166
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13166 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13166).real (BstLean.Part211.CentreSource 13166 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13166) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13166 160 (6 / 1000)
  have hj := jS_160_le (n := 13166) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13166 160 (6 / 1000) ^ 2 * 13166 /
      (((13166 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13166 160 (6 / 1000) ^ 2 * 13166 /
      (((13166 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13166 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13166 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13166) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13166 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13166

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13166
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13166) :=
  Ethm (paperCentres 13166) ∩ Ethp (paperCentres 13166)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13166)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13166)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13166) (paperCentres 13166)
  have he : exp (-(45 / 10000 * (13166 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13166 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13166) :=
  (passEvent ∩ agentEv (paperDesignP 13166) (DirectionError 13166) ∩
    agentEv (paperDesignP 13166) (CentreSources 13166 13166)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13166)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13166) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13166) hτ
  have hC := centreSources_ret_charge_row 13166 (paperDesignP 13166) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13166)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13166) (CentreSources 13166 13166)
  direction : analyticBase ⊆ agentEv (paperDesignP 13166) (DirectionError 13166)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13166)) : Set (Ret 13166) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13166)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13166)}
    (hT : (retDist (paperCentres 13166)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13166)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13166)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13166)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13166)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13166)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13166

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13166
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13166 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13166 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13166 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13166 13166 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13166)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13166)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13166
  have hb0 := BstLean.Part150.betaJ_nonneg 13166
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13166 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13166 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13166 * BstLean.Part150.betaJ 13166) * 13166) ≤
      (16316247 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13166)) * 13166 := by gcongr <;> linarith
      _ ≤ ((16316247 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13166 * 13166 *
      (1 + BstLean.Part154.deltaChi 13166 12 + 2 / π) / BstLean.Part154.csC) ≤
      (37351859 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13166 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((37351859 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13166 : ℝ) / BstLean.Part154.csC) ≤ (50411177 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13166 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50411177 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13166 : ℝ) * (16316247 / 100000) +
        2 * (1792 / 10000 / 13166) * (37351859 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (50411177 / 500000) *
          (81 / 1000 / 13166 + (1792 / 10000 / 13166) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13166

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13166
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13166 ∧
    1 ≤ gPlus 13166 ∧ gPlus 13166 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13166 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13166 : ℝ) < √(1 - 2 / (13166 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13166 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13166 (gMinus 13166) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13166 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13166 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13166 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13166)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13166 (gMinus 13166) (gPlus 13166)
      (finiteEnergy 13166 13166 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13166 (gMinus 13166) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13166 (gMinus 13166) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13166 (gMinus 13166) (54 / 100))
    (by linarith : energyRatio 13166 (gMinus 13166) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13166 (gMinus 13166) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13166 * kappa (energyRatio 13166 (gMinus 13166) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13166) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13166 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13166 13166 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13166 13166 (11 / 1000) / √13166 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13166)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13166 * kappa (energyRatio 13166 (gMinus 13166) (54 / 100))) +
      2 * √(12 * gPlus 13166) / 13166 + finiteEnergy 13166 13166 (11 / 1000) / √13166 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13166 θ ∧ meanLowerRoot 13166 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13166 - 2 / (13166 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13166 - 2 / (13166 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13166 θ ^ 2 / gPlus 13166) - 2 / (13166 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13166 * (kappa (meanLowerRoot 13166 θ ^ 2 / gPlus 13166) -
        2 / (13166 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13166) / 13166 -
        finiteEnergy 13166 13166 (11 / 1000) / √13166 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13166 θ ^ 2 / gPlus 13166 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13166)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13166 θ ^ 2 / gPlus 13166 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13166)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13166 θ ^ 2 / gPlus 13166 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13166 ^ 2 ≤
      kappa (meanLowerRoot 13166 θ ^ 2 / gPlus 13166) - 2 / (13166 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13166 *
      (kappa (meanLowerRoot 13166 θ ^ 2 / gPlus 13166) - 2 / (13166 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13166 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13166)
    linarith
  have ht : √(12 * gPlus 13166) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13166 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13166 13166 (11 / 1000) / √13166 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13166)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13166 (gMinus 13166) (gPlus 13166)
      (finiteEnergy 13166 13166 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13166) (hτ : 0 < (paperDesignP 13166).tau0 c) :
    eR c = (2 / (mA 13166 : ℝ)) *
      normSq (BstLean.Part150.bT 13166 13166 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13166).tau0 c)) /
      (2 / (13166 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13166).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13166).tau0 c))⁻¹ •
      BstLean.Part150.bT 13166 13166 (A1 c) (A2 c) c.1.2 ((paperDesignP 13166).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13166 : ℝ)) * normSq (bR c) / (2 / (13166 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13166}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13166) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13166).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13166 : ℝ) * (paperDesignP 13166).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13166 13166 c.1.2 ((paperDesignP 13166).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13166

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13167
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13167 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13167).real (BstLean.Part211.CentreSource 13167 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13167) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13167 160 (6 / 1000)
  have hj := jS_160_le (n := 13167) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13167 160 (6 / 1000) ^ 2 * 13167 /
      (((13167 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13167 160 (6 / 1000) ^ 2 * 13167 /
      (((13167 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13167 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13167 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13167) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13167 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13167

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13167
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13167) :=
  Ethm (paperCentres 13167) ∩ Ethp (paperCentres 13167)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13167)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13167)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13167) (paperCentres 13167)
  have he : exp (-(45 / 10000 * (13167 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13167 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13167) :=
  (passEvent ∩ agentEv (paperDesignP 13167) (DirectionError 13167) ∩
    agentEv (paperDesignP 13167) (CentreSources 13167 13167)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13167)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13167) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13167) hτ
  have hC := centreSources_ret_charge_row 13167 (paperDesignP 13167) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13167)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13167) (CentreSources 13167 13167)
  direction : analyticBase ⊆ agentEv (paperDesignP 13167) (DirectionError 13167)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13167)) : Set (Ret 13167) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13167)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13167)}
    (hT : (retDist (paperCentres 13167)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13167)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13167)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13167)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13167)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13167)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13167

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13167
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13167 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13167 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13167 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13167 13167 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13167)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13167)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13167
  have hb0 := BstLean.Part150.betaJ_nonneg 13167
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13167 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13167 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13167 * BstLean.Part150.betaJ 13167) * 13167) ≤
      (81584333 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13167)) * 13167 := by gcongr <;> linarith
      _ ≤ ((81584333 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13167 * 13167 *
      (1 + BstLean.Part154.deltaChi 13167 12 + 2 / π) / BstLean.Part154.csC) ≤
      (46691597 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13167 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((46691597 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13167 : ℝ) / BstLean.Part154.csC) ≤ (100826183 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13167 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100826183 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13167 : ℝ) * (81584333 / 500000) +
        2 * (1792 / 10000 / 13167) * (46691597 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (100826183 / 1000000) *
          (81 / 1000 / 13167 + (1792 / 10000 / 13167) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13167

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13167
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13167 ∧
    1 ≤ gPlus 13167 ∧ gPlus 13167 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13167 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13167 : ℝ) < √(1 - 2 / (13167 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13167 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13167 (gMinus 13167) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13167 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13167 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13167 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13167)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13167 (gMinus 13167) (gPlus 13167)
      (finiteEnergy 13167 13167 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13167 (gMinus 13167) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13167 (gMinus 13167) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13167 (gMinus 13167) (54 / 100))
    (by linarith : energyRatio 13167 (gMinus 13167) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13167 (gMinus 13167) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13167 * kappa (energyRatio 13167 (gMinus 13167) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13167) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13167 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13167 13167 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13167 13167 (11 / 1000) / √13167 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13167)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13167 * kappa (energyRatio 13167 (gMinus 13167) (54 / 100))) +
      2 * √(12 * gPlus 13167) / 13167 + finiteEnergy 13167 13167 (11 / 1000) / √13167 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13167 θ ∧ meanLowerRoot 13167 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13167 - 2 / (13167 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13167 - 2 / (13167 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13167 θ ^ 2 / gPlus 13167) - 2 / (13167 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13167 * (kappa (meanLowerRoot 13167 θ ^ 2 / gPlus 13167) -
        2 / (13167 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13167) / 13167 -
        finiteEnergy 13167 13167 (11 / 1000) / √13167 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13167 θ ^ 2 / gPlus 13167 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13167)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13167 θ ^ 2 / gPlus 13167 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13167)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13167 θ ^ 2 / gPlus 13167 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13167 ^ 2 ≤
      kappa (meanLowerRoot 13167 θ ^ 2 / gPlus 13167) - 2 / (13167 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13167 *
      (kappa (meanLowerRoot 13167 θ ^ 2 / gPlus 13167) - 2 / (13167 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13167 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13167)
    linarith
  have ht : √(12 * gPlus 13167) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13167 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13167 13167 (11 / 1000) / √13167 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13167)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13167 (gMinus 13167) (gPlus 13167)
      (finiteEnergy 13167 13167 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13167) (hτ : 0 < (paperDesignP 13167).tau0 c) :
    eR c = (2 / (mA 13167 : ℝ)) *
      normSq (BstLean.Part150.bT 13167 13167 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13167).tau0 c)) /
      (2 / (13167 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13167).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13167).tau0 c))⁻¹ •
      BstLean.Part150.bT 13167 13167 (A1 c) (A2 c) c.1.2 ((paperDesignP 13167).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13167 : ℝ)) * normSq (bR c) / (2 / (13167 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13167}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13167) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13167).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13167 : ℝ) * (paperDesignP 13167).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13167 13167 c.1.2 ((paperDesignP 13167).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13167

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13168
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13168 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13168).real (BstLean.Part211.CentreSource 13168 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13168) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13168 160 (6 / 1000)
  have hj := jS_160_le (n := 13168) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13168 160 (6 / 1000) ^ 2 * 13168 /
      (((13168 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13168 160 (6 / 1000) ^ 2 * 13168 /
      (((13168 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13168 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13168 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13168) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13168 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13168

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13168
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13168) :=
  Ethm (paperCentres 13168) ∩ Ethp (paperCentres 13168)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13168)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13168)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13168) (paperCentres 13168)
  have he : exp (-(45 / 10000 * (13168 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13168 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13168) :=
  (passEvent ∩ agentEv (paperDesignP 13168) (DirectionError 13168) ∩
    agentEv (paperDesignP 13168) (CentreSources 13168 13168)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13168)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13168) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13168) hτ
  have hC := centreSources_ret_charge_row 13168 (paperDesignP 13168) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13168)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13168) (CentreSources 13168 13168)
  direction : analyticBase ⊆ agentEv (paperDesignP 13168) (DirectionError 13168)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13168)) : Set (Ret 13168) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13168)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13168)}
    (hT : (retDist (paperCentres 13168)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13168)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13168)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13168)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13168)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13168)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13168

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13168
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13168 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13168 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13168 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13168 13168 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13168)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13168)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13168
  have hb0 := BstLean.Part150.betaJ_nonneg 13168
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13168 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13168 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13168 * BstLean.Part150.betaJ 13168) * 13168) ≤
      (81587431 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13168)) * 13168 := by gcongr <;> linarith
      _ ≤ ((81587431 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13168 * 13168 *
      (1 + BstLean.Part154.deltaChi 13168 12 + 2 / π) / BstLean.Part154.csC) ≤
      (4669337 / 25000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13168 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((4669337 / 25000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13168 : ℝ) / BstLean.Part154.csC) ≤ (100830011 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13168 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100830011 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13168 : ℝ) * (81587431 / 500000) +
        2 * (1792 / 10000 / 13168) * (4669337 / 25000) +
        4 * (1 / 2.506628) * 1.036505 * (100830011 / 1000000) *
          (81 / 1000 / 13168 + (1792 / 10000 / 13168) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13168

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13168
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13168 ∧
    1 ≤ gPlus 13168 ∧ gPlus 13168 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13168 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13168 : ℝ) < √(1 - 2 / (13168 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13168 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13168 (gMinus 13168) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13168 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13168 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13168 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13168)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13168 (gMinus 13168) (gPlus 13168)
      (finiteEnergy 13168 13168 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13168 (gMinus 13168) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13168 (gMinus 13168) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13168 (gMinus 13168) (54 / 100))
    (by linarith : energyRatio 13168 (gMinus 13168) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13168 (gMinus 13168) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13168 * kappa (energyRatio 13168 (gMinus 13168) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13168) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13168 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13168 13168 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13168 13168 (11 / 1000) / √13168 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13168)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13168 * kappa (energyRatio 13168 (gMinus 13168) (54 / 100))) +
      2 * √(12 * gPlus 13168) / 13168 + finiteEnergy 13168 13168 (11 / 1000) / √13168 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13168 θ ∧ meanLowerRoot 13168 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13168 - 2 / (13168 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13168 - 2 / (13168 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13168 θ ^ 2 / gPlus 13168) - 2 / (13168 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13168 * (kappa (meanLowerRoot 13168 θ ^ 2 / gPlus 13168) -
        2 / (13168 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13168) / 13168 -
        finiteEnergy 13168 13168 (11 / 1000) / √13168 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13168 θ ^ 2 / gPlus 13168 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13168)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13168 θ ^ 2 / gPlus 13168 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13168)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13168 θ ^ 2 / gPlus 13168 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13168 ^ 2 ≤
      kappa (meanLowerRoot 13168 θ ^ 2 / gPlus 13168) - 2 / (13168 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13168 *
      (kappa (meanLowerRoot 13168 θ ^ 2 / gPlus 13168) - 2 / (13168 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13168 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13168)
    linarith
  have ht : √(12 * gPlus 13168) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13168 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13168 13168 (11 / 1000) / √13168 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13168)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13168 (gMinus 13168) (gPlus 13168)
      (finiteEnergy 13168 13168 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13168) (hτ : 0 < (paperDesignP 13168).tau0 c) :
    eR c = (2 / (mA 13168 : ℝ)) *
      normSq (BstLean.Part150.bT 13168 13168 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13168).tau0 c)) /
      (2 / (13168 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13168).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13168).tau0 c))⁻¹ •
      BstLean.Part150.bT 13168 13168 (A1 c) (A2 c) c.1.2 ((paperDesignP 13168).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13168 : ℝ)) * normSq (bR c) / (2 / (13168 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13168}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13168) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13168).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13168 : ℝ) * (paperDesignP 13168).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13168 13168 c.1.2 ((paperDesignP 13168).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13168

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13169
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13169 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13169).real (BstLean.Part211.CentreSource 13169 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13169) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13169 160 (6 / 1000)
  have hj := jS_160_le (n := 13169) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13169 160 (6 / 1000) ^ 2 * 13169 /
      (((13169 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13169 160 (6 / 1000) ^ 2 * 13169 /
      (((13169 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13169 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13169 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13169) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13169 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13169

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13169
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13169) :=
  Ethm (paperCentres 13169) ∩ Ethp (paperCentres 13169)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13169)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13169)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13169) (paperCentres 13169)
  have he : exp (-(45 / 10000 * (13169 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13169 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13169) :=
  (passEvent ∩ agentEv (paperDesignP 13169) (DirectionError 13169) ∩
    agentEv (paperDesignP 13169) (CentreSources 13169 13169)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13169)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13169) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13169) hτ
  have hC := centreSources_ret_charge_row 13169 (paperDesignP 13169) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13169)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13169) (CentreSources 13169 13169)
  direction : analyticBase ⊆ agentEv (paperDesignP 13169) (DirectionError 13169)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13169)) : Set (Ret 13169) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13169)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13169)}
    (hT : (retDist (paperCentres 13169)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13169)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13169)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13169)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13169)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13169)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13169

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13169
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13169 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13169 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13169 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13169 13169 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13169)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13169)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13169
  have hb0 := BstLean.Part150.betaJ_nonneg 13169
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13169 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13169 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13169 * BstLean.Part150.betaJ 13169) * 13169) ≤
      (81590529 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13169)) * 13169 := by gcongr <;> linarith
      _ ≤ ((81590529 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13169 * 13169 *
      (1 + BstLean.Part154.deltaChi 13169 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186780571 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13169 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186780571 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13169 : ℝ) / BstLean.Part154.csC) ≤ (1260423 / 12500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13169 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((1260423 / 12500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13169 : ℝ) * (81590529 / 500000) +
        2 * (1792 / 10000 / 13169) * (186780571 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (1260423 / 12500) *
          (81 / 1000 / 13169 + (1792 / 10000 / 13169) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13169

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13169
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13169 ∧
    1 ≤ gPlus 13169 ∧ gPlus 13169 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13169 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13169 : ℝ) < √(1 - 2 / (13169 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13169 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13169 (gMinus 13169) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13169 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13169 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13169 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13169)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13169 (gMinus 13169) (gPlus 13169)
      (finiteEnergy 13169 13169 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13169 (gMinus 13169) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13169 (gMinus 13169) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13169 (gMinus 13169) (54 / 100))
    (by linarith : energyRatio 13169 (gMinus 13169) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13169 (gMinus 13169) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13169 * kappa (energyRatio 13169 (gMinus 13169) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13169) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13169 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13169 13169 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13169 13169 (11 / 1000) / √13169 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13169)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13169 * kappa (energyRatio 13169 (gMinus 13169) (54 / 100))) +
      2 * √(12 * gPlus 13169) / 13169 + finiteEnergy 13169 13169 (11 / 1000) / √13169 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13169 θ ∧ meanLowerRoot 13169 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13169 - 2 / (13169 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13169 - 2 / (13169 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13169 θ ^ 2 / gPlus 13169) - 2 / (13169 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13169 * (kappa (meanLowerRoot 13169 θ ^ 2 / gPlus 13169) -
        2 / (13169 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13169) / 13169 -
        finiteEnergy 13169 13169 (11 / 1000) / √13169 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13169 θ ^ 2 / gPlus 13169 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13169)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13169 θ ^ 2 / gPlus 13169 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13169)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13169 θ ^ 2 / gPlus 13169 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13169 ^ 2 ≤
      kappa (meanLowerRoot 13169 θ ^ 2 / gPlus 13169) - 2 / (13169 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13169 *
      (kappa (meanLowerRoot 13169 θ ^ 2 / gPlus 13169) - 2 / (13169 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13169 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13169)
    linarith
  have ht : √(12 * gPlus 13169) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13169 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13169 13169 (11 / 1000) / √13169 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13169)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13169 (gMinus 13169) (gPlus 13169)
      (finiteEnergy 13169 13169 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13169) (hτ : 0 < (paperDesignP 13169).tau0 c) :
    eR c = (2 / (mA 13169 : ℝ)) *
      normSq (BstLean.Part150.bT 13169 13169 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13169).tau0 c)) /
      (2 / (13169 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13169).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13169).tau0 c))⁻¹ •
      BstLean.Part150.bT 13169 13169 (A1 c) (A2 c) c.1.2 ((paperDesignP 13169).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13169 : ℝ)) * normSq (bR c) / (2 / (13169 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13169}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13169) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13169).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13169 : ℝ) * (paperDesignP 13169).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13169 13169 c.1.2 ((paperDesignP 13169).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13169

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13170
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13170 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13170).real (BstLean.Part211.CentreSource 13170 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13170) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13170 160 (6 / 1000)
  have hj := jS_160_le (n := 13170) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13170 160 (6 / 1000) ^ 2 * 13170 /
      (((13170 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13170 160 (6 / 1000) ^ 2 * 13170 /
      (((13170 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13170 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13170 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13170) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13170 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13170

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13170
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13170) :=
  Ethm (paperCentres 13170) ∩ Ethp (paperCentres 13170)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13170)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13170)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13170) (paperCentres 13170)
  have he : exp (-(45 / 10000 * (13170 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13170 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13170) :=
  (passEvent ∩ agentEv (paperDesignP 13170) (DirectionError 13170) ∩
    agentEv (paperDesignP 13170) (CentreSources 13170 13170)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13170)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13170) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13170) hτ
  have hC := centreSources_ret_charge_row 13170 (paperDesignP 13170) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13170)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13170) (CentreSources 13170 13170)
  direction : analyticBase ⊆ agentEv (paperDesignP 13170) (DirectionError 13170)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13170)) : Set (Ret 13170) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13170)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13170)}
    (hT : (retDist (paperCentres 13170)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13170)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13170)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13170)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13170)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13170)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13170

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13170
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13170 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13170 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13170 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13170 13170 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13170)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13170)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13170
  have hb0 := BstLean.Part150.betaJ_nonneg 13170
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13170 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13170 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13170 * BstLean.Part150.betaJ 13170) * 13170) ≤
      (163187253 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13170)) * 13170 := by gcongr <;> linarith
      _ ≤ ((163187253 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13170 * 13170 *
      (1 + BstLean.Part154.deltaChi 13170 12 + 2 / π) / BstLean.Part154.csC) ≤
      (186787663 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13170 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((186787663 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13170 : ℝ) / BstLean.Part154.csC) ≤ (25209417 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13170 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((25209417 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13170 : ℝ) * (163187253 / 1000000) +
        2 * (1792 / 10000 / 13170) * (186787663 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (25209417 / 250000) *
          (81 / 1000 / 13170 + (1792 / 10000 / 13170) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13170

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13170
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13170 ∧
    1 ≤ gPlus 13170 ∧ gPlus 13170 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13170 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13170 : ℝ) < √(1 - 2 / (13170 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13170 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13170 (gMinus 13170) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13170 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13170 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13170 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13170)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13170 (gMinus 13170) (gPlus 13170)
      (finiteEnergy 13170 13170 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13170 (gMinus 13170) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13170 (gMinus 13170) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13170 (gMinus 13170) (54 / 100))
    (by linarith : energyRatio 13170 (gMinus 13170) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13170 (gMinus 13170) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13170 * kappa (energyRatio 13170 (gMinus 13170) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13170) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13170 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13170 13170 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13170 13170 (11 / 1000) / √13170 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13170)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13170 * kappa (energyRatio 13170 (gMinus 13170) (54 / 100))) +
      2 * √(12 * gPlus 13170) / 13170 + finiteEnergy 13170 13170 (11 / 1000) / √13170 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13170 θ ∧ meanLowerRoot 13170 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13170 - 2 / (13170 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13170 - 2 / (13170 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13170 θ ^ 2 / gPlus 13170) - 2 / (13170 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13170 * (kappa (meanLowerRoot 13170 θ ^ 2 / gPlus 13170) -
        2 / (13170 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13170) / 13170 -
        finiteEnergy 13170 13170 (11 / 1000) / √13170 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13170 θ ^ 2 / gPlus 13170 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13170)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13170 θ ^ 2 / gPlus 13170 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13170)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13170 θ ^ 2 / gPlus 13170 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13170 ^ 2 ≤
      kappa (meanLowerRoot 13170 θ ^ 2 / gPlus 13170) - 2 / (13170 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13170 *
      (kappa (meanLowerRoot 13170 θ ^ 2 / gPlus 13170) - 2 / (13170 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13170 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13170)
    linarith
  have ht : √(12 * gPlus 13170) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13170 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13170 13170 (11 / 1000) / √13170 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13170)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13170 (gMinus 13170) (gPlus 13170)
      (finiteEnergy 13170 13170 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13170) (hτ : 0 < (paperDesignP 13170).tau0 c) :
    eR c = (2 / (mA 13170 : ℝ)) *
      normSq (BstLean.Part150.bT 13170 13170 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13170).tau0 c)) /
      (2 / (13170 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13170).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13170).tau0 c))⁻¹ •
      BstLean.Part150.bT 13170 13170 (A1 c) (A2 c) c.1.2 ((paperDesignP 13170).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13170 : ℝ)) * normSq (bR c) / (2 / (13170 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13170}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13170) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13170).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13170 : ℝ) * (paperDesignP 13170).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13170 13170 c.1.2 ((paperDesignP 13170).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13170

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13171
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13171 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13171).real (BstLean.Part211.CentreSource 13171 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13171) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13171 160 (6 / 1000)
  have hj := jS_160_le (n := 13171) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13171 160 (6 / 1000) ^ 2 * 13171 /
      (((13171 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13171 160 (6 / 1000) ^ 2 * 13171 /
      (((13171 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13171 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13171 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13171) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13171 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13171

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13171
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13171) :=
  Ethm (paperCentres 13171) ∩ Ethp (paperCentres 13171)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13171)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13171)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13171) (paperCentres 13171)
  have he : exp (-(45 / 10000 * (13171 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13171 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13171) :=
  (passEvent ∩ agentEv (paperDesignP 13171) (DirectionError 13171) ∩
    agentEv (paperDesignP 13171) (CentreSources 13171 13171)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13171)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13171) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13171) hτ
  have hC := centreSources_ret_charge_row 13171 (paperDesignP 13171) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13171)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13171) (CentreSources 13171 13171)
  direction : analyticBase ⊆ agentEv (paperDesignP 13171) (DirectionError 13171)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13171)) : Set (Ret 13171) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13171)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13171)}
    (hT : (retDist (paperCentres 13171)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13171)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13171)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13171)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13171)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13171)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13171

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13171
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13171 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13171 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13171 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13171 13171 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13171)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13171)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13171
  have hb0 := BstLean.Part150.betaJ_nonneg 13171
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13171 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13171 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13171 * BstLean.Part150.betaJ 13171) * 13171) ≤
      (163193449 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13171)) * 13171 := by gcongr <;> linarith
      _ ≤ ((163193449 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13171 * 13171 *
      (1 + BstLean.Part154.deltaChi 13171 12 + 2 / π) / BstLean.Part154.csC) ≤
      (93397377 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13171 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((93397377 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13171 : ℝ) / BstLean.Part154.csC) ≤ (100841497 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13171 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100841497 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13171 : ℝ) * (163193449 / 1000000) +
        2 * (1792 / 10000 / 13171) * (93397377 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100841497 / 1000000) *
          (81 / 1000 / 13171 + (1792 / 10000 / 13171) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13171

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13171
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13171 ∧
    1 ≤ gPlus 13171 ∧ gPlus 13171 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13171 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13171 : ℝ) < √(1 - 2 / (13171 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13171 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13171 (gMinus 13171) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13171 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13171 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13171 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13171)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13171 (gMinus 13171) (gPlus 13171)
      (finiteEnergy 13171 13171 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13171 (gMinus 13171) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13171 (gMinus 13171) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13171 (gMinus 13171) (54 / 100))
    (by linarith : energyRatio 13171 (gMinus 13171) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13171 (gMinus 13171) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13171 * kappa (energyRatio 13171 (gMinus 13171) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13171) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13171 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13171 13171 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13171 13171 (11 / 1000) / √13171 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13171)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13171 * kappa (energyRatio 13171 (gMinus 13171) (54 / 100))) +
      2 * √(12 * gPlus 13171) / 13171 + finiteEnergy 13171 13171 (11 / 1000) / √13171 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13171 θ ∧ meanLowerRoot 13171 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13171 - 2 / (13171 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13171 - 2 / (13171 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13171 θ ^ 2 / gPlus 13171) - 2 / (13171 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13171 * (kappa (meanLowerRoot 13171 θ ^ 2 / gPlus 13171) -
        2 / (13171 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13171) / 13171 -
        finiteEnergy 13171 13171 (11 / 1000) / √13171 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13171 θ ^ 2 / gPlus 13171 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13171)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13171 θ ^ 2 / gPlus 13171 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13171)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13171 θ ^ 2 / gPlus 13171 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13171 ^ 2 ≤
      kappa (meanLowerRoot 13171 θ ^ 2 / gPlus 13171) - 2 / (13171 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13171 *
      (kappa (meanLowerRoot 13171 θ ^ 2 / gPlus 13171) - 2 / (13171 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13171 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13171)
    linarith
  have ht : √(12 * gPlus 13171) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13171 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13171 13171 (11 / 1000) / √13171 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13171)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13171 (gMinus 13171) (gPlus 13171)
      (finiteEnergy 13171 13171 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13171) (hτ : 0 < (paperDesignP 13171).tau0 c) :
    eR c = (2 / (mA 13171 : ℝ)) *
      normSq (BstLean.Part150.bT 13171 13171 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13171).tau0 c)) /
      (2 / (13171 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13171).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13171).tau0 c))⁻¹ •
      BstLean.Part150.bT 13171 13171 (A1 c) (A2 c) c.1.2 ((paperDesignP 13171).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13171 : ℝ)) * normSq (bR c) / (2 / (13171 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13171}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13171) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13171).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13171 : ℝ) * (paperDesignP 13171).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13171 13171 c.1.2 ((paperDesignP 13171).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13171

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13172
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13172 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13172).real (BstLean.Part211.CentreSource 13172 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13172) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13172 160 (6 / 1000)
  have hj := jS_160_le (n := 13172) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13172 160 (6 / 1000) ^ 2 * 13172 /
      (((13172 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13172 160 (6 / 1000) ^ 2 * 13172 /
      (((13172 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13172 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13172 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13172) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13172 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13172

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13172
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13172) :=
  Ethm (paperCentres 13172) ∩ Ethp (paperCentres 13172)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13172)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13172)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13172) (paperCentres 13172)
  have he : exp (-(45 / 10000 * (13172 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13172 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13172) :=
  (passEvent ∩ agentEv (paperDesignP 13172) (DirectionError 13172) ∩
    agentEv (paperDesignP 13172) (CentreSources 13172 13172)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13172)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13172) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13172) hτ
  have hC := centreSources_ret_charge_row 13172 (paperDesignP 13172) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13172)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13172) (CentreSources 13172 13172)
  direction : analyticBase ⊆ agentEv (paperDesignP 13172) (DirectionError 13172)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13172)) : Set (Ret 13172) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13172)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13172)}
    (hT : (retDist (paperCentres 13172)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13172)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13172)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13172)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13172)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13172)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13172

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13172
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13172 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13172 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13172 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13172 13172 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13172)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13172)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13172
  have hb0 := BstLean.Part150.betaJ_nonneg 13172
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13172 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13172 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13172 * BstLean.Part150.betaJ 13172) * 13172) ≤
      (40799911 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13172)) * 13172 := by gcongr <;> linarith
      _ ≤ ((40799911 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13172 * 13172 *
      (1 + BstLean.Part154.deltaChi 13172 12 + 2 / π) / BstLean.Part154.csC) ≤
      (37360369 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13172 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((37360369 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13172 : ℝ) / BstLean.Part154.csC) ≤ (4033813 / 40000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13172 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((4033813 / 40000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13172 : ℝ) * (40799911 / 250000) +
        2 * (1792 / 10000 / 13172) * (37360369 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (4033813 / 40000) *
          (81 / 1000 / 13172 + (1792 / 10000 / 13172) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13172

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13172
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13172 ∧
    1 ≤ gPlus 13172 ∧ gPlus 13172 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13172 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13172 : ℝ) < √(1 - 2 / (13172 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13172 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13172 (gMinus 13172) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13172 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13172 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13172 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13172)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13172 (gMinus 13172) (gPlus 13172)
      (finiteEnergy 13172 13172 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13172 (gMinus 13172) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13172 (gMinus 13172) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13172 (gMinus 13172) (54 / 100))
    (by linarith : energyRatio 13172 (gMinus 13172) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13172 (gMinus 13172) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13172 * kappa (energyRatio 13172 (gMinus 13172) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13172) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13172 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13172 13172 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13172 13172 (11 / 1000) / √13172 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13172)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13172 * kappa (energyRatio 13172 (gMinus 13172) (54 / 100))) +
      2 * √(12 * gPlus 13172) / 13172 + finiteEnergy 13172 13172 (11 / 1000) / √13172 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13172 θ ∧ meanLowerRoot 13172 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13172 - 2 / (13172 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13172 - 2 / (13172 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13172 θ ^ 2 / gPlus 13172) - 2 / (13172 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13172 * (kappa (meanLowerRoot 13172 θ ^ 2 / gPlus 13172) -
        2 / (13172 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13172) / 13172 -
        finiteEnergy 13172 13172 (11 / 1000) / √13172 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13172 θ ^ 2 / gPlus 13172 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13172)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13172 θ ^ 2 / gPlus 13172 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13172)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13172 θ ^ 2 / gPlus 13172 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13172 ^ 2 ≤
      kappa (meanLowerRoot 13172 θ ^ 2 / gPlus 13172) - 2 / (13172 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13172 *
      (kappa (meanLowerRoot 13172 θ ^ 2 / gPlus 13172) - 2 / (13172 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13172 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13172)
    linarith
  have ht : √(12 * gPlus 13172) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13172 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13172 13172 (11 / 1000) / √13172 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13172)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13172 (gMinus 13172) (gPlus 13172)
      (finiteEnergy 13172 13172 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13172) (hτ : 0 < (paperDesignP 13172).tau0 c) :
    eR c = (2 / (mA 13172 : ℝ)) *
      normSq (BstLean.Part150.bT 13172 13172 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13172).tau0 c)) /
      (2 / (13172 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13172).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13172).tau0 c))⁻¹ •
      BstLean.Part150.bT 13172 13172 (A1 c) (A2 c) c.1.2 ((paperDesignP 13172).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13172 : ℝ)) * normSq (bR c) / (2 / (13172 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13172}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13172) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13172).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13172 : ℝ) * (paperDesignP 13172).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13172 13172 c.1.2 ((paperDesignP 13172).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13172

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13173
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13173 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13173).real (BstLean.Part211.CentreSource 13173 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13173) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13173 160 (6 / 1000)
  have hj := jS_160_le (n := 13173) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13173 160 (6 / 1000) ^ 2 * 13173 /
      (((13173 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13173 160 (6 / 1000) ^ 2 * 13173 /
      (((13173 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13173 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13173 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13173) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13173 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13173

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13173
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13173) :=
  Ethm (paperCentres 13173) ∩ Ethp (paperCentres 13173)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13173)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13173)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13173) (paperCentres 13173)
  have he : exp (-(45 / 10000 * (13173 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13173 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13173) :=
  (passEvent ∩ agentEv (paperDesignP 13173) (DirectionError 13173) ∩
    agentEv (paperDesignP 13173) (CentreSources 13173 13173)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13173)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13173) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13173) hτ
  have hC := centreSources_ret_charge_row 13173 (paperDesignP 13173) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13173)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13173) (CentreSources 13173 13173)
  direction : analyticBase ⊆ agentEv (paperDesignP 13173) (DirectionError 13173)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13173)) : Set (Ret 13173) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13173)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13173)}
    (hT : (retDist (paperCentres 13173)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13173)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13173)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13173)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13173)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13173)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13173

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13173
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13173 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13173 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13173 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13173 13173 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13173)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13173)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13173
  have hb0 := BstLean.Part150.betaJ_nonneg 13173
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13173 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13173 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13173 * BstLean.Part150.betaJ 13173) * 13173) ≤
      (81602919 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13173)) * 13173 := by gcongr <;> linarith
      _ ≤ ((81602919 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13173 * 13173 *
      (1 + BstLean.Part154.deltaChi 13173 12 + 2 / π) / BstLean.Part154.csC) ≤
      (23351117 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13173 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((23351117 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13173 : ℝ) / BstLean.Part154.csC) ≤ (100849153 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13173 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100849153 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13173 : ℝ) * (81602919 / 500000) +
        2 * (1792 / 10000 / 13173) * (23351117 / 125000) +
        4 * (1 / 2.506628) * 1.036505 * (100849153 / 1000000) *
          (81 / 1000 / 13173 + (1792 / 10000 / 13173) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13173

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13173
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13173 ∧
    1 ≤ gPlus 13173 ∧ gPlus 13173 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13173 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13173 : ℝ) < √(1 - 2 / (13173 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13173 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13173 (gMinus 13173) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13173 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13173 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13173 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13173)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13173 (gMinus 13173) (gPlus 13173)
      (finiteEnergy 13173 13173 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13173 (gMinus 13173) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13173 (gMinus 13173) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13173 (gMinus 13173) (54 / 100))
    (by linarith : energyRatio 13173 (gMinus 13173) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13173 (gMinus 13173) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13173 * kappa (energyRatio 13173 (gMinus 13173) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13173) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13173 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13173 13173 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13173 13173 (11 / 1000) / √13173 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13173)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13173 * kappa (energyRatio 13173 (gMinus 13173) (54 / 100))) +
      2 * √(12 * gPlus 13173) / 13173 + finiteEnergy 13173 13173 (11 / 1000) / √13173 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13173 θ ∧ meanLowerRoot 13173 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13173 - 2 / (13173 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13173 - 2 / (13173 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13173 θ ^ 2 / gPlus 13173) - 2 / (13173 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13173 * (kappa (meanLowerRoot 13173 θ ^ 2 / gPlus 13173) -
        2 / (13173 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13173) / 13173 -
        finiteEnergy 13173 13173 (11 / 1000) / √13173 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13173 θ ^ 2 / gPlus 13173 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13173)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13173 θ ^ 2 / gPlus 13173 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13173)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13173 θ ^ 2 / gPlus 13173 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13173 ^ 2 ≤
      kappa (meanLowerRoot 13173 θ ^ 2 / gPlus 13173) - 2 / (13173 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13173 *
      (kappa (meanLowerRoot 13173 θ ^ 2 / gPlus 13173) - 2 / (13173 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13173 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13173)
    linarith
  have ht : √(12 * gPlus 13173) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13173 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13173 13173 (11 / 1000) / √13173 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13173)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13173 (gMinus 13173) (gPlus 13173)
      (finiteEnergy 13173 13173 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13173) (hτ : 0 < (paperDesignP 13173).tau0 c) :
    eR c = (2 / (mA 13173 : ℝ)) *
      normSq (BstLean.Part150.bT 13173 13173 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13173).tau0 c)) /
      (2 / (13173 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13173).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13173).tau0 c))⁻¹ •
      BstLean.Part150.bT 13173 13173 (A1 c) (A2 c) c.1.2 ((paperDesignP 13173).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13173 : ℝ)) * normSq (bR c) / (2 / (13173 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13173}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13173) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13173).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13173 : ℝ) * (paperDesignP 13173).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13173 13173 c.1.2 ((paperDesignP 13173).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13173

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13174
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13174 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13174).real (BstLean.Part211.CentreSource 13174 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13174) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13174 160 (6 / 1000)
  have hj := jS_160_le (n := 13174) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13174 160 (6 / 1000) ^ 2 * 13174 /
      (((13174 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13174 160 (6 / 1000) ^ 2 * 13174 /
      (((13174 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13174 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13174 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13174) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13174 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13174

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13174
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13174) :=
  Ethm (paperCentres 13174) ∩ Ethp (paperCentres 13174)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13174)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13174)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13174) (paperCentres 13174)
  have he : exp (-(45 / 10000 * (13174 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13174 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13174) :=
  (passEvent ∩ agentEv (paperDesignP 13174) (DirectionError 13174) ∩
    agentEv (paperDesignP 13174) (CentreSources 13174 13174)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13174)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13174) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13174) hτ
  have hC := centreSources_ret_charge_row 13174 (paperDesignP 13174) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13174)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13174) (CentreSources 13174 13174)
  direction : analyticBase ⊆ agentEv (paperDesignP 13174) (DirectionError 13174)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13174)) : Set (Ret 13174) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13174)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13174)}
    (hT : (retDist (paperCentres 13174)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13174)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13174)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13174)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13174)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13174)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13174

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13174
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13174 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13174 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13174 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13174 13174 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13174)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13174)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13174
  have hb0 := BstLean.Part150.betaJ_nonneg 13174
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13174 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13174 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13174 * BstLean.Part150.betaJ 13174) * 13174) ≤
      (163212033 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13174)) * 13174 := by gcongr <;> linarith
      _ ≤ ((163212033 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13174 * 13174 *
      (1 + BstLean.Part154.deltaChi 13174 12 + 2 / π) / BstLean.Part154.csC) ≤
      (93408013 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13174 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((93408013 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13174 : ℝ) / BstLean.Part154.csC) ≤ (5042649 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13174 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((5042649 / 50000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13174 : ℝ) * (163212033 / 1000000) +
        2 * (1792 / 10000 / 13174) * (93408013 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (5042649 / 50000) *
          (81 / 1000 / 13174 + (1792 / 10000 / 13174) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13174

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13174
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13174 ∧
    1 ≤ gPlus 13174 ∧ gPlus 13174 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13174 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13174 : ℝ) < √(1 - 2 / (13174 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13174 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13174 (gMinus 13174) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13174 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13174 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13174 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13174)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13174 (gMinus 13174) (gPlus 13174)
      (finiteEnergy 13174 13174 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13174 (gMinus 13174) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13174 (gMinus 13174) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13174 (gMinus 13174) (54 / 100))
    (by linarith : energyRatio 13174 (gMinus 13174) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13174 (gMinus 13174) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13174 * kappa (energyRatio 13174 (gMinus 13174) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13174) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13174 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13174 13174 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13174 13174 (11 / 1000) / √13174 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13174)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13174 * kappa (energyRatio 13174 (gMinus 13174) (54 / 100))) +
      2 * √(12 * gPlus 13174) / 13174 + finiteEnergy 13174 13174 (11 / 1000) / √13174 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13174 θ ∧ meanLowerRoot 13174 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13174 - 2 / (13174 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13174 - 2 / (13174 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13174 θ ^ 2 / gPlus 13174) - 2 / (13174 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13174 * (kappa (meanLowerRoot 13174 θ ^ 2 / gPlus 13174) -
        2 / (13174 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13174) / 13174 -
        finiteEnergy 13174 13174 (11 / 1000) / √13174 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13174 θ ^ 2 / gPlus 13174 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13174)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13174 θ ^ 2 / gPlus 13174 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13174)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13174 θ ^ 2 / gPlus 13174 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13174 ^ 2 ≤
      kappa (meanLowerRoot 13174 θ ^ 2 / gPlus 13174) - 2 / (13174 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13174 *
      (kappa (meanLowerRoot 13174 θ ^ 2 / gPlus 13174) - 2 / (13174 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13174 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13174)
    linarith
  have ht : √(12 * gPlus 13174) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13174 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13174 13174 (11 / 1000) / √13174 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13174)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13174 (gMinus 13174) (gPlus 13174)
      (finiteEnergy 13174 13174 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13174) (hτ : 0 < (paperDesignP 13174).tau0 c) :
    eR c = (2 / (mA 13174 : ℝ)) *
      normSq (BstLean.Part150.bT 13174 13174 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13174).tau0 c)) /
      (2 / (13174 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13174).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13174).tau0 c))⁻¹ •
      BstLean.Part150.bT 13174 13174 (A1 c) (A2 c) c.1.2 ((paperDesignP 13174).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13174 : ℝ)) * normSq (bR c) / (2 / (13174 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13174}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13174) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13174).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13174 : ℝ) * (paperDesignP 13174).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13174 13174 c.1.2 ((paperDesignP 13174).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13174
